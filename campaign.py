"""Dependency-aware, auditable research campaigns layered over the existing harness.

Numerical evidence and literature never satisfy a proof dependency. Contracts are
compiled BEFORE candidate modules, and checked from a fresh module afterwards.
"""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import uuid

import harness as H

IDENT = re.compile(r'^[A-Za-z][A-Za-z0-9_]*$')
MODULE = re.compile(r'^(Mathlib|Batteries|Init)(\.[A-Za-z0-9_]+)*$')
PROOF_KINDS = {'lemma', 'target'}
SCOPES = {'infrastructure', 'special_case', 'conditional', 'general'}


def digest(value):
    data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True).encode()
    return hashlib.sha256(data).hexdigest()


def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    tmp.write_text(json.dumps(value, indent=2))
    tmp.replace(path)


def validate(plan):
    if plan.get('schema_version') != 1 or not IDENT.fullmatch(plan.get('id', '')):
        raise ValueError('campaign requires schema_version=1 and a safe identifier')
    nodes = plan.get('nodes', [])
    ids = [n.get('id', '') for n in nodes]
    if len(ids) != len(set(ids)) or any(not IDENT.fullmatch(i) for i in ids):
        raise ValueError('node identifiers must be unique and safe')
    by_id = {n['id']: n for n in nodes}
    for n in nodes:
        if n.get('kind') not in PROOF_KINDS | {'gap', 'experiment', 'literature'}:
            raise ValueError('unknown node kind')
        if n.get('scope') not in SCOPES:
            raise ValueError('explicit scope required')
        for dep in n.get('depends_on', []):
            if dep not in by_id:
                raise ValueError(f'unknown dependency {dep}')
            if by_id[dep]['kind'] in {'experiment', 'literature'}:
                raise ValueError('empirical/literature evidence cannot be a proof dependency; use evidence_for')
        for dst in n.get('evidence_for', []):
            if dst not in by_id:
                raise ValueError('unknown evidence target')
        for imp in n.get('imports', []):
            if not MODULE.fullmatch(imp):
                raise ValueError(f'unsupported contract import: {imp}')
        if n.get('type') and n['kind'] not in PROOF_KINDS:
            raise ValueError('only formal proof nodes have Lean contracts')
    visiting, visited = set(), set()
    def visit(i):
        if i in visiting:
            raise ValueError('cyclic proof dependencies')
        if i in visited:
            return
        visiting.add(i)
        for dep in by_id[i].get('depends_on', []):
            visit(dep)
        visiting.remove(i)
        visited.add(i)
    for i in ids:
        visit(i)
    roots = plan.get('targets', [])
    if not roots or any(i not in by_id or by_id[i]['kind'] != 'target' for i in roots):
        raise ValueError('targets must name target nodes')
    budget = plan.get('budget', {})
    for key in ('model_calls', 'lean_checks', 'wall_seconds'):
        if not isinstance(budget.get(key), (int, float)) or budget[key] <= 0:
            raise ValueError(f'positive campaign budget required: {key}')
    return by_id


class BudgetStop(RuntimeError):
    pass


class Campaign:
    def __init__(self, manifest):
        self.manifest = Path(manifest).resolve()
        self.plan = json.loads(self.manifest.read_text())
        self.nodes = validate(self.plan)
        self.root = self.manifest.parent / 'work'
        self.root.mkdir(exist_ok=True)
        self.environment = {p: digest((H.FORMAL / p).read_bytes())
                            for p in ('lean-toolchain', 'lake-manifest.json')}
        self.environment['verifier'] = digest(Path(__file__).read_bytes())
        self.environment['harness'] = digest(Path(H.__file__).read_bytes())

    @contextmanager
    def locked_state(self):
        with (self.root / 'state.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            p = self.root / 'state.json'
            state = json.loads(p.read_text()) if p.exists() else {'certificates': {}, 'evidence': [], 'usage': []}
            yield state
            atomic(p, state)

    def reserve(self, kind, timeout):
        # Charge a crash's full reservation until explicitly investigated. A
        # restart cannot erase already consumed requests or pending reservations.
        with self.locked_state() as state:
            entries = state['usage']
            limit = self.plan['budget']
            count = sum(e['kind'] == kind for e in entries)
            if count >= limit[kind]:
                raise BudgetStop(f'campaign {kind} budget exhausted')
            remaining = limit['wall_seconds'] - sum(e['seconds'] for e in entries)
            if remaining < 1:
                raise BudgetStop('campaign wall-clock allowance exhausted')
            allowance = min(timeout, remaining)
            token = uuid.uuid4().hex
            entries.append({'id': token, 'kind': kind, 'seconds': allowance, 'pending': True, 'at': H.now()})
        return token, allowance

    def settle(self, token, seconds):
        with self.locked_state() as state:
            entry = next(e for e in state['usage'] if e['id'] == token)
            entry.update(seconds=min(seconds, entry['seconds']), pending=False)

    def fingerprint(self, node_id):
        node = self.nodes[node_id]
        return digest({'node': node, 'environment': self.environment,
                       'dependencies': {i: self.fingerprint(i) for i in node.get('depends_on', [])}})

    def fresh(self, node_id, certs):
        cert = certs.get(node_id)
        if (not cert or cert.get('fingerprint') != self.fingerprint(node_id)
                or len(cert.get('files', {})) != 6
                or cert.get('certificate_hash') != digest({k: v for k, v in cert.items() if k != 'certificate_hash'})
                or set(cert.get('dependencies', {})) != set(self.nodes[node_id].get('depends_on', []))):
            return False
        for path, sha in cert.get('files', {}).items():
            p = Path(path)
            if not p.exists() or digest(p.read_bytes()) != sha:
                return False
        return all(self.fresh(d, certs) and
                   cert['dependencies'].get(d) == certs[d]['certificate_hash']
                   for d in self.nodes[node_id].get('depends_on', []))

    def status(self):
        with self.locked_state() as state:
            certs = state['certificates']
            rows = []
            for i, node in self.nodes.items():
                blocked = [d for d in node.get('depends_on', []) if not self.fresh(d, certs)]
                status = ('verified' if self.fresh(i, certs) else
                          'needs_formalization' if not node.get('type') and node['kind'] in PROOF_KINDS | {'gap'} else
                          'evidence_only' if node['kind'] in {'experiment', 'literature'} else
                          'blocked' if blocked else 'ready')
                rows.append({'id': i, 'status': status, 'scope': node['scope'], 'blocked_by': blocked,
                             'priority': node.get('priority', 0), 'claim': node.get('claim', '')})
            complete = all(self.fresh(i, certs) and self.nodes[i]['scope'] == 'general' for i in self.plan['targets'])
            return {'campaign': self.plan['id'], 'formal_targets_verified': complete, 'meaning_review': 'required independently of kernel verification', 'nodes': rows,
                    'model_calls': sum(e['kind'] == 'model_calls' for e in state['usage']),
                    'lean_checks': sum(e['kind'] == 'lean_checks' for e in state['usage']),
                    'charged_seconds': round(sum(e['seconds'] for e in state['usage']), 2),
                    'evidence_records': len(state['evidence'])}

    def next(self):
        # Favor ready work that unlocks the most downstream nodes, with an
        # explicit priority for essential library/API work.
        def descendants(i):
            seen = set()
            todo = [i]
            while todo:
                parent = todo.pop()
                for j, n in self.nodes.items():
                    if parent in n.get('depends_on', []) and j not in seen:
                        seen.add(j); todo.append(j)
            return len(seen)
        rows = self.status()['nodes']
        ready = [r for r in rows if r['status'] == 'ready']
        return sorted(ready, key=lambda r: (-r['priority'], -descendants(r['id']), r['id']))

    def record_evidence(self, node_id, path, description):
        if node_id not in self.nodes:
            raise ValueError('unknown evidence node')
        source = Path(path).resolve()
        sha = digest(source.read_bytes())
        dest = self.root / 'evidence' / (sha + source.suffix)
        dest.parent.mkdir(exist_ok=True); dest.write_bytes(source.read_bytes())
        entry = {'node': node_id, 'kind': 'unverified_evidence', 'description': description,
                 'sha256': sha, 'path': str(dest), 'at': H.now()}
        with self.locked_state() as state:
            state['evidence'].append(entry)
        return entry

    def _compile(self, module, text, folder, label, timeout):
        path = H.FORMAL.joinpath(*module.split('.')).with_suffix('.lean')
        olean = (H.FORMAL / '.lake/build/lib/lean').joinpath(*module.split('.')).with_suffix('.olean')
        path.parent.mkdir(parents=True, exist_ok=True); olean.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        token, allowance = self.reserve('lean_checks', timeout)
        started = time.monotonic()
        try:
            result = subprocess.run(['lake', 'env', 'lean', '-o', str(olean), str(path)],
                                    cwd=H.FORMAL, env=H.clean_env(), capture_output=True, text=True, timeout=allowance)
            raw = result.stdout + '\n' + result.stderr
            ok = result.returncode == 0 and not re.search(r"declaration uses [`']sorry", raw)
        except subprocess.TimeoutExpired:
            raw, ok = 'Lean timeout', False
        finally:
            self.settle(token, time.monotonic() - started)
        (folder / (label + '.log')).write_text(raw)
        (folder / (label + '.lean')).write_text(text)
        return ok, raw, [path, olean] if ok else [path]

    def verify(self, node_id, candidate, timeout=420):
        node = self.nodes[node_id]
        if node['kind'] not in PROOF_KINDS or not node.get('type'):
            raise ValueError('a precise formal proof contract is required before proof search')
        with self.locked_state() as state:
            certs = state['certificates']
            if any(not self.fresh(d, certs) for d in node.get('depends_on', [])):
                raise ValueError('proof dependencies are missing or stale')
            deps = {d: certs[d] for d in node.get('depends_on', [])}
        body = Path(candidate).read_text()
        # Candidate modules cannot run arbitrary elaborator IO or alter compiler
        # verification. Definitions and ordinary proof tactics remain available.
        clean = H.strip_comment_lines(body)
        forbidden = H.has_banned(body) or (re.search(
            r'\b(run_cmd|run_tac|initialize|elab|macro|syntax|unsafe|set_option)\b|^\s*#', clean, re.M) and 'metaprogramming/commands')
        if forbidden:
            return {'verified': False, 'errors': f'candidate rejected: {forbidden}'}
        for imp in H.import_lines(body):
            if not MODULE.fullmatch(imp):
                return {'verified': False, 'errors': 'candidate may only add standard library imports'}
        attempt = self.root / 'attempts' / node_id / uuid.uuid4().hex
        attempt.mkdir(parents=True)
        prefix = 'Formal.Campaigns.R' + digest({'id': self.plan['id'], 'node': node_id,
                                              'fingerprint': self.fingerprint(node_id), 'body': body})[:24]
        contract_mod, proof_mod, audit_mod = (prefix + '.' + k for k in ('Contract', 'Proof', 'Audit'))
        imports = list(dict.fromkeys(node.get('imports', []) + [c['module'] for c in deps.values()]))
        header = '\n'.join('import ' + m for m in imports) + '\nset_option autoImplicit false\n'
        # The expected type is elaborated in a separate module that has never
        # imported the candidate, preventing candidate notation/instances from
        # silently changing the contract's meaning.
        contract = header + f'namespace {prefix}\ndef Target : Prop :=\n{node["type"]}\nend {prefix}\n'
        ok, raw, files = self._compile(contract_mod, contract, attempt, 'contract', timeout)
        if not ok:
            return {'verified': False, 'errors': raw, 'stage': 'contract', 'attempt': str(attempt)}
        proof_imports = list(dict.fromkeys(H.import_lines(body) + node.get('imports', [])))
        proof_header = '\n'.join('import ' + m for m in proof_imports + [contract_mod])
        proof = proof_header + f'\nset_option autoImplicit false\nnamespace {prefix}\n' + H.strip_imports(body) + f'\nend {prefix}\n'
        ok, raw, pf = self._compile(proof_mod, proof, attempt, 'proof', timeout); files += pf
        if not ok:
            return {'verified': False, 'errors': raw, 'stage': 'proof', 'attempt': str(attempt)}
        audit = f'import {proof_mod}\nset_option autoImplicit false\nexample : {prefix}.Target := @{prefix}.result\n#print axioms {prefix}.result\n'
        ok, raw, af = self._compile(audit_mod, audit, attempt, 'audit', timeout); files += af
        m = re.search(r'depends on axioms:\s*\[([^\]]*)\]', raw)
        axioms = {v.strip() for v in m.group(1).split(',') if v.strip()} if m else (
            set() if 'does not depend on any axioms' in raw else {'UNKNOWN'})
        if not ok or not axioms <= H.STD_AXIOMS:
            return {'verified': False, 'errors': raw, 'stage': 'audit', 'axioms': sorted(axioms), 'attempt': str(attempt)}
        cert = {'fingerprint': self.fingerprint(node_id), 'module': proof_mod, 'declaration': prefix + '.result',
                'type': node['type'], 'scope': node['scope'], 'axioms': sorted(axioms), 'at': H.now(),
                'files': {str(p): digest(p.read_bytes()) for p in files}, 'attempt': str(attempt),
                'dependencies': {d: c['certificate_hash'] for d, c in deps.items()}}
        cert['certificate_hash'] = digest(cert)
        with self.locked_state() as state:
            # No concurrent dependency replacement may slip through certification.
            if any(not self.fresh(d, state['certificates']) or
                   state['certificates'][d]['certificate_hash'] != c['certificate_hash'] for d, c in deps.items()):
                raise ValueError('dependency changed during verification')
            state['certificates'][node_id] = cert
        atomic(attempt / 'certificate.json', cert)
        return {'verified': True, 'certificate': cert}

    def run_node(self, node_id, backend, rounds=3, timeout=420):
        if node_id not in {r['id'] for r in self.next()}:
            raise ValueError('node is not ready; resolve its contract/dependencies first')
        node = self.nodes[node_id]
        checkpoint = self.root / ('repair-' + node_id + '.json')
        previous = json.loads(checkpoint.read_text()) if checkpoint.exists() else {}
        if previous.get('fingerprint') != self.fingerprint(node_id):
            previous = {}
        with self.locked_state() as state:
            deps = {d: state['certificates'][d]['declaration'] for d in node.get('depends_on', [])}
        for _ in range(rounds):
            prompt = (f'Prove this exact Lean proposition for research node {node_id}.\n'
                      f'Claim scope: {node["scope"]}. This node is not the whole research conjecture.\n'
                      f'Imports: {node.get("imports", [])}\nType:\n{node["type"]}\n'
                      f'Verified dependency declarations: {deps}\n'
                      'Return one ```lean block with theorem result : <the exact type above> := by ... . '
                      'Helpers are allowed. No sorry, axioms, metaprogramming commands or set_option. '
                      'Preserve the latest candidate and repair its exact errors.\n'
                      f'Latest candidate:\n{previous.get("candidate", "(none)")}\n'
                      f'Compiler feedback:\n{previous.get("errors", "(none)")}')
            token, allowance = self.reserve('model_calls', backend.timeout)
            started = time.monotonic()
            old_timeout = backend.timeout
            backend.timeout = allowance
            request_dir = self.root / 'requests' / token
            request_dir.mkdir(parents=True)
            (request_dir / 'prompt.txt').write_text(prompt)
            atomic(request_dir / 'metadata.json', {'node': node_id, 'fingerprint': self.fingerprint(node_id),
                   'backend': type(backend).__name__, 'model': getattr(backend, 'model', None), 'at': H.now()})
            try:
                answer = backend.complete('prove', prompt)
                (request_dir / 'response.txt').write_text(answer)
            except Exception as exc:
                (request_dir / 'error.txt').write_text(str(exc))
                raise
            finally:
                backend.timeout = old_timeout
                self.settle(token, time.monotonic() - started)
            blocks = H.lean_blocks(answer)
            if not blocks:
                continue
            body = max(blocks, key=len)
            candidate = self.root / ('candidate-' + node_id + '.lean'); candidate.write_text(body)
            result = self.verify(node_id, candidate, timeout)
            previous = {'fingerprint': self.fingerprint(node_id), 'candidate': body, 'errors': result.get('errors', '')}
            atomic(checkpoint, previous)
            if result['verified']:
                return result
        return {'verified': False, 'errors': previous.get('errors', 'no candidate')}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['status', 'next', 'verify', 'run', 'evidence'])
    ap.add_argument('--manifest', required=True)
    ap.add_argument('--node')
    ap.add_argument('--candidate')
    ap.add_argument('--description', default='')
    ap.add_argument('--rounds', type=int, default=3)
    ap.add_argument('--lean-timeout', type=int, default=420)
    ap.add_argument('--llm-timeout', type=int, default=600)
    ap.add_argument('--backend', choices=['codex-cli', 'claude-cli'], default='claude-cli')
    ap.add_argument('--model')
    args = ap.parse_args(argv)
    if args.action in {'verify', 'run', 'evidence'} and not args.node:
        ap.error('--node is required for this action')
    if args.action in {'verify', 'evidence'} and not args.candidate:
        ap.error('--candidate is required for this action')
    if min(args.rounds, args.lean_timeout, args.llm_timeout) <= 0:
        ap.error('rounds and timeouts must be positive')
    try:
        c = Campaign(args.manifest)
        if args.node and args.node not in c.nodes:
            raise ValueError('unknown campaign node')
        if args.action == 'status': result = c.status()
        elif args.action == 'next': result = c.next()
        elif args.action == 'evidence': result = c.record_evidence(args.node, args.candidate, args.description)
        elif args.action == 'verify': result = c.verify(args.node, args.candidate, args.lean_timeout)
        else:
            backend = H.CodexCliBackend(args.model, args.llm_timeout) if args.backend == 'codex-cli' else H.ClaudeCliBackend(args.model, args.llm_timeout)
            result = c.run_node(args.node, backend, args.rounds, args.lean_timeout)
    except BudgetStop as e:
        result = {'verified': False, 'budget_stop': str(e)}
    except (ValueError, OSError) as e:
        result = {'verified': False, 'error': str(e)}
    print(json.dumps(result, indent=2))
    return 0 if not isinstance(result, dict) or (not result.get('error') and (args.action in {'status', 'next', 'evidence'} or result.get('verified'))) else 2


if __name__ == '__main__':
    raise SystemExit(main())
