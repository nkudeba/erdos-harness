"""Staged lesson learning with fresh held-out evaluations and a promotion gate.

This measures prompt/retrieval improvement, not model-weight training. One stochastic
comparison is evidence for further testing, not a statistical guarantee of improvement.
"""
import json
import os
import shutil
import subprocess
import sys
import uuid
from pathlib import Path
import harness as H


def improve(args):
    if set(args.problems) & set(args.eval_problems):
        raise ValueError('training and held-out problems must be disjoint')
    for pid in [*args.problems, *args.eval_problems]:
        if not str(pid).isdigit() or not (H.ROOT / 'problems' / f'erdos_{pid}.json').is_file():
            raise ValueError(f'unknown problem: {pid}')
    H.KNOWLEDGE.mkdir(parents=True, exist_ok=True)
    lock = H.KNOWLEDGE.parent / '.erdos-learning-lock'
    lock.mkdir()  # fail rather than race another learner
    try:
        return _cycles(args)
    finally:
        lock.rmdir()


def _cycles(args):
    root = H.RUNS / f'learning-{uuid.uuid4().hex[:12]}'
    root.mkdir(parents=True)

    fixtures = {}

    def execute(label, pid, knowledge, fixture=None):
        run = root / label
        if fixture:
            run.mkdir()
            (run / "state.json").write_text(json.dumps(fixture, indent=2))
        env = dict(os.environ, ERDOS_KNOWLEDGE=str(knowledge))
        cmd = [sys.executable, str(H.ROOT / 'harness.py'), 'run',
               '--problem', str(H.ROOT / 'problems' / f'erdos_{pid}.json'),
               '--resume', str(run), '--backend', args.backend, '--agentic', args.agentic,
               '--rounds', str(args.rounds), '--decompose-rounds', str(args.decompose_rounds),
               '--samples', '1']
        if args.model:
            cmd += ['--model', args.model]
        print(f'[learn] {label}', flush=True)
        with (root / f'{label}.log').open('w') as log:
            result = subprocess.run(cmd, cwd=H.ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        done = json.loads((run / 'DONE').read_text()) if (run / 'DONE').exists() else {}
        # Infrastructure failure is unknown, never a mathematical failure.
        status = None if result.returncode not in (0, 2) or done.get('fatal') else done.get('verify') is True
        return run, status

    def evaluate(label, knowledge):
        results = {}
        for pid in args.eval_problems:
            isolated = root / f'{label}-{pid}-knowledge'
            shutil.copytree(knowledge, isolated)
            run, results[pid] = execute(f'{label}-erdos{pid}', pid, isolated, fixtures.get(pid))
            if pid not in fixtures and (run / "state.json").exists():
                state = json.loads((run / "state.json").read_text())
                if "statement" in state:
                    fixtures[pid] = {k: state[k] for k in ("statement", "literature") if k in state}
        return results

    for cycle in range(1, args.cycles + 1):
        candidate = root / f'candidate-{cycle}'
        shutil.copytree(H.KNOWLEDGE, candidate)
        before = evaluate(f'cycle{cycle}-before', H.KNOWLEDGE)
        if any(v is None for v in before.values()):
            (root / 'blocked.json').write_text(json.dumps({'before': before, 'reason': 'provider or infrastructure error'}))
            return 1
        for pid in args.problems:
            run, status = execute(f'cycle{cycle}-train-erdos{pid}', pid, candidate)
            if status is None:
                return 1
            env = dict(os.environ, ERDOS_KNOWLEDGE=str(candidate))
            cmd = [sys.executable, str(H.ROOT / 'harness.py'), 'retrospect', str(run), '--backend', args.backend]
            if args.model:
                cmd += ['--model', args.model]
            with (root / f'retrospect-{cycle}-{pid}.log').open('w') as log:
                result = subprocess.run(cmd, cwd=H.ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                return 1
        after = evaluate(f'cycle{cycle}-after', candidate)
        env = dict(os.environ, ERDOS_KNOWLEDGE=str(candidate))
        with (root / f'regression-{cycle}.log').open('w') as log:
            regression = subprocess.run([sys.executable, str(H.ROOT / 'harness.py'), 'regress'],
                                        cwd=H.ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        promoted = regression.returncode == 0 and H.promotion_decision(before, after)
        record = {'cycle': cycle, 'before': before, 'after': after, 'promoted': promoted,
                  'saved_proofs_pass': regression.returncode == 0, 'backend': args.backend,
                  'model': args.model, 'candidate': str(candidate)}
        (root / f'cycle-{cycle}.json').write_text(json.dumps(record, indent=2))
        print(json.dumps(record), flush=True)
        if promoted:
            # Only lesson artifacts are promoted; evaluated proofs remain audit artifacts.
            for filename in ['playbook.md', 'lemmas.jsonl']:
                source = candidate / filename
                if source.exists():
                    pending = H.KNOWLEDGE / f'.{filename}.pending'
                    shutil.copyfile(source, pending)
                    pending.replace(H.KNOWLEDGE / filename)
        if any(v is None for v in after.values()) or regression.returncode:
            return 1
    return 0
