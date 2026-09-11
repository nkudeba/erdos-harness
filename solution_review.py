"""Conservative claim milestones. Review attestations are operator records, not authenticated identities."""
import hashlib
import json
from pathlib import Path


def fingerprint(problem, state, imports, environment):
    payload = {'problem': problem, 'statement': state.get('statement'), 'proof': state.get('proof'),
               'direction': state.get('direction'), 'imports': imports, 'environment': environment}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


def milestones(problem, state, imports, environment, attestations=()):
    digest = fingerprint(problem, state, imports, environment)
    v = state.get('verify') or {}
    # Bind mechanical results to the exact artifacts; legacy all_clear is insufficient.
    mechanical = (bool(state.get('proof')) and v.get('artifact_sha256') == digest
                  and all(v.get(k) is True for k in ('compiles', 'sorry_free', 'axioms_clean', 'frozen_match'))
                  and not v.get('banned') and set(v.get('axioms', ['UNKNOWN'])) <= {'Classical.choice', 'Quot.sound', 'propext'})
    valid = {}
    for a in attestations:
        if not isinstance(a, dict):
            continue
        if (a.get('artifact_sha256') != digest or a.get('approved') is not True
                or a.get('independent') is not True or not a.get('reviewer') or not a.get('evidence')):
            continue
        # Evidence must still exist and match its recorded content.
        try:
            if hashlib.sha256(Path(a['evidence']).read_bytes()).hexdigest() != a.get('evidence_sha256'):
                continue
        except (OSError, TypeError):
            continue
        valid[a.get('kind')] = a
    audited = mechanical and 'statement_audit' in valid and 'clean_replay' in valid
    reviewed = (audited and 'adversarial_checks' in valid and 'external_review' in valid
                and valid['external_review']['reviewer'] != valid['statement_audit']['reviewer'])
    subgoal = state.get('direction') == 'program'
    claim = bool(reviewed and not subgoal and v.get('faithful', {}).get('faithful') is True)
    stage = ('externally_reviewed' if reviewed else 'statement_independently_audited' if audited
             else 'mechanically_verified' if mechanical else 'candidate_solution' if state.get('proof') else 'no_candidate')
    return {'schema_version': 1, 'artifact_sha256': digest, 'stage': stage,
            'candidate_solution': bool(state.get('proof')), 'mechanically_verified': mechanical,
            'statement_independently_audited': bool(audited), 'externally_reviewed': bool(reviewed),
            'resolution_claim_eligible': claim, 'scope': 'sublemma' if subgoal else 'full_problem_candidate',
            'catalogue_status_changed': False,
            'pending': [k for k in ('clean_replay', 'statement_audit', 'adversarial_checks', 'external_review') if k not in valid],
            'notice': 'Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update.'}


def environment_snapshot(root):
    return {name: (root / name).read_text() if (root / name).exists() else None
            for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean')}


def load_attestations(run_dir):
    try:
        value = json.loads((run_dir / 'review-attestations.json').read_text())
        return value if isinstance(value, list) else []
    except (OSError, ValueError):
        return []


def main():
    import argparse
    p = argparse.ArgumentParser(description='Record independent review evidence for an exact harness artifact. Never run from a proof-generation prompt.')
    p.add_argument('run_dir', type=Path)
    p.add_argument('--kind', required=True, choices=['clean_replay', 'statement_audit', 'adversarial_checks', 'external_review'])
    p.add_argument('--reviewer', required=True)
    p.add_argument('--evidence', required=True, type=Path)
    p.add_argument('--attest-independent', action='store_true', required=True)
    a = p.parse_args()
    state = json.loads((a.run_dir / 'state.json').read_text())
    review = state['solution_review']
    record = {'kind': a.kind, 'reviewer': a.reviewer, 'evidence': str(a.evidence.resolve()),
              'evidence_sha256': hashlib.sha256(a.evidence.read_bytes()).hexdigest(),
              'artifact_sha256': review['artifact_sha256'], 'independent': True, 'approved': True}
    records = load_attestations(a.run_dir)
    records = [r for r in records if r.get('kind') != a.kind] + [record]
    dest = a.run_dir / 'review-attestations.json'
    tmp = dest.with_suffix('.tmp'); tmp.write_text(json.dumps(records, indent=2)); tmp.replace(dest)
    print('Evidence recorded. Resume verification to recompute milestones against current artifacts.')

if __name__ == '__main__':
    main()
