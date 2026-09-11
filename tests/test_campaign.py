"""Campaign invariants; no provider calls. Real Lean checks in the opt-in class."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from campaign import Campaign, BudgetStop, digest, validate


def plan():
    return {'schema_version': 1, 'id': 'Test', 'targets': ['goal'],
            'budget': {'model_calls': 2, 'lean_checks': 60, 'wall_seconds': 600},
            'nodes': [{'id': 'base', 'kind': 'lemma', 'scope': 'infrastructure',
                       'imports': ['Init'], 'type': 'True'},
                      {'id': 'goal', 'kind': 'target', 'scope': 'general',
                       'imports': ['Init'], 'type': 'True', 'depends_on': ['base']}]}


class CampaignTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'campaign.json'
        self.path.write_text(json.dumps(plan()))
        self.c = Campaign(self.path)

    def test_reject_bad_graphs(self):
        for mutation in ('cycle', 'unknown', 'evidence', 'import'):
            p = plan()
            if mutation == 'cycle': p['nodes'][0]['depends_on'] = ['goal']
            if mutation == 'unknown': p['nodes'][1]['depends_on'] = ['missing']
            if mutation == 'evidence':
                p['nodes'][0].update(kind='experiment'); p['nodes'][0].pop('type')
            if mutation == 'import': p['nodes'][0]['imports'] = ['Untrusted']
            with self.subTest(mutation=mutation), self.assertRaises(ValueError): validate(p)

    def test_evidence_does_not_discharge_contract(self):
        f = self.path.parent / 'evidence.txt'; f.write_text('A model says it is true')
        self.c.record_evidence('base', f, 'unverified')
        self.assertEqual([r['id'] for r in self.c.next()], ['base'])
        self.assertFalse(self.c.status()['formal_targets_verified'])

    def test_pending_budget_survives_restart(self):
        self.c.reserve('model_calls', 400)
        _, allowance = Campaign(self.path).reserve('model_calls', 400)
        self.assertEqual(allowance, 200)
        with self.assertRaises(BudgetStop): Campaign(self.path).reserve('model_calls', 1)
        with self.assertRaises(BudgetStop): Campaign(self.path).reserve('lean_checks', 1)

    def test_settlement_returns_unused_allowance(self):
        token, _ = self.c.reserve('lean_checks', 300)
        self.c.settle(token, 2)
        self.assertEqual(self.c.status()['charged_seconds'], 2)

    def test_dependency_change_invalidates_fingerprint(self):
        before = self.c.fingerprint('goal')
        self.c.nodes['base']['type'] = 'False'
        self.assertNotEqual(before, self.c.fingerprint('goal'))

    def test_malformed_certificate_is_not_fresh(self):
        self.assertFalse(self.c.fresh('base', {'base': {'fingerprint': self.c.fingerprint('base'), 'files': {}}}))

    def test_unformalized_gap_cannot_run(self):
        self.c.nodes['base'].pop('type')
        self.assertEqual(self.c.next(), [])
        with self.assertRaises(ValueError): self.c.run_node('base', None)

    def test_reject_axiom_and_extra_commands(self):
        f = self.path.parent / 'bad.lean'
        for body in ['axiom result : True', 'theorem result : True := by sorry', 'run_cmd pure ()']:
            f.write_text(body)
            self.assertFalse(self.c.verify('base', f)['verified'])


@unittest.skipUnless(os.environ.get('CAMPAIGN_LEAN_TESTS') == '1', 'set CAMPAIGN_LEAN_TESTS=1 for real Lean checks')
class LeanCampaignTests(CampaignTests):
    def candidate(self, text):
        f = self.path.parent / 'candidate.lean'; f.write_text(text); return f

    def test_contract_and_dependency_audit(self):
        first = self.c.verify('base', self.candidate('theorem result : True := True.intro'), timeout=60)
        self.assertTrue(first['verified'], first)
        declaration = first['certificate']['declaration']
        second = self.c.verify('goal', self.candidate(f'theorem result : True := {declaration}'), timeout=60)
        self.assertTrue(second['verified'], second)
        self.assertTrue(self.c.status()['formal_targets_verified'])
        self.c.nodes['goal']['scope'] = 'conditional'
        self.assertFalse(self.c.status()['formal_targets_verified'])
        self.c.nodes['goal']['scope'] = 'general'
        path = Path(next(iter(first['certificate']['files'])))
        original = path.read_bytes()
        try:
            path.write_bytes(original + b'\n-- changed\n')
            self.assertFalse(self.c.fresh('goal', {'base': first['certificate'], 'goal': second['certificate']}))
        finally: path.write_bytes(original)

    def test_wrong_type_and_added_assumption_fail(self):
        self.c.nodes['base']['type'] = 'False'
        for body in ['theorem result : True := True.intro', 'theorem result (h : False) : False := h']:
            result = self.c.verify('base', self.candidate(body), timeout=60)
            self.assertFalse(result['verified'], result)
            self.assertEqual(result['stage'], 'audit', result)

    def test_model_repair_consumes_exact_errors(self):
        class Backend:
            timeout = 60
            model = 'deterministic-test-double'
            def __init__(self): self.prompts = []
            def complete(self, purpose, prompt):
                self.prompts.append(prompt)
                return '```lean\ntheorem result : True := ' + ('False.elim bad' if len(self.prompts)==1 else 'True.intro') + '\n```'
        backend = Backend()
        result = self.c.run_node('base', backend, rounds=2, timeout=60)
        self.assertTrue(result['verified'], result)
        self.assertIn('False.elim bad', backend.prompts[1])
        self.assertIn('Unknown identifier', backend.prompts[1])
        self.assertEqual(self.c.status()['model_calls'], 2)
        self.assertEqual(len(list((self.c.root/'requests').glob('*/response.txt'))), 2)


if __name__ == '__main__': unittest.main()
