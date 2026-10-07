"""Outcome regressions without model calls or Lean startup."""
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

class Outcomes(unittest.TestCase):
    def test_frozen_statement_in_comment_or_string_is_rejected(self):
        frozen = "theorem erdos_1 : False :="
        for decoy in [f"/- outer /- nested -/ {frozen} -/", f'#check "{frozen}"']:
            self.assertFalse(H.contains_frozen(decoy + "\ntheorem erdos_1 : True := trivial", frozen))
        self.assertFalse(H.contains_frozen('theorem erdos_1 : "a" = "c" := by rfl',
                                           'theorem erdos_1 : "a" = "b" :='))
        self.assertIsNone(H.has_banned("/- sorry /- unsafe -/ axiom -/\ntheorem t : True := trivial"))

    def test_partial_proof_is_retained_but_explicit_sorry_axiom_is_banned(self):
        h = H.Harness.__new__(H.Harness)
        h.log = type('Log', (), {'event': lambda *a, **k: None})()
        partial = 'theorem erdos_1 : True := by sorry'
        self.assertTrue(h._screen([], 'test', '', 1, partial, H.statement_prefix(partial)))
        self.assertEqual(H.has_banned('exact sorryAx', allow_sorry=True), 'sorryAx')

    def test_holes_exclude_comments_strings_and_identifier_substrings(self):
        self.assertEqual(H.hole_count('private lemma sorry_named : True := by trivial -- sorry\n/- sorry -/'), 0)
        self.assertEqual(H.hole_count('theorem t : True := by sorry'), 1)

    def test_source_retrieval_is_bounded_to_mathlib(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(H, 'MATHLIB_SRC', Path(tmp) / 'Mathlib'):
            (Path(tmp) / 'Mathlib').mkdir()
            (Path(tmp) / 'Mathlib' / 'Example.lean').write_text('theorem example_test : True := trivial')
            self.assertIn('example_test', H.run_retrieval_directives('-- READ: Mathlib.Example')[0])
            self.assertEqual(H.run_retrieval_directives('-- READ: ../../secret'), [])

    def test_refinement_progress_survives_provider_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            h = H.Harness.__new__(H.Harness)
            h.problem = {'id': '1', 'statement': 'True'}
            h.args = type('Args', (), {'decompose_rounds': 2, 'no_cascade': True})()
            h.imports = []
            h.log = H.RunLog(Path(tmp))
            h.state_path = Path(tmp) / 'state.json'
            target = 'theorem erdos_1 : True := by sorry'
            current = 'private lemma step : True := by sorry\n' + target
            repaired = 'private lemma step : True := by trivial\n' + target
            h.state = {'statement': target, 'decomposition': {'code': current}}
            h.check = lambda *args: {'ok': True, 'sorries': True, 'errors': []}
            with patch.object(h, 'ask', side_effect=['```lean\n' + repaired + '\n```', RuntimeError('credits')]):
                with self.assertRaisesRegex(RuntimeError, 'credits'):
                    h.stage_decompose()
            self.assertEqual(json.loads(h.state_path.read_text())['decomposition']['code'], repaired)

    def test_resume_goes_directly_to_saved_decomposition(self):
        with tempfile.TemporaryDirectory() as tmp:
            h = H.Harness.__new__(H.Harness)
            h.problem = {'id': '1'}
            h.args = type('Args', (), {'backend': 'file', 'resume': tmp})()
            h.run_dir = Path(tmp)
            h.log = H.RunLog(h.run_dir)
            h.state = {'decomposition': {'code': 'saved'}, 'verify': {'all_clear': True}}
            h.stage_literature = h.stage_formalize = lambda: None
            h.stage_prove = lambda: self.fail('must reuse saved decomposition')
            h.stage_decompose = lambda: True
            h.stage_verify = lambda: None
            h.report = lambda proved: None
            self.assertEqual(h.run(), 0)

    def test_final_guard_runs_even_for_resumed_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            h = H.Harness.__new__(H.Harness)
            h.problem = {'id': '1'}
            h.state = {'statement': 'theorem erdos_1 : False := by sorry',
                       'proof': 'theorem erdos_1 : True := by trivial',
                       'verify': {'all_clear': True, 'faithful': {'faithful': True}}}
            h.state_path = Path(tmp) / 'state.json'
            h.log = H.RunLog(Path(tmp))
            h.check = lambda *args: {'ok': True, 'sorries': False, 'raw': "'erdos_1' does not depend on any axioms"}
            h.ask = lambda *args: self.fail('semantic judge must not run on a changed statement')
            self.assertFalse(h.stage_verify()['all_clear'])

    def test_provider_error_with_text_is_not_completion(self):
        response = type('Response', (), {'returncode': 0, 'stdout': json.dumps({'is_error': True, 'result': 'Spend limit reached'}), 'stderr': ''})()
        with patch.object(H, 'run_tracked', return_value=response):
            with self.assertRaisesRegex(RuntimeError, 'Spend limit'):
                H.ClaudeCliBackend(None, 1).complete('prove', 'test')

    def test_failed_judge_cannot_exit_success(self):
        for verdict, expected in [(False, 2), (None, 2), ('false', 2), (True, 0)]:
            with self.subTest(verdict=verdict), tempfile.TemporaryDirectory() as tmp:
                h = H.Harness.__new__(H.Harness)
                h.problem = {'id': '1'}
                h.args = type('Args', (), {'backend': 'file', 'resume': None})()
                h.run_dir = Path(tmp)
                h.log = H.RunLog(h.run_dir)
                h.state = {'verify': {'all_clear': verdict}}
                h.stage_literature = h.stage_formalize = lambda: None
                h.stage_prove = lambda: True
                h.stage_verify = lambda: None
                h.report = lambda proved: None
                self.assertEqual(h.run(), expected)

if __name__ == '__main__':
    unittest.main()
