import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock
import harness as H

class SandboxRecovery(unittest.TestCase):
    def setup_h(self, root, candidate, summary=True):
        h=H.Harness.__new__(H.Harness)
        h.run_dir=Path(root)
        h.args=SimpleNamespace(resume=root)
        h.state={'statement':'theorem erdos_1 : True := by sorry'}
        h.save=Mock();h.log=SimpleNamespace(event=Mock());h._record=Mock()
        h.check=Mock(return_value={'ok':True,'sorries':False,'body':candidate})
        h.initial_retrieval=Mock(side_effect=RuntimeError('ordinary proving starts'))
        sandbox=h.run_dir/'sandbox'/'proof-r1-g0';sandbox.mkdir(parents=True)
        (sandbox/'Attempt.lean').write_text(candidate)
        if summary:(sandbox/'SUMMARY.md').write_text('Finished attempt')
        return h

    def test_recovery_checks_artifact_before_any_new_proof_call(self):
        with tempfile.TemporaryDirectory() as tmp:
            h=self.setup_h(tmp,'theorem erdos_1 : True := by trivial')
            self.assertTrue(h.stage_prove())
            h.check.assert_called_once();h.initial_retrieval.assert_not_called()
            self.assertEqual(h.state['proof'],'theorem erdos_1 : True := by trivial')
            self.assertTrue(h.state['proof_recovery']['mechanical_repair_only'])

    def test_changed_contract_gaps_and_unfinished_artifacts_are_not_recovered(self):
        for source,summary in [('theorem erdos_1 : False := by trivial',True),
                               ('theorem erdos_1 : True := by sorry',True),
                               ('theorem erdos_1 : True := by trivial',False)]:
            with self.subTest(source=source,summary=summary),tempfile.TemporaryDirectory() as tmp:
                h=self.setup_h(tmp,source,summary)
                with self.assertRaisesRegex(RuntimeError,'ordinary proving'):h.stage_prove()
                h.check.assert_not_called();self.assertNotIn('proof',h.state)

    def test_failed_compile_is_not_promoted(self):
        with tempfile.TemporaryDirectory() as tmp:
            h=self.setup_h(tmp,'theorem erdos_1 : True := by missing_tactic')
            h.check.return_value={'ok':False,'sorries':False}
            with self.assertRaisesRegex(RuntimeError,'ordinary proving'):h.stage_prove()
            self.assertNotIn('proof',h.state)
