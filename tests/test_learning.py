import argparse
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H
import learning

class LearningTests(unittest.TestCase):
    def test_promotion_gate(self):
        self.assertTrue(H.promotion_decision({'1': True, '2': False}, {'1': True, '2': True}))
        self.assertFalse(H.promotion_decision({'1': True, '2': False}, {'1': False, '2': True}))
        self.assertFalse(H.promotion_decision({'1': False}, {'1': False}))
        self.assertFalse(H.promotion_decision({'1': False}, {'1': None}))
        self.assertFalse(H.promotion_decision({}, {}))

    def test_workflow_stages_and_promotes_only_on_gain(self):
        for after, regression_ok, promote in [(True, True, True), (False, True, False), (True, False, False), (None, True, False)]:
            with self.subTest(after=after, regression_ok=regression_ok), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                knowledge = root / 'knowledge'
                knowledge.mkdir()
                (knowledge / 'playbook.md').write_text('original')
                args = argparse.Namespace(problems=['1'], eval_problems=['2'], cycles=1,
                    backend='codex-cli', agentic='off', rounds=1, decompose_rounds=0, model=None)
                def fake_run(cmd, **kwargs):
                    action = cmd[2]
                    rc = 0
                    if action == 'run':
                        run = Path(cmd[cmd.index('--resume') + 1]); run.mkdir(exist_ok=True)
                        if '-after-' in run.name:
                            self.assertEqual(json.loads((run / 'state.json').read_text())['statement'], 'fixed statement')
                        (run / 'state.json').write_text(json.dumps({'statement': 'fixed statement', 'literature': 'same context'}))
                        success = False if '-before-' in run.name else after if '-after-' in run.name else True
                        (run / 'DONE').write_text(json.dumps({'verify': success}))
                        rc = 1 if success is None else 0 if success else 2
                    elif action == 'retrospect':
                        Path(kwargs['env']['ERDOS_KNOWLEDGE'], 'playbook.md').write_text('candidate lesson')
                        # Active lessons must remain unchanged throughout evaluation.
                        self.assertEqual((knowledge / 'playbook.md').read_text(), 'original')
                    elif action == 'regress':
                        rc = 0 if regression_ok else 1
                    return type('Result', (), {'returncode': rc})()
                with patch.object(H, 'ROOT', root), patch.object(H, 'RUNS', root / 'runs'), patch.object(H, 'KNOWLEDGE', knowledge), patch.object(learning.subprocess, 'run', side_effect=fake_run):
                    learning._cycles(args)
                self.assertEqual((knowledge / 'playbook.md').read_text(), 'candidate lesson' if promote else 'original')

if __name__ == '__main__':
    unittest.main()
