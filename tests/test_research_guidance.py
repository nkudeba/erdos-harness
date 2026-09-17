"""Current Atlas next steps reach actual providers without changing frozen inputs."""
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch
import harness as H


class ResearchGuidance(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.patch = patch.object(H, 'ROOT', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.source = self.root / 'atlas-data/research-guidance/699.md'
        self.source.parent.mkdir(parents=True)
        self.source.write_text('Audit the bound; then use n-2. NOT VERIFIED.')
        self.h = H.Harness.__new__(H.Harness)
        self.h.problem = {'id': '699', 'statement': 'unchanged target'}
        self.h.state = {'statement': 'frozen target', 'literature': 'old checkpoint'}
        self.h.run_dir = self.root / 'run'
        self.h.run_dir.mkdir()
        self.h.log = H.RunLog(self.h.run_dir)
        self.h._check_run_budget = Mock()
        self.h.llm = SimpleNamespace(complete=Mock(return_value='response'), last_meta={})

    def test_current_guidance_reaches_provider_and_transcript_after_resume(self):
        original = json.dumps(self.h.problem)
        for stage in ('assess', 'reduce', 'experiments', 'plan', 'prove', 'refine', 'decompose'):
            self.h.ask(stage, 'old plan')
            prompt = self.h.llm.complete.call_args.args[1]
            self.assertIn('then use n-2', prompt)
            self.assertIn('not a verified proof', prompt)
        self.source.write_text('Updated next step, still unverified.')
        self.h.ask('plan', 'old checkpoint')
        self.assertIn('Updated next step', self.h.llm.complete.call_args.args[1])
        self.assertEqual(json.dumps(self.h.problem), original)
        self.assertEqual(self.h.state['statement'], 'frozen target')
        self.assertTrue(any('Updated next step' in p.read_text()
                            for p in (self.h.run_dir / 'transcripts').glob('*.md')))
        facts = H.collect_run_facts(self.h.run_dir, '699')
        self.assertTrue(facts['operator_context'])
        self.assertTrue(any(e.get('sha256') for e in facts['events']
                            if e.get('event') == 'operator_guidance'))

    def test_agentic_provider_and_saved_task_receive_guidance(self):
        sandbox = self.root / 'sandbox'
        sandbox.mkdir()
        self.h._sandbox = Mock(return_value=sandbox)
        self.h.args = SimpleNamespace(agentic_turns=1)
        self.h.llm.complete_agentic = Mock(return_value='no proof')
        self.h._agentic_attempt('test', 'frozen target', 'original task')
        prompt = self.h.llm.complete_agentic.call_args.args[1]
        self.assertIn('then use n-2', prompt)
        self.assertEqual((sandbox / 'TASK.md').read_text(), prompt)

    def test_formalization_and_blind_judges_are_unchanged(self):
        for stage in ('formalize', 'crosscheck', 'readings', 'backtranslate', 'faithful', 'brief'):
            self.h.ask(stage, 'unchanged')
            self.assertEqual(self.h.llm.complete.call_args.args[1], 'unchanged')

    def test_no_guidance_and_non_numeric_id_leave_prompt_alone(self):
        self.source.unlink()
        self.assertEqual(self.h._with_research_guidance('plan', 'p'), 'p')
        self.h.problem['id'] = '../699'
        self.assertEqual(self.h._with_research_guidance('plan', 'p'), 'p')


if __name__ == '__main__':
    unittest.main()
