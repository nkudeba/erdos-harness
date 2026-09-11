import json,tempfile,unittest
from pathlib import Path
from types import SimpleNamespace
import harness as H
class LiteratureFallback(unittest.TestCase):
 def setup_h(self,tmp,subtype='error_max_budget_usd',budget=12):
  h=H.Harness.__new__(H.Harness);h.problem={'id':'649','notes':'Published modular obstruction','statement':'original'};h.state={};h.imports=[]
  h.run_dir=Path(tmp);h.state_path=h.run_dir/'state.json';h.log=H.RunLog(h.run_dir)
  h.args=SimpleNamespace(skip_literature=False,literature_web=True,web_budget=2.5,run_budget=budget)
  def fail(*a,**k):raise RuntimeError(subtype)
  h.llm=SimpleNamespace(complete_web=fail,last_meta={'cost_usd':2.6,'subtype':subtype})
  h.ask=lambda *a:self.fail('must use supplied notes without spending again')
  return h
 def test_bounded_lookup_failure_keeps_notes_and_cost(self):
  with tempfile.TemporaryDirectory() as tmp:
   h=self.setup_h(tmp);h.stage_literature()
   self.assertIn('Published modular',h.state['literature']);self.assertEqual(h.spent_usd(),2.6)
   self.assertEqual(h.state['literature_provenance']['mode'],'source_notes_fallback')
 def test_hard_provider_error_does_not_continue(self):
  with tempfile.TemporaryDirectory() as tmp:
   h=self.setup_h(tmp,'Spend limit reached')
   with self.assertRaisesRegex(RuntimeError,'Spend limit'):h.stage_literature()
   self.assertNotIn('literature',h.state)
 def test_run_budget_wins_over_fallback(self):
  with tempfile.TemporaryDirectory() as tmp:
   h=self.setup_h(tmp,budget=2)
   with self.assertRaises(H.Harness.BudgetExhausted):h.stage_literature()
 def test_without_source_notes_failure_is_not_silenced(self):
  with tempfile.TemporaryDirectory() as tmp:
   h=self.setup_h(tmp);h.problem['notes']=''
   with self.assertRaises(RuntimeError):h.stage_literature()
 def test_retrieved_route_reaches_formalization(self):
  text=H.formalize_prompt({'id':'105','statement':'full question'},2,[],[],'exact coordinate witness')
  self.assertIn('exact coordinate witness',text)
  self.assertIn('never weaken',text)
 def test_informal_context_is_deduplicated_and_attributed(self):
  with tempfile.TemporaryDirectory() as tmp:
   h=self.setup_h(tmp);p=Path(tmp)/'notes.txt';p.write_text('A published rational witness')
   h.args.informal_context=[str(p)];h.stage_informal_context();h.stage_informal_context()
   self.assertEqual(len(h.state['operator_context']),1)
   self.assertEqual(h.state['literature'].count('published rational witness'),1)
   p.write_text('```lean\ntheorem borrowed := by trivial\n```')
   with self.assertRaises(ValueError):h.stage_informal_context()
