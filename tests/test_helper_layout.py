import unittest
import harness as H
class HelperLayout(unittest.TestCase):
 def setUp(self):
  self.frozen='def targetDef : Nat := 2\n\ntheorem erdos_1 : targetDef = 2 :='
 def test_hoists_private_helper_without_changing_contract(self):
  code=self.frozen.replace('\n\ntheorem','\n\nprivate lemma helper : True := by trivial\n\ntheorem')+' by rfl'
  self.assertFalse(H.contains_frozen(code,self.frozen))
  repaired=H.normalize_helper_layout(code,self.frozen)
  self.assertTrue(H.contains_frozen(repaired,self.frozen));self.assertTrue(repaired.startswith('private lemma'))
 def test_changed_definition_or_theorem_not_repaired(self):
  for frozen in [self.frozen.replace(':= 2',':= 3'),self.frozen.replace('targetDef = 2','True')]:
   code=frozen.replace('\n\ntheorem','\n\nprivate lemma helper : True := by trivial\n\ntheorem')+' by trivial'
   self.assertEqual(H.normalize_helper_layout(code,self.frozen),code)
 def test_scope_directives_are_not_relocated(self):
  code=self.frozen.replace('\n\ntheorem','\n\nprivate lemma helper : True := by trivial\nopen Nat\n\ntheorem')+' by rfl'
  self.assertEqual(H.normalize_helper_layout(code,self.frozen),code)
 def test_closed_goal_branch_repair_is_narrow(self):
  code='      | (right; left; linarith)\n'
  fixed=H.repair_closed_goal_branches(code,['line 1: No goals to be solved'])
  self.assertIn('right <;> left <;> linarith',fixed)
  self.assertEqual(H.repair_closed_goal_branches(code,['unknown identifier']),code)
 def test_closed_goal_before_branch_search_is_allowed(self):
  code='    first\n    | (left; linarith)\n'
  repaired=H.repair_closed_goal_branches(code,['line 1: No goals to be solved'])
  self.assertIn('all_goals first',repaired)
  self.assertEqual(H.repair_closed_goal_branches(repaired,['No goals to be solved']),repaired)
 def test_out_of_credits_is_a_hard_provider_failure(self):
  self.assertIsNotNone(H.ClaudeCliBackend.HARD_RE.search('Your workspace is out of credits'))

 def test_final_check_does_not_silently_repair_stored_artifact(self):
  import tempfile, threading
  from pathlib import Path
  from types import SimpleNamespace
  from unittest.mock import Mock
  with tempfile.TemporaryDirectory() as tmp:
   h=H.Harness.__new__(H.Harness);h._lock=threading.Lock();h.checks=0
   h.imports=[];h.state={};h.run_dir=Path(tmp);h.log=SimpleNamespace(event=Mock())
   h.lean=SimpleNamespace(check=Mock(return_value={'ok':False,'sorries':False,'errors':['No goals to be solved'],'infos':[]}))
   body='  first\n  | (left; linarith)\n'
   result=h.check(body,'final-verify')
   self.assertEqual(result['body'],body)
   self.assertFalse(result['ok'])
   h.lean.check.assert_called_once()

 def test_closed_goal_during_multilocation_normalization(self):
  code='    norm_num at hne hpLine hqLine ⊢\n'
  self.assertEqual(H.repair_closed_goal_branches(code,['No goals to be solved']), '    try norm_num at *\n')
  self.assertEqual(H.repair_closed_goal_branches(code,['unsolved goals']),code)

 def test_indented_scope_and_command_directives_are_not_relocated(self):
  for directive in ['  open Nat', '  #check Nat']:
   code=self.frozen.replace('\n\ntheorem','\n\nprivate lemma helper : True := by trivial\n'+directive+'\n\ntheorem')+' by rfl'
   self.assertEqual(H.normalize_helper_layout(code,self.frozen),code)

 def test_repair_failure_logs_new_diagnostic_even_at_same_error_count(self):
  import tempfile, threading
  from pathlib import Path
  from types import SimpleNamespace
  from unittest.mock import Mock
  with tempfile.TemporaryDirectory() as tmp:
   h=H.Harness.__new__(H.Harness);h._lock=threading.Lock();h.checks=0
   h.imports=[];h.state={};h.run_dir=Path(tmp);h.log=SimpleNamespace(event=Mock())
   h.lean=SimpleNamespace(check=Mock(side_effect=[
    {'ok':False,'sorries':False,'errors':['No goals to be solved'],'infos':[]},
    {'ok':False,'sorries':False,'errors':['unsolved goals: new diagnostic'],'infos':[]}]))
   h.check('  | (left; linarith)\n','proof-test')
   h.log.event.assert_any_call('lean','closed_goal_branch_repair_result',name='proof-test',ok=False,errors=['unsolved goals: new diagnostic'])

 def test_simplifier_no_progress_repair_is_narrow(self):
  code='  simp only [h]\n'
  self.assertEqual(H.repair_closed_goal_branches(code,['`simp` made no progress']), '  try simp only [h]\n')
  self.assertEqual(H.repair_closed_goal_branches(code,['unknown identifier h']),code)

 def test_bounded_repair_uses_new_diagnostics_and_saves_compiled_body(self):
  import tempfile, threading
  from pathlib import Path
  from types import SimpleNamespace
  from unittest.mock import Mock
  with tempfile.TemporaryDirectory() as tmp:
   h=H.Harness.__new__(H.Harness);h._lock=threading.Lock();h.checks=0
   h.imports=[];h.state={};h.run_dir=Path(tmp);h.log=SimpleNamespace(event=Mock())
   h.lean=SimpleNamespace(check=Mock(side_effect=[
    {'ok':False,'sorries':False,'errors':['No goals to be solved'],'infos':[]},
    {'ok':False,'sorries':False,'errors':['`simp` made no progress'],'infos':[]},
    {'ok':True,'sorries':False,'errors':[],'infos':[]}]))
   result=h.check('  norm_num at h1 h2 ⊢\n  simp only [h]\n','proof-test')
   self.assertTrue(result['ok']);self.assertEqual(h.lean.check.call_count,3)
   self.assertIn('try norm_num at *',result['body']);self.assertIn('try simp only',result['body'])
