"""Repair feedback must describe the exact persisted candidate, including zero-hole failures."""
import copy
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import harness as H

SKELETON='theorem erdos_1 : True := by\n  sorry'
BROKEN='theorem erdos_1 : True := by\n  exact missing_witness'
GOOD='theorem erdos_1 : True := by\n  exact True.intro'

class RepairCheckpointTests(unittest.TestCase):
    def make(self,state,rounds,replies):
        h=H.Harness.__new__(H.Harness)
        h.state=copy.deepcopy(state)
        h.args=SimpleNamespace(decompose_rounds=rounds, no_cascade=True)
        h.problem={'id':'1','statement':'True'}
        h.imports=[]
        h.log=SimpleNamespace(event=lambda *a,**k:None)
        h.save=lambda:None
        h.prompts=[]
        def ask(purpose,prompt):
            h.prompts.append(prompt)
            return '```lean\n'+replies.pop(0)+'\n```'
        h.ask=ask
        h.check=lambda code,name:dict(ok=code!=BROKEN,sorries='sorry' in code,errors=['unknown missing_witness'] if code==BROKEN else [],body=code)
        return h

    def test_failed_candidate_and_errors_survive_resume(self):
        state={'statement':SKELETON,'decomposition':{'code':SKELETON}}
        h=self.make(state,1,[BROKEN])
        with patch.object(H,'run_retrieval_directives',return_value=[]):
            self.assertFalse(h.stage_decompose())
        self.assertEqual(h.state['decomposition']['candidate'],BROKEN)
        self.assertEqual(h.state['decomposition']['code'],SKELETON)
        resumed=self.make(h.state,1,[GOOD])
        with patch.object(H,'run_retrieval_directives',return_value=[]):
            self.assertTrue(resumed.stage_decompose())
        self.assertIn(BROKEN,resumed.prompts[0])
        self.assertIn('unknown missing_witness',resumed.prompts[0])
        self.assertEqual(resumed.state['proof'],GOOD)
        self.assertEqual(resumed.state['decomposition']['rounds_used'],2)

    def test_feedback_tracks_failed_candidate_within_run(self):
        h=self.make({'statement':SKELETON,'decomposition':{'code':SKELETON}},2,[BROKEN,GOOD])
        with patch.object(H,'run_retrieval_directives',return_value=[]):
            self.assertTrue(h.stage_decompose())
        self.assertIn(BROKEN,h.prompts[1])
        self.assertIn('unknown missing_witness',h.prompts[1])

class SearchContinuityTests(unittest.TestCase):
    def test_complete_candidate_is_not_truncated(self):
        h=H.Harness.__new__(H.Harness)
        code='-- long context\n'*1000+GOOD
        attempts=[]
        h._record(attempts,'candidate','plan',1,code,dict(ok=False,errors=['type mismatch']))
        self.assertEqual(attempts[0]['code'],code)
        self.assertTrue(H.contains_frozen(attempts[0]['code'],H.statement_prefix(SKELETON)))

    def test_near_complete_candidate_beats_trivial_outline(self):
        h=H.Harness.__new__(H.Harness)
        outline=dict(code=SKELETON,compiled=True,n_sorries=1,errors=[],round=2)
        close=dict(code=BROKEN,compiled=False,errors=['unknown'],round=1)
        self.assertEqual(h._best_partials([outline,close],1),[close])
        close['timeout']=True
        self.assertEqual(h._best_partials([outline,close],1),[outline])

    def test_retrieval_is_accumulated_deduplicated_and_bounded(self):
        self.assertEqual(H.merge_retrieval(['source A'],['source B','source A']),['source A','source B'])
        result=H.merge_retrieval(['a'*20000,'b'*20000],['c'*20000])
        self.assertEqual(result,['b'*20000,'c'*20000])
        self.assertLessEqual(sum(map(len,result)),48000)

    def test_decomposition_receives_prove_evidence_and_failed_candidate(self):
        state={'statement':SKELETON,'proof_retrieval':['essential library signature'],
               'attempts':[dict(name='outline',plan='outline',code=SKELETON,compiled=True,n_sorries=1,errors=[],round=1),
                           dict(name='almost',plan='repair',code=BROKEN,compiled=False,errors=['unknown missing_witness'],round=2)]}
        h=RepairCheckpointTests().make(state,1,[GOOD])
        with patch.object(H,'run_retrieval_directives',return_value=[]):
            self.assertTrue(h.stage_decompose())
        self.assertIn(BROKEN,h.prompts[0])
        self.assertIn('essential library signature',h.prompts[0])

class NoOutlineRepairTests(unittest.TestCase):
    def test_complete_failure_can_seed_repair_without_generating_outline(self):
        state={'statement':SKELETON,'attempts':[
            dict(name='almost',plan='repair',code=BROKEN,compiled=False,errors=['unknown'],round=1)]}
        h=RepairCheckpointTests().make(state,1,[GOOD])
        with patch.object(H,'run_retrieval_directives',return_value=[]):
            self.assertTrue(h.stage_decompose())
        self.assertEqual(len(h.prompts),1)
        self.assertIn(BROKEN,h.prompts[0])


class AgenticContractTests(unittest.TestCase):
    def test_codex_can_inspect_sources_without_claude_only_tools(self):
        p=H.agentic_prompt({'id':'1','statement':'True'},SKELETON,'','','',[],8,tool_backend='codex-cli')
        self.assertIn('read-only shell commands',p)
        self.assertIn('session timeout is the enforced budget',p)
        self.assertNotIn('only allowed shell command',p)
        self.assertIn('Do not read other harness runs',p)
    def test_claude_retains_its_restricted_shell_contract(self):
        p=H.agentic_prompt({'id':'1','statement':'True'},SKELETON,'','','',[],8)
        self.assertIn('Read/Grep/Glob',p)
        self.assertIn('only allowed shell command',p)

if __name__=='__main__': unittest.main()
