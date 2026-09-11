import json
import tempfile
import unittest
from pathlib import Path
from solution_review import fingerprint, milestones
import hashlib

class ReviewTests(unittest.TestCase):
    def setUp(self):
        self.problem={'id':'201','open':True,'statement':'Full claim'}
        self.state={'statement':'frozen', 'proof':'proof', 'verify':{'compiles':True,'sorry_free':True,'axioms_clean':True,'frozen_match':True,'banned':None,'axioms':[], 'faithful':{'faithful':True}}}
        self.env={'lean':'pinned'}
        self.state['verify']['artifact_sha256']=fingerprint(self.problem,self.state,[],self.env)
    def result(self,records=()): return milestones(self.problem,self.state,[],self.env,records)
    def test_automatic_judge_cannot_promote(self):
        self.state['verify']['all_clear']=True
        self.assertEqual(self.result()['stage'],'mechanically_verified')
        self.assertFalse(self.result()['resolution_claim_eligible'])
    def test_stale_and_legacy_results_fail_closed(self):
        self.state['proof']='changed'
        self.assertFalse(self.result()['mechanically_verified'])
        self.state['verify'].pop('artifact_sha256')
        self.assertFalse(self.result()['mechanically_verified'])
    def test_environment_and_statement_changes_invalidate(self):
        self.env['lean']='new'
        self.assertFalse(self.result()['mechanically_verified'])
    def test_full_review_and_invalidated_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'review.md';p.write_text('independent evidence')
            records=[{'kind':k,'artifact_sha256':self.result()['artifact_sha256'],'approved':True,'independent':True,'reviewer':k,'evidence':str(p),'evidence_sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for k in ('clean_replay','statement_audit','adversarial_checks','external_review')]
            self.assertTrue(self.result(records)['resolution_claim_eligible'])
            records[-1]['reviewer']='statement_audit'
            self.assertFalse(self.result(records)['resolution_claim_eligible'])
            records[-1]['reviewer']='external_review'
            p.write_text('changed')
            self.assertFalse(self.result(records)['resolution_claim_eligible'])
    def test_sublemma_cannot_be_full_resolution(self):
        self.state['direction']='program'
        self.state['verify']['artifact_sha256']=fingerprint(self.problem,self.state,[],self.env)
        self.assertEqual(self.result()['scope'],'sublemma')
        self.assertFalse(self.result()['resolution_claim_eligible'])
    def test_failed_guard_blocks_mechanical(self):
        for key in ['compiles','sorry_free','axioms_clean','frozen_match']:
            self.state['verify'][key]=False
            self.assertFalse(self.result()['mechanically_verified'])
            self.state['verify'][key]=True

    def test_interrupted_reverification_clears_old_success(self):
        import harness as H
        with tempfile.TemporaryDirectory() as tmp:
            h=H.Harness.__new__(H.Harness)
            h.problem=self.problem;h.state=self.state;h.imports=[]
            h.state_path=Path(tmp)/'state.json'
            h.check=lambda *args: (_ for _ in ()).throw(RuntimeError('interrupted'))
            with self.assertRaisesRegex(RuntimeError,'interrupted'):
                h.stage_verify()
            saved=json.loads(h.state_path.read_text())
            self.assertNotIn('verify',saved)
            self.assertFalse(saved['solution_review']['mechanically_verified'])
    def test_semantic_provider_failure_preserves_mechanical_checkpoint(self):
        import harness as H
        with tempfile.TemporaryDirectory() as tmp:
            h=H.Harness.__new__(H.Harness);h.problem={'id':'1','statement':'True'}
            h.state={'statement':'theorem erdos_1 : True := by sorry','proof':'theorem erdos_1 : True := by trivial'}
            h.imports=[];h.run_dir=Path(tmp);h.state_path=h.run_dir/'state.json'
            h.check=lambda *args:{'ok':True,'sorries':False,'raw':"'erdos_1' does not depend on any axioms"}
            h.ask=lambda *args:(_ for _ in ()).throw(RuntimeError('out of credits'))
            with self.assertRaises(RuntimeError):h.stage_verify()
            saved=json.loads(h.state_path.read_text())
            self.assertTrue(saved['solution_review']['mechanically_verified'])
            self.assertFalse(saved['verify']['all_clear'])
