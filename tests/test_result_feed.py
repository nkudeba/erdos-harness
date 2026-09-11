import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import shutil
import result_feed as F

class FeedTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name);self.run=self.root/'runs'/'sample-erdos201';self.run.mkdir(parents=True)
  self.state={'problem_input':{'id':'201','open':True},'proof':'SECRET PROOF','outcome':'proved','verify':{'all_clear':True,'faithful':{'faithful':True}},'stop_reason':'SECRET TOKEN'}
  (self.run/'state.json').write_text(json.dumps(self.state))
 def test_allowlist_does_not_publish_private_content(self):
  row=F.summarize(self.run,self.root);serialized=json.dumps(row)
  self.assertNotIn('SECRET',serialized);self.assertNotIn(str(self.root),serialized)
  self.assertFalse(row['mechanical']);self.assertFalse(row['claimEligible']);self.assertEqual(row['stage'],'legacy_automated_verification')
 def test_failed_upload_does_not_acknowledge_and_retry_is_idempotent(self):
  local=self.root/'local';local.mkdir();(local/'config.json').write_text('{"url":"https://example.invalid"}')
  with patch.object(F,'upload',side_effect=OSError('offline')):
   with self.assertRaises(OSError):F.sync(self.root,local)
  self.assertFalse((local/'ack.json').exists())
  with patch.object(F,'upload') as upload:
   self.assertEqual(F.sync(self.root,local),1);self.assertEqual(F.sync(self.root,local),0)
   self.assertEqual(upload.call_args.args[1],[])
 def test_crash_and_restart_override_stale_completion(self):
  (self.run/'DONE').write_text(json.dumps({'fatal':'private detail'}));self.assertEqual(F.summarize(self.run,self.root)['outcome'],'infrastructure_error')
  (self.run/'log.jsonl').write_text(json.dumps({'stage':'run','event':'start'})+'\n')
  self.assertEqual(F.summarize(self.run,self.root)['outcome'],'running')
 def test_invalid_problem_not_exported(self):
  self.state['problem_input']['id']='9999';(self.run/'state.json').write_text(json.dumps(self.state));self.assertIsNone(F.summarize(self.run,self.root))


class RankingPublication(unittest.TestCase):
    """Score revisions ride the run-summary channel so the site needs no redeploy to show them."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        (self.tmp / "atlas-data").mkdir()
        self.write(score=8, rationale=["near-misses are all proved-safe families"], requirements=["verify the claim"])

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write(self, score, rationale, requirements, pid=488):
        (self.tmp / "atlas-data" / "rankings.json").write_text(json.dumps({"problems": [
            {"id": pid, "score": score, "rationale": rationale, "requirements": requirements},
            {"id": 999, "score": 40, "rationale": ["unreviewed"], "requirements": []}]}))
        (self.tmp / "atlas-data" / "reviewed.json").write_text(json.dumps({str(pid): {"score": score}}))

    def test_only_reviewed_problems_are_published(self):
        rows = F.ranking_rows(self.tmp)
        self.assertEqual([r["problem"] for r in rows], [488])   # 999 has no review, so it is not a revision

    def test_payload_matches_the_site_validator(self):
        row = F.ranking_rows(self.tmp)[0]
        # Must match lib/live-results.ts validateRanking exactly, or the site rejects the payload.
        self.assertEqual(sorted(row), ["brief", "partialScore", "problem", "rationale", "requirements",
                                       "revision", "score", "updatedAt"])
        self.assertTrue(row["brief"] is None or isinstance(row["brief"], str))
        self.assertRegex(row["revision"], r"^\d{20}$")
        self.assertRegex(row["updatedAt"], r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d{3}Z$")
        self.assertTrue(1 <= row["score"] <= 99)
        self.assertTrue(all(0 < len(s) <= 600 for s in row["rationale"] + row["requirements"]))
        self.assertTrue(row["partialScore"] is None or 1 <= row["partialScore"] <= 80)

    def test_partial_score_rides_along_and_changes_the_revision(self):
        """The second axis is published too, so the site does not have to rebuild to show it."""
        self.assertIsNone(F.ranking_rows(self.tmp)[0]["partialScore"])   # absent from the fixture
        first = F.ranking_rows(self.tmp)[0]["revision"]
        data = json.loads((self.tmp / "atlas-data" / "rankings.json").read_text())
        data["problems"][0]["partial"] = {"score": 63}
        (self.tmp / "atlas-data" / "rankings.json").write_text(json.dumps(data))
        row = F.ranking_rows(self.tmp)[0]
        self.assertEqual(row["partialScore"], 63)
        self.assertNotEqual(row["revision"][-6:], first[-6:], "a changed axis must publish a new revision")

    def test_revision_tracks_content_not_the_clock(self):
        first = F.ranking_rows(self.tmp)[0]["revision"]
        self.assertEqual(first[-6:], F.ranking_rows(self.tmp)[0]["revision"][-6:])   # unchanged content
        self.write(score=8, rationale=["a different reason"], requirements=["verify the claim"])
        self.assertNotEqual(first[-6:], F.ranking_rows(self.tmp)[0]["revision"][-6:])
        self.write(score=42, rationale=["near-misses are all proved-safe families"], requirements=["verify the claim"])
        self.assertNotEqual(first[-6:], F.ranking_rows(self.tmp)[0]["revision"][-6:])

    def test_oversized_and_malformed_entries_are_dropped(self):
        self.write(score=8, rationale=["x" * 900, "kept"], requirements=[""])
        row = F.ranking_rows(self.tmp)[0]
        self.assertEqual(row["rationale"], ["kept"])
        self.assertEqual(row["requirements"], [])
        self.write(score=0, rationale=["out of range"], requirements=[])
        self.assertEqual(F.ranking_rows(self.tmp), [])

    def test_missing_atlas_files_are_not_an_error(self):
        shutil.rmtree(self.tmp / "atlas-data")
        self.assertEqual(F.ranking_rows(self.tmp), [])

    def test_old_site_rejecting_rankings_still_gets_the_runs(self):
        """A site built before live rankings 400s the extra field; runs must still publish."""
        import urllib.error
        seen = []

        def fake_post(config, body):
            seen.append(sorted(body))
            if "rankings" in body:
                raise urllib.error.HTTPError("u", 400, "Invalid results payload", {}, None)
            return {"accepted": len(body["runs"])}

        with patch.object(F, "post", fake_post):
            took = F.upload({"url": "https://h/x", "host": "h", "ingest_key": "k", "dispatch_token": "t"},
                            [], F.ranking_rows(self.tmp))
        self.assertFalse(took, "must report that the revisions were not accepted")
        self.assertEqual(seen, [["rankings", "runs", "schemaVersion"], ["runs", "schemaVersion"]])

    def test_new_site_accepts_both(self):
        with patch.object(F, "post", lambda c, b: {"accepted": len(b["runs"]), "rankings": len(b.get("rankings", []))}):
            self.assertTrue(F.upload({"url": "https://h/x", "host": "h", "ingest_key": "k", "dispatch_token": "t"},
                                     [], F.ranking_rows(self.tmp)))

    def test_a_real_failure_is_not_swallowed(self):
        import urllib.error

        def fake_post(config, body):
            raise urllib.error.HTTPError("u", 401, "Unauthorized publisher", {}, None)

        with patch.object(F, "post", fake_post):
            with self.assertRaises(urllib.error.HTTPError):
                F.upload({"url": "https://h/x", "host": "h", "ingest_key": "k", "dispatch_token": "t"},
                         [], F.ranking_rows(self.tmp))


class PartialAxisOverride(unittest.TestCase):
    """CLAUDE.md: two axes, never summed. `score` asks whether a COMPLETE proof is reachable; `partial`
    asks how much certified partial value is. record_finding could revise score but not partial, so the
    axis that actually matters for an open problem stayed heuristic forever -- and banked partial value
    got smuggled into `score` instead, which is what put #677 above #273 against the assessment."""

    def test_a_manual_partial_overrides_the_heuristic_and_keeps_score_independent(self):
        import json as _json, subprocess as _sp, sys as _sys, pathlib as _p
        rev = _p.Path("atlas-data/reviewed.json")
        data = _json.loads(rev.read_text())
        self.assertEqual(data["273"]["partial"], 64)
        self.assertEqual(data["273"]["score"], 12)
        ranked = {r["id"]: r for r in _json.loads(_p.Path("atlas-data/rankings.json").read_text())["problems"]}
        self.assertEqual(ranked[273]["partial"]["score"], 64)      # override reached the ranking
        self.assertEqual(ranked[273]["score"], 12)                  # and did not leak into the other axis
        self.assertLess(ranked[273]["rank"], ranked[677]["rank"])   # the corrected ordering holds
        labels = [s["label"] for s in ranked[273]["partial"]["signals"]]
        self.assertIn("Manual partial-value review", labels)        # the adjustment is visible, not silent
