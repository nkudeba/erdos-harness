"""hardsteps_lean.py writes a time-split record for a whole-problem Lean stage, so the audit's blindness checks run.

#1125's Lean proof passed all seven Lean checks and still got the verdict FAIL: no time-split record pointed at the Lean
run, so `benchmark_record` failed before provenance, probe, masking or the prompt scan ran, and the Atlas could not
count the proof."""
import importlib.util, json, tempfile, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("hardsteps_lean", ROOT / "experiments" / "idea-engine-2026-10-02" / "hardsteps_lean.py")
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)


class LeanStageRecord(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve()
        self._root, self._results = L.ROOT, L.RESULTS
        L.ROOT, L.RESULTS = self.root, self.root / "benchmarks" / "timesplit" / "results"
        L.RESULTS.mkdir(parents=True)
        (L.RESULTS / "engine-x.jsonl").write_text(json.dumps(
            {"problem": "1125", "alias": 77933, "run_dir": "runs/eng", "answer": True, "truth": "true", "split": "dev",
             "spend": 13.04}) + "\n")
        (L.RESULTS / "engine-x.grades.jsonl").write_text(json.dumps({"problem": "1125", "run_dir": "runs/eng"}) + "\n")
        self.eng, self.lean = self.root / "runs" / "eng", self.root / "runs" / "lean-erdos877933"
        for d in (self.eng, self.lean, self.root / "runs" / "hardstep"):
            d.mkdir(parents=True)
        (self.lean / "state.json").write_text(json.dumps({"benchmark": True, "verify": {"all_clear": True}}))
        (self.lean / "DONE").write_text(json.dumps({"exit": 0}))
        (self.lean / "SUMMARY.line").write_text("RUN-SUMMARY problem=877933 exit=0 spend=$2.79 llm_calls=9")

    def tearDown(self):
        L.ROOT, L.RESULTS = self._root, self._results
        self.tmp.cleanup()

    def test_a_verified_whole_problem_stage_is_recorded_as_solved(self):
        L.record_alias(self.eng, self.lean, "877933")
        L.record_alias(self.eng, self.lean, "877933")               # idempotent
        aliases = (L.RESULTS / "engine-x-lean.aliases.jsonl").read_text().splitlines()
        self.assertEqual([json.loads(a)["alias"] for a in aliases], [877933])
        row = L.record_result(self.eng, self.lean, "deep/C1", "877933", 0)
        self.assertEqual((row["problem"], row["alias"], row["tag"]), ("1125", 877933, "engine-x-lean"))
        self.assertEqual(row["run_dir"], "runs/lean-erdos877933")
        self.assertEqual((row["engine_run"], row["engine_alias"], row["engine_claim"]), ("runs/eng", 77933, "deep/C1"))
        self.assertTrue(row["solved"])
        self.assertFalse(row["contradiction"])
        self.assertEqual(row["spend"], 2.79)
        self.assertTrue(row["protocol"]["masked"] and row["protocol"]["benchmark"])

    def test_an_unverified_stage_is_not_solved(self):
        (self.lean / "DONE").write_text(json.dumps({"exit": 3}))
        self.assertFalse(L.record_result(self.eng, self.lean, "deep/C1", "877933", 3)["solved"])

    def test_a_stage_from_a_run_with_no_time_split_record_writes_nothing(self):
        self.assertIsNone(L.record_result(self.root / "runs" / "hardstep", self.lean, "r1s1/C1", "877933", 0))
        L.record_alias(self.root / "runs" / "hardstep", self.lean, "877933")
        self.assertFalse((L.RESULTS / "engine-x-lean.aliases.jsonl").exists())


if __name__ == "__main__":
    unittest.main()
