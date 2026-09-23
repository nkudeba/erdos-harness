import json, subprocess, sys, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "atlas-data"))
import predict


class ReferenceClassCeilings(unittest.TestCase):
    """The priority score is a sum of hand-assigned points and has never been checked against an
    outcome, so it is not a probability. These estimates are reference-class ceilings, computed with
    zero model calls, and must never be dressed up as calibrated."""

    def setUp(self):
        self.obs = {"reconstruct": {"trials": 19, "successes": 19},
                    "resolve_open": {"trials": 7, "successes": 0}}

    def _p(self, **kw):
        base = {"id": 1, "status": "Unsolved", "state": "verifiable", "harness": "Untried",
                "assessed": {"searchFloor": None}, "partial": {"score": 50}}
        base.update(kw)
        return base

    def test_a_floor_beyond_reach_pins_the_ceiling_to_zero(self):
        r = predict.estimate(self._p(assessed={"searchFloor": 1e22}), self.obs)
        self.assertEqual(r["p_resolve_ceiling"], 0.0)
        self.assertEqual(r["reachability"], 0.0)
        self.assertIn("exceeds the bounded-search reach", r["reasons"][0])

    def test_an_open_problem_needing_an_infinite_argument_pins_to_zero(self):
        r = predict.estimate(self._p(state="open"), self.obs)
        self.assertEqual(r["p_resolve_ceiling"], 0.0)
        self.assertIn("new mathematics", r["reasons"][0])

    def test_a_reachable_finite_certificate_survives_but_stays_small(self):
        r = predict.estimate(self._p(assessed={"searchFloor": 1000}), self.obs)
        self.assertGreater(r["p_resolve_ceiling"], 0)
        self.assertLess(r["p_resolve_ceiling"], 0.2)

    def test_zero_successes_does_not_become_exactly_zero(self):
        """0/7 is not proof of impossibility; the Jeffreys prior keeps the class rate positive."""
        mean, lo, hi = predict.jeffreys(0, 7)
        self.assertGreater(mean, 0)
        self.assertLess(mean, 0.15)
        self.assertLess(lo, mean)
        self.assertGreater(hi, mean)

    def test_an_untried_solved_problem_gets_no_estimate_at_all(self):
        """19/19 was earned on targets chosen for being reconstructable. Applying it to a problem
        nobody has looked at would launder that selection into a prediction."""
        r = predict.estimate(self._p(status="Solved", state="open", harness="Untried"), self.obs)
        self.assertIsNone(r["p_resolve_ceiling"])
        self.assertFalse(r["estimable"])
        self.assertTrue(any("selection-biased" in x for x in r["reasons"]))

    def test_nothing_is_ever_marked_calibrated(self):
        for kw in ({}, {"state": "open"}, {"assessed": {"searchFloor": 1e22}}):
            self.assertFalse(predict.estimate(self._p(**kw), self.obs)["calibrated"])


class TheLogIsWriteAheadOfOutcomes(unittest.TestCase):
    """Hermetic: a temp log and temp runs/. The old test scored the LIVE log, whose settled rows then made it fail."""

    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "runs").mkdir()
        self.log = self.root / "predictions.jsonl"

    def tearDown(self):
        self.tmp.cleanup()

    def run_(self, name, start, done=None):
        d = self.root / "runs" / name
        d.mkdir()
        (d / "log.jsonl").write_text(json.dumps({"ts": start, "stage": "run", "event": "start"}) + "\n")
        if done is not None:
            (d / "DONE").write_text(json.dumps(done))

    def predict(self, *rows):
        self.log.write_text("".join(json.dumps(r) + "\n" for r in rows))

    def score(self):
        out = subprocess.run([sys.executable, str(ROOT / "atlas-data" / "predict.py"), "score",
                              "--log", str(self.log), "--runs", str(self.root / "runs")],
                             capture_output=True, text=True, cwd=str(ROOT))
        self.assertEqual(out.returncode, 0, out.stderr)
        return out.stdout

    def test_score_reports_honestly_with_no_settled_outcomes(self):
        self.run_("20260101-000000-000000-erdos5", "2026-01-01T00:00:00Z")            # still running: no DONE
        self.predict({"problem": "5", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.2, "by": "operator"},
                     {"problem": "6", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.1, "by": "operator"})
        out = self.score()
        self.assertIn("2 predictions logged, 0 with a settled outcome", out)
        self.assertIn("none settled yet", out)
        self.assertNotIn("Brier score:", out)

    def test_no_brier_when_every_outcome_is_the_same(self):
        """The live failure: 0-probability predictions of failures printed a perfect 0.0000."""
        for i, n in enumerate(("7", "273", "699")):
            self.run_(f"2026010{i+1}-000000-000000-erdos{n}", f"2026-01-0{i+1}T00:00:00Z", {"exit": 2})
        self.predict(*[{"problem": n, "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.0,
                        "by": f"triage/2026010{i+1}-000000-000000-erdos{n}"} for i, n in enumerate(("7", "273", "699"))])
        out = self.score()
        self.assertIn("3 with a settled outcome", out)
        self.assertIn("no Brier score: all 3 settled outcomes are 0", out)
        self.assertNotIn("Brier score: 0.0000", out)                       # never fake a perfect score

    def test_varied_outcomes_get_a_brier_with_a_reference(self):
        self.run_("20260101-000000-000000-erdos1", "2026-01-01T00:00:00Z", {"exit": 0})
        self.run_("20260102-000000-000000-erdos2", "2026-01-02T00:00:00Z", {"proved": False, "outcome": "partial", "verify": None})
        self.predict({"problem": "1", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.5, "by": "triage/20260101-000000-000000-erdos1"},
                     {"problem": "2", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.5, "by": "triage/20260102-000000-000000-erdos2"})
        out = self.score()
        self.assertIn("Brier score: 0.2500 over n=2", out)
        self.assertIn("constant forecast at the observed rate 0.500", out)
        self.assertIn("too few to calibrate", out)

    def test_a_prediction_is_settled_by_the_attempt_after_it_not_an_older_one(self):
        self.run_("20260101-000000-000000-erdos9", "2026-01-01T00:00:00Z", {"exit": 2})     # before the prediction
        self.predict({"problem": "9", "at": "2026-02-01T00:00:00+00:00", "p_resolve": 0.1, "by": "operator"})
        self.assertIn("0 with a settled outcome", self.score())
        self.run_("20260301-000000-000000-erdos9", "2026-03-01T00:00:00Z", {"exit": 0})     # the attempt it was for
        self.predict({"problem": "9", "at": "2026-02-01T00:00:00+00:00", "p_resolve": 0.1, "by": "operator"},
                     {"problem": "10", "at": "2026-02-01T00:00:00+00:00", "p_resolve": 0.9, "by": "operator"})
        self.run_("20260301-000000-000000-erdos10", "2026-03-01T00:00:00Z", {"exit": 2})
        out = self.score()
        self.assertIn("2 with a settled outcome", out)
        self.assertIn("Brier score: 0.8100", out)                           # (0.1-1)^2 and (0.9-0)^2

    def test_a_failed_attempt_stays_failed_when_a_later_run_succeeds(self):
        self.run_("20260101-000000-000000-erdos3", "2026-01-01T00:00:00Z", {"exit": 3})
        self.run_("20260201-000000-000000-erdos3", "2026-02-01T00:00:00Z", {"exit": 0})
        self.run_("20260101-000000-000000-erdos4", "2026-01-01T00:00:00Z", {"exit": 0})
        self.predict({"problem": "3", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.3, "by": "triage/20260101-000000-000000-erdos3"},
                     {"problem": "4", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.3, "by": "triage/20260101-000000-000000-erdos4"})
        self.assertIn("observed rate 0.500", self.score())                  # 3 failed (0), 4 succeeded (1)

    def test_fatal_and_benchmark_runs_settle_nothing(self):
        self.run_("20260101-000000-000000-erdos8", "2026-01-01T00:00:00Z", {"proved": False, "fatal": "OAuth expired"})
        self.run_("20260101-000000-000000-bench-erdos8", "2026-01-01T00:00:00Z", {"exit": 0})
        self.predict({"problem": "8", "at": "2025-12-31T00:00:00+00:00", "p_resolve": 0.3, "by": "operator"})
        self.assertIn("0 with a settled outcome", self.score())


if __name__ == "__main__":
    unittest.main()
