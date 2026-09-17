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
    def test_score_reports_honestly_with_no_settled_outcomes(self):
        out = subprocess.run([sys.executable, str(ROOT / "atlas-data" / "predict.py"), "score"],
                             capture_output=True, text=True, cwd=str(ROOT))
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertRegex(out.stdout, r"no predictions logged yet|predictions logged")
        self.assertNotIn("Brier score: 0.0000", out.stdout)   # never fake a perfect score


if __name__ == "__main__":
    unittest.main()
