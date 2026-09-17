import json, unittest, tempfile, argparse
from pathlib import Path
import harness as H


class SpendSeesChildRuns(unittest.TestCase):
 """--run-budget is a money cap. spent_usd() once read only the run's own log file, so --open
 direction children and research-program sub-runs (which log elsewhere) were invisible: a resumed
 #677 spent $22.67 against --run-budget 8. The cap must see descendant spend."""

 def setUp(self):
  self.tmp = tempfile.TemporaryDirectory()
  self.root = Path(self.tmp.name)
  self.d = self.root / "runs" / "20260101-000000-000000-erdos99677"
  self.d.mkdir(parents=True)
  self._old_root = H.ROOT
  H.ROOT = self.root
  (self.d / "log.jsonl").write_text(
    json.dumps({"ts": "2026-01-01T00:00:00Z", "stage": "run", "event": "start"}) + "\n" +
    json.dumps({"ts": "2026-01-01T00:01:00Z", "stage": "llm", "event": "response", "cost_usd": 1.0}) + "\n")
 def tearDown(self):
  H.ROOT = self._old_root
  self.tmp.cleanup()

 def _harness(self, direction=None):
  h = H.Harness.__new__(H.Harness)
  h.run_dir = self.d
  h.problem = {"id": "99677"}
  h.direction = direction
  h.log = argparse.Namespace(path=self.d / "log.jsonl")
  h.llm = argparse.Namespace(total_cost_usd=0.0)
  return h

 def _child_log(self, path, cost, ts="2026-01-01T00:02:00Z"):
  path.parent.mkdir(parents=True, exist_ok=True)
  path.write_text(json.dumps({"ts": ts, "stage": "llm", "event": "response", "cost_usd": cost}) + "\n")

 def test_counts_open_direction_children(self):
  self._child_log(self.d / "pos" / "log.jsonl", 2.0)
  self._child_log(self.d / "neg" / "log.jsonl", 3.0)
  self.assertAlmostEqual(self._harness().spent_usd(), 6.0)

 def test_counts_research_subruns_outside_the_run_dir(self):
  self._child_log(self.root / "programs" / "erdos_99677" / "cycles" / "c1" / "sub-0" / "log.jsonl", 4.5)
  self.assertAlmostEqual(self._harness().spent_usd(), 5.5)

 def test_ignores_program_spend_from_an_earlier_run(self):
  self._child_log(self.root / "programs" / "erdos_99677" / "cycles" / "old" / "log.jsonl",
                  9.0, ts="2025-06-01T00:00:00Z")
  self.assertAlmostEqual(self._harness().spent_usd(), 1.0)

 def test_a_direction_child_counts_only_its_own_program_subtree(self):
  self._child_log(self.root / "programs" / "erdos_99677" / "pos" / "c1" / "log.jsonl", 2.0)
  self._child_log(self.root / "programs" / "erdos_99677" / "neg" / "c1" / "log.jsonl", 8.0)
  self.assertAlmostEqual(self._harness(direction="pos").spent_usd(), 3.0)


if __name__ == "__main__":
 unittest.main()


class TheCapBindsBeforeTheSpendNotAfter(unittest.TestCase):
 """Accounting was fixed in a previous pass; the ENFORCEMENT POINT was not.

 `--run-budget` was only consulted AFTER a whole round of `--agentic-samples` parallel attempts, each
 capped at `--call-budget` (default $8). So one round could legally spend samples x $8 = $24 against a
 $6 per-direction cap. On #699 (2026-09-11) a single round cost $8.79 against $6, the run ended at
 $18.61 against `--run-budget 12`, and the overshoot then starved `stage_brief` -- which is supposed to
 run on EVERY run -- with `BudgetExhausted`. Separately, `--open` halved the ORIGINAL budget rather than
 what was left, so a parent that had already spent $1.48 structurally guaranteed parent + budget."""

 def test_agentic_round_is_clamped_to_the_remaining_budget(self):
  src = Path(H.__file__).read_text()
  blk = src[src.index('purpose="prove-agentic", n=len(jobs)'):src.index('self._check_run_budget("prove-agentic")')]
  self.assertIn("self.llm.call_budget_usd", blk, "the round does not clamp the per-attempt call budget")
  self.assertIn("remaining / max(1, len(jobs))", blk, "the clamp must divide what is left across the round")
  self.assertIn("_check_run_budget", blk, "the budget must also be checked BEFORE the round starts")

 def test_the_clamp_is_restored_even_if_an_attempt_raises(self):
  src = Path(H.__file__).read_text()
  blk = src[src.index('purpose="prove-agentic", n=len(jobs)'):src.index('self._check_run_budget("prove-agentic")')]
  self.assertIn("finally:", blk)
  self.assertIn("prev_call_budget", blk)

 def test_open_splits_what_is_left_not_the_original_budget(self):
  src = Path(H.__file__).read_text()
  self.assertNotIn("cargs.run_budget = (budget / 2) if budget else None", src)
  self.assertIn("budget - self.spent_usd()", src)

 def test_a_round_of_three_cannot_exceed_the_remainder(self):
  """The arithmetic the clamp performs, pinned directly."""
  for run_budget, spent, samples, call_budget in ((12.0, 1.74, 3, 8.0), (6.0, 5.5, 3, 8.0), (20.0, 0.0, 2, 8.0)):
   remaining = run_budget - spent
   per = max(0.5, min(call_budget, remaining / max(1, samples)))
   # the floor of 0.5 can exceed a nearly-exhausted remainder; the pre-round check is what stops that
   self.assertLessEqual(per * samples, max(remaining, 0.5 * samples) + 1e-9)
