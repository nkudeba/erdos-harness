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


class SpendIsAttributedByOwnership(unittest.TestCase):
 """Attribution by time alone charged an older run, when resumed, with every later run's sub-runs (the first
 masked #275 run would have read $23.74 against a true $8.05). Sub-runs now record `owner_runs`."""

 def setUp(self):
  self.tmp = tempfile.TemporaryDirectory()
  self.root = Path(self.tmp.name)
  self._old_root = H.ROOT
  H.ROOT = self.root
  self.old = self._run("20260101-000000-000000-erdos99", "2026-01-01T00:00:00Z", 1.0)
  self.new = self._run("20260201-000000-000000-erdos99", "2026-02-01T00:00:00Z", 2.0)
 def tearDown(self):
  H.ROOT = self._old_root
  self.tmp.cleanup()

 def _run(self, name, ts, cost):
  d = self.root / "runs" / name
  d.mkdir(parents=True)
  (d / "log.jsonl").write_text(json.dumps({"ts": ts, "stage": "run", "event": "start"}) + "\n" +
                               json.dumps({"ts": ts, "stage": "llm", "event": "response", "cost_usd": cost}) + "\n")
  return d

 def _harness(self, d):
  h = H.Harness.__new__(H.Harness)
  h.run_dir, h.problem, h.direction = d, {"id": "99"}, None
  h.log = argparse.Namespace(path=d / "log.jsonl")
  h.llm = argparse.Namespace(total_cost_usd=0.0)
  return h

 def _sub(self, rel, cost, ts, owners=None):
  d = self.root / "programs" / "erdos_99" / rel
  d.mkdir(parents=True)
  (d / "log.jsonl").write_text(json.dumps({"ts": ts, "stage": "llm", "event": "response", "cost_usd": cost}) + "\n")
  if owners is not None:
   (d / "state.json").write_text(json.dumps({"owner_runs": [str(o.resolve()) for o in owners]}))

 def test_a_resumed_older_run_is_not_charged_a_newer_runs_subruns(self):
  self._sub("cycles/new-c1/hyp-0", 5.0, "2026-02-01T01:00:00Z", owners=[self.new])
  self.assertAlmostEqual(self._harness(self.old).spent_usd(), 1.0)     # the old rule read 6.0
  self.assertAlmostEqual(self._harness(self.new).spent_usd(), 7.0)

 def test_ownership_beats_the_time_window(self):
  # the old run's sub-run, resumed after the new run started, still belongs to the old run only
  self._sub("cycles/old-c1/hyp-0", 3.0, "2026-03-01T00:00:00Z", owners=[self.old])
  self.assertAlmostEqual(self._harness(self.old).spent_usd(), 4.0)
  self.assertAlmostEqual(self._harness(self.new).spent_usd(), 2.0)

 def test_a_grandchild_is_charged_to_the_root(self):
  child = self.root / "programs" / "erdos_99" / "cycles" / "new-c1" / "hyp-0"
  self._sub("cycles/new-c1/hyp-0", 1.0, "2026-02-01T01:00:00Z", owners=[self.new])
  self._sub("sub/erdos_99_hyp_a/cycles/c1/hyp-0", 4.0, "2026-02-01T02:00:00Z", owners=[child, self.new])
  self.assertAlmostEqual(self._harness(self.new).spent_usd(), 7.0)

 def test_legacy_subruns_keep_the_time_window(self):
  self._sub("cycles/legacy/hyp-0", 9.0, "2026-02-01T05:00:00Z")          # no owner_runs
  self.assertAlmostEqual(self._harness(self.new).spent_usd(), 11.0)

 def test_a_legacy_window_ends_where_the_next_run_starts(self):
  """The live #275 case: unmarked sub-runs of the second run must not be charged to the first."""
  self._sub("cycles/old-legacy/hyp-0", 4.0, "2026-01-01T01:00:00Z")      # during the old run
  self._sub("cycles/new-legacy/hyp-0", 6.0, "2026-02-01T01:00:00Z")      # during the new run
  self.assertAlmostEqual(self._harness(self.old).spent_usd(), 5.0)       # the old rule read 11.0
  self.assertAlmostEqual(self._harness(self.new).spent_usd(), 8.0)

 def test_owner_chain_extends_the_parents(self):
  h = self._harness(self.new)
  h.state = {"owner_runs": ["/runs/root"]}
  self.assertEqual(H.owner_chain(h), [str(self.new.resolve()), "/runs/root"])


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


class OpenBudgetHandover(unittest.TestCase):
 """A direction that stops early used to strand its unspent half of the --open budget."""

 def _stub(self, spent, cap):
  return argparse.Namespace(spent_usd=lambda: spent, args=argparse.Namespace(run_budget=cap))

 def _parent(self, spent):
  h = H.Harness.__new__(H.Harness)
  events = []
  h.log = argparse.Namespace(event=lambda *a, **k: events.append((a, k)))
  h.spent_usd = lambda: spent
  return h, events

 def test_the_survivor_gets_what_the_run_has_left(self):
  parent, events = self._parent(3.5)                 # 0.5 parent + 1.0 pos + 2.0 neg
  kids = {"pos": self._stub(1.0, 4.75), "neg": self._stub(2.0, 4.75)}
  parent._hand_over_budget("neg", kids, {"neg": 3}, 10.0)
  self.assertAlmostEqual(kids["pos"].args.run_budget, 1.0 + 6.5)
  self.assertEqual(events[0][0], ("open", "budget_handover"))

 def test_an_overshooting_sibling_lowers_the_cap(self):
  parent, _ = self._parent(9.8)
  kids = {"pos": self._stub(1.0, 4.75), "neg": self._stub(8.3, 4.75)}
  parent._hand_over_budget("neg", kids, {"neg": 3}, 10.0)
  self.assertAlmostEqual(kids["pos"].args.run_budget, 1.2)

 def test_nothing_changes_when_both_are_done_or_there_is_no_budget(self):
  parent, events = self._parent(3.0)
  kids = {"pos": self._stub(1.0, 4.0), "neg": self._stub(2.0, 4.0)}
  parent._hand_over_budget("neg", kids, {"neg": 3, "pos": 3}, 10.0)
  parent._hand_over_budget("neg", kids, {"neg": 3}, None)
  self.assertEqual(kids["pos"].args.run_budget, 4.0)
  self.assertEqual(events, [])

 def test_run_open_calls_it_when_a_direction_ends(self):
  import inspect
  self.assertIn("self._hand_over_budget(direction, children, results, budget)", inspect.getsource(H.Harness.run_open))
