import json, unittest, tempfile
from pathlib import Path
import harness as H


def ev(**kw):
 kw.setdefault("ts", "2026-01-01T00:00:00Z")
 return json.dumps(kw)


class RunSummaryLine(unittest.TestCase):
 """One greppable line per run so any driver (Codex, Claude Code, cron, plain shell) can
 report a finished run with `tail -1` instead of parsing log.jsonl."""

 def setUp(self):
  self.tmp = tempfile.TemporaryDirectory()
  self.d = Path(self.tmp.name) / "20260101-000000-000000-erdos99677"
  self.d.mkdir(parents=True)
 def tearDown(self):
  self.tmp.cleanup()

 def _write(self, events, state=None, done=None):
  (self.d / "log.jsonl").write_text("\n".join(events) + "\n")
  if state is not None: (self.d / "state.json").write_text(json.dumps(state))
  if done is not None: (self.d / "DONE").write_text(json.dumps(done))

 def test_reports_outcome_spend_and_prefix(self):
  self._write([ev(stage="run", event="start"),
               ev(event="response", cost_usd=1.25),
               ev(event="response", cost_usd=0.75),
               ev(stage="run", event="end", outcome="proved")],
              state={"outcome": "proved", "verify": {"all_clear": True}, "mode": "fast"})
  line = H.run_summary_line(self.d, 0)
  self.assertTrue(line.startswith(H.RUN_SUMMARY_PREFIX))
  for want in ("problem=99677", "exit=0", "outcome=proved", "verified=True", "spend=$2.00", "mode=fast"):
   self.assertIn(want, line)

 def test_subrun_outcome_never_leaks_into_the_parent(self):
  """A research sub-run logs its own run/end with outcome=proved. An OPEN problem whose parent
  has not finished must NOT be reported as proved."""
  self._write([ev(stage="run", event="start")], state={"mode": "research"})
  sub = self.d / "pos"; sub.mkdir()
  (sub / "log.jsonl").write_text(ev(stage="run", event="end", outcome="proved") + "\n"
                                 + ev(event="lemma_certified", name="erdos_99677_sub1_1") + "\n"
                                 + ev(event="response", cost_usd=3.0) + "\n")
  (sub / "state.json").write_text(json.dumps({"outcome": "infrastructure_error"}))
  line = H.run_summary_line(self.d, 3)
  self.assertIn("outcome=running", line)
  self.assertNotIn("outcome=proved", line)
  self.assertIn("directions=pos:infrastructure_error", line)
  self.assertIn("lemmas=1", line)          # the child's certified lemma still counts
  self.assertIn("spend=$3.00", line)       # and so does its spend

 def test_unknown_cost_is_reported_as_unavailable_not_zero(self):
  self._write([ev(stage="run", event="start"), ev(event="response")], state={"outcome": "partial"})
  self.assertIn("spend=unavailable", H.run_summary_line(self.d, 3))

 def test_emit_never_raises_and_persists(self):
  self._write([ev(stage="run", event="start")], state={"outcome": "partial"})
  line = H.emit_run_summary(self.d, 3)
  self.assertEqual((self.d / "SUMMARY.line").read_text().strip(), line)
  self.assertIsInstance(H.emit_run_summary(Path("/nonexistent/nope"), 1), str)


if __name__ == "__main__":
 unittest.main()


class ReprintDoesNotClobber(unittest.TestCase):
 """The record a run writes about itself is authoritative. A later reprint with a wrong
 caller-supplied exit code must not overwrite it — that once turned a crashed open-problem
 run into `exit=0`, which in this harness means proved-and-verified."""

 def setUp(self):
  self.tmp = tempfile.TemporaryDirectory()
  self.d = Path(self.tmp.name) / "20260101-000000-000000-erdos99273"
  self.d.mkdir(parents=True)
  (self.d / "log.jsonl").write_text(ev(stage="run", event="start") + "\n")
  (self.d / "state.json").write_text(json.dumps({"mode": "research"}))
  (self.d / "DONE").write_text(json.dumps({"open": {}, "exit": 2}))
 def tearDown(self):
  self.tmp.cleanup()

 def test_exit_code_comes_from_DONE_when_caller_gives_none(self):
  self.assertIn("exit=2", H.run_summary_line(self.d, None))

 def test_reprint_is_read_only_by_default(self):
  authoritative = H.emit_run_summary(self.d, 2)                  # the run reports itself
  H.emit_run_summary(self.d, 0, persist=False)                   # a watcher reprints it wrongly
  self.assertEqual((self.d / "SUMMARY.line").read_text().strip(), authoritative)
  self.assertIn("exit=2", (self.d / "SUMMARY.line").read_text())

 def test_explicit_write_still_allowed(self):
  H.emit_run_summary(self.d, 2)
  H.emit_run_summary(self.d, 3, persist=True)
  self.assertIn("exit=3", (self.d / "SUMMARY.line").read_text())
