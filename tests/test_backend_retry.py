"""Backend robustness: transient provider errors are retried with backoff; hard errors are not."""
import json, sys, unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H


def _resp(rc, payload=None, stdout=None, stderr=""):
    return type("R", (), {"returncode": rc, "stdout": stdout if stdout is not None else json.dumps(payload), "stderr": stderr})()


class Retry(unittest.TestCase):
    def test_transient_error_then_success(self):
        seq = [_resp(1, {"is_error": True, "subtype": "success", "result": "API Error: Can't reach the API server (ENOTFOUND)"}),
               _resp(0, {"is_error": False, "result": "PONG", "total_cost_usd": 0.1, "num_turns": 1})]
        sleeps = []
        with patch.object(H, "run_tracked", side_effect=seq), patch.object(H.time, "sleep", sleeps.append):
            b = H.ClaudeCliBackend(None, 10)
            self.assertEqual(b.complete("t", "x"), "PONG")
        self.assertEqual(sleeps, [45])
        self.assertEqual(b.calls, 2)

    def test_hard_error_not_retried(self):
        seq = [_resp(1, {"is_error": True, "subtype": "error", "result": "Spend limit reached for this month"})]
        with patch.object(H, "run_tracked", side_effect=seq), patch.object(H.time, "sleep", lambda s: None):
            with self.assertRaisesRegex(RuntimeError, "Spend limit"):
                H.ClaudeCliBackend(None, 10).complete("t", "x")

    def test_empty_failure_retried_then_gives_up(self):
        seq = [_resp(1, stdout="", stderr="")] * 4
        sleeps = []
        with patch.object(H, "run_tracked", side_effect=seq), patch.object(H.time, "sleep", sleeps.append):
            with self.assertRaises(RuntimeError):
                H.ClaudeCliBackend(None, 10).complete("t", "x")
        self.assertEqual(sleeps, [45, 90, 180])

    def test_interrupted_stream_is_retried(self):
        """#1055, 2026-10-08: a call killed after its init event (a stream cut by a system sleep) was a hard failure."""
        init = json.dumps({"type": "system", "subtype": "init", "cwd": "/x", "session_id": "s"})
        done = "\n".join([init, json.dumps({"type": "result", "subtype": "success", "is_error": False, "result": "PONG",
                                             "total_cost_usd": 0.1, "num_turns": 1})])
        seq = [_resp(-15, stdout=init + "\n"), _resp(0, stdout=done)]
        sleeps = []
        with patch.object(H, "run_tracked", side_effect=seq), patch.object(H.time, "sleep", sleeps.append):
            self.assertEqual(H.ClaudeCliBackend(None, 10).complete("t", "x"), "PONG")
        self.assertEqual(sleeps, [45])

    def test_record_carries_harness_notes(self):
        h = H.Harness.__new__(H.Harness)
        attempts = []
        res = {"errors": ["line 1:1: unsolved goals"], "notes": ["harness note: `Nat.foo` is not a known declaration"],
               "ok": False, "timeout": False}
        H.Harness._record(h, attempts, "proof-r1-a0", "plan", 1, "theorem t : True := by\n  sorry", res)
        self.assertEqual(len(attempts[0]["errors"]), 2)
        self.assertIn("not a known declaration", attempts[0]["errors"][1])
        self.assertIsNone(attempts[0]["n_sorries"])


if __name__ == "__main__":
    unittest.main()


class Harvest(unittest.TestCase):
    def test_helper_named_like_main_theorem_is_kept(self):
        import tempfile
        proof = ("-- IMPORTS: Mathlib.Data.Nat.Choose.Central\n\nprivate lemma erdos_397_key (a : ℕ) : a = a := rfl\n\n"
                 "theorem erdos_397 : True := trivial")
        with tempfile.TemporaryDirectory() as tmp, patch.object(H, "KNOWLEDGE", Path(tmp)):
            self.assertEqual(H.harvest_lemmas(proof, "397", "run"), 1)
            self.assertEqual(H.harvest_lemmas(proof, "397", "run"), 0)   # dedupe
            entry = json.loads((Path(tmp) / "lemmas.jsonl").read_text().splitlines()[0])
            self.assertEqual(entry["name"], "erdos_397_key")
            self.assertEqual(entry["imports"], ["Mathlib.Data.Nat.Choose.Central"])
            self.assertIn("needs: -- IMPORTS: Mathlib.Data.Nat.Choose.Central", H.lemmas_for("erdos_397_key a"))


class EffortTuning(unittest.TestCase):
    def test_effort_and_budget_follow_purpose(self):
        calls = []
        def fake_run(cmd, **kw):
            calls.append(cmd)
            return _resp(0, {"is_error": False, "result": "ok", "total_cost_usd": 0.01, "num_turns": 1})
        with patch.object(H, "run_tracked", side_effect=fake_run):
            b = H.ClaudeCliBackend(None, 10, 8.0)
            b.complete("literature", "x"); b.complete("formalize", "x"); b.complete("prove", "x")
        lit, form, prove = calls
        self.assertIn("medium", lit[lit.index("--effort") + 1]); self.assertEqual(lit[lit.index("--max-budget-usd") + 1], "2.5")
        self.assertIn("high", form[form.index("--effort") + 1]); self.assertEqual(form[form.index("--max-budget-usd") + 1], "4.0")
        self.assertNotIn("--effort", prove); self.assertEqual(prove[prove.index("--max-budget-usd") + 1], "8.0")


class ModelDefault(unittest.TestCase):
    """No --model must mean Opus 5.5, never the claude CLI's own default (Fable on this account) or Opus 5."""
    def _model(self, b):
        calls = []
        ok = _resp(0, {"is_error": False, "result": "ok", "total_cost_usd": 0.0, "num_turns": 1})
        with patch.object(H, "run_tracked", side_effect=lambda cmd, **k: calls.append(cmd) or ok):
            b.complete("prove", "x")
        return calls[0][calls[0].index("--model") + 1]

    def test_omitted_model_uses_opus_5_5(self):
        self.assertEqual(H.DEFAULT_CLAUDE_MODEL, "claude-opus-5-5")
        self.assertEqual(self._model(H.ClaudeCliBackend(None, 10)), "claude-opus-5-5")

    def test_explicit_model_wins(self):
        self.assertEqual(self._model(H.ClaudeCliBackend("claude-sonnet-5", 10)), "claude-sonnet-5")


class NoAmbientContext(unittest.TestCase):
    """Every claude call loads no settings source, so no CLAUDE.md (repo or global) reaches the model."""
    def test_every_call_kind_passes_empty_setting_sources(self):
        calls = []
        ok = _resp(0, {"is_error": False, "result": "ok", "total_cost_usd": 0.0, "num_turns": 1})
        with patch.object(H, "run_tracked", side_effect=lambda cmd, **k: calls.append(cmd) or ok):
            b = H.ClaudeCliBackend(None, 10)
            b.complete("prove", "x")
            b.complete_web("literature", "x")
            b.complete_agentic("prove", "x", Path("/tmp"), 3)
        for cmd in calls:
            i = cmd.index("--setting-sources")
            self.assertEqual(cmd[i + 1], "")


class JudgeVerdict(unittest.TestCase):
    def test_malformed_but_unambiguous(self):
        t = '```json\n{"faithful": true, "issues": ["a", "b"]}\n,"verdict": "ok."}\n```'
        v = H.judge_verdict(t)
        self.assertIs(v["faithful"], True)
        self.assertIn("read leniently", v["issues"][-1])
        self.assertEqual(v["verdict"], "ok.")
    def test_well_formed(self):
        self.assertIs(H.judge_verdict('```json\n{"faithful": false, "issues": []}\n```')["faithful"], False)
    def test_ambiguous_or_missing_is_no_verdict(self):
        self.assertIsNone(H.judge_verdict('"faithful": true ... "faithful": false')["faithful"])
        self.assertIsNone(H.judge_verdict("looks fine to me")["faithful"])


class JudgeIssuesAreNotTruncated(unittest.TestCase):
    def test_a_bracket_inside_an_issue_does_not_end_the_array(self):
        t = ('```json\n{"faithful": true, "issues": ["the count of C in [0, x] is at most eps x", "k = 0 is harmless"]}\n'
             ',"verdict": "ok."}\n```')
        v = H.judge_verdict(t)
        self.assertEqual(v["issues"][:2], ["the count of C in [0, x] is at most eps x", "k = 0 is harmless"])
    def test_the_recorded_16_response(self):
        import pathlib
        f = pathlib.Path(H.ROOT) / "runs" / "20260923-084313-598873-bench-erdos45592" / "pos" / "transcripts" / "009-faithful.md"
        if not f.exists():
            self.skipTest("run transcript not present")
        v = H.judge_verdict(f.read_text().split("## response", 1)[1])
        self.assertIs(v["faithful"], True)
        self.assertEqual(len(v["issues"]), 5)                       # four issues + the leniency note
        self.assertIn("[0, x]", v["issues"][1])


class Papercuts(unittest.TestCase):
    def test_a_bare_problem_id_resolves_to_the_problem_file(self):
        self.assertEqual(H.resolve_problem_path("242"), H.ROOT / "problems" / "erdos_242.json")
        self.assertEqual(H.resolve_problem_path("problems/erdos_242.json"), Path("problems/erdos_242.json"))
        self.assertEqual(H.resolve_problem_path("999999"), Path("999999"))          # no such problem: unchanged

    def test_lean_check_resolves_a_relative_destination(self):
        import tempfile, os
        seen = {}
        class P:
            def __init__(self, cmd, **k):
                seen["cmd"] = cmd
                self.returncode, self.args, self.pid = 0, cmd, 0
            def communicate(self, timeout=None):
                return "", ""
        with tempfile.TemporaryDirectory() as tmp, patch.object(H.subprocess, "Popen", P):
            old = os.getcwd()
            os.chdir(tmp)
            try:
                H.LeanChecker(Path(tmp), 5).check("example : True := trivial", Path("rel/x.lean"))
            finally:
                os.chdir(old)
        self.assertTrue(Path(seen["cmd"][-1]).is_absolute())


def _stream(result_event, texts):
    lines = [json.dumps({"type": "system", "subtype": "init"})]
    lines += [json.dumps({"type": "assistant", "message": {"content": [{"type": "text", "text": t}]}}) for t in texts]
    lines.append(json.dumps({"type": "result", **result_event}))
    return "\n".join(lines) + "\n"


class OverBudgetRecovery(unittest.TestCase):
    """A call that finished its turn past `--max-budget-usd` is billed in full, and the json result drops its text
    (measured 2026-09-24). A text-only call keeps the answer from the stream; a tool-using session still fails."""

    OVER = {"subtype": "error_max_budget_usd", "is_error": True, "stop_reason": "end_turn", "total_cost_usd": 0.1,
            "num_turns": 1, "errors": ["Reached maximum budget ($0.03)"]}

    def test_text_call_keeps_the_paid_answer(self):
        with patch.object(H, "run_tracked", return_value=_resp(1, stdout=_stream(self.OVER, ["", "THE ANSWER"]))):
            b = H.ClaudeCliBackend(None, 10)
            self.assertEqual(b.complete("plan", "x"), "THE ANSWER")
        self.assertTrue(b.last_meta["recovered_over_budget"])
        self.assertAlmostEqual(b.total_cost_usd, 0.1)                 # the spend is still counted

    def test_an_unfinished_turn_is_not_recovered(self):
        cut = {**self.OVER, "stop_reason": "max_tokens"}
        with patch.object(H, "run_tracked", return_value=_resp(1, stdout=_stream(cut, ["half an answer"]))), \
             patch.object(H.time, "sleep", lambda s: None):
            with self.assertRaisesRegex(RuntimeError, "error_max_budget_usd"):
                H.ClaudeCliBackend(None, 10).complete("plan", "x")

    def test_tool_sessions_still_fail_over_budget(self):
        with patch.object(H, "run_tracked", return_value=_resp(1, stdout=_stream(self.OVER, ["step 3 of 9"]))), \
             patch.object(H.time, "sleep", lambda s: None):
            with self.assertRaisesRegex(RuntimeError, "error_max_budget_usd"):
                H.ClaudeCliBackend(None, 10).complete_agentic("prove-agentic", "x", Path("/tmp"), 5)

    def test_a_continued_answer_is_kept_whole(self):
        """A text answer past the per-message cap continues in a second message, and `result` holds only that one."""
        ok = {"subtype": "success", "is_error": False, "result": "=== TARGET T9\nthe rest", "total_cost_usd": 3.6,
              "num_turns": 2}
        with patch.object(H, "run_tracked", return_value=_resp(0, stdout=_stream(ok, ["=== DIRECTION\nTRUE\n",
                                                                                       "=== TARGET T9\nthe rest"]))):
            self.assertEqual(H.ClaudeCliBackend(None, 10).complete("engine-frontier", "x"),
                             "=== DIRECTION\nTRUE\n=== TARGET T9\nthe rest")

    def test_a_tool_session_still_returns_its_final_reply(self):
        ok = {"subtype": "success", "is_error": False, "result": "FINAL", "total_cost_usd": 0.5, "num_turns": 4}
        with patch.object(H, "run_tracked", return_value=_resp(0, stdout=_stream(ok, ["I will run a script", "FINAL"]))):
            self.assertEqual(H.ClaudeCliBackend(None, 10).complete_agentic("prove-agentic", "x", Path("/tmp"), 5), "FINAL")

    def test_a_normal_stream_returns_the_result(self):
        ok = {"subtype": "success", "is_error": False, "result": "PONG", "total_cost_usd": 0.01, "num_turns": 1}
        with patch.object(H, "run_tracked", return_value=_resp(0, stdout=_stream(ok, ["PONG"]))):
            self.assertEqual(H.ClaudeCliBackend(None, 10).complete("t", "x"), "PONG")
