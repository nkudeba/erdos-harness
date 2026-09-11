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
        with patch.object(H.subprocess, "run", side_effect=seq), patch.object(H.time, "sleep", sleeps.append):
            b = H.ClaudeCliBackend(None, 10)
            self.assertEqual(b.complete("t", "x"), "PONG")
        self.assertEqual(sleeps, [45])
        self.assertEqual(b.calls, 2)

    def test_hard_error_not_retried(self):
        seq = [_resp(1, {"is_error": True, "subtype": "error", "result": "Spend limit reached for this month"})]
        with patch.object(H.subprocess, "run", side_effect=seq), patch.object(H.time, "sleep", lambda s: None):
            with self.assertRaisesRegex(RuntimeError, "Spend limit"):
                H.ClaudeCliBackend(None, 10).complete("t", "x")

    def test_empty_failure_retried_then_gives_up(self):
        seq = [_resp(1, stdout="", stderr="")] * 4
        sleeps = []
        with patch.object(H.subprocess, "run", side_effect=seq), patch.object(H.time, "sleep", sleeps.append):
            with self.assertRaises(RuntimeError):
                H.ClaudeCliBackend(None, 10).complete("t", "x")
        self.assertEqual(sleeps, [45, 90, 180])

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
        with patch.object(H.subprocess, "run", side_effect=fake_run):
            b = H.ClaudeCliBackend(None, 10, 8.0)
            b.complete("literature", "x"); b.complete("formalize", "x"); b.complete("prove", "x")
        lit, form, prove = calls
        self.assertIn("medium", lit[lit.index("--effort") + 1]); self.assertEqual(lit[lit.index("--max-budget-usd") + 1], "2.5")
        self.assertIn("high", form[form.index("--effort") + 1]); self.assertEqual(form[form.index("--max-budget-usd") + 1], "4.0")
        self.assertNotIn("--effort", prove); self.assertEqual(prove[prove.index("--max-budget-usd") + 1], "8.0")
