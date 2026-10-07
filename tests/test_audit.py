"""audit.py: the mechanical audit that lets a verified proof stand without a human reading it. The pure parts run
everywhere; the Lean parts (a proof of `3 < 2` through a redefined `<`, which every TEXT check accepts) run under
DEDUCTIVE_LEAN_TESTS=1, as the other Lean-backed tests do."""
import importlib.util, os, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("audit", ROOT / "audit.py")
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)


class SourceScan(unittest.TestCase):
    def test_comments_and_strings(self):
        src = 'theorem t : True := by\n  -- sorry here is a comment\n  /- block /- nested sorry -/ still -/\n  trivial\n#check "a -- b"\n'
        body = A.strip_comments(src)
        self.assertNotIn("sorry", body)
        self.assertIn('"a -- b"', body)                       # a string literal is not a comment

    def test_forbidden_constructs(self):
        bad = {
            "sorry/admit": "theorem t : False := by sorry",
            "native_decide / compiled-code trust": "example : 2 + 2 = 4 := by native_decide",
            "kernel bypass option": "set_option debug.skipKernelTC true in\ntheorem t : False := by trivial",
            "elaboration-time code": "run_cmd Lean.logInfo \"x\"",
            "axiom / opaque declaration": "axiom cheat : False",
            "new syntax / elaborators": "macro \"evil\" : command => `(run_cmd pure ())",
            "unsafe": "unsafe def f : Nat := 0",
        }
        for label, src in bad.items():
            self.assertIn(label, A.forbidden_constructs(src), label)
        ok = "notation \"‖\" x \"‖\" => abs x\ntheorem t : 1 = 1 := rfl -- an axiom-free sorry-free proof\n"
        self.assertEqual(A.forbidden_constructs(ok), [])
        # a fresh tactic keyword (a certificate tactic, as in masked #67734's proof) is allowed: its term is
        # kernel-checked. Hooks on existing syntax and environment edits are not.
        self.assertEqual(A.forbidden_constructs('elab "prove_search46" : tactic => do\n  pure ()'), [])
        self.assertIn("new syntax / elaborators", A.forbidden_constructs('elab "evil" : command => pure ()'))
        self.assertIn("environment manipulation", A.forbidden_constructs('elab "t" : tactic => do\n  modifyEnv id'))
        self.assertIn("elaborator attributes", A.forbidden_constructs("@[command_elab Foo] def f := 0"))

    def test_frozen_names_are_fully_qualified(self):
        # train #678's statement defines `lcmInterval` inside `namespace Finset`; the constant is Finset.lcmInterval,
        # and looking up the bare name found nothing in either elaboration, which read as a failed identity check
        frozen = ("namespace Finset\ndef lcmInterval (n k : ℕ) : ℕ := n + k\nend Finset\n\nopen Finset\n\n"
                  "theorem erdos_28730 : lcmInterval 1 2 = 3 := by\n  sorry\n")
        self.assertEqual(A.frozen_names(frozen), ("erdos_28730", ["Finset.lcmInterval"]))
        self.assertEqual(A.frozen_names("namespace A\nsection\ndef f : ℕ := 0\nend\ndef g : ℕ := 1\nend A\n"
                                        "def _root_.h : ℕ := 2\ntheorem t : True := by\n  sorry"),
                         ("t", ["A.f", "A.g", "h"]))

    def test_frozen_names(self):
        frozen = ("def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=\n  True\n\n"
                  "theorem erdos_82251 :\n    ∀ a : ℕ, HasEqualIntervalSums (fun _ => a) 1 := by\n  sorry\n")
        self.assertEqual(A.frozen_names(frozen), ("erdos_82251", ["HasEqualIntervalSums"]))


class Parsing(unittest.TestCase):
    def test_dump_and_axioms(self):
        out = ("AUDIT-DUMP erdos_1 KIND theorem LEVELS [] TYPE 123 VALUE none\n"
               "AUDIT-DUMP D KIND def LEVELS [] TYPE 9 VALUE (some 42)\n"
               "'erdos_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
        self.assertEqual(A.parse_dump(out)["erdos_1"], "KIND theorem LEVELS [] TYPE 123 VALUE none")
        self.assertEqual(A.parse_axioms(out, "erdos_1"), {"propext", "Classical.choice", "Quot.sound"})
        self.assertEqual(A.parse_axioms("'x' does not depend on any axioms", "x"), set())
        self.assertIsNone(A.parse_axioms("nothing", "x"))

    def test_identity_patterns(self):
        import re
        pats = dict(A.identity_patterns({"problem": "1213"}))
        name = pats["Erdős by name"]
        self.assertTrue(re.search(name, "This is an Erdős problem."))
        self.assertTrue(re.search(name, "see erdosproblems.com"))
        self.assertFalse(re.search(name, "the Erdős–Ko–Rado theorem"))     # a named result stays in masked prompts
        self.assertFalse(re.search(name, "theorem erdos_82251 :"))           # the alias theorem name is not the id
        num = pats["problem number with context"]
        self.assertTrue(re.search(num, "Problem #1213 asks"))
        self.assertFalse(re.search(num, "the sum is 1213"))                 # arithmetic is not an identity


class ComparatorWiring(unittest.TestCase):
    """The Comparator/nanoda checks (2026-10-07) need no Lean to test their wiring."""

    def test_the_challenge_is_the_frozen_statement_under_the_proof_s_header(self):
        proof = "import Mathlib.Tactic\nset_option maxHeartbeats 400000\n\ndef f (n : ℕ) : ℕ := n\n\ntheorem erdos_T : f 1 = 1 := by\n  rfl\n"
        frozen = "def f (n : ℕ) : ℕ := n\n\ntheorem erdos_T : f 1 = 1 := by\n  sorry\n"
        ch, sol, cfg = A.comparator_files(proof, frozen, "erdos_T", ["f"], "Formal.Audit.AX")
        self.assertTrue(ch.startswith("import Mathlib.Tactic\nset_option maxHeartbeats 400000"))
        self.assertIn("theorem erdos_T : f 1 = 1 := by\n  sorry", ch)
        self.assertEqual(sol, proof)
        self.assertEqual((cfg["challenge_module"], cfg["solution_module"]), ("Formal.Audit.AX.Challenge", "Formal.Audit.AX.Solution"))
        self.assertEqual((cfg["theorem_names"], cfg["definition_names"]), (["erdos_T"], ["f"]))
        self.assertEqual(set(cfg["permitted_axioms"]), A.STD_AXIOMS)

    def test_no_tools_means_no_checks(self):
        import os
        from unittest.mock import patch
        with patch.dict(os.environ, {"COMPARATOR_BIN": "/nonexistent/comparator"}):
            self.assertIsNone(A.comparator_tools())
            self.assertEqual(A.comparator_checks("theorem erdos_T : True := trivial", "theorem erdos_T : True := by\n  sorry", "t"), {})


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "Lean-backed; set DEDUCTIVE_LEAN_TESTS=1")
class LeanChecks(unittest.TestCase):
    FROZEN = "theorem erdos_T : (3 : ℕ) < 2 := by\n  sorry\n"

    def test_a_redefined_order_passes_every_text_check_and_fails_identity(self):
        tampered = ("import Mathlib.Tactic\n\ninstance evilLT : LT ℕ := ⟨fun _ _ => True⟩\n\n"
                    "theorem erdos_T : (3 : ℕ) < 2 := by\n  exact True.intro\n")
        self.assertIn(self.FROZEN.split(":= by")[0].strip(), tampered)     # the harness's text match passes
        r = A.lean_checks(tampered, self.FROZEN, ["Mathlib.Tactic"], "test-tamper")
        for k in ("source_scan", "imports", "compiles", "no_sorry_warning", "axioms"):
            self.assertTrue(r[k]["ok"], k)
        self.assertFalse(r["statement_identity"]["ok"])
        if "comparator" in r:                        # installed (tools/install.sh): its challenge uses the real `<`
            self.assertFalse(r["comparator"]["ok"])

    def test_an_honest_proof_passes(self):
        frozen = "theorem erdos_T : (2 : ℕ) < 3 := by\n  sorry\n"
        honest = "import Mathlib.Tactic\n\ntheorem erdos_T : (2 : ℕ) < 3 := by\n  norm_num\n"
        r = A.lean_checks(honest, frozen, ["Mathlib.Tactic"], "test-honest")
        self.assertTrue(all(c["ok"] for c in r.values()), r)


if __name__ == "__main__":
    unittest.main()


class HarnessVerifyUsesTheAudit(unittest.TestCase):
    """stage_verify runs the audit on a mechanically clean final proof and clears only if it passes."""

    def _harness(self, tmp):
        import sys
        sys.path.insert(0, str(ROOT))
        import harness as H
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "1", "statement": "Is 3 < 2?"}
        h.state = {"statement": "theorem erdos_1 : (3 : ℕ) < 2 := by\n  sorry",
                   "proof": "instance evilLT : LT ℕ := ⟨fun _ _ => True⟩\n\ntheorem erdos_1 : (3 : ℕ) < 2 := by\n  exact True.intro"}
        h.state_path = Path(tmp) / "state.json"
        h.run_dir = Path(tmp)
        h.imports = ["Mathlib.Tactic"]
        h.log = H.RunLog(Path(tmp))
        h.args = type("Args", (), {"audit": "on"})()
        h.check = lambda *a: {"ok": True, "sorries": False, "raw": "'erdos_1' does not depend on any axioms"}
        return H, h

    def test_a_failed_statement_identity_blocks_all_clear_and_skips_the_judge(self):
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as tmp:
            H, h = self._harness(tmp)
            h.ask = lambda *a, **k: self.fail("the semantic judge must not run on a proof the audit rejected")
            failing = {"statement_identity": {"ok": False, "detail": "differs at: erdos_1, evilLT"},
                       "kernel_replay": {"ok": True, "detail": ""}}
            with patch.object(H.Harness, "_audit_final", return_value=failing):
                v = h.stage_verify()
            self.assertTrue(v["frozen_match"])                      # the text check alone would have passed it
            self.assertFalse(v["all_clear"])
            self.assertFalse(v["audit"]["statement_identity"]["ok"])

    def test_audit_off_keeps_the_old_path(self):
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as tmp:
            H, h = self._harness(tmp)
            h.args = type("Args", (), {"audit": "off"})()
            h.ask = lambda *a, **k: '{"faithful": false, "issues": ["judge"], "verdict": "no"}'
            with patch.object(H.Harness, "_audit_final", side_effect=AssertionError("audit must not run")):
                v = h.stage_verify()
            self.assertNotIn("audit", v)

    def test_audit_passes_allows_only_an_unavailable_kernel_replay(self):
        import sys
        sys.path.insert(0, str(ROOT))
        import harness as H
        self.assertTrue(H.audit_passes({"statement_identity": {"ok": True}, "kernel_replay": {"ok": None}}))
        self.assertFalse(H.audit_passes({"statement_identity": {"ok": None}, "kernel_replay": {"ok": True}}))
        self.assertFalse(H.audit_passes({"statement_identity": {"ok": True}, "kernel_replay": {"ok": False}}))
        self.assertFalse(H.audit_passes({}))
