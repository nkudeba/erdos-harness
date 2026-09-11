"""Unit tests for harness.py pure helpers (no Lean, no LLM). Run: python3 -m pytest tests/ -q  (or python3 tests/test_helpers.py)"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import harness as H


def test_statement_prefix_stops_at_by_sorry():
    s = "theorem erdos_1 (n : ℕ) (h : n = let k := 2; k) : n = 2 := by\n  sorry"
    assert H.statement_prefix(s).endswith(":=")
    assert "sorry" not in H.statement_prefix(s)


def test_contains_frozen_ignores_comments_and_whitespace():
    frozen = H.statement_prefix("theorem erdos_9 : 1 + 1 = 2 := by\n  sorry")
    attempt = "-- CANDIDATE 1\n-- some note\ntheorem erdos_9 :\n    1 + 1 = 2 := by\n  norm_num"
    assert H.contains_frozen(attempt, frozen)
    assert not H.contains_frozen("theorem erdos_9 : 1 + 1 = 3 := by norm_num", frozen)


def test_has_banned_word_boundaries_and_comments():
    assert H.has_banned("theorem t : True := by sorry") == "sorry"
    assert H.has_banned("theorem t : True := by sorry", allow_sorry=True) is None
    assert H.has_banned("-- the axiom of choice is fine to mention\ntheorem t : True := trivial") is None
    assert H.has_banned("axiom bad : False") == "axiom"
    assert H.has_banned("theorem t : 2 + 2 = 4 := by native_decide") == "native_decide"
    assert H.has_banned("theorem t : 2 + 2 = 4 := by decide") is None
    assert H.has_banned("theorem unsafe_looking : True := trivial") is None  # identifier, not keyword


def test_extract_directive_imports_and_compose():
    body = "-- IMPORTS: Mathlib.Data.Nat.Prime.Basic, Mathlib.Tactic.Ring\ntheorem t : True := trivial"
    assert H.extract_directive_imports(body) == ["Mathlib.Data.Nat.Prime.Basic", "Mathlib.Tactic.Ring"]
    src = H.compose(body, ["Mathlib.Tactic.Ring"])
    assert src.count("import Mathlib.Tactic.Ring") == 1
    assert "import Mathlib.Data.Nat.Prime.Basic" in src
    assert "set_option maxHeartbeats" in src


def test_lean_blocks_and_json_block():
    text = "ATTEMPT 1: plan\n```lean\ntheorem a : True := trivial\n```\n```json\n{\"faithful\": true}\n```\n```json\n[1,2]\n```"
    assert H.lean_blocks(text) == ["theorem a : True := trivial"]
    assert H.json_block(text) == {"faithful": True}
    assert H.json_block("```json\n[1,2]\n```") is None


def test_lean_message_parsing_multiline():
    chk = H.LeanChecker(H.FORMAL, 1)
    out = ("/tmp/x.lean:3:2: error: unsolved goals\nn : ℕ\n⊢ n = n\n"
           "/tmp/x.lean:9:0: warning: declaration uses 'sorry'\n")
    msgs = chk._parse(out)
    assert [m["sev"] for m in msgs] == ["error", "warning"]
    assert "⊢ n = n" in msgs[0]["msg"]


def test_lean_message_parsing_with_diagnostic_codes():
    chk = H.LeanChecker(H.FORMAL, 1)
    out = ("/tmp/x.lean:8:23: error(lean.unknownIdentifier): Unknown identifier `Polynomial.X`\n"
           "/tmp/x.lean:9:0: warning(lean.sorry): declaration uses 'sorry'\n"
           "/tmp/x.lean:11:82: error: unsolved goals\n⊢ False\n")
    msgs = chk._parse(out)
    assert [m["sev"] for m in msgs] == ["error", "warning", "error"], msgs
    assert "Polynomial.X" in msgs[0]["msg"]
    assert H.unknown_names_from_errors([msgs[0]["msg"]]) == ["Polynomial.X"]


if __name__ == "__main__":
    import inspect
    fails = 0
    for name, fn in list(globals().items()):
        if name.startswith("test_") and inspect.isfunction(fn):
            try:
                fn(); print("ok  ", name)
            except Exception as e:
                fails += 1; print("FAIL", name, repr(e))
    sys.exit(1 if fails else 0)
