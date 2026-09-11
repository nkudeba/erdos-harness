"""End-to-end pipeline test with a scripted fake LLM (real Lean, no API spend). ~3 min.
Run: python3 tests/test_pipeline_mock.py
Scenario (Erdős #674): round-1 prove attempt is broken (unknown identifier from a non-imported module +
a bad tactic); the harness must auto-import the module, record the failed code, and surface it as REPAIR
CONTEXT in round 2, where the fake LLM returns the known-good proof only if that context is present."""
import sys, os, json, argparse, shutil, tempfile
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import harness as H

STATEMENT = "theorem erdos_674 : ∃ x y z : ℕ, 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z := by\n  sorry"
GOOD = """-- IMPORTS: Mathlib.Tactic.NormNum.Pow
private lemma erdos674_key (X Y Z : ℕ) (h2 : 12 * X + 8 * Y = 11 * Z)
    (h3 : 6 * X + 8 * Y = 7 * Z) :
    ((2 : ℕ) ^ 12 * 3 ^ 6) ^ X * ((2 : ℕ) ^ 8 * 3 ^ 8) ^ Y = ((2 : ℕ) ^ 11 * 3 ^ 7) ^ Z := by
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_mul, mul_mul_mul_comm, ← pow_add, ← pow_add, h2, h3]

theorem erdos_674 : ∃ x y z : ℕ, 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z := by
  refine ⟨2 ^ 12 * 3 ^ 6, 2 ^ 8 * 3 ^ 8, 2 ^ 11 * 3 ^ 7, by norm_num, by norm_num,
    by norm_num, ?_⟩
  exact erdos674_key (2 ^ 12 * 3 ^ 6) (2 ^ 8 * 3 ^ 8) (2 ^ 11 * 3 ^ 7)
    (by norm_num) (by norm_num)"""
# broken: references Polynomial.X (lives in Mathlib.Algebra.Polynomial.Basic, not imported by the problem's header)
BAD = """private lemma silly : (Polynomial.X : Polynomial ℤ) = Polynomial.X := rfl

theorem erdos_674 : ∃ x y z : ℕ, 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z := by
  refine ⟨2, 2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num"""


class FakeLLM:
    def __init__(self):
        self.last_meta = {"cost_usd": 0.01, "turns": 1}
        self.prompts = []

    def complete(self, purpose, prompt):
        self.prompts.append((purpose, prompt))
        if purpose == "literature":
            return "Ko 1940: witness x = 2^12*3^6, y = 2^8*3^8, z = 2^11*3^7. Useful: Nat.succ_mul_centralBinom_succ (irrelevant), pow_mul, mul_pow, Nat.totally_fake_lemma."
        if purpose == "formalize":
            return f"```lean\n-- CANDIDATE 1\n{STATEMENT}\n```\n```lean\n-- CANDIDATE 2\n{STATEMENT}\n```\nFAITHFULNESS NOTES: fine."
        if purpose == "assess":
            return '```json\n{"shape": "witness", "status": "resolved", "depth": "trivial", "computable": true, "known_bound": null, "routes": ["explicit witness"], "recommended_mode": "fast", "budget_tier": "S", "rationale": "known witness"}\n```'
        if purpose == "critic":
            return "- the plan was fine; fix the arithmetic"
        if purpose == "crosscheck":
            return '```json\n{"ranking": [0, 1], "issues": {"0": "none found"}, "sanity_lean": ""}\n```'
        if purpose == "prove":
            if "REPAIR CONTEXT" in prompt and "silly" in prompt:
                return f"ATTEMPT 1: repair\n```lean\n{GOOD}\n```"
            return f"ATTEMPT 1: broken on purpose\n```lean\n{BAD}\n```"
        if purpose == "backtranslate":
            return "There exist naturals x, y, z > 1 with x^x * y^y = z^z."
        if purpose == "faithful":
            return '```json\n{"faithful": true, "issues": [], "verdict": "same"}\n```'
        raise AssertionError(purpose)


def main():
    tmp = tempfile.mkdtemp(prefix="erdos-mock-", dir=os.environ.get("ERDOS_TEST_TMP") or None)
    args = argparse.Namespace(problem=str(H.ROOT / "problems" / "erdos_674.json"), resume=tmp, backend="file",
                              model=None, samples=1, rounds=3, decompose_rounds=2, skip_literature=False,
                              lean_timeout=420, llm_timeout=60, call_budget=1.0, agentic="off", agentic_after=1,
                              agentic_samples=1, agentic_turns=5)
    # Mock judgments must never overwrite the real verified-proof library.
    H.RUNS = H.Path(tmp) / "runs"
    H.RUNS.mkdir()
    H.KNOWLEDGE = H.Path(tmp) / "knowledge"
    H.KNOWLEDGE.mkdir()
    shutil.copy(H.ROOT / "knowledge" / "playbook.md", H.KNOWLEDGE / "playbook.md")
    h = H.Harness(args)
    fake = FakeLLM()
    h.llm = fake
    rc = h.run()
    events = [json.loads(l) for l in open(h.log.path)]
    ev = {(e["stage"], e["event"]) for e in events}
    assert rc == 0, "pipeline should prove"
    assert h.state["verify"]["all_clear"], h.state["verify"]
    assert ("lean", "auto_import") in ev, "auto-import should have fired for Polynomial.X"
    assert "Mathlib.Algebra.Polynomial.Basic" in h.state.get("auto_imports", []), h.state.get("auto_imports")
    prove_prompts = [p for (pu, p) in fake.prompts if pu == "prove"]
    assert len(prove_prompts) == 2, len(prove_prompts)
    assert "REPAIR CONTEXT" in prove_prompts[1] and "silly" in prove_prompts[1], "round 2 must carry the failed code"
    assert "DECLARATION CHECK" in prove_prompts[0] and "Nat.totally_fake_lemma" in prove_prompts[0] and "NOT FOUND" in prove_prompts[0]
    assert "PLAYBOOK" in prove_prompts[0]
    assert (H.Path(tmp) / "final" / "Erdos674.lean").exists()
    rep = (H.Path(tmp) / "report.md").read_text()
    assert "cost: $" in rep and "auto-added" in rep, rep[:600]
    assert h.state["attempts"][0]["code"].startswith("private lemma silly")
    print("PIPELINE MOCK TEST PASSED; run dir:", tmp)
    print("prove attempts recorded:", [(a["name"], a.get("compiled"), len(a["errors"])) for a in h.state["attempts"]])
    print("report head:\n" + "\n".join(rep.splitlines()[:9]))
    shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
