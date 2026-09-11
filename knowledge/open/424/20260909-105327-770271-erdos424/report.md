# Open problem #424 — two-direction attack (run 20260909-105327-770271-erdos424)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Let $a_1=2$ and $a_2=3$ and continue the sequence by appending to $a_1,\ldots,a_n$ all possible values of $a_ia_j-1$ with $i\neq j$. Is it true that the set of integers which eventually appear has positive density?
- triage: fast — open + research depth without --allow-research: fast+agentic+decompose, then partial results

## Direction `pos` — outcome: **partial** (exit 3)
```lean
/-- Smallest set containing `2, 3` and closed under `(a, b) ↦ a * b - 1` for `a ≠ b`. -/
def Erdos424.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}

theorem erdos_424 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤ ((Erdos424.hofSet ∩ Set.Icc 1 x).ncard : ℝ) := by
  sorry
```
- partial results: {'dir': '/Users/nicolas.kudeba/workspace/erdos-harness/knowledge/partial/424/pos', 'lemmas': ['Erdos424Aux.two_mem', 'Erdos424Aux.three_mem']}
- spent: $3.67

## Direction `neg` — outcome: **not_proved** (exit 2)
```lean
/-- Smallest set containing `2, 3` and closed under `(a, b) ↦ a * b - 1` for `a ≠ b`. -/
def Erdos424.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}

theorem erdos_424_neg :
    ¬ (∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤ ((Erdos424.hofSet ∩ Set.Icc 1 x).ncard : ℝ)) := by
  sorry
```
- spent: $3.45

