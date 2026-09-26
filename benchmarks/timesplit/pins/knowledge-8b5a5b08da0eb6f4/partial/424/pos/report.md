# Partial result — Erdős #424 (run pos)

**Status: PARTIAL — the main theorem was NOT proved.** These sorry-free auxiliary lemmas compiled against the frozen setting and are kept for reuse. They are NOT a resolution of the problem and require human review before any external claim.

## Frozen target (unproved)
```lean
/-- Smallest set containing `2, 3` and closed under `(a, b) ↦ a * b - 1` for `a ≠ b`. -/
def Erdos424.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}

theorem erdos_424 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤ ((Erdos424.hofSet ∩ Set.Icc 1 x).ncard : ℝ) := by
  sorry
```

## Compiled lemmas
- `Erdos424Aux.two_mem`
- `Erdos424Aux.three_mem`

```lean
private def Erdos424Aux.hofSet' : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}


def Erdos424.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}


-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
/-- Local copy of the frozen set (definitionally equal to `Erdos424.hofSet`), so helper lemmas can
live above the frozen block. -/

private lemma Erdos424Aux.two_mem : 2 ∈ Erdos424Aux.hofSet' :=
  fun _ h2 _ _ => h2


private lemma Erdos424Aux.three_mem : 3 ∈ Erdos424Aux.hofSet' :=
  fun _ _ h3 _ => h3

```
