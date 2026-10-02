# Partial result — Erdős #455 (run hyp-0)

**Status: PARTIAL — the main theorem was NOT proved.** These sorry-free auxiliary lemmas compiled against the frozen setting and are kept for reuse. They are NOT a resolution of the problem and require human review before any external claim.

## Frozen target (unproved)
```lean
open Filter ENNReal

def Erdos455ConvexChain (p : ℕ → ℕ) (L : ℕ) : Prop :=
  (∀ i, i ≤ L → (p i).Prime) ∧ (∀ i, i < L → p i < p (i + 1)) ∧
    (∀ i, i + 2 ≤ L → p (i + 1) - p i ≤ p (i + 2) - p (i + 1))

theorem erdos_455_hyp_no_short_convex_chain_hyp_flat_chain :
    ∀ K : ℕ, ∃ N : ℕ, ∀ L : ℕ, N ≤ L → ∀ q : ℕ → ℕ, Erdos455ConvexChain q L →
      L ≤ K * (q 1 - q 0) → (∀ i, i < L → q (i + 1) - q i ≤ K * L) →
      K * L ^ 2 < q L := by
  sorry
```

## Compiled lemmas
- `e455_gap_ge`

```lean
def Erdos455ConvexChain (p : ℕ → ℕ) (L : ℕ) : Prop :=
  (∀ i, i ≤ L → (p i).Prime) ∧ (∀ i, i < L → p i < p (i + 1)) ∧
    (∀ i, i + 2 ≤ L → p (i + 1) - p i ≤ p (i + 2) - p (i + 1))


-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
open Filter ENNReal


private lemma e455_gap_ge (q : ℕ → ℕ) (L : ℕ) (hc : Erdos455ConvexChain q L) :
    ∀ i, i < L → q 1 - q 0 ≤ q (i + 1) - q i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hc.2.2 i (by omega)
    have e : i + 2 = i + 1 + 1 := by omega
    rw [e] at h2
    exact le_trans h1 h2

```
