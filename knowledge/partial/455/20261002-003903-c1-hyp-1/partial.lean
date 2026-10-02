import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

def Erdos455ConvexChain (p : ℕ → ℕ) (L : ℕ) : Prop :=
  (∀ i, i ≤ L → (p i).Prime) ∧ (∀ i, i < L → p i < p (i + 1)) ∧
    (∀ i, i + 2 ≤ L → p (i + 1) - p i ≤ p (i + 2) - p (i + 1))


-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
open Filter ENNReal


private lemma erdos455_gap_mono (q : ℕ → ℕ) (L : ℕ) (h : Erdos455ConvexChain q L) :
    ∀ i, i < L → q 1 - q 0 ≤ q (i + 1) - q i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := h.2.2 k (by omega)
    show q 1 - q 0 ≤ q (k + 2) - q (k + 1)
    omega


private lemma erdos455_gap_mono' (q : ℕ → ℕ) (L : ℕ) (h : Erdos455ConvexChain q L) :
    ∀ i, i < L → q 1 - q 0 ≤ q (i + 1) - q i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := h.2.2 k (by omega)
    have e : k + 1 + 1 = k + 2 := rfl
    rw [e]
    omega
