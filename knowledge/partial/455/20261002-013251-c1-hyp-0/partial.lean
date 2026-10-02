import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Formal.Programs.Erdos455PosSubad487df8

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


private lemma erdos455_gap_mono (q : ℕ → ℕ) (L : ℕ) (hc : Erdos455ConvexChain q L) :
    ∀ i, i < L → q 1 - q 0 ≤ q (i + 1) - q i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ n ih =>
    intro hn
    exact le_trans (ih (by omega)) (hc.2.2 n (by omega))


private lemma erdos455_chain_mono (q : ℕ → ℕ) (L : ℕ)
    (h : ∀ i, i < L → q i < q (i + 1)) : ∀ i, i ≤ L → q 0 + i ≤ q i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := h n (by omega)
    omega


private lemma erdos455_gap_ge (q : ℕ → ℕ) (L : ℕ) (hc : Erdos455ConvexChain q L) :
    ∀ i, i < L → q 1 - q 0 ≤ q (i + 1) - q i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hc.2.2 n (by omega)
    have e2 : n + 1 + 1 = n + 2 := rfl
    rw [e2]
    omega
