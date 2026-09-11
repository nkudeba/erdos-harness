import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Data.Fin.VecNotation

theorem erdos_493 :
    ∃ k N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n →
      ∃ a : Fin k → ℤ, (∀ i, 2 ≤ a i) ∧ (∏ i, a i) - (∑ i, a i) = n := by
  refine ⟨2, 0, fun n hn => ⟨![2, n + 2], ?_, ?_⟩⟩
  · have h0 : (0 : ℤ) ≤ n := by simpa using hn
    rw [Fin.forall_fin_two]
    constructor <;> simp <;> omega
  · simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
