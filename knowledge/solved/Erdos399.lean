import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

theorem erdos_399 :
    ∃ n x y k : ℕ, 1 < x * y ∧ 2 < k ∧
      (Nat.factorial n = x ^ k + y ^ k ∨ Nat.factorial n + y ^ k = x ^ k) := by
  refine ⟨10, 48, 36, 4, by norm_num, by norm_num, Or.inr ?_⟩
  norm_num [Nat.factorial]
