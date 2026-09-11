import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
-- IMPORTS: Mathlib.Data.Real.Basic
-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
-- IMPORTS: Mathlib.Data.Real.Basic
-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
-- IMPORTS: Mathlib.Data.Real.Basic
-- IMPORTS: Mathlib.Data.Real.Basic
theorem erdos_105 :
    ∃ (n : ℕ) (A B : Finset (ℝ × ℝ)),
      A.card = n ∧
      B.card = n - 3 ∧
      Disjoint A B ∧
      (¬ ∃ a b c : ℝ,
        (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ p ∈ A, a * p.1 + b * p.2 = c) ∧
      (∀ a b c : ℝ,
        (a ≠ 0 ∨ b ≠ 0) →
        (∃ p ∈ A, ∃ q ∈ A,
          p ≠ q ∧
          a * p.1 + b * p.2 = c ∧
          a * q.1 + b * q.2 = c) →
        ∃ r ∈ B, a * r.1 + b * r.2 = c) := by
  classical
  refine ⟨9,
    {(-1, 1), (0, 0), (0, 1 / 3), (0, 1 / 2), (1 / 4, 1 / 4),
      (2 / 5, 1 / 5), (1 / 2, 0), (2 / 3, 0), (1, 0)},
    {(-1 / 2, 1 / 2), (0, 2 / 5), (1 / 3, 1 / 6), (1 / 3, 1 / 3),
      (3 / 4, 0), (2, -1)}, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num [Finset.disjoint_left, Prod.mk.injEq]
  · rintro ⟨a, b, c, hab, h⟩
    have h0 := h (0, 0) (by simp)
    have h1 := h (1, 0) (by simp)
    have h2 := h (-1, 1) (by simp)
    norm_num at h0 h1 h2
    rcases hab with ha | hb
    · exact ha (by linarith)
    · exact hb (by linarith)
  · intro a b c _ h
    rcases h with ⟨p, hp, q, hq, hne, hpLine, hqLine⟩
    try simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try norm_num at *
    all_goals
      try simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
        exists_eq_left, Prod.fst, Prod.snd]
      all_goals first
      | (left <;> linarith)
      | (right <;> left <;> linarith)
      | (right <;> right <;> left <;> linarith)
      | (right <;> right <;> right <;> left <;> linarith)
      | (right <;> right <;> right <;> right <;> left <;> linarith)
      | (right <;> right <;> right <;> right <;> right <;> linarith)
