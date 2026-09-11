import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Algebra.Order.Field.Rat
-- IMPORTS: Mathlib.Tactic.LinearCombination

private lemma erdos_316_int (S : Finset ℕ) (hS : ∀ n ∈ S, n ∣ 120) :
    ∃ k : ℕ, 120 * ∑ n ∈ S, (1 : ℚ) / n = k := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨k, hk⟩ := ih fun n hn => hS n (Finset.mem_insert_of_mem hn)
    obtain ⟨m, hm⟩ := hS a (Finset.mem_insert_self a s)
    have ha0 : (a : ℚ) ≠ 0 := by
      have : a ≠ 0 := by
        rintro rfl
        omega
      exact_mod_cast this
    have hm' : (120 : ℚ) = a * m := by exact_mod_cast hm
    refine ⟨m + k, ?_⟩
    rw [Finset.sum_insert ha, mul_add, hk]
    push_cast
    linear_combination (1 / (a : ℚ)) * hm' + (m : ℚ) * mul_one_div_cancel ha0

theorem erdos_316 :
    ∃ A : Finset ℕ, (∀ n ∈ A, 2 ≤ n) ∧ (∑ n ∈ A, (1 : ℚ) / n) < 2 ∧
      ∀ A₁ A₂ : Finset ℕ, A₁ ∪ A₂ = A → Disjoint A₁ A₂ →
        ¬ ((∑ n ∈ A₁, (1 : ℚ) / n) < 1 ∧ (∑ n ∈ A₂, (1 : ℚ) / n) < 1) := by
  refine ⟨{2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60}, ?_, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  · norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  · intro A₁ A₂ hU hD ⟨h1, h2⟩
    have hdvd : ∀ n ∈ ({2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60} : Finset ℕ),
        n ∣ 120 := by decide
    obtain ⟨k₁, hk₁⟩ := erdos_316_int A₁
      fun n hn => hdvd n (by rw [← hU]; exact Finset.mem_union_left _ hn)
    obtain ⟨k₂, hk₂⟩ := erdos_316_int A₂
      fun n hn => hdvd n (by rw [← hU]; exact Finset.mem_union_right _ hn)
    have htot : ∑ n ∈ A₁, (1 : ℚ) / n + ∑ n ∈ A₂, (1 : ℚ) / n = 239 / 120 := by
      rw [← Finset.sum_union hD, hU]
      norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    have hk₁' : k₁ < 120 := by
      have : (k₁ : ℚ) < 120 := by
        rw [← hk₁]
        linarith
      exact_mod_cast this
    have hk₂' : k₂ < 120 := by
      have : (k₂ : ℚ) < 120 := by
        rw [← hk₂]
        linarith
      exact_mod_cast this
    have hsum : (k₁ : ℚ) + k₂ = 239 := by
      rw [← hk₁, ← hk₂]
      linarith
    have hsum' : k₁ + k₂ = 239 := by exact_mod_cast hsum
    omega
