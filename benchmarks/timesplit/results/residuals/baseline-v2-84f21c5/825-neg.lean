open scoped ArithmeticFunction.sigma

def erdos81796NotSemi (n : ℕ) : Prop :=
  ¬ ∃ s ⊆ n.properDivisors, n = s.sum id

-- Base case: 70 is weird (sigma(70) = 144 > 140, and no subset of {1,2,5,7,10,14,35} sums to 70).
-- Finite check over 128 subsets.
namespace erdos_81796_neg_hyp_base_ns
-- CHECK: Nat.weird_seventy Nat.Weird Nat.Pseudoperfect Nat.Abundant
open scoped ArithmeticFunction.sigma

theorem erdos_81796_neg_hyp_base :
    σ 1 70 > 2 * 70 ∧ erdos81796NotSemi 70 := by
  have hw := Nat.weird_seventy
  unfold Nat.Weird at hw
  obtain ⟨hab, hnp⟩ := hw
  unfold Nat.Abundant at hab
  constructor
  · rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  · rintro ⟨s, hs, heq⟩
    apply hnp
    unfold Nat.Pseudoperfect
    refine ⟨by norm_num, s, hs, ?_⟩
    simpa using heq.symm
end erdos_81796_neg_hyp_base_ns

theorem erdos_81796_neg_hyp_base :
    σ 1 70 > 2 * 70 ∧ erdos81796NotSemi 70 := by
  exact erdos_81796_neg_hyp_base_ns.erdos_81796_neg_hyp_base



-- Abundancy-increment step. This is the genuinely open core: every weird number can be
-- "upgraded" to a non-semiperfect number whose abundancy is larger by at least 1.
-- It is implied by the target (choose a counterexample with abundancy above sigma(n)/n + 1),
-- and together with the base case it implies the target by induction.
theorem erdos_81796_neg_hyp_step :
    ∀ n : ℕ, erdos81796NotSemi n → σ 1 n > 2 * n →
      ∃ m : ℕ, 0 < m ∧ erdos81796NotSemi m ∧ σ 1 n * m + n * m ≤ σ 1 m * n := by
  sorry

theorem erdos_81796_neg :
    ¬ (∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) := by
  rintro ⟨C, hC, H⟩
  have key : ∀ k : ℕ, ∃ n : ℕ, erdos81796NotSemi n ∧ σ 1 n > (k + 2) * n := by
    intro k
    induction k with
    | zero =>
      obtain ⟨h1, h2⟩ := erdos_81796_neg_hyp_base
      refine ⟨70, h2, ?_⟩
      omega
    | succ k ih =>
      obtain ⟨n, hn, hσ⟩ := ih
      have hle : 2 * n ≤ (k + 2) * n := Nat.mul_le_mul_right n (by omega)
      have h2 : σ 1 n > 2 * n := by omega
      obtain ⟨m, hmpos, hm, hineq⟩ := erdos_81796_neg_hyp_step n hn h2
      refine ⟨m, hm, ?_⟩
      have a : (k + 2) * n * m < σ 1 n * m := by nlinarith
      have b : (k + 1 + 2) * m * n < σ 1 m * n := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right b
  obtain ⟨n, hn, hσ⟩ := key ⌈C⌉₊
  have h1 : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have h3 : (((⌈C⌉₊ + 2) * n : ℕ) : ℝ) < ((σ 1 n : ℕ) : ℝ) := by exact_mod_cast hσ
  push_cast at h3
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : ((σ 1 n : ℕ) : ℝ) > C * n := by nlinarith
  exact hn (H n hlt)