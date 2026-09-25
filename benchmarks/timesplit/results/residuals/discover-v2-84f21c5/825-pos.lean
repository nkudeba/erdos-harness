open scoped ArithmeticFunction.sigma

def erdos_31442_Semiperfect (n : ℕ) : Prop :=
  ∃ s ⊆ n.properDivisors, n = s.sum id

-- Derived (R1): if d = Σ_{e∈S} e with each e a proper divisor of d, and n = k*d,
-- then n = Σ_{e∈S} k*e. The terms k*e are distinct proper divisors of n.
-- The cases n = 0 and d = 0 hold via s = ∅.
namespace erdos_31442_hyp_multiple_ns
open scoped ArithmeticFunction.sigma

open scoped ArithmeticFunction.sigma

theorem erdos_31442_hyp_multiple :
    ∀ d n : ℕ, d ∣ n → erdos_31442_Semiperfect d → erdos_31442_Semiperfect n := by
  intro d n hdn hd
  obtain ⟨s, hs, hsum⟩ := hd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, Finset.empty_subset _, by simp⟩
  obtain ⟨k, rfl⟩ := hdn
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine ⟨s.image (fun e => e * k), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have he' := Nat.mem_properDivisors.mp (hs he)
    rw [Nat.mem_properDivisors]
    refine ⟨Nat.mul_dvd_mul_right he'.1 k, ?_⟩
    nlinarith [he'.2]
  · rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_right hk hxy)]
    conv_lhs => rw [hsum]
    simp [Finset.sum_mul]
end erdos_31442_hyp_multiple_ns

theorem erdos_31442_hyp_multiple :
    ∀ d n : ℕ, d ∣ n → erdos_31442_Semiperfect d → erdos_31442_Semiperfect n := by
  exact erdos_31442_hyp_multiple_ns.erdos_31442_hyp_multiple



-- Derived: explicit witnesses 6 = 1+2+3, 20 = 1+4+5+10, 28 = 1+2+4+7+14,
-- 945 = 315+189+135+105+63+45+35+27+15+9+7.
namespace erdos_31442_hyp_small_ns
open scoped ArithmeticFunction.sigma

private lemma erdos_31442_sp6 : erdos_31442_Semiperfect 6 := by
  unfold erdos_31442_Semiperfect
  refine ⟨{1, 2, 3}, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
    norm_num
  · decide

private lemma erdos_31442_sp20 : erdos_31442_Semiperfect 20 := by
  unfold erdos_31442_Semiperfect
  refine ⟨{1, 4, 5, 10}, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
    norm_num
  · decide

private lemma erdos_31442_sp28 : erdos_31442_Semiperfect 28 := by
  unfold erdos_31442_Semiperfect
  refine ⟨{1, 2, 4, 7, 14}, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
    norm_num
  · decide

private lemma erdos_31442_sp945 : erdos_31442_Semiperfect 945 := by
  unfold erdos_31442_Semiperfect
  refine ⟨{315, 189, 135, 105, 63, 45, 35, 27, 15, 9, 7}, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
    norm_num
  · decide

open scoped ArithmeticFunction.sigma

theorem erdos_31442_hyp_small :
    erdos_31442_Semiperfect 6 ∧ erdos_31442_Semiperfect 20 ∧
      erdos_31442_Semiperfect 28 ∧ erdos_31442_Semiperfect 945 := by
  exact ⟨erdos_31442_sp6, erdos_31442_sp20, erdos_31442_sp28, erdos_31442_sp945⟩
end erdos_31442_hyp_small_ns

theorem erdos_31442_hyp_small :
    erdos_31442_Semiperfect 6 ∧ erdos_31442_Semiperfect 20 ∧
      erdos_31442_Semiperfect 28 ∧ erdos_31442_Semiperfect 945 := by
  exact erdos_31442_hyp_small_ns.erdos_31442_hyp_small



-- Hard core (the open Benkoski–Erdős question, reduced): large abundancy forces some
-- semiperfect divisor, for n divisible by none of 6, 20, 28, 945.
-- C ≥ 72/35 is forced by n = 70 (R3).
theorem erdos_31442_hyp_core :
    ∃ C : ℝ, C ≥ 72 / 35 ∧
      ∀ n : ℕ, ¬ 6 ∣ n → ¬ 20 ∣ n → ¬ 28 ∣ n → ¬ 945 ∣ n →
        (σ 1 n : ℝ) > C * n → ∃ d, d ∣ n ∧ erdos_31442_Semiperfect d := by
  sorry

open scoped ArithmeticFunction.sigma

theorem erdos_31442 :
    ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id := by
  obtain ⟨C, hC, h⟩ := erdos_31442_hyp_core
  obtain ⟨h6s, h20s, h28s, h945s⟩ := erdos_31442_hyp_small
  refine ⟨C, by linarith, ?_⟩
  intro n hn
  by_cases h6 : 6 ∣ n
  · exact erdos_31442_hyp_multiple 6 n h6 h6s
  by_cases h20 : 20 ∣ n
  · exact erdos_31442_hyp_multiple 20 n h20 h20s
  by_cases h28 : 28 ∣ n
  · exact erdos_31442_hyp_multiple 28 n h28 h28s
  by_cases h945 : 945 ∣ n
  · exact erdos_31442_hyp_multiple 945 n h945 h945s
  obtain ⟨d, hd, hsd⟩ := h n h6 h20 h28 h945 (by exact_mod_cast hn)
  exact erdos_31442_hyp_multiple d n hd hsd