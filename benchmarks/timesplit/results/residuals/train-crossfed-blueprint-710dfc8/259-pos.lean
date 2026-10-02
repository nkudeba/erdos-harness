open scoped ArithmeticFunction.Moebius

def erdos_71497_A (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (n : ℤ) * (μ n) ^ 2 * 2 ^ (N - n)

def erdos_71497_y (p : ℤ) (q : ℕ) (N : ℕ) : ℤ :=
  p * 2 ^ N - (q : ℤ) * erdos_71497_A N

namespace erdos_71497_hyp_tail_bounds_ns
-- IMPORTS: Mathlib.NumberTheory.ArithmeticFunction.Moebius
-- IMPORTS: Mathlib.Analysis.SpecificLimits.Normed
open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Moebius

private lemma mu_sq_eq (n : ℕ) : (μ n) ^ 2 = if Squarefree n then (1:ℤ) else 0 := by
  split_ifs with h
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h, ← pow_mul, mul_comm, pow_mul]
    norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    norm_num

theorem erdos_71497_hyp_tail_bounds :
    ∀ r : ℚ, (r : ℝ) = ∑' n : ℕ, ((μ n : ℤ) : ℝ) ^ 2 * (n : ℝ) / (2 : ℝ) ^ n →
      ∀ N : ℕ, 1 ≤ erdos_71497_y r.num r.den N ∧
        erdos_71497_y r.num r.den N ≤ (r.den : ℤ) * ((N : ℤ) + 2) - 1 := by
  intro r hr N
  set f : ℕ → ℝ := fun n => ((μ n : ℤ) : ℝ) ^ 2 * (n : ℝ) / (2 : ℝ) ^ n with hf
  have hr' : (r : ℝ) = ∑' n, f n := hr
  have hc : ∀ n : ℕ, ((μ n : ℤ) : ℝ) ^ 2 = if Squarefree n then (1:ℝ) else 0 := by
    intro n
    rw [← Int.cast_pow, mu_sq_eq]
    split_ifs <;> simp
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n; simp only [hf]; positivity
  have hf1 : ∀ n : ℕ, f n ≤ (n : ℝ) / (2:ℝ) ^ n := by
    intro n; simp only [hf]; rw [hc n]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul, zero_div]; positivity
  have hA : HasSum (fun k : ℕ => (k : ℝ) * ((1:ℝ)/2) ^ k) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2 : ℝ))
      (by norm_num [Real.norm_eq_abs])
    have e : (1/2:ℝ) / (1 - 1/2) ^ 2 = 2 := by norm_num
    rw [e] at h
    exact h
  have hB : HasSum (fun k : ℕ => ((1:ℝ)/2) ^ k) 2 := hasSum_geometric_two
  have hgs : Summable (fun n : ℕ => (n : ℝ) / (2:ℝ) ^ n) := by
    refine hA.summable.congr ?_
    intro n
    show (n:ℝ) * ((1:ℝ)/2) ^ n = (n:ℝ) / (2:ℝ) ^ n
    rw [one_div_pow]; ring
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hf1 hgs
  have hsplit : ∑ i ∈ Finset.range (N + 1), f i + ∑' i, f (i + (N + 1)) = ∑' n, f n :=
    Summable.sum_add_tsum_nat_add (N + 1) hs
  have hrST : (r:ℝ) = ∑ i ∈ Finset.range (N + 1), f i + ∑' i, f (i + (N + 1)) :=
    hr'.trans hsplit.symm
  have hdpos : (0:ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero r.den_nz)
  have hd : (r.den : ℝ) ≠ 0 := hdpos.ne'
  have hnum : (r.num : ℝ) = (r.den : ℝ) * (r : ℝ) := by
    rw [Rat.cast_def]
    field_simp
    try ring
  have hAr : ((erdos_71497_A N : ℤ) : ℝ) = (2:ℝ) ^ N * ∑ i ∈ Finset.range (N + 1), f i := by
    unfold erdos_71497_A
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp only [hf]
    rw [pow_sub₀ (2:ℝ) two_ne_zero hn']
    ring
  have hy : ((erdos_71497_y r.num r.den N : ℤ) : ℝ)
      = (r.den:ℝ) * (2:ℝ) ^ N * ∑' i, f (i + (N + 1)) := by
    unfold erdos_71497_y
    push_cast
    rw [hAr, hnum]
    linear_combination ((r.den:ℝ) * (2:ℝ) ^ N) * hrST
  have hsT : Summable (fun i => f (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hs
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hpos : 0 < f (p - (N + 1) + (N + 1)) := by
    rw [Nat.sub_add_cancel hpN]
    simp only [hf]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    norm_num
    first | exact hp0 | exact hp.pos | exact div_pos hp0 (by positivity) | positivity
  have hTpos : 0 < ∑' i, f (i + (N + 1)) :=
    Summable.tsum_pos hsT (fun i => hf0 _) (p - (N + 1)) hpos
  have hG : HasSum (fun k : ℕ => (((k + (N + 1) : ℕ) : ℝ)) / (2:ℝ) ^ (k + (N + 1)))
      (((N:ℝ) + 2) / (2:ℝ) ^ N) := by
    have h := (hA.add (hB.mul_left ((N:ℝ) + 1))).mul_left (1 / (2:ℝ) ^ (N + 1))
    have hfun : (fun k : ℕ => (((k + (N + 1) : ℕ) : ℝ)) / (2:ℝ) ^ (k + (N + 1))) =
        (fun i : ℕ => 1 / (2:ℝ) ^ (N + 1) *
          ((i:ℝ) * ((1:ℝ)/2) ^ i + ((N:ℝ) + 1) * ((1:ℝ)/2) ^ i)) := by
      funext k
      push_cast
      rw [pow_add, one_div_pow]
      field_simp
      try ring
    have hval : ((N:ℝ) + 2) / (2:ℝ) ^ N = 1 / (2:ℝ) ^ (N + 1) * (2 + ((N:ℝ) + 1) * 2) := by
      rw [pow_succ]; field_simp; ring
    rw [hfun, hval]
    exact h
  have hle : (fun i => f (i + (N + 1))) ≤
      (fun k : ℕ => (((k + (N + 1) : ℕ) : ℝ)) / (2:ℝ) ^ (k + (N + 1))) := by
    intro b; exact hf1 _
  have hns : ¬ Squarefree (3 * (N + 1) + (N + 1)) := by
    intro h
    have h2 := h 2 (Dvd.intro (N + 1) (by ring))
    rw [Nat.isUnit_iff] at h2
    omega
  have hi : (fun i => f (i + (N + 1))) (3 * (N + 1)) <
      (fun k : ℕ => (((k + (N + 1) : ℕ) : ℝ)) / (2:ℝ) ^ (k + (N + 1))) (3 * (N + 1)) := by
    simp only [hf]
    rw [hc, if_neg hns, zero_mul, zero_div]
    exact div_pos (by positivity) (by positivity)
  have hTlt : ∑' i, f (i + (N + 1)) < ((N:ℝ) + 2) / (2:ℝ) ^ N := by
    have key := Summable.tsum_lt_tsum hle hi hsT hG.summable
    exact key.trans_eq hG.tsum_eq
  have hy0 : (0:ℝ) < ((erdos_71497_y r.num r.den N : ℤ) : ℝ) := by
    rw [hy]; exact mul_pos (mul_pos hdpos (by positivity)) hTpos
  have hy1 : ((erdos_71497_y r.num r.den N : ℤ) : ℝ) < (r.den : ℝ) * ((N:ℝ) + 2) := by
    rw [hy]
    have h2N : (0:ℝ) < (2:ℝ) ^ N := by positivity
    calc (r.den:ℝ) * (2:ℝ) ^ N * ∑' i, f (i + (N + 1))
        < (r.den:ℝ) * (2:ℝ) ^ N * (((N:ℝ) + 2) / (2:ℝ) ^ N) :=
          mul_lt_mul_of_pos_left hTlt (mul_pos hdpos h2N)
      _ = (r.den : ℝ) * ((N:ℝ) + 2) := by
          first | (field_simp; done) | (field_simp; ring)
  have hz0 : 0 < erdos_71497_y r.num r.den N := by exact_mod_cast hy0
  have hz1 : erdos_71497_y r.num r.den N < (r.den : ℤ) * ((N : ℤ) + 2) := by
    exact_mod_cast hy1
  exact ⟨by linarith [Int.add_one_le_iff.mpr hz0], by linarith [Int.add_one_le_iff.mpr hz1]⟩
end erdos_71497_hyp_tail_bounds_ns

theorem erdos_71497_hyp_tail_bounds :
    ∀ r : ℚ, (r : ℝ) = ∑' n : ℕ, ((μ n : ℤ) : ℝ) ^ 2 * (n : ℝ) / (2 : ℝ) ^ n →
      ∀ N : ℕ, 1 ≤ erdos_71497_y r.num r.den N ∧
        erdos_71497_y r.num r.den N ≤ (r.den : ℤ) * ((N : ℤ) + 2) - 1 := by
  exact erdos_71497_hyp_tail_bounds_ns.erdos_71497_hyp_tail_bounds



namespace erdos_71497_hyp_recurrence_ns
open scoped ArithmeticFunction.Moebius

private lemma erdos_71497_A_succ (N : ℕ) :
    erdos_71497_A (N + 1) = 2 * erdos_71497_A N + ((N : ℤ) + 1) * (μ (N + 1)) ^ 2 := by
  unfold erdos_71497_A
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [show N + 1 - n = N - n + 1 by omega, pow_succ]
    ring
  · rw [Nat.sub_self, pow_zero, mul_one]
    push_cast
    ring

open scoped ArithmeticFunction.Moebius

theorem erdos_71497_hyp_recurrence :
    ∀ (p : ℤ) (q : ℕ) (N : ℕ),
      erdos_71497_y p q (N + 1) =
        2 * erdos_71497_y p q N - (q : ℤ) * ((N : ℤ) + 1) * (μ (N + 1)) ^ 2 := by
  intro p q N
  unfold erdos_71497_y
  rw [erdos_71497_A_succ]
  ring
end erdos_71497_hyp_recurrence_ns

theorem erdos_71497_hyp_recurrence :
    ∀ (p : ℤ) (q : ℕ) (N : ℕ),
      erdos_71497_y p q (N + 1) =
        2 * erdos_71497_y p q N - (q : ℤ) * ((N : ℤ) + 1) * (μ (N + 1)) ^ 2 := by
  exact erdos_71497_hyp_recurrence_ns.erdos_71497_hyp_recurrence



namespace erdos_71497_hyp_window_ns
open scoped ArithmeticFunction.Moebius

-- CHECK: ArithmeticFunction.moebius_eq_zero_of_not_squarefree
private lemma erdos_71497_A_succ (N : ℕ) :
    erdos_71497_A (N + 1) = 2 * erdos_71497_A N + ((N : ℤ) + 1) * (μ (N + 1)) ^ 2 := by
  unfold erdos_71497_A
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    have h : N + 1 - n = (N - n) + 1 := by omega
    rw [h, pow_succ]
    ring
  · rw [Nat.sub_self, pow_zero, mul_one]
    push_cast
    ring

private lemma erdos_71497_y_succ (p : ℤ) (q : ℕ) (N : ℕ) (h : ¬ Squarefree (N + 1)) :
    erdos_71497_y p q (N + 1) = 2 * erdos_71497_y p q N := by
  have hmu : μ (N + 1) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
  unfold erdos_71497_y
  rw [erdos_71497_A_succ, hmu]
  ring

open scoped ArithmeticFunction.Moebius

theorem erdos_71497_hyp_window :
    ∀ (p : ℤ) (q : ℕ) (N L : ℕ),
      (∀ j : ℕ, 1 ≤ j → j ≤ L → ¬ Squarefree (N + j)) →
        erdos_71497_y p q (N + L) = 2 ^ L * erdos_71497_y p q N := by
  intro p q N L h
  induction L with
  | zero => simp
  | succ L ih =>
    have hsq : ¬ Squarefree (N + L + 1) := by
      have := h (L + 1) (by omega) le_rfl
      rwa [show N + (L + 1) = N + L + 1 by omega] at this
    have ih' := ih (fun j h1 h2 => h j h1 (by omega))
    rw [show N + (L + 1) = N + L + 1 by omega, erdos_71497_y_succ p q (N + L) hsq, ih', pow_succ]
    ring
end erdos_71497_hyp_window_ns

theorem erdos_71497_hyp_window :
    ∀ (p : ℤ) (q : ℕ) (N L : ℕ),
      (∀ j : ℕ, 1 ≤ j → j ≤ L → ¬ Squarefree (N + j)) →
        erdos_71497_y p q (N + L) = 2 ^ L * erdos_71497_y p q N := by
  exact erdos_71497_hyp_window_ns.erdos_71497_hyp_window



theorem erdos_71497_hyp_no_bounded_orbit :
    ∀ (p : ℤ) (q : ℕ), 0 < q →
      ∃ N : ℕ, ¬ (1 ≤ erdos_71497_y p q N ∧
        erdos_71497_y p q N ≤ (q : ℤ) * ((N : ℤ) + 2) - 1) := by
  sorry

open scoped ArithmeticFunction.Moebius

theorem erdos_71497 :
    Irrational (∑' n : ℕ, (μ n) ^ 2 * n / (2 ^ n)) := by
  intro h
  rw [Set.mem_range] at h
  obtain ⟨r, hr⟩ := h
  have hpos := erdos_71497_hyp_tail_bounds r hr
  obtain ⟨N, hN⟩ := erdos_71497_hyp_no_bounded_orbit r.num r.den (Nat.pos_of_ne_zero r.den_nz)
  exact hN (hpos N)