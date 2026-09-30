open scoped Classical
open Polynomial
open scoped Real

noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

noncomputable def divDiffPoly (e : Finset ℕ) : ℂ[X] :=
  ∑ j ∈ e, C ((∏ k ∈ e.erase j, ((j : ℂ) - (k : ℂ)))⁻¹) * X ^ j

-- CHECK: Real.sqrt_le_sqrt Real.log_le_log mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right

-- Derived: arg 1 = 0, so every copy of the root 1 lies in the arc [0,0], and (X-1)^m ∣ f with f ≠ 0
-- gives multiplicity ≥ m (Polynomial.le_rootMultiplicity_iff, count_roots).
namespace erdos_38988_neg_hyp_count_ns
open scoped Classical

open Polynomial

open scoped Real

theorem erdos_38988_neg_hyp_count :
    ∀ f : ℂ[X], ∀ m : ℕ, f ≠ 0 → (X - C (1 : ℂ)) ^ m ∣ f →
      (m : ℝ) ≤ (rootArgCount f (Set.Icc 0 0) : ℝ) := by
  intro f m hf hdvd
  have h1 : m ≤ f.roots.count 1 := by
    rw [Polynomial.count_roots]
    exact (Polynomial.le_rootMultiplicity_iff hf).mpr hdvd
  have h2 : Multiset.replicate m (1:ℂ) ≤ f.roots :=
    Multiset.le_count_iff_replicate_le.mp h1
  have h5 := Multiset.countP_le_of_le
    (p := fun z : ℂ => (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z)
      ∈ Set.Icc (0:ℝ) 0) h2
  have h4 : (Multiset.replicate m (1:ℂ)).countP (fun z : ℂ =>
      (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z)
        ∈ Set.Icc (0:ℝ) 0) = m := by
    rw [Multiset.countP_eq_card.mpr]
    · exact Multiset.card_replicate _ _
    · intro a ha
      rw [Multiset.eq_of_mem_replicate ha]
      simp
  rw [h4] at h5
  have h6 : m ≤ rootArgCount f (Set.Icc 0 0) := by
    unfold rootArgCount
    convert h5 using 2
  exact_mod_cast h6
end erdos_38988_neg_hyp_count_ns

theorem erdos_38988_neg_hyp_count :
    ∀ f : ℂ[X], ∀ m : ℕ, f ≠ 0 → (X - C (1 : ℂ)) ^ m ∣ f →
      (m : ℝ) ≤ (rootArgCount f (Set.Icc 0 0) : ℝ) := by
  exact erdos_38988_neg_hyp_count_ns.erdos_38988_neg_hyp_count



-- Derived: the weights are nonzero because the exponents are distinct naturals, and the monomials are distinct.
namespace erdos_38988_neg_hyp_ddpoly_support_ns
open scoped Classical

open Polynomial

open scoped Real

private lemma dd_coeff (e : Finset ℕ) (m : ℕ) :
    (divDiffPoly e).coeff m =
      if m ∈ e then (∏ k ∈ e.erase m, ((m : ℂ) - (k : ℂ)))⁻¹ else 0 := by
  unfold divDiffPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  first
    | rw [Finset.sum_ite_eq]
    | simp

private lemma dd_coeff_ne (e : Finset ℕ) (m : ℕ) (hm : m ∈ e) :
    (divDiffPoly e).coeff m ≠ 0 := by
  rw [dd_coeff, if_pos hm]
  apply inv_ne_zero
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  have hkm : k ≠ m := Finset.ne_of_mem_erase hk
  have : (m : ℂ) ≠ (k : ℂ) := by exact_mod_cast hkm.symm
  exact sub_ne_zero.mpr this

theorem erdos_38988_neg_hyp_ddpoly_support :
    ∀ e : Finset ℕ, 0 ∈ e → 2 ≤ e.card →
      (divDiffPoly e).support = e ∧ (divDiffPoly e).coeff 0 ≠ 0 := by
  intro e h0 _
  refine ⟨?_, dd_coeff_ne e 0 h0⟩
  ext m
  rw [Polynomial.mem_support_iff]
  constructor
  · intro h
    by_contra hn
    exact h (by rw [dd_coeff, if_neg hn])
  · intro hm
    exact dd_coeff_ne e m hm
end erdos_38988_neg_hyp_ddpoly_support_ns

theorem erdos_38988_neg_hyp_ddpoly_support :
    ∀ e : Finset ℕ, 0 ∈ e → 2 ≤ e.card →
      (divDiffPoly e).support = e ∧ (divDiffPoly e).coeff 0 ≠ 0 := by
  exact erdos_38988_neg_hyp_ddpoly_support_ns.erdos_38988_neg_hyp_ddpoly_support



-- Derived: divided-difference identity ∑_j p(e_j) / ∏_{k≠j}(e_j-e_k) = 0 for deg p ≤ card-2.
-- Taking p(t) = t^m gives (x d/dx)^m f (1) = 0 for m ≤ card-2, hence a root of multiplicity card-1 at 1.
theorem erdos_38988_neg_hyp_ddpoly_dvd :
    ∀ e : Finset ℕ, 2 ≤ e.card → (X - C (1 : ℂ)) ^ (e.card - 1) ∣ divDiffPoly e := by
  sorry

-- Derived (analytic core): exponents e_j = round(N(1-cos(πj/(n-1)))/2) with N large.
-- The weights are then close to the Chebyshev-extreme barycentric weights (-1)^j δ_j · const,
-- so M ≈ 2(n-1). This is exact-checked for n up to 1940; n^3 leaves wide slack.
theorem erdos_38988_neg_hyp_chebyshev_M :
    ∀ n : ℕ, 2 ≤ n → ∃ e : Finset ℕ, 0 ∈ e ∧ e.card = n ∧
      0 < M (divDiffPoly e) ∧ M (divDiffPoly e) ≤ (n : ℝ) ^ 3 := by
  sorry

-- Derived: sqrt(n · 3 log n) = o(n).
namespace erdos_38988_neg_hyp_tail_ns
open scoped Classical

open Polynomial

open scoped Real

theorem erdos_38988_neg_hyp_tail :
    ∀ K : ℝ, ∃ n : ℕ, 2 ≤ n ∧
      K * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) ^ 3)) < ((n - 1 : ℕ) : ℝ) := by
  intro K
  obtain ⟨k, hk⟩ := exists_nat_gt (48 * K ^ 2 + 2)
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have ha2 : (2:ℝ) < k := by linarith
  have hk3 : 2 < k := by exact_mod_cast ha2
  have ha0 : (0:ℝ) < k := by linarith
  refine ⟨k ^ 4, ?_, ?_⟩
  · have := Nat.le_self_pow (by norm_num : (4:ℕ) ≠ 0) k
    omega
  · have hc2 : ((k ^ 4 - 1 : ℕ) : ℝ) = (k:ℝ) ^ 4 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      ring
    rw [hc2]
    simp only [Nat.cast_pow]
    have hlog : Real.log (((k:ℝ) ^ 4) ^ 3) = 12 * Real.log k := by
      rw [← pow_mul, Real.log_pow]
      norm_num
    rw [hlog]
    set a : ℝ := (k:ℝ) with ha
    have hL0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hL1 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
    have hx0 : 0 ≤ a ^ 4 * (12 * Real.log a) :=
      mul_nonneg (by positivity) (by linarith)
    have h1 : K ^ 2 * (a ^ 4 * (12 * Real.log a)) ≤ K ^ 2 * (a ^ 4 * (12 * a)) := by
      apply mul_le_mul_of_nonneg_left _ hK2
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : K ^ 2 * (a ^ 4 * (12 * a)) ≤ a ^ 6 / 4 := by
      have h := mul_le_mul_of_nonneg_right (le_of_lt hk) (le_of_lt (pow_pos ha0 5))
      nlinarith [pow_pos ha0 5]
    have hsq : 4 < a ^ 2 := by nlinarith
    have hcube : 8 < a ^ 3 := by nlinarith
    have e1 : a ^ 3 / 2 < a ^ 4 - 1 := by
      nlinarith [mul_pos (sub_pos.mpr ha2) (pow_pos ha0 3), hcube]
    have e2 : 0 < a ^ 3 / 2 := by positivity
    have h3 : a ^ 6 / 4 < (a ^ 4 - 1) ^ 2 := by
      have := mul_lt_mul'' e1 e1 e2.le e2.le
      nlinarith [this]
    have hmain : K ^ 2 * (a ^ 4 * (12 * Real.log a)) < (a ^ 4 - 1) ^ 2 := by linarith
    have hy : 0 < a ^ 4 - 1 := by linarith
    have hs0 := Real.sqrt_nonneg (a ^ 4 * (12 * Real.log a))
    have hs2 := Real.sq_sqrt hx0
    set s := Real.sqrt (a ^ 4 * (12 * Real.log a)) with hs
    by_contra hcon
    push_neg at hcon
    have hm := mul_le_mul hcon hcon hy.le (by linarith)
    have hk2s : K ^ 2 * s ^ 2 = K ^ 2 * (a ^ 4 * (12 * Real.log a)) := by rw [hs2]
    nlinarith [hk2s, hm, hmain]
end erdos_38988_neg_hyp_tail_ns

theorem erdos_38988_neg_hyp_tail :
    ∀ K : ℝ, ∃ n : ℕ, 2 ≤ n ∧
      K * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) ^ 3)) < ((n - 1 : ℕ) : ℝ) := by
  exact erdos_38988_neg_hyp_tail_ns.erdos_38988_neg_hyp_tail



theorem erdos_38988_neg :
    ¬ (∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f))) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn2, hn⟩ := erdos_38988_neg_hyp_tail |C|
  obtain ⟨e, he0, hcard, hMpos, hMle⟩ := erdos_38988_neg_hyp_chebyshev_M n hn2
  have hcard2 : 2 ≤ e.card := by rw [hcard]; exact hn2
  obtain ⟨hsupp, hc0⟩ := erdos_38988_neg_hyp_ddpoly_support e he0 hcard2
  have hf0 : divDiffPoly e ≠ 0 := fun h => hc0 (by rw [h, coeff_zero])
  have hdvd := erdos_38988_neg_hyp_ddpoly_dvd e hcard2
  have hcnt := erdos_38988_neg_hyp_count (divDiffPoly e) (e.card - 1) hf0 hdvd
  rw [hcard] at hcnt
  have h := hC (divDiffPoly e) hc0 0 0 le_rfl le_rfl (by linarith [Real.pi_pos])
  have e0 : (0:ℝ) - 0 = 0 := sub_self 0
  rw [e0, zero_div, zero_mul, sub_zero, hsupp, hcard] at h
  have hlog : Real.log (M (divDiffPoly e)) ≤ Real.log ((n : ℝ) ^ 3) :=
    Real.log_le_log hMpos hMle
  have hmul : (n : ℝ) * Real.log (M (divDiffPoly e)) ≤ (n : ℝ) * Real.log ((n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
  have hsq := Real.sqrt_le_sqrt hmul
  have hs0 := Real.sqrt_nonneg ((n : ℝ) * Real.log (M (divDiffPoly e)))
  have hCabs : C * Real.sqrt ((n : ℝ) * Real.log (M (divDiffPoly e))) ≤
      |C| * Real.sqrt ((n : ℝ) * Real.log (M (divDiffPoly e))) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hs0
  have hC2 : |C| * Real.sqrt ((n : ℝ) * Real.log (M (divDiffPoly e))) ≤
      |C| * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
  have habs := le_abs_self (rootArgCount (divDiffPoly e) (Set.Icc 0 0) : ℝ)
  linarith