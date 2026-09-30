open scoped Classical
open Polynomial
open scoped Real

noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

-- Derived: f ≠ 0 since coeff 0 ≠ 0; count 1 f.roots = rootMultiplicity 1 f (Polynomial.count_roots);
-- arg 1 = 0 ∈ Icc 0 0, so every copy of 1 in f.roots is counted by the countP.
namespace erdos_20995_neg_hyp_count_ns
open scoped Classical

open Polynomial

open scoped Real

-- CHECK: Polynomial.count_roots Multiset.count_cons Multiset.countP_cons
private lemma count_one_le_countP_aux (p : ℂ → Prop) [DecidablePred p] (hp : p 1)
    (s : Multiset ℂ) : s.count 1 ≤ s.countP p := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.count_cons, Multiset.countP_cons]
    split_ifs with h1 h2 <;> simp_all <;> omega

theorem erdos_20995_neg_hyp_count :
    ∀ f : ℂ[X], f.coeff 0 ≠ 0 → rootMultiplicity 1 f ≤ rootArgCount f (Set.Icc 0 0) := by
  intro f h0
  rw [← Polynomial.count_roots]
  unfold rootArgCount
  convert count_one_le_countP_aux
    (fun z : ℂ => (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈
      Set.Icc (0:ℝ) 0) (by simp [Complex.arg_one]) f.roots
end erdos_20995_neg_hyp_count_ns

theorem erdos_20995_neg_hyp_count :
    ∀ f : ℂ[X], f.coeff 0 ≠ 0 → rootMultiplicity 1 f ≤ rootArgCount f (Set.Icc 0 0) := by
  exact erdos_20995_neg_hyp_count_ns.erdos_20995_neg_hyp_count



-- Derived: sqrt((m+1) log(4m)) = o(m), so for any fixed C ≥ 0 some m ≥ 1 beats it.
namespace erdos_20995_neg_hyp_growth_ns
open scoped Classical

open Polynomial

open scoped Real

private lemma sqrt_bound_aux3 (C X m : ℝ) (hC : 0 ≤ C) (hX : 0 ≤ X) (hm : 0 ≤ m)
    (h : C ^ 2 * X < m ^ 2) : C * Real.sqrt X < m := by
  have e1 : C * Real.sqrt X = Real.sqrt (C ^ 2 * X) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
  rw [e1]
  have h2 := Real.sqrt_lt_sqrt (mul_nonneg (sq_nonneg C) hX) h
  rwa [Real.sqrt_sq hm] at h2

theorem erdos_20995_neg_hyp_growth :
    ∀ C : ℝ, 0 ≤ C → ∃ m : ℕ, 1 ≤ m ∧
      C * Real.sqrt (((m : ℝ) + 1) * Real.log (4 * (m : ℝ))) < (m : ℝ) := by
  intro C hC
  obtain ⟨k, hk, hk1n⟩ : ∃ k : ℕ, 8 * C ^ 2 < (k : ℝ) ∧ 1 ≤ k :=
    ⟨⌈8 * C ^ 2⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (8 * C ^ 2)], by omega⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1n
  refine ⟨k ^ 2, ?_, ?_⟩
  · nlinarith
  · push_cast
    have hlog : Real.log (4 * (k : ℝ) ^ 2) ≤ 4 * k := by
      have e : (4 : ℝ) * (k : ℝ) ^ 2 = (2 * k) ^ 2 := by ring
      rw [e, Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * k by linarith)
      push_cast
      linarith
    have hlog0 : 0 ≤ Real.log (4 * (k : ℝ) ^ 2) := Real.log_nonneg (by nlinarith)
    apply sqrt_bound_aux3 C _ _ hC (mul_nonneg (by positivity) hlog0) (by positivity)
    have hXle : ((k : ℝ) ^ 2 + 1) * Real.log (4 * (k : ℝ) ^ 2) ≤ ((k : ℝ) ^ 2 + 1) * (4 * k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hXle (sq_nonneg C)
    have h2 : C ^ 2 * (((k : ℝ) ^ 2 + 1) * (4 * k)) < ((k : ℝ) / 8) * (((k : ℝ) ^ 2 + 1) * (4 * k)) :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have h3 : ((k : ℝ) / 8) * (((k : ℝ) ^ 2 + 1) * (4 * k)) ≤ ((k : ℝ) ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hk2)]
    linarith
end erdos_20995_neg_hyp_growth_ns

theorem erdos_20995_neg_hyp_growth :
    ∀ C : ℝ, 0 ≤ C → ∃ m : ℕ, 1 ≤ m ∧
      C * Real.sqrt (((m : ℝ) + 1) * Real.log (4 * (m : ℝ))) < (m : ℝ) := by
  exact erdos_20995_neg_hyp_growth_ns.erdos_20995_neg_hyp_growth



-- Derived: f = Σ_{j=0}^m c_j x^{e_j} with c_j = 1/Π_{i≠j}(e_j - e_i) (divided-difference weights)
-- vanishes to order m at x = 1. Take e_0 = 0 < e_1 < ... < e_m = D, with e_j = round(D(1-cos(jπ/m))/2)
-- and D large. The weights are then ≈ const·(-1)^j δ_j, where δ_j = 1/2 at the endpoints and 1 otherwise
-- (Chebyshev barycentric weights). This gives Σ|c_j| / sqrt(|c_0||c_m|) ≈ 2m ≤ 4m, and n = m+1.
theorem erdos_20995_neg_hyp_family :
    ∀ m : ℕ, 1 ≤ m → ∃ f : ℂ[X], f.coeff 0 ≠ 0 ∧ m ≤ rootMultiplicity 1 f ∧
      ((f.support.card : ℕ) : ℝ) ≤ (m : ℝ) + 1 ∧ 1 ≤ M f ∧ M f ≤ 4 * (m : ℝ) := by
  sorry

theorem erdos_20995_neg :
    ¬ (∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f))) := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm1, hgrow⟩ := erdos_20995_neg_hyp_growth |C| (abs_nonneg C)
  obtain ⟨f, hf0, hmult, hcard, hM1, hM⟩ := erdos_20995_neg_hyp_family m hm1
  have hcount := erdos_20995_neg_hyp_count f hf0
  have h := hC f hf0 0 0 le_rfl le_rfl (by linarith [Real.pi_pos])
  have e : ((rootArgCount f (Set.Icc 0 0) : ℕ) : ℝ) - (0 - 0) / (2 * π) * (f.natDegree : ℝ)
      = ((rootArgCount f (Set.Icc 0 0) : ℕ) : ℝ) := by ring
  have h' : ((rootArgCount f (Set.Icc 0 0) : ℕ) : ℝ) ≤
      C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) :=
    le_trans (le_of_eq e.symm) (le_trans (le_abs_self _) h)
  have hMpos : 0 < M f := by linarith
  have hlog : Real.log (M f) ≤ Real.log (4 * (m : ℝ)) := Real.log_le_log hMpos hM
  have hlog0 : 0 ≤ Real.log (M f) := Real.log_nonneg hM1
  have hprod : (f.support.card : ℝ) * Real.log (M f) ≤ ((m : ℝ) + 1) * Real.log (4 * (m : ℝ)) :=
    mul_le_mul hcard hlog hlog0 (by positivity)
  have hsq := Real.sqrt_le_sqrt hprod
  have hC1 : C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) ≤
      |C| * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
  have hC2 : |C| * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) ≤
      |C| * Real.sqrt (((m : ℝ) + 1) * Real.log (4 * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
  have hm : (m : ℝ) ≤ ((rootArgCount f (Set.Icc 0 0) : ℕ) : ℝ) := by
    exact_mod_cast le_trans hmult hcount
  linarith