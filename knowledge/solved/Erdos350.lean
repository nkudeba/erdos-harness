import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option maxHeartbeats 1000000
set_option autoImplicit false

open MeasureTheory

/-! ### Elementary logarithm bounds -/

private lemma erdos_350_log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have h := Real.log_le_sub_one_of_pos (x := 1 + x) (by linarith)
  linarith

private lemma erdos_350_neg_log_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) := by
  have h : Real.log (1 - x) ≤ Real.log 1 := Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_one] at h
  linarith

private lemma erdos_350_x_le_neg_log {x : ℝ} (hx1 : x < 1) : x ≤ -Real.log (1 - x) := by
  have h := Real.log_le_sub_one_of_pos (x := 1 - x) (by linarith)
  linarith

/-! ### The generating function bound -/

private lemma erdos_350_prod_pow (x : ℝ) (S : Finset ℕ) :
    ∏ i ∈ S, x ^ i = x ^ (∑ i ∈ S, i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_add]

private lemma erdos_350_zero_not_mem (A : Finset ℕ)
    (hdis : ∀ S ⊆ A, ∀ T ⊆ A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T) : (0 : ℕ) ∉ A := by
  intro h
  have h1 : (∅ : Finset ℕ) = ({0} : Finset ℕ) :=
    hdis ∅ (Finset.empty_subset A) {0} (Finset.singleton_subset_iff.mpr h) (by simp)
  exact Finset.singleton_ne_empty (0 : ℕ) h1.symm

private lemma erdos_350_prod_le (A : Finset ℕ)
    (hdis : ∀ S ⊆ A, ∀ T ⊆ A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∏ n ∈ A, (1 + x ^ n) ≤ (1 - x)⁻¹ := by
  classical
  have hd : (0 : ℝ) < 1 - x := by linarith
  obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range
    (A.powerset.image (fun S : Finset ℕ => ∑ n ∈ S, n))
  have hinj : ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, (∑ n ∈ S, n) = (∑ n ∈ T, n) → S = T :=
    fun S hS T hT h => hdis S (Finset.mem_powerset.mp hS) T (Finset.mem_powerset.mp hT) h
  have himg : ∑ m ∈ A.powerset.image (fun S : Finset ℕ => ∑ n ∈ S, n), x ^ m
      = ∑ t ∈ A.powerset, x ^ (∑ n ∈ t, n) := Finset.sum_image hinj
  have hexp := Finset.prod_add (fun n : ℕ => x ^ n) (fun _ : ℕ => (1 : ℝ)) A
  simp only [Finset.prod_const_one, mul_one] at hexp
  have hgeom : (∑ m ∈ Finset.range M, x ^ m) ≤ (1 - x)⁻¹ := by
    have h1 : (∑ m ∈ Finset.range M, x ^ m) * (1 - x) ≤ 1 := by
      nlinarith [geom_sum_mul x M, pow_nonneg hx0 M]
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hd))
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hd), mul_one, one_mul] at h2
  calc ∏ n ∈ A, (1 + x ^ n) = ∏ n ∈ A, (x ^ n + 1) :=
        Finset.prod_congr rfl (fun n _ => add_comm _ _)
    _ = ∑ t ∈ A.powerset, ∏ i ∈ t, x ^ i := hexp
    _ = ∑ t ∈ A.powerset, x ^ (∑ n ∈ t, n) :=
        Finset.sum_congr rfl (fun t _ => erdos_350_prod_pow x t)
    _ = ∑ m ∈ A.powerset.image (fun S : Finset ℕ => ∑ n ∈ S, n), x ^ m := himg.symm
    _ ≤ ∑ m ∈ Finset.range M, x ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg hM (fun m _ _ => pow_nonneg hx0 m)
    _ ≤ (1 - x)⁻¹ := hgeom

private lemma erdos_350_log_le (A : Finset ℕ)
    (hdis : ∀ S ⊆ A, ∀ T ⊆ A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑ n ∈ A, Real.log (1 + x ^ n) ≤ -Real.log (1 - x) := by
  have hpos : ∀ n ∈ A, (0 : ℝ) < 1 + x ^ n := by
    intro n _
    have h := pow_nonneg hx0.le n
    linarith
  have hprodpos : (0 : ℝ) < ∏ n ∈ A, (1 + x ^ n) := Finset.prod_pos hpos
  have h1 : Real.log (∏ n ∈ A, (1 + x ^ n)) = ∑ n ∈ A, Real.log (1 + x ^ n) := by
    apply Real.log_prod
    intro n hn
    exact ne_of_gt (hpos n hn)
  have h2 : Real.log (∏ n ∈ A, (1 + x ^ n)) ≤ Real.log ((1 - x)⁻¹) :=
    Real.log_le_log hprodpos (erdos_350_prod_le A hdis hx0.le hx1)
  rw [Real.log_inv, h1] at h2
  exact h2

/-! ### Measurability and integrability -/

private lemma erdos_350_meas_f (n : ℕ) :
    AEStronglyMeasurable (fun x : ℝ => Real.log (1 + x ^ n) / x) volume :=
  (((measurable_const.add (measurable_id'.pow_const n)).log).div
    measurable_id').aestronglyMeasurable

private lemma erdos_350_meas_g :
    AEStronglyMeasurable (fun x : ℝ => -Real.log (1 - x) / x) volume :=
  ((((measurable_const.sub measurable_id').log).neg).div
    measurable_id').aestronglyMeasurable

private lemma erdos_350_volume_ne_top {a b : ℝ} : volume (Set.Ioo a b) ≠ ⊤ := by
  simp [Real.volume_Ioo]

private lemma erdos_350_int_f (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => Real.log (1 + x ^ n) / x) (Set.Ioo (0 : ℝ) 1) := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_const erdos_350_volume_ne_top
  refine MeasureTheory.Integrable.mono' hconst (erdos_350_meas_f n).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : x < 1 := hx.2
  have hpn : (0 : ℝ) ≤ x ^ n := pow_nonneg hx0.le n
  have hlog0 : 0 ≤ Real.log (1 + x ^ n) := Real.log_nonneg (by linarith)
  have hxn : x ^ n ≤ x := by
    calc x ^ n ≤ x ^ 1 := pow_le_pow_of_le_one hx0.le hx1.le hn
      _ = x := pow_one x
  have hle : Real.log (1 + x ^ n) ≤ x := le_trans (erdos_350_log_one_add_le hpn) hxn
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog0 hx0.le), div_le_one hx0]
  exact hle

private lemma erdos_350_int_f1 :
    IntegrableOn (fun x : ℝ => Real.log (1 + x) / x) (Set.Ioo (0 : ℝ) 1) := by
  have h := erdos_350_int_f 1 le_rfl
  simpa [pow_one] using h

private lemma erdos_350_int_neg_log :
    IntegrableOn (fun x : ℝ => -Real.log (1 - x)) (Set.Ioc (0 : ℝ) 1) := by
  have hc : Continuous fun x : ℝ => (1 - x) * Real.log (1 - x) := by
    have h : Continuous fun x : ℝ => 1 - x := by continuity
    exact Real.continuous_mul_log.comp h
  refine intervalIntegral.integrableOn_deriv_of_nonneg
    (g := fun x : ℝ => (1 - x) * Real.log (1 - x) + x) ((hc.add continuous_id).continuousOn)
    ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    have hne : (1 : ℝ) - x ≠ 0 := by
      intro h
      linarith [sub_eq_zero.mp h]
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log hne).comp x h1
    have h3 : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        ((-1) * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1))) x := h1.mul h2
    have h4 := h3.add (hasDerivAt_id' (x := x))
    have hcancel : (1 - x) * ((1 - x)⁻¹ * (-1)) = -1 := by
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have h5 : (-1 : ℝ) * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1)) + 1
        = -Real.log (1 - x) := by
      rw [hcancel]; ring
    rw [h5] at h4
    exact h4
  · intro x hx
    exact erdos_350_neg_log_nonneg hx.1.le hx.2

private lemma erdos_350_int_g :
    IntegrableOn (fun x : ℝ => -Real.log (1 - x) / x) (Set.Ioo (0 : ℝ) 1) := by
  have hA : IntegrableOn (fun x : ℝ => -Real.log (1 - x) / x)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    have hconst : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Set.Ioo (0 : ℝ) (1 / 2)) volume :=
      integrableOn_const erdos_350_volume_ne_top
    refine MeasureTheory.Integrable.mono' hconst erdos_350_meas_g.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 / 2 := hx.2
    have hnn : 0 ≤ -Real.log (1 - x) := erdos_350_neg_log_nonneg hx0.le (by linarith)
    have hkey : -Real.log (1 - x) ≤ 2 * x := by
      have h1 : (1 : ℝ) / (1 + 2 * x) ≤ 1 - x := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have h2 : Real.log (1 / (1 + 2 * x)) ≤ Real.log (1 - x) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub] at h2
      have h3 : Real.log (1 + 2 * x) ≤ 2 * x :=
        erdos_350_log_one_add_le (by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn hx0.le), div_le_iff₀ hx0]
    nlinarith
  have hB : IntegrableOn (fun x : ℝ => -Real.log (1 - x) / x)
      (Set.Ico (1 / 2 : ℝ) 1) := by
    have hsub : Set.Ico (1 / 2 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨by linarith [hx.1], le_of_lt hx.2⟩
    have hbase : IntegrableOn (fun x : ℝ => 2 * -Real.log (1 - x))
        (Set.Ico (1 / 2 : ℝ) 1) volume :=
      (erdos_350_int_neg_log.mono_set hsub).const_mul 2
    refine MeasureTheory.Integrable.mono' hbase erdos_350_meas_g.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hx0 : (1 : ℝ) / 2 ≤ x := hx.1
    have hx0' : (0 : ℝ) < x := by linarith
    have hx1 : x < 1 := hx.2
    have hnn : 0 ≤ -Real.log (1 - x) := erdos_350_neg_log_nonneg (by linarith) hx1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn hx0'.le), div_le_iff₀ hx0']
    nlinarith
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioo (0 : ℝ) (1 / 2) ∪ Set.Ico (1 / 2 : ℝ) 1 := by
    intro x hx
    by_cases h : x < 1 / 2
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨not_lt.mp h, hx.2⟩
  exact (hA.union hB).mono_set hsub

/-! ### Change of variables `u = x ^ n` -/

private lemma erdos_350_image (n : ℕ) (hn : 1 ≤ n) :
    (fun x : ℝ => x ^ n) '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := hn
    exact_mod_cast this
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨hx0, hx1⟩, rfl⟩
    exact ⟨pow_pos hx0 n, pow_lt_one₀ hx0.le hx1 (by omega)⟩
  · intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    refine ⟨y ^ ((n : ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hy0 _, ?_⟩, ?_⟩
    · exact Real.rpow_lt_one hy0.le hy1 (inv_pos.mpr hnR)
    · exact Real.rpow_inv_natCast_pow hy0.le (by omega)

private lemma erdos_350_scale (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ) :
    (∫ u in Set.Ioo (0 : ℝ) 1, g u)
      = ∫ x in Set.Ioo (0 : ℝ) 1, (n : ℝ) * x ^ (n - 1) * g (x ^ n) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => x ^ n) ((n : ℝ) * x ^ (n - 1))
        (Set.Ioo (0 : ℝ) 1) x :=
    fun x _ => (hasDerivAt_pow n x).hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => x ^ n) (Set.Ioo (0 : ℝ) 1) :=
    (pow_left_strictMonoOn₀ (M₀ := ℝ) (by omega : n ≠ 0)).injOn.mono
      (fun x hx => le_of_lt hx.1)
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj g
  rw [erdos_350_image n hn] at h
  refine h.trans ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx.1
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hx0.le _)), smul_eq_mul]

private lemma erdos_350_int_fn (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x) / x)
      = (n : ℝ) * ∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x ^ n) / x := by
  have h := erdos_350_scale n hn (fun u => Real.log (1 + u) / u)
  refine h.trans ?_
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      (n : ℝ) * x ^ (n - 1) * (Real.log (1 + x ^ n) / x ^ n)
        = (n : ℝ) * (Real.log (1 + x ^ n) / x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hp : (0 : ℝ) < x ^ (n - 1) := pow_pos hx0 _
    have hxn : x ^ n = x ^ (n - 1) * x := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hxn]
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt,
    MeasureTheory.integral_const_mul]

private lemma erdos_350_I_eq :
    (∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x)
      = 2 * ∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x) / x := by
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ((2 : ℕ) : ℝ) * x ^ (2 - 1) * (-Real.log (1 - x ^ 2) / x ^ 2)
        = 2 * (-Real.log (1 - x) / x) - 2 * (Real.log (1 + x) / x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    have hfac : (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [h21, pow_one, hfac, Real.log_mul (by linarith) (by linarith)]
    have hne : x ≠ 0 := ne_of_gt hx0
    push_cast
    field_simp
    ring
  have key : (∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x)
      = 2 * (∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x)
        - 2 * ∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x) / x := by
    have h := erdos_350_scale 2 (by norm_num) (fun u => -Real.log (1 - u) / u)
    refine h.trans ?_
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt,
      MeasureTheory.integral_sub (erdos_350_int_g.const_mul 2)
        (erdos_350_int_f1.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  linarith

private lemma erdos_350_C_ge_one :
    (1 : ℝ) ≤ ∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x := by
  have h1 : (∫ _x in Set.Ioo (0 : ℝ) 1, (1 : ℝ))
      ≤ ∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x := by
    refine MeasureTheory.setIntegral_mono_on
      (integrableOn_const erdos_350_volume_ne_top) erdos_350_int_g measurableSet_Ioo ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    rw [le_div_iff₀ hx0, one_mul]
    exact erdos_350_x_le_neg_log hx1
  simpa [MeasureTheory.setIntegral_const, Real.volume_Ioo] using h1

private lemma erdos_350_int_mono (A : Finset ℕ) (h0 : (0 : ℕ) ∉ A)
    (hb : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∑ n ∈ A, Real.log (1 + x ^ n) ≤ -Real.log (1 - x)) :
    (∑ n ∈ A, ∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x ^ n) / x)
      ≤ ∫ x in Set.Ioo (0 : ℝ) 1, -Real.log (1 - x) / x := by
  have hint : ∀ n ∈ A, IntegrableOn (fun x : ℝ => Real.log (1 + x ^ n) / x)
      (Set.Ioo (0 : ℝ) 1) := by
    intro n hn
    refine erdos_350_int_f n ?_
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · exact absurd hn h0
    · exact hp
  have hswap := MeasureTheory.integral_finsetSum
    (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
    (f := fun (n : ℕ) (x : ℝ) => Real.log (1 + x ^ n) / x) A hint
  rw [← hswap]
  refine MeasureTheory.setIntegral_mono_on
    (MeasureTheory.integrable_finsetSum
      (f := fun (n : ℕ) (x : ℝ) => Real.log (1 + x ^ n) / x) A hint)
    erdos_350_int_g measurableSet_Ioo ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have h := mul_le_mul_of_nonneg_right (hb x hx) (le_of_lt (inv_pos.mpr hx0))
  simpa [Finset.sum_mul, div_eq_mul_inv] using h

private lemma erdos_350_le (A : Finset ℕ)
    (hdis : ∀ S ⊆ A, ∀ T ⊆ A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T) :
    ∑ n ∈ A, (1 : ℝ) / (n : ℝ) ≤ 2 := by
  have h0 := erdos_350_zero_not_mem A hdis
  have hCI := erdos_350_I_eq
  have hC1 := erdos_350_C_ge_one
  have hmono := erdos_350_int_mono A h0
    (fun x hx => erdos_350_log_le A hdis hx.1 hx.2)
  have hterm : ∀ n ∈ A, (∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x ^ n) / x)
      = (∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x) / x) * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact absurd hn h0
      · exact hp
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h := erdos_350_int_fn n hn1
    rw [mul_one_div, h]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmono
  have hIpos : (0 : ℝ) < ∫ x in Set.Ioo (0 : ℝ) 1, Real.log (1 + x) / x := by
    linarith
  by_contra hcon
  have hcon' : (2 : ℝ) < ∑ n ∈ A, (1 : ℝ) / (n : ℝ) := not_le.mp hcon
  nlinarith [hmono, hIpos, hCI, hcon']

theorem erdos_350 (A : Finset ℕ)
    (hdis : ∀ S ⊆ A, ∀ T ⊆ A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T) :
    ∑ n ∈ A, (1 : ℝ) / (n : ℝ) < 2 := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = (∑ n ∈ A, n) + 1 := ⟨_, rfl⟩
  have hNerase : ∀ S : Finset ℕ, N ∉ S.erase N := fun S h => absurd rfl (Finset.ne_of_mem_erase h)
  have hNA : N ∉ A := by
    intro h
    have hle : N ≤ ∑ n ∈ A, n :=
      Finset.single_le_sum (f := fun n : ℕ => n) (fun i _ => Nat.zero_le i) h
    omega
  have hsubA : ∀ S : Finset ℕ, S ⊆ insert N A → N ∉ S → S ⊆ A := by
    intro S hS hNS y hy
    rcases Finset.mem_insert.mp (hS hy) with rfl | h
    · exact absurd hy hNS
    · exact h
  have hdis' : ∀ S ⊆ insert N A, ∀ T ⊆ insert N A, ∑ n ∈ S, n = ∑ n ∈ T, n → S = T := by
    intro S hS T hT hST
    by_cases hNS : N ∈ S <;> by_cases hNT : N ∈ T
    · have hSe : S.erase N ⊆ A :=
        hsubA _ (fun y hy => hS (Finset.mem_of_mem_erase hy)) (hNerase S)
      have hTe : T.erase N ⊆ A :=
        hsubA _ (fun y hy => hT (Finset.mem_of_mem_erase hy)) (hNerase T)
      have e1 : ∑ n ∈ S.erase N, n + N = ∑ n ∈ S, n := by
        have hins : insert N (S.erase N) = S := Finset.insert_erase hNS
        calc ∑ n ∈ S.erase N, n + N = ∑ n ∈ insert N (S.erase N), n := by
              rw [Finset.sum_insert (hNerase S)]
              exact Nat.add_comm _ _
          _ = ∑ n ∈ S, n := by rw [hins]
      have e2 : ∑ n ∈ T.erase N, n + N = ∑ n ∈ T, n := by
        have hins : insert N (T.erase N) = T := Finset.insert_erase hNT
        calc ∑ n ∈ T.erase N, n + N = ∑ n ∈ insert N (T.erase N), n := by
              rw [Finset.sum_insert (hNerase T)]
              exact Nat.add_comm _ _
          _ = ∑ n ∈ T, n := by rw [hins]
      have heq : ∑ n ∈ S.erase N, n = ∑ n ∈ T.erase N, n := by omega
      have hee : S.erase N = T.erase N := hdis _ hSe _ hTe heq
      rw [← Finset.insert_erase hNS, ← Finset.insert_erase hNT, hee]
    · exfalso
      have h1 : ∑ n ∈ T, n ≤ ∑ n ∈ A, n := Finset.sum_le_sum_of_subset (hsubA T hT hNT)
      have h2 : N ≤ ∑ n ∈ S, n :=
        Finset.single_le_sum (f := fun n : ℕ => n) (fun i _ => Nat.zero_le i) hNS
      omega
    · exfalso
      have h1 : ∑ n ∈ S, n ≤ ∑ n ∈ A, n := Finset.sum_le_sum_of_subset (hsubA S hS hNS)
      have h2 : N ≤ ∑ n ∈ T, n :=
        Finset.single_le_sum (f := fun n : ℕ => n) (fun i _ => Nat.zero_le i) hNT
      omega
    · exact hdis S (hsubA S hS hNS) T (hsubA T hT hNT) hST
  have hle := erdos_350_le (insert N A) hdis'
  rw [Finset.sum_insert hNA] at hle
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  linarith
