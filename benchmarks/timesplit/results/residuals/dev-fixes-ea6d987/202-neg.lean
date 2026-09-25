open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- Elementary: for N ≥ 3, log N > 1 (since exp 1 < 3), so log log N > 0,
-- the product is positive, its square root is positive, and exp of it exceeds 1.
namespace erdos_81305_neg_hyp_scale_gt_one_ns
open Real

open Filter Real

theorem erdos_81305_neg_hyp_scale_gt_one :
    ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  intro N hN
  unfold scaleL
  have hN3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have he : Real.exp 1 < (N:ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have h1 : 1 < Real.log (N:ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have h2 : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos h1
  have h3 : 0 < Real.log (N:ℝ) * Real.log (Real.log (N:ℝ)) := mul_pos (by linarith) h2
  have h4 : 0 < Real.sqrt (Real.log (N:ℝ) * Real.log (Real.log (N:ℝ))) := Real.sqrt_pos.mpr h3
  have h5 := Real.exp_lt_exp.mpr h4
  rwa [Real.exp_zero] at h5
end erdos_81305_neg_hyp_scale_gt_one_ns

theorem erdos_81305_neg_hyp_scale_gt_one :
    ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  exact erdos_81305_neg_hyp_scale_gt_one_ns.erdos_81305_neg_hyp_scale_gt_one



-- Conjecture (the hard core): the exponent in the upper bound of the
-- Erdős–Szemerédi type N / L(N)^c can be taken strictly larger than 1.
-- If f(N) = N·L^{-1+o(1)} held, this upper bound would force o(N) ≤ 1 - c < 0
-- eventually, which is impossible. This is a strictly stronger statement than
-- the target: it specifies the side on which the exponent deviates from 1.
theorem erdos_81305_neg_hyp_upper :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-c) := by
  sorry

theorem erdos_81305_neg :
    ¬ (∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N)) := by
  rintro ⟨o, ho, hev⟩
  obtain ⟨c, hc, hub⟩ := erdos_81305_neg_hyp_upper
  have hε : (0:ℝ) < (c - 1) / 2 := by linarith
  have hsmall := ho.def hε
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ :=
    (hev.and (hub.and (hsmall.and (eventually_ge_atTop 3)))).exists
  have hL := erdos_81305_neg_hyp_scale_gt_one N hN4
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN4
    linarith
  have h1 : (N:ℝ) * scaleL N ^ (-1 + o N) ≤ (N:ℝ) * scaleL N ^ (-c) := by
    linarith [hN1, hN2]
  have h2 : scaleL N ^ (-1 + o N) ≤ scaleL N ^ (-c) := le_of_mul_le_mul_left h1 hNpos
  have h3 : -1 + o N ≤ -c := (Real.rpow_le_rpow_left_iff hL).mp h2
  have h5 : |o N| ≤ (c - 1) / 2 := by simpa [Real.norm_eq_abs] using hN3
  have h6 := neg_abs_le (o N)
  linarith