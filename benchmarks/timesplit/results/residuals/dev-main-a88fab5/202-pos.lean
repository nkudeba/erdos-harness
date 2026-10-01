open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- For N ≥ 3, log N > 1 (as N > e), so log (log N) > 0, the product is positive,
-- the sqrt is positive and exp of a positive number exceeds 1.
namespace erdos_20311_hyp_scale_gt_one_ns
open Real

open Filter Real

theorem erdos_20311_hyp_scale_gt_one : ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  intro N hN
  unfold scaleL
  have h3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : 1 < Real.log (N:ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hll : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos hlog
  have hp : 0 < Real.log (N:ℝ) * Real.log (Real.log (N:ℝ)) := mul_pos (by linarith) hll
  have hs : 0 < Real.sqrt (Real.log (N:ℝ) * Real.log (Real.log (N:ℝ))) := Real.sqrt_pos.mpr hp
  have := Real.exp_lt_exp.mpr hs
  rwa [Real.exp_zero] at this
end erdos_20311_hyp_scale_gt_one_ns

theorem erdos_20311_hyp_scale_gt_one : ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  exact erdos_20311_hyp_scale_gt_one_ns.erdos_20311_hyp_scale_gt_one



-- PUBLISHED: R. de la Bretèche, K. Ford, J. Vandehey, "On non-intersecting arithmetic progressions", Acta Arith. 157 (2013), main theorem (lower bound f(N) ≥ N / L(N)^{1+o(1)}, by explicit construction)
theorem erdos_20311_hyp_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (N : ℝ) * scaleL N ^ (-1 - ε) ≤ (f N : ℝ) := by
  sorry

-- The conjectured matching upper bound f(N) ≤ N / L(N)^{1-o(1)}. Any counterexample to the target
-- that respects the published lower bound must violate this for some ε and infinitely many N.
theorem erdos_20311_hyp_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) := by
  sorry

theorem erdos_20311 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  have hLev : ∀ᶠ N : ℕ in atTop, 1 < scaleL N := by
    filter_upwards [eventually_ge_atTop 3] with N hN using erdos_20311_hyp_scale_gt_one N hN
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < f N := by
    filter_upwards [erdos_20311_hyp_lower 1 one_pos, eventually_ge_atTop 1, hLev] with N h1 hN hLN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hLpos : 0 < scaleL N := by linarith
    have := mul_pos hN' (Real.rpow_pos_of_pos hLpos (-1 - 1))
    linarith
  refine ⟨fun N => Real.log ((f N : ℝ) / N) / Real.log (scaleL N) + 1, ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl, Asymptotics.isLittleO_one_iff]
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [erdos_20311_hyp_lower (ε / 2) (by linarith),
      erdos_20311_hyp_upper (ε / 2) (by linarith), hLev, hpos, eventually_ge_atTop 1]
      with N hlo hup hLN hfN hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hlogL : 0 < Real.log (scaleL N) := Real.log_pos hLN
    have hLpos : 0 < scaleL N := by linarith
    have hq : 0 < (f N : ℝ) / N := div_pos hfN hN'
    have h1 : Real.log ((f N : ℝ) / N) ≤ (-1 + ε / 2) * Real.log (scaleL N) := by
      rw [← Real.log_rpow hLpos]
      apply Real.log_le_log hq
      rw [div_le_iff₀ hN', mul_comm]
      exact hup
    have h2 : (-1 - ε / 2) * Real.log (scaleL N) ≤ Real.log ((f N : ℝ) / N) := by
      rw [← Real.log_rpow hLpos]
      apply Real.log_le_log (Real.rpow_pos_of_pos hLpos _)
      rw [le_div_iff₀ hN', mul_comm]
      exact hlo
    have h1' := (div_le_iff₀ hlogL).mpr h1
    have h2' := (le_div_iff₀ hlogL).mpr h2
    show dist (Real.log ((f N : ℝ) / N) / Real.log (scaleL N) + 1) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  · filter_upwards [hLev, hpos, eventually_ge_atTop 1] with N hLN hfN hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hNne : (N : ℝ) ≠ 0 := hN'.ne'
    have hlogL : 0 < Real.log (scaleL N) := Real.log_pos hLN
    have hlogne : Real.log (scaleL N) ≠ 0 := hlogL.ne'
    have hLpos : 0 < scaleL N := by linarith
    have hcanc : Real.log (scaleL N) * (Real.log ((f N : ℝ) / N) / Real.log (scaleL N))
        = Real.log ((f N : ℝ) / N) := by
      field_simp
    have hpow : scaleL N ^ (-1 + (Real.log ((f N : ℝ) / N) / Real.log (scaleL N) + 1))
        = (f N : ℝ) / N := by
      rw [show -1 + (Real.log ((f N : ℝ) / N) / Real.log (scaleL N) + 1)
          = Real.log ((f N : ℝ) / N) / Real.log (scaleL N) by ring]
      rw [Real.rpow_def_of_pos hLpos, hcanc]
      exact Real.exp_log (div_pos hfN hN')
    have key : (N : ℝ) * scaleL N ^ (-1 + (Real.log ((f N : ℝ) / N) / Real.log (scaleL N) + 1))
        = f N := by
      rw [hpow]
      field_simp
    exact key.symm