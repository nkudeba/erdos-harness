open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- Elementary: for N ≥ 16, log N > 1, so log log N > 0, the product under sqrt is > 0,
-- its sqrt is > 0 and exp of it is > 1.
namespace erdos_87512_hyp_scale_gt_one_ns
open Real

open Filter Real

theorem erdos_87512_hyp_scale_gt_one : ∀ᶠ N : ℕ in atTop, 1 < scaleL N := by
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  unfold scaleL
  have h3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog : 1 < Real.log (N:ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) (show Real.exp 1 < (N:ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hll : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos hlog
  have hprod : 0 < Real.log (N:ℝ) * Real.log (Real.log (N:ℝ)) :=
    mul_pos (by linarith) hll
  have hs : 0 < Real.sqrt (Real.log (N:ℝ) * Real.log (Real.log (N:ℝ))) :=
    Real.sqrt_pos.mpr hprod
  have h := Real.exp_lt_exp.mpr hs
  rwa [Real.exp_zero] at h
end erdos_87512_hyp_scale_gt_one_ns

theorem erdos_87512_hyp_scale_gt_one : ∀ᶠ N : ℕ in atTop, 1 < scaleL N := by
  exact erdos_87512_hyp_scale_gt_one_ns.erdos_87512_hyp_scale_gt_one



-- Lower half of the exponent-1 statement (construction side). Recalled from memory as a
-- theorem of Chen / de la Bretèche–Ford–Vandehey (Acta Arith. 2013); the citation and the
-- exponent are UNVERIFIED (the literature report recalls exponent sqrt 2 instead), so it
-- is recorded as a conjecture, not as a published premise.
theorem erdos_87512_hyp_lower : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, (N : ℝ) * scaleL N ^ (-1 - ε) ≤ (f N : ℝ) := by
  sorry

-- Upper half (counting side). This is the genuinely open core: the best recalled upper bound
-- is N / L^(sqrt 3 / 2 + o(1)), which is weaker. Any counterexample to the target that has
-- the lower bound must violate this.
theorem erdos_87512_hyp_upper : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) := by
  sorry

theorem erdos_87512 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  refine ⟨fun N => Real.log ((f N : ℝ) / (N : ℝ)) / Real.log (scaleL N) + 1, ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [erdos_87512_hyp_lower c hc, erdos_87512_hyp_upper c hc,
      erdos_87512_hyp_scale_gt_one, eventually_ge_atTop 1] with N hlo hup hL h1
    have hN : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr (by omega)
    have hL0 : (0:ℝ) < scaleL N := lt_trans one_pos hL
    have hlogL : 0 < Real.log (scaleL N) := Real.log_pos hL
    have hf : (0:ℝ) < (f N : ℝ) :=
      lt_of_lt_of_le (mul_pos hN (Real.rpow_pos_of_pos hL0 _)) hlo
    have hq : 0 < (f N : ℝ) / (N:ℝ) := div_pos hf hN
    have hup' : (f N : ℝ) / (N:ℝ) ≤ scaleL N ^ (-1 + c) := by
      rw [div_le_iff₀ hN]
      linarith [mul_comm (N:ℝ) (scaleL N ^ (-1 + c))]
    have hlo' : scaleL N ^ (-1 - c) ≤ (f N : ℝ) / (N:ℝ) := by
      rw [le_div_iff₀ hN]
      linarith [mul_comm (N:ℝ) (scaleL N ^ (-1 - c))]
    have h1' : Real.log ((f N:ℝ) / (N:ℝ)) ≤ (-1 + c) * Real.log (scaleL N) := by
      rw [← Real.log_rpow hL0]
      exact Real.log_le_log hq hup'
    have h2' : (-1 - c) * Real.log (scaleL N) ≤ Real.log ((f N:ℝ) / (N:ℝ)) := by
      rw [← Real.log_rpow hL0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hL0 _) hlo'
    have h3 : Real.log ((f N:ℝ) / (N:ℝ)) / Real.log (scaleL N) ≤ -1 + c := by
      rw [div_le_iff₀ hlogL]
      exact h1'
    have h4 : -1 - c ≤ Real.log ((f N:ℝ) / (N:ℝ)) / Real.log (scaleL N) := by
      rw [le_div_iff₀ hlogL]
      exact h2'
    show ‖Real.log ((f N:ℝ) / (N:ℝ)) / Real.log (scaleL N) + 1‖ ≤ c * ‖(1:ℝ)‖
    rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · filter_upwards [erdos_87512_hyp_lower 1 one_pos, erdos_87512_hyp_scale_gt_one,
      eventually_ge_atTop 1] with N hlo hL h1
    have hN : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr (by omega)
    have hNne : (N:ℝ) ≠ 0 := hN.ne'
    have hL0 : (0:ℝ) < scaleL N := lt_trans one_pos hL
    have hlogL : 0 < Real.log (scaleL N) := Real.log_pos hL
    have hne : Real.log (scaleL N) ≠ 0 := hlogL.ne'
    have hf : (0:ℝ) < (f N : ℝ) :=
      lt_of_lt_of_le (mul_pos hN (Real.rpow_pos_of_pos hL0 _)) hlo
    have hq : 0 < (f N : ℝ) / (N:ℝ) := div_pos hf hN
    show (f N : ℝ) = (N:ℝ) * scaleL N ^
      (-1 + (Real.log ((f N : ℝ) / (N : ℝ)) / Real.log (scaleL N) + 1))
    have e1 : -1 + (Real.log ((f N : ℝ) / (N : ℝ)) / Real.log (scaleL N) + 1)
        = Real.log ((f N : ℝ) / (N : ℝ)) / Real.log (scaleL N) := by ring
    have e2 : Real.log (scaleL N) * (Real.log ((f N : ℝ) / (N : ℝ)) / Real.log (scaleL N))
        = Real.log ((f N : ℝ) / (N : ℝ)) := by
      first
        | (field_simp; done)
        | (rw [mul_comm]; exact div_mul_cancel₀ _ hne)
    rw [e1, Real.rpow_def_of_pos hL0, e2, Real.exp_log hq]
    first
      | (field_simp; done)
      | (rw [mul_comm]; exact div_mul_cancel₀ _ hNne)