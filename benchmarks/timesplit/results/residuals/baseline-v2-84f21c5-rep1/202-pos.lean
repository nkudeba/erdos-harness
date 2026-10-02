open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- CHECK: Asymptotics.isLittleO_one_iff Metric.tendsto_nhds Real.rpow_def_of_pos Real.log_rpow Real.log_le_log Real.log_lt_log Real.exp_one_lt_d9 le_div_iff₀ div_le_iff₀ Real.rpow_pos_of_pos

-- PUBLISHED: R. de la Bretèche, K. Ford, J. Vandehey, "On non-intersecting arithmetic progressions",
-- Acta Arith. 157 (2013), main theorem (lower bound): f(N) ≥ N / L(N)^{1+o(1)}, with L = scaleL.
-- This is the construction half only. It does not imply the target.
theorem erdos_99930_hyp_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * scaleL N ^ (-1 - ε) ≤ (f N : ℝ) := by
  sorry

-- CONJECTURE (de la Bretèche–Ford–Vandehey 2013): the lower-bound construction is optimal,
-- i.e. f(N) ≤ N / L(N)^{1-o(1)}. Their proven bound has exponent √3/2 in place of 1.
-- This is the genuinely open core.
theorem erdos_99930_hyp_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) := by
  sorry

theorem erdos_99930 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  have key : ∀ N : ℕ, 3 ≤ N → 0 < Real.log (scaleL N) := by
    intro N hN
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    have h1 : 1 < Real.log N := by
      have he := Real.exp_one_lt_d9
      have hlt : Real.exp 1 < (N:ℝ) := by linarith
      have := Real.log_lt_log (Real.exp_pos 1) hlt
      rwa [Real.log_exp] at this
    have h2 : 0 < Real.log (Real.log N) := Real.log_pos h1
    have h0 : 0 < Real.log N := by linarith
    unfold scaleL
    rw [Real.log_exp]
    exact Real.sqrt_pos.mpr (mul_pos h0 h2)
  refine ⟨fun N => 1 + Real.log ((f N : ℝ) / N) / Real.log (scaleL N), ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1:ℝ) from rfl, Asymptotics.isLittleO_one_iff,
      Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [erdos_99930_hyp_lower (ε/2) (by linarith),
      erdos_99930_hyp_upper (ε/2) (by linarith), eventually_ge_atTop 3] with N hlo hup h3
    have hNpos : (0:ℝ) < N := by
      have : (3:ℝ) ≤ N := by exact_mod_cast h3
      linarith
    have hL : 0 < scaleL N := Real.exp_pos _
    have hl := key N h3
    have hp1 : 0 < scaleL N ^ (-1 - ε/2) := Real.rpow_pos_of_pos hL _
    have hp2 : 0 < scaleL N ^ (-1 + ε/2) := Real.rpow_pos_of_pos hL _
    have hf : (0:ℝ) < f N := lt_of_lt_of_le (mul_pos hNpos hp1) hlo
    have hq : (0:ℝ) < (f N : ℝ) / N := div_pos hf hNpos
    have hq1 : scaleL N ^ (-1 - ε/2) ≤ (f N : ℝ) / N :=
      (le_div_iff₀ hNpos).mpr (by rw [mul_comm]; exact hlo)
    have hq2 : (f N : ℝ) / N ≤ scaleL N ^ (-1 + ε/2) :=
      (div_le_iff₀ hNpos).mpr (by rw [mul_comm]; exact hup)
    have ht1 := Real.log_le_log hp1 hq1
    have ht2 := Real.log_le_log hq hq2
    rw [Real.log_rpow hL] at ht1 ht2
    have hd1 : -1 - ε/2 ≤ Real.log ((f N : ℝ) / N) / Real.log (scaleL N) := by
      rw [le_div_iff₀ hl]; linarith
    have hd2 : Real.log ((f N : ℝ) / N) / Real.log (scaleL N) ≤ -1 + ε/2 := by
      rw [div_le_iff₀ hl]; linarith
    rw [Real.dist_eq]
    show |(1 + Real.log ((f N : ℝ) / N) / Real.log (scaleL N)) - 0| < ε
    rw [sub_zero, abs_lt]
    constructor <;> linarith
  · filter_upwards [erdos_99930_hyp_lower 1 one_pos, eventually_ge_atTop 3] with N hN h3
    show (f N : ℝ) = (N:ℝ) * scaleL N ^ (-1 + (1 + Real.log ((f N : ℝ) / N) / Real.log (scaleL N)))
    have hNpos : (0:ℝ) < N := by
      have : (3:ℝ) ≤ N := by exact_mod_cast h3
      linarith
    have hL : 0 < scaleL N := Real.exp_pos _
    have hf : (0:ℝ) < f N := lt_of_lt_of_le (mul_pos hNpos (Real.rpow_pos_of_pos hL _)) hN
    have hl := key N h3
    have hne : Real.log (scaleL N) ≠ 0 := ne_of_gt hl
    have hq : (0:ℝ) < (f N : ℝ) / N := div_pos hf hNpos
    rw [Real.rpow_def_of_pos hL]
    have hexp : Real.log (scaleL N) * (-1 + (1 + Real.log ((f N : ℝ) / N) / Real.log (scaleL N)))
        = Real.log ((f N : ℝ) / N) := by
      rw [show (-1 + (1 + Real.log ((f N : ℝ) / N) / Real.log (scaleL N)))
          = Real.log ((f N : ℝ) / N) / Real.log (scaleL N) by ring]
      first
        | (field_simp; done)
        | (field_simp; ring)
        | exact mul_div_cancel₀ _ hne
    rw [hexp, Real.exp_log hq]
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    first
      | (field_simp; done)
      | (field_simp; ring)
      | exact (mul_div_cancel₀ _ hNne).symm