-- CHECK: Asymptotics.IsLittleO.def Filter.Eventually.and_frequently Filter.Frequently.exists
-- CHECK: Real.rpow_lt_rpow_of_exponent_lt Real.add_one_lt_exp Real.exp_one_lt_d9 Real.log_lt_log
open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- CONJECTURE (weak form of de la Bretèche–Ford–Vandehey 2013, who conjecture f N = N / L(N)^(√2+o(1))):
-- along infinitely many N, f N is below N · L(N)^(-c) for some fixed exponent c > 1.
-- Their conjectured exponent √2 > 1 gives this with any c ∈ (1, √2). This is the open core.
theorem erdos_20311_neg_hyp_upper_freq :
    ∃ c : ℝ, 1 < c ∧ ∃ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-c) := by
  sorry

theorem erdos_20311_neg :
    ¬ (∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N)) := by
  rintro ⟨o, ho, hf⟩
  obtain ⟨c, hc1, hcf⟩ := erdos_20311_neg_hyp_upper_freq
  have hε : (0:ℝ) < (c - 1) / 2 := by linarith
  have h1 := ho.def hε
  have h3 : ∀ᶠ N : ℕ in atTop, 3 ≤ N := eventually_ge_atTop 3
  obtain ⟨N, ⟨hoN, hfN, hN3⟩, hcN⟩ := ((h1.and (hf.and h3)).and_frequently hcf).exists
  have hoN' : |o N| ≤ (c - 1) / 2 := by
    simpa [Real.norm_eq_abs] using hoN
  have hN3r : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlog : 1 < Real.log (N:ℝ) := by
    have he : Real.exp 1 < (N:ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  have hloglog : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos hlog
  have hprod : 0 < Real.log (N:ℝ) * Real.log (Real.log (N:ℝ)) :=
    mul_pos (by linarith) hloglog
  have hsq : 0 < Real.sqrt (Real.log (N:ℝ) * Real.log (Real.log (N:ℝ))) :=
    Real.sqrt_pos.mpr hprod
  have hL : 1 < scaleL N := by
    unfold scaleL
    have := Real.add_one_lt_exp (ne_of_gt hsq)
    linarith
  have hexp : -c < -1 + o N := by
    have := (abs_le.mp hoN').1
    linarith
  have hpow : scaleL N ^ (-c) < scaleL N ^ (-1 + o N) :=
    Real.rpow_lt_rpow_of_exponent_lt hL hexp
  have hmul : (N:ℝ) * scaleL N ^ (-c) < (N:ℝ) * scaleL N ^ (-1 + o N) :=
    mul_lt_mul_of_pos_left hpow hNpos
  linarith