open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- Derived: the single modulus n = (1) with a = (0) is admissible when N ≥ 1, so 1 is in the set.
-- StrictMono n into {1..N} is injective, so r ≤ N and the set is bounded; hence sSup ≥ 1.
namespace erdos_30426_hyp_f_pos_ns
open Real

open Filter Real

theorem erdos_30426_hyp_f_pos : ∀ N : ℕ, 1 ≤ N → 1 ≤ f N := by
  intro N hN
  unfold f
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro r ⟨n, a, hmono, hb, -⟩
    have hinj := hmono.injective
    have h1 : (Finset.univ.image n).card = r := by
      rw [Finset.card_image_of_injective _ hinj]; simp
    have h2 : Finset.univ.image n ⊆ Finset.Icc 1 N := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [Finset.mem_Icc]
      exact ⟨(hb i).1, (hb i).2⟩
    have h3 := Finset.card_le_card h2
    simp at h3
    omega
  · refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
    · intro i j hij
      exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
    · intro i
      exact ⟨Nat.one_pos, hN⟩
    · intro m i j _ _
      exact Subsingleton.elim i j
end erdos_30426_hyp_f_pos_ns

theorem erdos_30426_hyp_f_pos : ∀ N : ℕ, 1 ≤ N → 1 ≤ f N := by
  exact erdos_30426_hyp_f_pos_ns.erdos_30426_hyp_f_pos



-- Derived: for N ≥ 16 we have log N > e, so log (log N) > 1 > 0, and the square root is positive.
namespace erdos_30426_hyp_s_pos_ns
-- CHECK: Real.log_two_gt_d9 Real.log_pow Real.log_le_log
open Real

open Filter Real

theorem erdos_30426_hyp_s_pos :
    ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
  filter_upwards [eventually_ge_atTop 16] with N hN
  have h16 : (16:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog16 : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hle : Real.log (16:ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) h16
  have h1 : 1 < Real.log (N : ℝ) := by
    norm_num at h2
    linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos h1
  exact Real.sqrt_pos.mpr (mul_pos (by linarith) hll)
end erdos_30426_hyp_s_pos_ns

theorem erdos_30426_hyp_s_pos :
    ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
  exact erdos_30426_hyp_s_pos_ns.erdos_30426_hyp_s_pos



-- PUBLISHED: de la Bretèche, Ford, Vandehey 2013, Acta Arith. 157, main theorem, upper-bound half
-- (f(N) ≤ N / L(N)^{1+o(1)}), stated in logarithmic form. CONSTANT TO BE VERIFIED.
theorem erdos_30426_hyp_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((f N : ℕ) : ℝ) ≤ Real.log (N : ℝ)
        - (1 - ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
  sorry

-- PUBLISHED: de la Bretèche, Ford, Vandehey 2013, Acta Arith. 157, main theorem, lower-bound half
-- (construction giving f(N) ≥ N / L(N)^{1+o(1)}), stated in logarithmic form. CONSTANT TO BE VERIFIED.
theorem erdos_30426_hyp_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) - (1 + ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))
        ≤ Real.log ((f N : ℕ) : ℝ) := by
  sorry

theorem erdos_30426 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  classical
  refine ⟨fun N => 1 + (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) /
      Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [erdos_30426_hyp_upper c hc, erdos_30426_hyp_lower c hc,
      erdos_30426_hyp_s_pos] with N hu hl hs
    simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs]
    set s := Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) with hsdef
    rw [abs_le]
    constructor
    · have h1 : -(1 + c) ≤ (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) / s := by
        rw [le_div_iff₀ hs]
        linarith
      linarith
    · have h2 : (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) / s ≤ -(1 - c) := by
        rw [div_le_iff₀ hs]
        linarith
      linarith
  · filter_upwards [erdos_30426_hyp_s_pos, eventually_ge_atTop 1] with N hs hN
    beta_reduce
    have h1 := erdos_30426_hyp_f_pos N hN
    have hf : (0 : ℝ) < ((f N : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < f N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    set s := Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) with hsdef
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hL : scaleL N = Real.exp s := rfl
    rw [hL, Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]
    have key : s * (-1 + (1 + (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) / s))
        = Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ) := by
      rw [show -1 + (1 + (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) / s)
          = (Real.log ((f N : ℕ) : ℝ) - Real.log (N : ℝ)) / s by ring]
      rw [mul_div_assoc', div_eq_iff hs0]
      ring
    rw [key, Real.exp_sub, Real.exp_log hf, Real.exp_log hNpos]
    rw [mul_div_assoc', eq_div_iff hN0]
    ring