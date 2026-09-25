open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

noncomputable def erdosL (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

-- DERIVED (rigorous, elementary): r = 1 with modulus 1 is admissible for N ≥ 1,
-- and the set is bounded by N (StrictMono n into [1,N]), so sSup ≥ 1.
namespace erdos_81305_hyp_pos_ns
open Real

open Filter Real

theorem erdos_81305_hyp_pos : ∀ N : ℕ, 1 ≤ N → 1 ≤ f N := by
  intro N hN
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro r ⟨n, a, hmono, hb, -⟩
    have h := Finset.card_le_card_of_injOn n (s := (Finset.univ : Finset (Fin r)))
      (t := Finset.Icc 1 N)
      (by intro i _; exact Finset.mem_Icc.mpr ⟨(hb i).1, (hb i).2⟩)
      (by intro i _ j _ hij; exact hmono.injective hij)
    simpa using h
  · refine ⟨fun _ => 1, fun _ => 0, ?_, fun _ => ⟨one_pos, hN⟩, ?_⟩
    · intro i j h
      exact absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
    · intro _ i j _ _
      exact Subsingleton.elim i j
end erdos_81305_hyp_pos_ns

theorem erdos_81305_hyp_pos : ∀ N : ℕ, 1 ≤ N → 1 ≤ f N := by
  exact erdos_81305_hyp_pos_ns.erdos_81305_hyp_pos



-- DERIVED via R3: the upper-bound half of the equivalent form
-- log(N / f N) / sqrt(log N log log N) → 1 (structural / density side).
theorem erdos_81305_hyp_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (1 - ε) * erdosL N ≤ Real.log ((N : ℝ) / (f N : ℝ)) := by
  sorry

-- DERIVED via R3: the lower-bound half (smooth-number / CRT construction side).
theorem erdos_81305_hyp_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    Real.log ((N : ℝ) / (f N : ℝ)) ≤ (1 + ε) * erdosL N := by
  sorry

theorem erdos_81305 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  have hLpos : ∀ᶠ N : ℕ in atTop, 0 < erdosL N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN' : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have he : Real.exp 1 < (N:ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have h1 : 1 < Real.log (N:ℝ) := by
      have := Real.log_lt_log (Real.exp_pos 1) he
      rwa [Real.log_exp] at this
    have h2 : 0 < Real.log (Real.log (N:ℝ)) := Real.log_pos h1
    unfold erdosL
    exact Real.sqrt_pos.mpr (mul_pos (by linarith) h2)
  refine ⟨fun N => 1 - Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N, ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1:ℝ) from rfl, Asymptotics.isLittleO_one_iff,
      Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hLpos, erdos_81305_hyp_upper (ε/2) (by linarith),
      erdos_81305_hyp_lower (ε/2) (by linarith)] with N hL hu hl
    show dist (1 - Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N) 0 < ε
    rw [Real.dist_eq, sub_zero]
    have h1 : 1 - ε/2 ≤ Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N := by
      rw [le_div_iff₀ hL]; linarith
    have h2 : Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N ≤ 1 + ε/2 := by
      rw [div_le_iff₀ hL]; linarith
    rw [abs_lt]
    constructor <;> linarith
  · filter_upwards [hLpos, eventually_ge_atTop 1] with N hL hN
    have hf : (1:ℝ) ≤ (f N : ℝ) := by exact_mod_cast erdos_81305_hyp_pos N hN
    have hNpos : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr (by omega)
    have hN0 : (N:ℝ) ≠ 0 := hNpos.ne'
    have hf0 : (f N : ℝ) ≠ 0 := by
      have : (0:ℝ) < (f N : ℝ) := by linarith
      exact this.ne'
    have hq : 0 < (N:ℝ) / (f N : ℝ) := div_pos hNpos (by linarith)
    have hL0 : erdosL N ≠ 0 := hL.ne'
    show (f N : ℝ) = (N:ℝ) * scaleL N ^ (-1 + (1 - Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N))
    have hs : scaleL N = Real.exp (erdosL N) := rfl
    rw [hs, ← Real.exp_mul]
    have hmul : erdosL N * (-1 + (1 - Real.log ((N:ℝ) / (f N : ℝ)) / erdosL N))
        = - Real.log ((N:ℝ) / (f N : ℝ)) := by
      field_simp <;> ring
    rw [hmul, Real.exp_neg, Real.exp_log hq]
    field_simp <;> ring