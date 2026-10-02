-- CHECK: Nat.findGreatest_of_ne_zero Nat.le_findGreatest Nat.factorial_mul_descFactorial Set.infinite_of_forall_exists_gt tendsto_natCast_atTop_atTop
open Filter

-- Derived from the standard construction (a₁ = n-k, a₂ = 2k) together with reduction R1.
-- n! = (n-k)! · n.descFactorial k, so (n-k)!(2k)! ∣ n!·P_r^n iff (2k)! ∣ n.descFactorial k · P_r^n.
-- Content: for every C, all large r admit infinitely many n for which some k > C·log n is
-- absorbed by n(n-1)⋯(n-k+1) times the smooth factor. Heuristic support: the smooth slack
-- 2k·Σ_{p≤p_r} log p/(p-1) diverges by Mertens, so the CRT density cost per unit of k tends to 0.
theorem erdos_43665_hyp_descfact :
    ∀ C : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → 1 ≤ r →
      {n : ℕ | ∃ k : ℕ, 0 < k ∧ k < n ∧ (k : ℝ) > (C : ℝ) * Real.log n ∧
        (2 * k).factorial ∣
          n.descFactorial k * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  sorry

theorem erdos_43665 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  classical
  choose R hR using erdos_43665_hyp_descfact
  refine ⟨fun r => ((Nat.findGreatest (fun C => R C ≤ r) r : ℕ) : ℝ), ?_, ?_⟩
  · have hg : Tendsto (fun r => Nat.findGreatest (fun C => R C ≤ r) r) atTop atTop := by
      rw [tendsto_atTop]
      intro C
      rw [eventually_atTop]
      exact ⟨max C (R C), fun r hr =>
        Nat.le_findGreatest (le_of_max_le_left hr) (le_of_max_le_right hr)⟩
    exact tendsto_natCast_atTop_atTop.comp hg
  · intro r hr
    try dsimp only
    rcases Nat.eq_zero_or_pos (Nat.findGreatest (fun C => R C ≤ r) r) with h0 | hpos
    · rw [h0]
      apply Set.infinite_of_forall_exists_gt
      intro a
      refine ⟨a + 1, ?_, by omega⟩
      simp only [Set.mem_setOf_eq]
      refine ⟨a + 1, 1, by omega, by omega, ?_, ?_⟩
      · push_cast
        linarith
      · rw [Nat.factorial_one, mul_one]
        exact Dvd.intro _ rfl
    · have hRm : R (Nat.findGreatest (fun C => R C ≤ r) r) ≤ r :=
        Nat.findGreatest_of_ne_zero (P := fun C => R C ≤ r) rfl hpos.ne'
      refine (hR _ r hRm hr).mono ?_
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      obtain ⟨k, hk0, hkn, hlog, hdvd⟩ := hn
      refine ⟨n - k, 2 * k, by omega, by omega, ?_, ?_⟩
      · rw [Nat.cast_sub hkn.le]
        push_cast
        linarith
      · rw [← Nat.factorial_mul_descFactorial hkn.le, mul_assoc]
        exact mul_dvd_mul_left _ hdvd