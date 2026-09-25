-- The negation reduces, by contrapositive alone, to the statement below: some C > 0 for which every K ≥ 3 gives a finite set.
-- Believed FALSE:
--  * The literature points to an affirmative resolution of this problem (#729), alongside the AI-assisted solution of #728.
--  * The proved Kummer criterion leaves room. The only proved upper bound, k < q*(log_q(n+k)+1), allows k ≫ C log n once K is chosen large relative to C.
--  * Data at n ≤ 100 shows abundant members with excess well above C log n.
theorem erdos_83986_neg_hyp_finite_for_some_C :
    ∃ (C : ℝ), C > 0 ∧ ∀ K ≥ 3, ¬ Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
  sorry

theorem erdos_83986_neg :
    ¬ (∀ (C : ℝ) (hC : C > 0),
      ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 }) := by
  intro h
  obtain ⟨C, hC, hfin⟩ := erdos_83986_neg_hyp_finite_for_some_C
  obtain ⟨K, hK, hinf⟩ := h C hC
  exact hfin K hK hinf