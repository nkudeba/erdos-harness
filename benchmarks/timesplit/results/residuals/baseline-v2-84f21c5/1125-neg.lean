-- Normalized counterexample witness (R1, R2: WLOG f 0 = 1, f 1 = 0).
-- Believed FALSE: Kemperman (Trans. AMS 135 (1969)) proved, as recalled, that every f
-- satisfying the condition is nondecreasing, which would rule out any such witness.
-- The glue only turns this witness into the negated target.
theorem erdos_58615_neg_hyp_normalized_witness :
    ∃ f : ℝ → ℝ, (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) ∧
      f 0 = 1 ∧ f 1 = 0 := by
  sorry

theorem erdos_58615_neg :
    ¬ (∀ (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
    Monotone f) := by
  intro hall
  obtain ⟨f, hf, h0, h1⟩ := erdos_58615_neg_hyp_normalized_witness
  have hm := hall f hf
  have h01 := hm (show (0:ℝ) ≤ 1 by norm_num)
  rw [h0, h1] at h01
  norm_num at h01