-- Derived reduction. Suppose f satisfies the inequality only for base points x ≥ 0, and f 1 < f 0.
-- Put F x = f 1 for x < 0 and F x = max (f x) (f 1) for x ≥ 0. Then F satisfies the inequality everywhere:
--   for x < 0, both right-hand values are ≥ f 1 = F x;
--   for x ≥ 0, use the max-closure of solutions (R3).
-- F keeps the descent F 0 = f 0 > f 1 = F 1.
-- So this half-line statement is strictly weaker than an honest counterexample, and it implies the target.
-- Any counterexample restricts to it (R3 normalisation gives a = 0, b = 1).
theorem erdos_38829_neg_hyp_halfline :
    ∃ f : ℝ → ℝ,
      (∀ x : ℝ, 0 ≤ x → ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) ∧
      f 1 < f 0 := by
  sorry

theorem erdos_38829_neg :
    ¬ (∀ (f : ℝ → ℝ),
      (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
      Monotone f) := by
  intro H
  obtain ⟨f, hf, hdesc⟩ := erdos_38829_neg_hyp_halfline
  let F : ℝ → ℝ := fun x => if x < 0 then f 1 else max (f x) (f 1)
  have key : ∀ y : ℝ, f 1 ≤ F y := by
    intro y
    show f 1 ≤ (if y < 0 then f 1 else max (f y) (f 1))
    split_ifs
    · exact le_refl _
    · exact le_max_right _ _
  have hF : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * F x ≤ F (x + h) + F (x + 2 * h) := by
    intro x h hh
    by_cases hx : x < 0
    · have e : F x = f 1 := by
        show (if x < 0 then f 1 else max (f x) (f 1)) = f 1
        exact if_pos hx
      rw [e]
      linarith [key (x + h), key (x + 2 * h)]
    · have hx0 : 0 ≤ x := not_lt.mp hx
      have h1 : ¬ (x + h < 0) := not_lt.mpr (by linarith)
      have h2 : ¬ (x + 2 * h < 0) := not_lt.mpr (by linarith)
      have e0 : F x = max (f x) (f 1) := by
        show (if x < 0 then f 1 else max (f x) (f 1)) = max (f x) (f 1)
        exact if_neg hx
      have e1 : F (x + h) = max (f (x + h)) (f 1) := by
        show (if x + h < 0 then f 1 else max (f (x + h)) (f 1)) = max (f (x + h)) (f 1)
        exact if_neg h1
      have e2 : F (x + 2 * h) = max (f (x + 2 * h)) (f 1) := by
        show (if x + 2 * h < 0 then f 1 else max (f (x + 2 * h)) (f 1)) =
          max (f (x + 2 * h)) (f 1)
        exact if_neg h2
      rw [e0, e1, e2]
      have hineq := hf x hx0 h hh
      rcases le_total (f x) (f 1) with hc | hc
      · rw [max_eq_right hc]
        linarith [le_max_right (f (x + h)) (f 1), le_max_right (f (x + 2 * h)) (f 1)]
      · rw [max_eq_left hc]
        linarith [le_max_left (f (x + h)) (f 1), le_max_left (f (x + 2 * h)) (f 1)]
  have hmono := H F hF
  have h01 : F 0 ≤ F 1 := hmono zero_le_one
  have e0 : F 0 = max (f 0) (f 1) := by
    show (if (0:ℝ) < 0 then f 1 else max (f 0) (f 1)) = max (f 0) (f 1)
    exact if_neg (lt_irrefl 0)
  have e1 : F 1 = max (f 1) (f 1) := by
    show (if (1:ℝ) < 0 then f 1 else max (f 1) (f 1)) = max (f 1) (f 1)
    exact if_neg (not_lt.mpr zero_le_one)
  rw [e0, e1, max_eq_left hdesc.le, max_self] at h01
  linarith