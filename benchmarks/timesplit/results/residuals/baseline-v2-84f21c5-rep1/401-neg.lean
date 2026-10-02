open Filter

-- CHECK: Real.log_natCast_nonneg Set.not_infinite Filter.eventually_atTop Filter.Tendsto.eventually_ge_atTop

/-- `erdos43665S r c` is the set of `n` admitting a witness pair with excess above `c * log n`. -/
def erdos43665S (r : ℕ) (c : ℝ) : Set ℕ :=
  {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
    (a₁ : ℝ) + a₂ > n + c * Real.log n ∧
    a₁.factorial * a₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}

-- Uniform-in-r version of the Erdős–Graham bound a₁+a₂ ≤ n + O_r(log n): one constant C
-- works for every r. Structural reduction R2 shows the frozen target is equivalent to this
-- statement: f is removed and replaced by a single ∃C ∀r claim. Genuinely open core.
theorem erdos_43665_neg_hyp_uniform :
    ∃ C : ℝ, ∀ r : ℕ, 1 ≤ r → (erdos43665S r C).Finite := by
  sorry

theorem erdos_43665_neg :
    ¬ (∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite) := by
  rintro ⟨f, hf, hS⟩
  obtain ⟨C, hC⟩ := erdos_43665_neg_hyp_uniform
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (hf.eventually_ge_atTop C)
  have hr : 1 ≤ max R 1 := le_max_right _ _
  have hfr : C ≤ f (max R 1) := hR (max R 1) (le_max_left _ _)
  have hfin : Set.Finite
      {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f (max R 1) * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range (max R 1), Nat.nth Nat.Prime i) ^ n} := by
    apply (hC (max R 1) hr).subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    obtain ⟨a₁, a₂, h1, h2, h3, h4⟩ := hn
    simp only [erdos43665S, Set.mem_setOf_eq]
    refine ⟨a₁, a₂, h1, h2, ?_, h4⟩
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hm : C * Real.log n ≤ f (max R 1) * Real.log n :=
      mul_le_mul_of_nonneg_right hfr hlog
    linarith
  exact (Set.not_infinite.mpr hfin) (hS (max R 1) hr)