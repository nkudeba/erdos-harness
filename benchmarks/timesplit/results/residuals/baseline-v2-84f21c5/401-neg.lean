open Filter

-- CHECK: Real.log_natCast_nonneg Filter.Eventually.exists Filter.eventually_ge_atTop Set.Finite.subset

/-- The n-set of the R1/R2 normal form: fixed integer constant `C`, the first `r` primes,
and the ordering `a₂ ≤ a₁`. -/
def erdos86376GoodSet (C r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧ a₂ ≤ a₁ ∧
    (a₁ : ℝ) + a₂ > n + (C : ℝ) * Real.log n ∧
    a₁.factorial * a₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}

-- Conjecture (the hard core, R1 normal form with R2 asserted): a counterexample to the
-- affirmative answer is exactly one integer constant C that leaves only finitely many n for
-- every r ≥ 1. The glue below derives the frozen target from it via R1(i) (threshold
-- monotonicity, using log n ≥ 0) and R2 (symmetry in a₁, a₂).
theorem erdos_86376_neg_hyp_core :
    ∃ C : ℕ, ∀ r : ℕ, 1 ≤ r → (erdos86376GoodSet C r).Finite := by
  sorry

theorem erdos_86376_neg :
    ¬ (∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite) := by
  rintro ⟨f, hf, hinf⟩
  obtain ⟨C, hC⟩ := erdos_86376_neg_hyp_core
  have h1 : ∀ᶠ r in atTop, (C : ℝ) ≤ f r := hf.eventually (eventually_ge_atTop (C : ℝ))
  obtain ⟨r, hfr, hr⟩ := (h1.and (eventually_ge_atTop 1)).exists
  refine hinf r hr ((hC r hr).subset ?_)
  intro n hn
  obtain ⟨a₁, a₂, ha₁, ha₂, hsum, hdvd⟩ := hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hle : (C : ℝ) * Real.log n ≤ f r * Real.log n :=
    mul_le_mul_of_nonneg_right hfr hlog
  simp only [erdos86376GoodSet, Set.mem_setOf_eq]
  rcases le_total a₂ a₁ with h | h
  · exact ⟨a₁, a₂, ha₁, ha₂, h, by linarith, hdvd⟩
  · refine ⟨a₂, a₁, ha₂, ha₁, h, by linarith, ?_⟩
    rw [mul_comm a₂.factorial a₁.factorial]
    exact hdvd