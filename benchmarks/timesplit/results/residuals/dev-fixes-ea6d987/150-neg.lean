open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- CHECK: Filter.Frequently.and_eventually Filter.Frequently.exists lt_mem_nhds gt_mem_nhds
-- Conjecture (oscillation, lower side): along infinitely many n the extremal count is below 1.47^n.
-- Above the best lower-bound constructions I recall (3^{1/3} ≈ 1.4422; Gaspers–Mackenzie ≈ 1.4521, from memory).
-- Any counterexample to convergence must have liminf c(n)^{1/n} < limsup; this pins the liminf side.
theorem erdos_39240_neg_hyp_freq_small :
    ∃ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ 147 / 100 := by
  sorry

-- Conjecture (oscillation, upper side): along infinitely many n the extremal count exceeds 1.5^n.
-- Consistent with the Fomin–Villanger upper bound O(φ^n), φ ≈ 1.618. This pins the limsup side.
theorem erdos_39240_neg_hyp_freq_large :
    ∃ᶠ n : ℕ in atTop, (3 / 2 : ℝ) ≤ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) := by
  sorry

theorem erdos_39240_neg :
    ¬ (∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) := by
  rintro ⟨α, -, hT⟩
  have hlo := erdos_39240_neg_hyp_freq_small
  have hhi := erdos_39240_neg_hyp_freq_large
  by_cases h : α ≤ 147 / 100
  · have hα : α < 3 / 2 := by linarith
    have ev : ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) < 3 / 2 :=
      hT.eventually (gt_mem_nhds hα)
    obtain ⟨n, h1, h2⟩ := (hhi.and_eventually ev).exists
    linarith
  · push_neg at h
    have ev : ∀ᶠ n : ℕ in atTop, (147 / 100 : ℝ) < (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) :=
      hT.eventually (lt_mem_nhds h)
    obtain ⟨n, h1, h2⟩ := (hlo.and_eventually ev).exists
    linarith