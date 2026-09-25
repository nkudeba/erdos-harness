open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- Derived from the published bound on minimal separators (Fomin–Villanger 2012: at most O(φ^n)).
-- By R1, every minimal cut is a minimal (a,b)-separator.
-- Hence c(n) ≤ C·φ^n, and since C^(1/n) → 1 and φ < 1.7, eventually c(n)^(1/n) ≤ 17/10.
theorem erdos_39240_hyp_upper :
    ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ 17 / 10 := by
  sorry

-- Hard core: existence of the limit of c(n)^(1/n).
-- It should follow from Fekete's lemma applied to log c, via a gluing that gives c(m+n+O(1)) ≥ c(m)·c(n).
-- It is also needed that c(n) is nondecreasing (coning, checked) and that c(n) ≥ 3^((n-4)/3).
theorem erdos_39240_hyp_limit_exists :
    ∃ α : ℝ, Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  sorry

theorem erdos_39240 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨α, hα⟩ := erdos_39240_hyp_limit_exists
  refine ⟨α, ?_, hα⟩
  have h : α ≤ 17 / 10 := le_of_tendsto hα erdos_39240_hyp_upper
  linarith