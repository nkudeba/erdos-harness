open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- Oscillation hypothesis: the only way the target can hold, given limsup ≤ φ < 2
-- (Gaspers–Mackenzie via the full-component invariant) and liminf ≥ 3^(1/3) (theta graph).
-- Believed FALSE: the limit is reported to exist (Seymour), which contradicts this.
theorem erdos_21225_neg_hyp_oscillates :
    ∃ β γ : ℝ, β < γ ∧
      (∃ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ β) ∧
      (∃ᶠ n : ℕ in atTop, γ ≤ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) := by
  sorry

theorem erdos_21225_neg :
    ¬ (∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) := by
  rintro ⟨α, _, hα⟩
  obtain ⟨β, γ, hβγ, h1, h2⟩ := erdos_21225_neg_hyp_oscillates
  by_cases h : α < γ
  · have e1 := hα.eventually_lt_const h
    obtain ⟨n, hn1, hn2⟩ := (h2.and_eventually e1).exists
    exact absurd hn2 (not_lt.mpr hn1)
  · have hb : β < α := lt_of_lt_of_le hβγ (not_lt.mp h)
    have e2 := hα.eventually_const_lt hb
    obtain ⟨n, hn1, hn2⟩ := (h1.and_eventually e2).exists
    exact absurd hn2 (not_lt.mpr hn1)