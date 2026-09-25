open Filter

-- Configuration form of the target via reduction R1: a₁ = b·p₂p₃, a₂ = b·p₁p₃, a₃ = b·p₁p₂ with p₁ < p₂ < p₃.
-- BELIEVED FALSE. For n ∈ (N/2, N], let A_N be the set of n with no prime pair q < q' < 2q such that q·q' ∣ n.
-- The window argument shows A_N contains no configuration: every p_i lies in [m/N, 2m/N), so p₂p₃ ∣ a₁ with p₂ < p₃ < 2p₂.
-- A union bound gives |A_N| ≥ (1/2 − Σ 1/(2qq') − o(1))·N ≥ 0.27·N, since Σ 1/(qq') ≈ 0.44 converges.
-- This hypothesis is recorded only so that the glue compiles. The program should stop on this direction.
theorem erdos_25211_hyp_config :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
        ∃ b p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
          b * p₂ * p₃ ∈ A ∧ b * p₁ * p₃ ∈ A ∧ b * p₁ * p₂ ∈ A := by
  sorry

theorem erdos_25211 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ,
          p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃ := by
  intro ε hε
  filter_upwards [erdos_25211_hyp_config ε hε] with N hN
  intro A hA hcard
  obtain ⟨b, p₁, p₂, p₃, h1, h2, h3, h12, h23, hb1, hb2, hb3⟩ := hN A hA hcard
  exact ⟨_, hb1, _, hb2, _, hb3, p₁, p₂, p₃, h1, h2, h3, h12.ne, (h12.trans h23).ne, h23.ne,
    by ring, by ring⟩