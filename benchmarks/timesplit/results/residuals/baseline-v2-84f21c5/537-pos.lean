open Filter

/-- `A` contains a "prime triangle" `{t*q*r, t*p*r, t*p*q}` with primes `p < q < r`. -/
def erdos_45350_triangle (A : Finset ℕ) : Prop :=
  ∃ t p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
    t * q * r ∈ A ∧ t * p * r ∈ A ∧ t * p * q ∈ A

-- CONJECTURE (hard core, open). Obtained from the target by the checked substitution R1:
-- a₁p₁ = a₂p₂ = a₃p₃ with distinct primes holds iff (a₁,a₂,a₃) = (tqr, tpr, tpq).
-- This is the 3-uniform "prime triangle" density statement.
-- A counterexample family would have to be triangle-free in every graph G_t
-- (edges {p,q} with t*p*q ∈ A), so each G_t obeys Mantel's bound.
theorem erdos_45350_hyp_triangle :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N → erdos_45350_triangle A := by
  sorry

open Filter

theorem erdos_45350 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ,
          p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃ := by
  intro ε hε
  filter_upwards [erdos_45350_hyp_triangle ε hε] with N hN
  intro A hA hcard
  obtain ⟨t, p, q, r, hp, hq, hr, hpq, hqr, h1, h2, h3⟩ := hN A hA hcard
  refine ⟨t * q * r, h1, t * p * r, h2, t * p * q, h3, p, q, r, hp, hq, hr,
    ne_of_lt hpq, ?_, ne_of_lt hqr, ?_, ?_⟩
  · omega
  · ring
  · ring