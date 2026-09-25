open Function Set
open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

open scoped Pointwise Asymptotics
open Filter

noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard

-- Counterexample-family hypothesis: unboundedly large Sidon sets with at most B isolated sums.
-- A counterexample must satisfy it. By the (numerically checked) identity
-- iso = n + R_D/2 - Q - n[1 ∈ D*] + X, with Q ≤ 2n and X ≥ 0, every member has R_D ≤ 4n + 2B + O(1).
-- All data (exact n ≤ 8, beam n ≤ 20, Ruzsa/Erdős–Turán families p ≤ 29) give R_D ≈ n²/4, so it is believed FALSE.
theorem erdos_54847_neg_hyp_family :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N, ∃ A : Set ℕ, A.ncard = n ∧ IsSidon A ∧
      {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard ≤ B := by
  sorry

theorem erdos_54847_neg :
    ¬ (Tendsto f atTop atTop) := by
  intro h
  obtain ⟨B, hB⟩ := erdos_54847_neg_hyp_family
  have hev := h.eventually (eventually_ge_atTop (B + 1))
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨n, hn, A, hA, hS, hc⟩ := hB N
  have h1 : f n ≤ {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard := by
    unfold f
    exact ciInf_le (OrderBot.bddBelow _)
      (⟨A, hA, hS⟩ : {A : Set ℕ | A.ncard = n ∧ IsSidon A})
  have h2 : B + 1 ≤ f n := hN n hn
  have h3 := le_trans h2 (le_trans h1 hc)
  omega