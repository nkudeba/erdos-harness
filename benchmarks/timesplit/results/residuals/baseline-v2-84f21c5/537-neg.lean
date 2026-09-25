def erdos_45350_TriFree (A : Finset ℕ) : Prop :=
  ∀ k p q r : ℕ, p.Prime → q.Prime → r.Prime → p ≠ q → p ≠ r → q ≠ r →
    ¬ (q * r * k ∈ A ∧ p * r * k ∈ A ∧ p * q * k ∈ A)

-- Derived (R1, Euclid's lemma): p₁ ∣ a₂p₂ with p₁ ≠ p₂ gives p₁ ∣ a₂, and likewise for every pair.
-- So p₁p₂p₃ ∣ m := a₁p₁, and with k := m/(p₁p₂p₃) we get aᵢ = (product of the other two primes)·k.
-- The case m = 0 gives k = 0.
namespace erdos_45350_neg_hyp_factor_ns
open Filter

theorem erdos_45350_neg_hyp_factor :
    ∀ a₁ a₂ a₃ p₁ p₂ p₃ : ℕ, p₁.Prime → p₂.Prime → p₃.Prime →
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      a₁ * p₁ = a₂ * p₂ → a₂ * p₂ = a₃ * p₃ →
      ∃ k : ℕ, a₁ = p₂ * p₃ * k ∧ a₂ = p₁ * p₃ * k ∧ a₃ = p₁ * p₂ * k := by
  intro a₁ a₂ a₃ p₁ p₂ p₃ hp₁ hp₂ hp₃ hne12 hne13 hne23 h1 h2
  have h12 : p₂ ∣ a₁ := by
    have hd : p₂ ∣ a₁ * p₁ := ⟨a₂, by rw [h1]; ring⟩
    rcases (Nat.Prime.dvd_mul hp₂).mp hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp h) (Ne.symm hne12)
  have h13 : p₃ ∣ a₁ := by
    have hd : p₃ ∣ a₁ * p₁ := ⟨a₃, by rw [h1, h2]; ring⟩
    rcases (Nat.Prime.dvd_mul hp₃).mp hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp₃ hp₁).mp h) (Ne.symm hne13)
  have hcop : Nat.Coprime p₂ p₃ := (Nat.coprime_primes hp₂ hp₃).mpr hne23
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h12 h13
  refine ⟨k, hk, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hp₂.pos
    calc p₂ * a₂ = a₂ * p₂ := mul_comm _ _
      _ = a₁ * p₁ := h1.symm
      _ = p₂ * (p₁ * p₃ * k) := by rw [hk]; ring
  · apply Nat.eq_of_mul_eq_mul_left hp₃.pos
    calc p₃ * a₃ = a₃ * p₃ := mul_comm _ _
      _ = a₁ * p₁ := by rw [h1, h2]
      _ = p₃ * (p₁ * p₂ * k) := by rw [hk]; ring
end erdos_45350_neg_hyp_factor_ns

theorem erdos_45350_neg_hyp_factor :
    ∀ a₁ a₂ a₃ p₁ p₂ p₃ : ℕ, p₁.Prime → p₂.Prime → p₃.Prime →
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      a₁ * p₁ = a₂ * p₂ → a₂ * p₂ = a₃ * p₃ →
      ∃ k : ℕ, a₁ = p₂ * p₃ * k ∧ a₂ = p₁ * p₃ * k ∧ a₃ = p₁ * p₂ * k := by
  exact erdos_45350_neg_hyp_factor_ns.erdos_45350_neg_hyp_factor



-- Open core: a counterexample to the positive statement is exactly a family of dense sets
-- A_N ⊆ [1,N], one for infinitely many N, with no triangle {qrk, prk, pqk}.
-- Given R1, this is equivalent to the target.
theorem erdos_45350_neg_hyp_dense :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ N : ℕ in Filter.atTop,
      ∃ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N ∧ erdos_45350_TriFree A := by
  sorry

open Filter

theorem erdos_45350_neg :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ,
          p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) := by
  intro H
  obtain ⟨ε, hε, hfreq⟩ := erdos_45350_neg_hyp_dense
  have h2 := (H ε hε).and_frequently hfreq
  obtain ⟨N, hP, A, hA, hcard, htri⟩ := h2.exists
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, p₁, p₂, p₃, hp₁, hp₂, hp₃, h12, h13, h23, e1, e2⟩ :=
    hP A hA hcard
  obtain ⟨k, rfl, rfl, rfl⟩ :=
    erdos_45350_neg_hyp_factor a₁ a₂ a₃ p₁ p₂ p₃ hp₁ hp₂ hp₃ h12 h13 h23 e1 e2
  exact htri k p₁ p₂ p₃ hp₁ hp₂ hp₃ h12 h13 h23 ⟨ha₁, ha₂, ha₃⟩