open Finset Filter
open scoped Asymptotics

def TripleFree80212 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    a + b ∈ A → a + c ∈ A → b + c ∈ A → False

-- Derived (R1): a counterexample to the positive statement is exactly a triple-free family whose
-- excess over 5N/8 is unbounded. Largeness of N is automatic: |A| ≤ N forces N ≥ 8K/3.
-- This is the open core (the disproof itself); small-N data (N ≤ 50) shows excess ≤ 9/4 so far.
theorem erdos_80212_neg_hyp_unbounded :
    ∀ K : ℕ, ∃ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, TripleFree80212 A ∧
      (A.card : ℝ) ≥ (5 / 8 : ℝ) * N + (K : ℝ) := by
  sorry

theorem erdos_80212_neg :
    ¬ (∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A) := by
  rintro ⟨C, hC, hev⟩
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  obtain ⟨N, A, hAsub, hfree, hcard⟩ := erdos_80212_neg_hyp_unbounded (⌈C⌉₊ + N0)
  have hcardle : A.card ≤ N := by
    calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hAsub
      _ = N := by simp
  have hcardR : (A.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcardle
  have hCle : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hceil0 : (0 : ℝ) ≤ (⌈C⌉₊ : ℝ) := Nat.cast_nonneg _
  have hN00 : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg _
  push_cast at hcard
  have hNR : (N0 : ℝ) ≤ (N : ℝ) := by linarith
  have hNN0 : N0 ≤ N := by exact_mod_cast hNR
  have hbig : (A.card : ℝ) ≥ (5 / 8 : ℝ) * N + C := by linarith
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h1, h2, h3⟩ := hN0 N hNN0 A hAsub hbig
  exact hfree a ha b hb c hc hab hac hbc h1 h2 h3