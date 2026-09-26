open Finset Filter
open scoped Asymptotics

def TripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    a + b ∈ A → a + c ∈ A → b + c ∈ A → False

-- Hard-case hypothesis. Write S = A ∩ [1, N/2] and T = A ∩ (N/2, N].
-- The case |S| ≤ N/8 + C is certified in the glue, because |T| ≤ ⌈N/2⌉.
-- This hypothesis covers the other case: a small part larger than N/8 + C
-- must force at least |S| - N/8 - C values of (N/2, N] out of A.
-- Motivation: by R2 every bad triple has two members in S, and the extremal
-- sets found have S = {odd x ≤ N/4}, which has size N/8.
theorem erdos_80212_hyp_small_part_forces_gaps :
    ∃ C : ℝ, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, TripleFree A →
        (N : ℝ) / 8 + C < ((A.filter (fun x => x ≤ N / 2)).card : ℝ) →
        ((A.filter (fun x => ¬ x ≤ N / 2)).card : ℝ) ≤
          (N : ℝ) / 2 + (N : ℝ) / 8 + C - ((A.filter (fun x => x ≤ N / 2)).card : ℝ) := by
  sorry

theorem erdos_80212 :
    ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A := by
  obtain ⟨C, hC⟩ := erdos_80212_hyp_small_part_forces_gaps
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  filter_upwards [hC] with N hN
  intro A hA hcard
  by_contra hno
  have hTF : TripleFree A := by
    intro a ha b hb c hc hab hac hbc h1 h2 h3
    exact hno ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h1, h2, h3⟩
  have hsplit : (A.filter (fun x => x ≤ N / 2)).card
      + (A.filter (fun x => ¬ x ≤ N / 2)).card = A.card := by
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hTsub : A.filter (fun x => ¬ x ≤ N / 2) ⊆ Finset.Ioc (N / 2) N := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hx1 := hA hx.1
    rw [Finset.mem_Icc] at hx1
    rw [Finset.mem_Ioc]
    have hx2 := hx.2
    omega
  have hTcard : (A.filter (fun x => ¬ x ≤ N / 2)).card ≤ N - N / 2 := by
    have h := Finset.card_le_card hTsub
    rw [Nat.card_Ioc] at h
    exact h
  have hTreal : ((A.filter (fun x => ¬ x ≤ N / 2)).card : ℝ) ≤ (N : ℝ) / 2 + 1 / 2 := by
    have h2 : 2 * (A.filter (fun x => ¬ x ≤ N / 2)).card ≤ N + 1 := by omega
    have h3 : ((2 * (A.filter (fun x => ¬ x ≤ N / 2)).card : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  have hsplitR : ((A.filter (fun x => x ≤ N / 2)).card : ℝ)
      + ((A.filter (fun x => ¬ x ≤ N / 2)).card : ℝ) = (A.card : ℝ) := by
    exact_mod_cast hsplit
  have hCm : C ≤ max C 0 := le_max_left _ _
  by_cases hbig : (N : ℝ) / 8 + C < ((A.filter (fun x => x ≤ N / 2)).card : ℝ)
  · have h := hN A hA hTF hbig
    linarith
  · have h := not_lt.mp hbig
    linarith