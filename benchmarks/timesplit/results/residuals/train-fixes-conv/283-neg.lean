def Rep50182 (p : Polynomial ℚ) (m : ℤ) : Prop :=
  ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), Polynomial.eval (n i : ℚ) p

def RepR2_50182 (p : Polynomial ℚ) (m : ℤ) : Prop :=
  ∃ k ≥ 3, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  2 ≤ n 1 ∧ n 1 ≤ (k : ℤ) - 1 ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), Polynomial.eval (n i : ℚ) p

namespace erdos_50182_neg_hyp_cube_int_ns
open Filter Polynomial Finset

theorem erdos_50182_neg_hyp_cube_int :
    ∀ n : ℤ, ∃ z : ℤ, Polynomial.eval (n : ℚ) (Polynomial.X ^ 3 : Polynomial ℚ) = z := by
  intro n
  exact ⟨n ^ 3, by simp⟩
end erdos_50182_neg_hyp_cube_int_ns

-- X^3 is integer-valued: eval n (X^3) = n^3.
theorem erdos_50182_neg_hyp_cube_int :
    ∀ n : ℤ, ∃ z : ℤ, Polynomial.eval (n : ℚ) (Polynomial.X ^ 3 : Polynomial ℚ) = z := by
  exact erdos_50182_neg_hyp_cube_int_ns.erdos_50182_neg_hyp_cube_int

namespace erdos_50182_neg_hyp_cube_lc_ns
open Filter Polynomial Finset

theorem erdos_50182_neg_hyp_cube_lc :
    (Polynomial.X ^ 3 : Polynomial ℚ).leadingCoeff > 0 := by
  rw [Polynomial.leadingCoeff_X_pow]
  norm_num
end erdos_50182_neg_hyp_cube_lc_ns

-- X^3 is monic.
theorem erdos_50182_neg_hyp_cube_lc :
    (Polynomial.X ^ 3 : Polynomial ℚ).leadingCoeff > 0 := by
  exact erdos_50182_neg_hyp_cube_lc_ns.erdos_50182_neg_hyp_cube_lc

-- R2: k = 1 forces n 1 = 1 and m = p(1); otherwise n 1 ≥ 2, and 1 < k / n 1 gives n 1 ≤ k - 1, so k ≥ 3.
theorem erdos_50182_neg_hyp_r2 :
    ∀ (p : Polynomial ℚ) (m : ℤ), Rep50182 p m →
      RepR2_50182 p m ∨ (m : ℚ) = Polynomial.eval 1 p := by
  sorry

-- Open core: X^3 would be a counterexample, i.e. unboundedly many m have no representation with k ≥ 3 and 2 ≤ n_1 ≤ k-1.
theorem erdos_50182_neg_hyp_cube_gap :
    ∀ N : ℤ, ∃ m ≥ N, ¬ RepR2_50182 (Polynomial.X ^ 3 : Polynomial ℚ) m ∧
      (m : ℚ) ≠ Polynomial.eval 1 (Polynomial.X ^ 3 : Polynomial ℚ) := by
  sorry

open Filter Polynomial Finset

def Condition (p : ℚ[X]) : Prop :=
  (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) → p.leadingCoeff > 0 →
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
  ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

theorem erdos_50182_neg :
    ¬ (∀ p : ℚ[X], Condition p) := by
  intro h
  have hnd : ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ,
      Polynomial.eval (n : ℚ) (Polynomial.X ^ 3 : Polynomial ℚ) = d * z) := by
    rintro ⟨d, hd, hdiv⟩
    obtain ⟨z, hz⟩ := hdiv 1 le_rfl
    have h1 : (1 : ℚ) = (d : ℚ) * (z : ℚ) := by simpa using hz
    have h2 : (1 : ℤ) = d * z := by exact_mod_cast h1
    by_cases hz0 : z ≤ 0
    · nlinarith
    · push_neg at hz0
      nlinarith
  have hc := h (Polynomial.X ^ 3 : Polynomial ℚ)
  unfold Condition at hc
  have hev := hc erdos_50182_neg_hyp_cube_int_ns.erdos_50182_neg_hyp_cube_int
    erdos_50182_neg_hyp_cube_lc_ns.erdos_50182_neg_hyp_cube_lc hnd
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m, hm, hnot, hne⟩ := erdos_50182_neg_hyp_cube_gap N
  rcases erdos_50182_neg_hyp_r2 (Polynomial.X ^ 3 : Polynomial ℚ) m (hN m hm) with h3 | h1
  · exact hnot h3
  · exact hne h1