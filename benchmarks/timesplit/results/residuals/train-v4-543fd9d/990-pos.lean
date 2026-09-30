open scoped Classical
open Polynomial
open scoped Real

noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

-- CHECK: le_or_gt Real.sqrt_le_sqrt Real.sqrt_eq_zero_of_nonpos Real.sqrt_nonneg mul_nonpos_of_nonneg_of_nonpos

-- PUBLISHED: P. Erdős and P. Turán, "On the distribution of roots of polynomials",
-- Ann. of Math. 51 (1950), Theorem I (constant improved by T. Ganelius, Ark. Mat. 1954,
-- and Amoroso–Mignotte 1996). Stated for closed sectors [α,β] ⊆ [0,2π] with
-- d = natDegree f, M(f) = (Σ|a_i|)/sqrt(|a_0||a_d|); constant C ≥ 0 absolute.
theorem erdos_38988_hyp_erdos_turan :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) := by
  sorry

-- CONJECTURE (hard core): the sparse regime d > n. When d ≤ n the published
-- Erdős–Turán bound already gives C·sqrt(d log M) ≤ C·sqrt(n log M); so any
-- counterexample to the target must satisfy support.card < natDegree.
theorem erdos_38988_hyp_sparse_regime :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ[X], f.coeff 0 ≠ 0 → f.support.card < f.natDegree →
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
  sorry

theorem erdos_38988 :
    ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
  obtain ⟨C1, hC1, h1⟩ := erdos_38988_hyp_erdos_turan
  obtain ⟨C2, hC2, h2⟩ := erdos_38988_hyp_sparse_regime
  refine ⟨max C1 C2, ?_⟩
  intro f hf0 α β hα hαβ hβ
  have hs : 0 ≤ Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := Real.sqrt_nonneg _
  by_cases hd : f.support.card < f.natDegree
  · refine le_trans (h2 f hf0 hd α β hα hαβ hβ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs
  · push_neg at hd
    have hdR : (f.natDegree : ℝ) ≤ (f.support.card : ℝ) := by exact_mod_cast hd
    have hsq : Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) ≤
        Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
      rcases le_or_gt 0 (Real.log (M f)) with hL | hL
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hdR hL)
      · have hneg : (f.natDegree : ℝ) * Real.log (M f) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hL.le
        rw [Real.sqrt_eq_zero_of_nonpos hneg]
        exact Real.sqrt_nonneg _
    refine le_trans (h1 f hf0 α β hα hαβ hβ) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hsq hC1) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hs