open scoped Classical
open Polynomial
open scoped Real

noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

noncomputable def disc (f : ℂ[X]) (α β : ℝ) : ℝ :=
  (rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)

def DiscBound (B : ℝ) (f : ℂ[X]) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π → |disc f α β| ≤ B

-- CHECK: Real.sqrt_eq_zero_of_nonpos Real.sqrt_le_sqrt Real.sqrt_sq
-- Derived: argument principle on the annular sector {r<|z|<R, α<arg z<β}, r→0, R→∞.
-- On each ray, Re/Im of e^{iψ} f(t e^{iφ}) are real polynomials with ≤ n monomials,
-- so by Descartes' rule each has ≤ n-1 positive zeros; the argument change per ray is O(n).
-- Weakened from the explicit constant 2 to an existential constant K (numerically K = 1 suffices).
theorem erdos_20995_hyp_descartes :
    ∃ K : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → DiscBound (K * (f.support.card : ℝ)) f := by
  sorry

-- PUBLISHED: P. Erdős and P. Turán, "On the distribution of roots of polynomials",
-- Ann. of Math. 51 (1950), Theorem I (constant 16; their M uses sup_{|z|=1}|f|, which is
-- at most the coefficient sum used here, so the stated form follows).
theorem erdos_20995_hyp_et :
    ∃ C0 : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 →
      DiscBound (C0 * Real.sqrt ((f.natDegree : ℝ) * Real.log (M f))) f := by
  sorry

-- Core (open): the sparse Erdős–Turán bound, needed only when log M < n < d.
-- The regime n ≤ log M is closed by the Descartes hypothesis; the regime d ≤ n by Erdős–Turán.
theorem erdos_20995_hyp_core :
    ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → Real.log (M f) < (f.support.card : ℝ) →
      (f.support.card : ℝ) < (f.natDegree : ℝ) →
      DiscBound (C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f))) f := by
  sorry

theorem erdos_20995 :
    ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
  obtain ⟨K, hK⟩ := erdos_20995_hyp_descartes
  obtain ⟨C0, hE⟩ := erdos_20995_hyp_et
  obtain ⟨C, hC⟩ := erdos_20995_hyp_core
  refine ⟨max K 0 + max C0 0 + max C 0, ?_⟩
  intro f hf α β hα hαβ hβ
  have hS : 0 ≤ Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := Real.sqrt_nonneg _
  have hK1 : K ≤ max K 0 := le_max_left _ _
  have hK2 : 0 ≤ max K 0 := le_max_right _ _
  have hC01 : C0 ≤ max C0 0 := le_max_left _ _
  have hC02 : 0 ≤ max C0 0 := le_max_right _ _
  have hC1 : C ≤ max C 0 := le_max_left _ _
  have hC2 : 0 ≤ max C 0 := le_max_right _ _
  have hn : (0 : ℝ) ≤ (f.support.card : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ (f.natDegree : ℝ) := Nat.cast_nonneg _
  have key : |disc f α β| ≤
      max K 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) +
      max C0 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) +
      max C 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
    by_cases h1 : Real.log (M f) < (f.support.card : ℝ)
    · by_cases h2 : (f.support.card : ℝ) < (f.natDegree : ℝ)
      · have h := hC f hf h1 h2 α β hα hαβ hβ
        have h3 := mul_le_mul_of_nonneg_right hC1 hS
        linarith [mul_nonneg hK2 hS, mul_nonneg hC02 hS]
      · push_neg at h2
        have h := hE f hf α β hα hαβ hβ
        have hsq : Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) ≤
            Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
          by_cases hl : 0 ≤ Real.log (M f)
          · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h2 hl)
          · push_neg at hl
            have hneg : (f.natDegree : ℝ) * Real.log (M f) ≤ 0 := by nlinarith
            rw [Real.sqrt_eq_zero_of_nonpos hneg]
            exact hS
        have hsq0 : 0 ≤ Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) := Real.sqrt_nonneg _
        have h3 : C0 * Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) ≤
            max C0 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) :=
          le_trans (mul_le_mul_of_nonneg_right hC01 hsq0) (mul_le_mul_of_nonneg_left hsq hC02)
        linarith [mul_nonneg hK2 hS, mul_nonneg hC2 hS]
    · push_neg at h1
      have h := hK f hf α β hα hαβ hβ
      have hsq : (f.support.card : ℝ) ≤ Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
        have hle : (f.support.card : ℝ) ^ 2 ≤ (f.support.card : ℝ) * Real.log (M f) := by
          rw [sq]
          exact mul_le_mul_of_nonneg_left h1 hn
        calc (f.support.card : ℝ) = Real.sqrt ((f.support.card : ℝ) ^ 2) := (Real.sqrt_sq hn).symm
          _ ≤ Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := Real.sqrt_le_sqrt hle
      have h3 : K * (f.support.card : ℝ) ≤
          max K 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) :=
        le_trans (mul_le_mul_of_nonneg_right hK1 hn) (mul_le_mul_of_nonneg_left hsq hK2)
      linarith [mul_nonneg hC02 hS, mul_nonneg hC2 hS]
  unfold disc at key
  have e : (max K 0 + max C0 0 + max C 0) * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) =
      max K 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) +
      max C0 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) +
      max C 0 * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by ring
  rw [e]
  exact key