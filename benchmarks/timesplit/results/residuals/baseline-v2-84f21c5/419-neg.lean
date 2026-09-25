open Filter
open scoped ArithmeticFunction.sigma

noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

-- Any counterexample to the equality must supply a cluster point outside limitPointSet (reduction R2).
-- Believed FALSE: by R1 plus Lemmas A and B, R(n) = (1 + 1/m(n)) * exp(eps_n) with eps_n -> 0 uniformly,
-- so every cluster point lies in {1} ∪ {1 + 1/k}.
theorem erdos_24786_neg_hyp_extra_cluster_point :
    ∃ x : ℝ, MapClusterPt x atTop factorialDivisorRatio ∧ x ∉ limitPointSet := by
  sorry

theorem erdos_24786_neg :
    ¬ ({x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet) := by
  intro h
  obtain ⟨x, hx, hxL⟩ := erdos_24786_neg_hyp_extra_cluster_point
  apply hxL
  have hmem : x ∈ {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} := hx
  rw [h] at hmem
  exact hmem