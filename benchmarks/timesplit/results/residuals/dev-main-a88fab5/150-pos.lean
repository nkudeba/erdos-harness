open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- CHECK: le_of_tendsto Real.pow_rpow_inv_natCast Real.rpow_le_rpow

-- PUBLISHED: Fomin, Kratsch, Todinca, Villanger, "Exact algorithms for treewidth and minimum fill-in",
-- SIAM J. Comput. 38 (2008): a graph on n vertices has O(1.7087^n) minimal separators;
-- improved by Gaspers–Mackenzie (WG 2015 / J. Graph Theory 2018) to O(1.6181^n).
-- Every minimal cut in the sense of IsMinimalCut (R2: full components) is a minimal (u,v)-separator,
-- so either bound gives c(n) ≤ C·1.7087^n, hence c(n) ≤ 1.7^n for all large n (using the 1.6181 bound).
theorem erdos_21225_hyp_upper_bound :
    ∃ N : ℕ, ∀ n ≥ N, (maxMinimalCuts n : ℝ) ≤ (17 / 10 : ℝ) ^ n := by
  sorry

-- CONJECTURE (open core): existence of the limit of c(n)^{1/n}. Expected route: supermultiplicativity
-- c(a+b+O(1)) ≥ c(a)c(b) via a cut-preserving gluing, plus monotonicity c(n+1) ≥ c(n)
-- (universal vertex) and Fekete's lemma; the two-sided restricted count f(n) already satisfies this.
theorem erdos_21225_hyp_limit_exists :
    ∃ α : ℝ, Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  sorry

theorem erdos_21225 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨α, hα⟩ := erdos_21225_hyp_limit_exists
  obtain ⟨N, hN⟩ := erdos_21225_hyp_upper_bound
  refine ⟨α, ?_, hα⟩
  have h : α ≤ 17 / 10 := by
    apply le_of_tendsto hα
    rw [Filter.eventually_atTop]
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : n ≠ 0 := by omega
    have h1 := hN n hnN
    show (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ 17 / 10
    calc (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)
        ≤ ((17 / 10 : ℝ) ^ n) ^ (1 / n : ℝ) := by
          apply Real.rpow_le_rpow (Nat.cast_nonneg _) h1
          positivity
      _ = 17 / 10 := by
          rw [one_div]
          exact Real.pow_rpow_inv_natCast (by norm_num) hn0
  linarith