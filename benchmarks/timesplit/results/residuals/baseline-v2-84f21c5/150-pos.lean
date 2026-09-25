-- CHECK: Real.pow_rpow_inv_natCast Real.rpow_le_rpow le_of_tendsto Filter.eventually_ge_atTop
open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- Derived from PUBLISHED: Fomin–Kratsch–Todinca–Villanger (SIAM J. Comput. 2008) and
-- Fomin–Villanger (Combinatorica 2012): an n-vertex graph has O(1.7087^n) minimal separators.
-- By R1 (every minimal cut T equals N(C) for each of its >= 2 full components), every
-- minimal cut is a minimal separator. So c(n) <= K * 1.7087^n <= 1.8^n for large n.
theorem erdos_26015_hyp_upper :
    ∃ β : ℝ, 0 ≤ β ∧ β < 2 ∧ ∃ N : ℕ, ∀ n ≥ N, (maxMinimalCuts n : ℝ) ≤ β ^ n := by
  sorry

-- Open core: existence of the limit of c(n)^(1/n). Expected route: s(n) = max number of
-- minimal a-b separators; gluing at {a,b} gives s(m+n-2) >= s(m) s(n); s(n) <= c(n) <= n^2 s(n);
-- then Fekete.
theorem erdos_26015_hyp_limit :
    ∃ L : ℝ, Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 L) := by
  sorry

theorem erdos_26015 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨L, hL⟩ := erdos_26015_hyp_limit
  obtain ⟨β, hβ0, hβ2, N, hN⟩ := erdos_26015_hyp_upper
  have hev : ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ β := by
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have h1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hnN : N ≤ n := le_trans (le_max_left N 1) hn
    have hn0 : n ≠ 0 := by omega
    calc (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ (β ^ n) ^ (1 / n : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (hN n hnN) (by positivity)
      _ = β := by
          rw [one_div]
          exact Real.pow_rpow_inv_natCast hβ0 hn0
  exact ⟨L, lt_of_le_of_lt (le_of_tendsto hL hev) hβ2, hL⟩