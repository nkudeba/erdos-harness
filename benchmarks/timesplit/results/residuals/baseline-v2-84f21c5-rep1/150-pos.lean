open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- CHECK: Real.pow_rpow_inv_natCast Real.rpow_le_rpow le_of_tendsto

-- Open core: existence of lim c(n)^(1/n). Fekete via supermultiplicativity is the natural
-- attack, but no valid gluing is known (disjoint union collapses cuts, joins are additive).
theorem erdos_55259_hyp_limit_exists :
    ∃ L : ℝ, Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 L) := by
  sorry

-- Derived: by reduction (a) every inclusion-minimal cut T equals N(C) for a full component C
-- of G - T, so T is a minimal (a,b)-separator; Fomin–Villanger (Combinatorica 2012) /
-- Gaspers–Mackenzie (JGT 2018) bound those by O(n * phi^n), hence c(n) <= 1.7^n eventually.
theorem erdos_55259_hyp_exp_upper :
    ∃ β : ℝ, 0 ≤ β ∧ β < 2 ∧ ∃ N : ℕ, ∀ n ≥ N, (maxMinimalCuts n : ℝ) ≤ β ^ n := by
  sorry

theorem erdos_55259 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨L, hL⟩ := erdos_55259_hyp_limit_exists
  obtain ⟨β, hβ0, hβ2, N, hb⟩ := erdos_55259_hyp_exp_upper
  have hev : ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ β := by
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have h1 : 1 ≤ n := le_of_max_le_right hn
    have hNn : N ≤ n := le_of_max_le_left hn
    have hn1 : n ≠ 0 := by omega
    calc (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ (β ^ n) ^ (1 / n : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (hb n hNn) (by positivity)
      _ = β := by
          rw [one_div]
          exact Real.pow_rpow_inv_natCast hβ0 hn1
  have hLβ : L ≤ β := le_of_tendsto hL hev
  exact ⟨L, by linarith, hL⟩