-- CHECK: Real.pow_rpow_inv_natCast Real.rpow_le_rpow Metric.tendsto_atTop Real.dist_eq
open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- CONJECTURE (open core). Fomin–Villanger / Gaspers–Mackenzie give limsup c(n)^{1/n} ≤ φ < 2.
-- If that bound holds, the target is equivalent to c(n)^{1/n} failing to converge.
-- For a bounded sequence, failing to converge means oscillating between two exponential rates
-- β < γ along infinitely many n. This hypothesis is that oscillation, stated with integer
-- powers and no real roots. Any proof of the target must establish an equivalent of it.
theorem erdos_55259_neg_hyp_oscillation :
    ∃ β γ : ℝ, 0 < β ∧ β < γ ∧
      (∀ N : ℕ, ∃ n ≥ N, (maxMinimalCuts n : ℝ) ≤ β ^ n) ∧
      (∀ N : ℕ, ∃ n ≥ N, γ ^ n ≤ (maxMinimalCuts n : ℝ)) := by
  sorry

theorem erdos_55259_neg :
    ¬ (∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) := by
  rintro ⟨α, -, hα⟩
  obtain ⟨β, γ, hβ, hβγ, hlow, hhigh⟩ := erdos_55259_neg_hyp_oscillation
  have key : ∀ n : ℕ, n ≠ 0 → ∀ x : ℝ, 0 ≤ x → (x ^ n) ^ (1 / n : ℝ) = x := by
    intro n hn x hx
    rw [one_div]
    exact Real.pow_rpow_inv_natCast hx hn
  rw [Metric.tendsto_atTop] at hα
  obtain ⟨N, hN⟩ := hα ((γ - β) / 2) (by linarith)
  obtain ⟨n1, hn1, h1⟩ := hlow (N + 1)
  obtain ⟨n2, hn2, h2⟩ := hhigh (N + 1)
  have hn1' : n1 ≠ 0 := by omega
  have hn2' : n2 ≠ 0 := by omega
  have e1 : (maxMinimalCuts n1 : ℝ) ^ (1 / n1 : ℝ) ≤ β := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) h1
      (by positivity : (0:ℝ) ≤ 1 / (n1:ℝ))
    rwa [key n1 hn1' β hβ.le] at h
  have e2 : γ ≤ (maxMinimalCuts n2 : ℝ) ^ (1 / n2 : ℝ) := by
    have h := Real.rpow_le_rpow (pow_nonneg (by linarith) _) h2
      (by positivity : (0:ℝ) ≤ 1 / (n2:ℝ))
    rwa [key n2 hn2' γ (by linarith)] at h
  have d1 : dist ((maxMinimalCuts n1 : ℝ) ^ (1 / n1 : ℝ)) α < (γ - β) / 2 :=
    hN n1 (by omega)
  have d2 : dist ((maxMinimalCuts n2 : ℝ) ^ (1 / n2 : ℝ)) α < (γ - β) / 2 :=
    hN n2 (by omega)
  rw [Real.dist_eq, abs_lt] at d1 d2
  linarith