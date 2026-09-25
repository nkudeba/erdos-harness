open scoped Classical
open Filter Asymptotics

noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
    H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

-- Existence of a counterexample family, stated quantitatively: a fixed c > 0 with
-- h2(G_n) ≥ c n^2 for infinitely many n. Any counterexample must satisfy this.
-- BELIEVED FALSE: it contradicts Sankar (2022), who proved h2 = o(n^2) when maxDegree = o(n^{1/2}).
theorem erdos_80394_neg_hyp_quadratic_family :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ∀ n : ℕ, SimpleGraph (Fin n),
      (∀ n, (G n).CliqueFree 3) ∧
      (fun n => ((G n).maxDegree : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) ∧
      ∀ N : ℕ, ∃ n ≥ N, c * (n : ℝ) ^ 2 ≤ (h2 (G n) : ℝ) := by
  sorry

theorem erdos_80394_neg :
    ¬ (∀ (G : ∀ n : ℕ, SimpleGraph (Fin n)),
      (∀ n, (G n).CliqueFree 3) →
      (fun n => ((G n).maxDegree : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (fun n => (h2 (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2)) := by
  intro hall
  obtain ⟨c, hc, G, htf, hdeg, hfreq⟩ := erdos_80394_neg_hyp_quadratic_family
  have ho := hall G htf hdeg
  have hev := ho.def (half_pos hc)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨n, hn, hcn⟩ := hfreq (N + 1)
  have h1 := hN n (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnpos 2
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (h2 (G n))),
    Real.norm_of_nonneg (le_of_lt hsq)] at h1
  nlinarith [mul_pos hc hsq]