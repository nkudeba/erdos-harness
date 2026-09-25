open scoped Classical

/-- `H` is an admissible completion of `G`: a triangle-free supergraph in which every pair of
distinct vertices is adjacent or has a common neighbour. -/
def IsTFDiam2Ext {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  G ≤ H ∧ H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y)

-- Hard core (deferred). If the published o(n^{1/2}) theorem (Sankar 2022, citation unverified;
-- Alon earlier for n^{1/2-ε}) is correct, it should give this sparse completion statement:
-- for every ε there is a δ such that every large triangle-free G with Δ(G) ≤ δ√n has an
-- admissible completion H with at most εn² edges in total.
-- By R2 this is equivalent in strength to the target, so it is recorded as the open core,
-- not as a published premise.
theorem erdos_80394_hyp_core :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 → ((G.maxDegree : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2)) →
      ∃ H : SimpleGraph (Fin n), IsTFDiam2Ext G H ∧
        (H.edgeFinset.card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

open scoped Classical
open Filter Asymptotics

noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
    H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

theorem erdos_80394 :
    ∀ (G : ∀ n : ℕ, SimpleGraph (Fin n)),
      (∀ n, (G n).CliqueFree 3) →
      (fun n => ((G n).maxDegree : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (fun n => (h2 (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  intro G hG hΔ
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, N, hN⟩ := erdos_80394_hyp_core c hc
  have h1 := (Asymptotics.isLittleO_iff.mp hΔ) hδ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h1
  refine Filter.eventually_atTop.mpr ⟨max M N, fun n hn => ?_⟩
  have hMn : M ≤ n := le_trans (le_max_left _ _) hn
  have hNn : N ≤ n := le_trans (le_max_right _ _) hn
  have hdeg' : ((G n).maxDegree : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := hM n hMn
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h
    exact h
  obtain ⟨H, ⟨hGH, hH3, hHd⟩, hcard⟩ := hN n hNn (G n) (hG n) hdeg'
  have hmem : (H.edgeFinset \ (G n).edgeFinset).card ∈
      {k : ℕ | ∃ H' : SimpleGraph (Fin n),
        G n ≤ H' ∧
        H'.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H'.Adj x y ∨ ∃ z, H'.Adj x z ∧ H'.Adj z y) ∧
        (H'.edgeFinset \ (G n).edgeFinset).card = k} :=
    ⟨H, hGH, hH3, hHd, rfl⟩
  have hle : h2 (G n) ≤ (H.edgeFinset \ (G n).edgeFinset).card := by
    unfold h2
    exact Nat.sInf_le hmem
  have hle2 : (H.edgeFinset \ (G n).edgeFinset).card ≤ H.edgeFinset.card :=
    Finset.card_le_card Finset.sdiff_subset
  have hcast : (h2 (G n) : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
    exact_mod_cast le_trans hle hle2
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (sq_nonneg _)]
  linarith