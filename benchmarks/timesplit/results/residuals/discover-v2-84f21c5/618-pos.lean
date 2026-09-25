open scoped Classical

noncomputable def farPairs33134 {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ ¬ H.Adj p.1 p.2 ∧ ¬ ∃ z, H.Adj p.1 z ∧ H.Adj z p.2)).card

-- DERIVED (reduction R1): extend H0 greedily to a maximal triangle-free graph H.
-- An edge xy is only ever added when x,y are non-adjacent with no common neighbour
-- in the current graph ⊇ H0, hence x,y form an H0-far pair. So at most farPairs H0
-- edges are added beyond H0. Maximality gives the diameter-2 condition.
namespace erdos_33134_hyp_greedy_completion_ns
-- CHECK: SimpleGraph.is3Clique_iff SimpleGraph.fromRel_adj SimpleGraph.edgeFinset_ssubset_edgeFinset Sym2.eq_swap
open scoped Classical

open scoped Classical

open Filter Asymptotics

private lemma tf_iff33134 {n : ℕ} (K : SimpleGraph (Fin n)) :
    K.CliqueFree 3 ↔ ∀ a b c, K.Adj a b → K.Adj a c → K.Adj b c → False := by
  constructor
  · intro hK a b c hab hac hbc
    exact hK {a, b, c} (SimpleGraph.is3Clique_iff.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩)
  · intro h s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h a b c hab hac hbc

private def addE33134 {n : ℕ} (H : SimpleGraph (Fin n)) (x y : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => H.Adj u v ∨ (u = x ∧ v = y))

private lemma addE_adj33134 {n : ℕ} (H : SimpleGraph (Fin n)) (x y a b : Fin n) :
    (addE33134 H x y).Adj a b ↔
      a ≠ b ∧ (H.Adj a b ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) := by
  unfold addE33134
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (h | h) | (h | ⟨h1, h2⟩)⟩
    · exact ⟨hne, Or.inl h⟩
    · exact ⟨hne, Or.inr (Or.inl h)⟩
    · exact ⟨hne, Or.inl h.symm⟩
    · exact ⟨hne, Or.inr (Or.inr ⟨h2, h1⟩)⟩
  · rintro ⟨hne, h | h | ⟨h1, h2⟩⟩
    · exact ⟨hne, Or.inl (Or.inl h)⟩
    · exact ⟨hne, Or.inl (Or.inr h)⟩
    · exact ⟨hne, Or.inr (Or.inr ⟨h2, h1⟩)⟩

private lemma extend33134 {n : ℕ} (H0 : SimpleGraph (Fin n)) :
    ∀ k : ℕ, ∀ H : SimpleGraph (Fin n), H0 ≤ H → H.CliqueFree 3 →
      (∀ a b, H.Adj a b → H0.Adj a b ∨ (¬ H0.Adj a b ∧ ¬ ∃ z, H0.Adj a z ∧ H0.Adj z b)) →
      n.choose 2 - H.edgeFinset.card = k →
      ∃ H' : SimpleGraph (Fin n), H0 ≤ H' ∧ H'.CliqueFree 3 ∧
        (∀ a b, H'.Adj a b → H0.Adj a b ∨ (¬ H0.Adj a b ∧ ¬ ∃ z, H0.Adj a z ∧ H0.Adj z b)) ∧
        (∀ x y : Fin n, x ≠ y → H'.Adj x y ∨ ∃ z, H'.Adj x z ∧ H'.Adj z y) := by
  intro k
  induction k using Nat.strong_induction_on
  rename_i k ih
  intro H hle htf hall hk
  by_cases hd : ∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y
  · exact ⟨H, hle, htf, hall, hd⟩
  push_neg at hd
  obtain ⟨x, y, hxy, hnadj, hno⟩ := hd
  have hHtf := (tf_iff33134 H).mp htf
  obtain ⟨H1, hadj⟩ : ∃ H1 : SimpleGraph (Fin n), ∀ a b, H1.Adj a b ↔
      a ≠ b ∧ (H.Adj a b ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) :=
    ⟨addE33134 H x y, addE_adj33134 H x y⟩
  have hHH1 : H ≤ H1 := by
    intro a b h
    exact (hadj a b).mpr ⟨h.ne, Or.inl h⟩
  have hxy1 : H1.Adj x y := (hadj x y).mpr ⟨hxy, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have hred : ∀ p w, H1.Adj p w → w ≠ x → w ≠ y → H.Adj p w := by
    intro p w h hwx hwy
    rcases ((hadj p w).mp h).2 with h' | ⟨_, h'⟩ | ⟨_, h'⟩
    · exact h'
    · exact absurd h' hwy
    · exact absurd h' hwx
  have hP : ∀ u v w, H1.Adj u w → H1.Adj v w →
      ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → False := by
    intro u v w huw hvw hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hwx : w ≠ x := fun h => huw.ne (h1.trans h.symm)
      have hwy : w ≠ y := fun h => hvw.ne (h2.trans h.symm)
      have a1 := hred u w huw hwx hwy
      have a2 := hred v w hvw hwx hwy
      rw [h1] at a1
      rw [h2] at a2
      exact hno w a1 a2.symm
    · have hwy : w ≠ y := fun h => huw.ne (h1.trans h.symm)
      have hwx : w ≠ x := fun h => hvw.ne (h2.trans h.symm)
      have a1 := hred u w huw hwx hwy
      have a2 := hred v w hvw hwx hwy
      rw [h1] at a1
      rw [h2] at a2
      exact hno w a2 a1.symm
  have htf1 : H1.CliqueFree 3 := by
    rw [tf_iff33134]
    intro a b c hab hac hbc
    by_cases e1 : (a = x ∧ b = y) ∨ (a = y ∧ b = x)
    · exact hP a b c hac hbc e1
    by_cases e2 : (a = x ∧ c = y) ∨ (a = y ∧ c = x)
    · exact hP a c b hab hbc.symm e2
    by_cases e3 : (b = x ∧ c = y) ∨ (b = y ∧ c = x)
    · exact hP b c a hab.symm hac.symm e3
    have g : ∀ p q, H1.Adj p q → ¬((p = x ∧ q = y) ∨ (p = y ∧ q = x)) → H.Adj p q := by
      intro p q h hn
      rcases ((hadj p q).mp h).2 with h' | h'
      · exact h'
      · exact absurd h' hn
    exact hHtf a b c (g a b hab e1) (g a c hac e2) (g b c hbc e3)
  have hall1 : ∀ a b, H1.Adj a b →
      H0.Adj a b ∨ (¬ H0.Adj a b ∧ ¬ ∃ z, H0.Adj a z ∧ H0.Adj z b) := by
    intro a b h
    rcases ((hadj a b).mp h).2 with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hall a b h'
    · right
      rw [h1, h2]
      refine ⟨fun h0 => hnadj (hle h0), ?_⟩
      rintro ⟨z, hz1, hz2⟩
      exact hno z (hle hz1) (hle hz2)
    · right
      rw [h1, h2]
      refine ⟨fun h0 => hnadj (hle h0.symm), ?_⟩
      rintro ⟨z, hz1, hz2⟩
      exact hno z (hle hz2.symm) (hle hz1.symm)
  have hle1 : H0 ≤ H1 := le_trans hle hHH1
  have hlt : H < H1 := by
    refine lt_of_le_of_ne hHH1 ?_
    intro heq
    rw [← heq] at hxy1
    exact hnadj hxy1
  have hcard : H.edgeFinset.card < H1.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have hbound : H1.edgeFinset.card ≤ n.choose 2 := by
    have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H1)
    simpa [Fintype.card_fin] using this
  exact ih (n.choose 2 - H1.edgeFinset.card) (by omega) H1 hle1 htf1 hall1 rfl

theorem erdos_33134_hyp_greedy_completion :
    ∀ (n : ℕ) (G H0 : SimpleGraph (Fin n)), G ≤ H0 → H0.CliqueFree 3 →
      ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        (H.edgeFinset \ G.edgeFinset).card ≤
          (H0.edgeFinset \ G.edgeFinset).card + farPairs33134 H0 := by
  intro n G H0 hGH0 htf0
  have hall0 : ∀ a b, H0.Adj a b →
      H0.Adj a b ∨ (¬ H0.Adj a b ∧ ¬ ∃ z, H0.Adj a z ∧ H0.Adj z b) :=
    fun a b h => Or.inl h
  obtain ⟨H, hle, htf, hall, hd⟩ := extend33134 H0 _ H0 le_rfl htf0 hall0 rfl
  refine ⟨H, le_trans hGH0 hle, htf, hd, ?_⟩
  set F := ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ ¬ H0.Adj p.1 p.2 ∧ ¬ ∃ z, H0.Adj p.1 z ∧ H0.Adj z p.2)) with hF
  have hsub : H.edgeFinset \ G.edgeFinset ⊆
      (H0.edgeFinset \ G.edgeFinset) ∪ F.image (fun p => s(p.1, p.2)) := by
    intro e he
    induction e using Sym2.ind
    rename_i a b
    simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨hHab, hGab⟩ := he
    rw [Finset.mem_union]
    rcases hall a b hHab with h0 | ⟨hn1, hn2⟩
    · left
      simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨h0, hGab⟩
    · right
      rw [Finset.mem_image]
      rcases lt_or_gt_of_ne hHab.ne with hlt | hlt
      · refine ⟨(a, b), ?_, rfl⟩
        rw [hF, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt, hn1, hn2⟩
      · refine ⟨(b, a), ?_, Sym2.eq_swap⟩
        rw [hF, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hlt, fun h => hn1 h.symm, ?_⟩
        rintro ⟨z, hz1, hz2⟩
        exact hn2 ⟨z, hz2.symm, hz1.symm⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (H0.edgeFinset \ G.edgeFinset) (F.image (fun p => s(p.1, p.2)))
  have h3 : (F.image (fun p => s(p.1, p.2))).card ≤ farPairs33134 H0 := Finset.card_image_le
  omega
end erdos_33134_hyp_greedy_completion_ns

theorem erdos_33134_hyp_greedy_completion :
    ∀ (n : ℕ) (G H0 : SimpleGraph (Fin n)), G ≤ H0 → H0.CliqueFree 3 →
      ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        (H.edgeFinset \ G.edgeFinset).card ≤
          (H0.edgeFinset \ G.edgeFinset).card + farPairs33134 H0 := by
  exact erdos_33134_hyp_greedy_completion_ns.erdos_33134_hyp_greedy_completion



-- DERIVED (hub construction, operator guidance): take m = ⌈(Δ+1)√n⌉ hubs t_j.
-- Join each t_j to an independent random set I_j avoiding N(t_j) ∪ N(N(t_j)).
-- This gives ≤ m n new edges, and a Chebyshev argument leaves ≤ m n + ε_n n^2 far pairs.
-- This is uniform in G, so it is stated as a single ε–δ statement over all n ≥ N.
theorem erdos_33134_hyp_hub_construction :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
        ((G.maxDegree : ℕ) : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2) →
        ∃ H0 : SimpleGraph (Fin n), G ≤ H0 ∧ H0.CliqueFree 3 ∧
          (((H0.edgeFinset \ G.edgeFinset).card + farPairs33134 H0 : ℕ) : ℝ)
            ≤ ε * (n : ℝ) ^ 2 := by
  sorry

open scoped Classical
open Filter Asymptotics

noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
    H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

theorem erdos_33134 :
    ∀ (G : ∀ n : ℕ, SimpleGraph (Fin n)),
      (∀ n, (G n).CliqueFree 3) →
      (fun n => ((G n).maxDegree : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (fun n => (h2 (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  intro G hG hΔ
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := erdos_33134_hyp_hub_construction ε hε
  have h1 := Asymptotics.isLittleO_iff.mp hΔ hδ
  filter_upwards [h1, Filter.eventually_ge_atTop N] with n hn hnN
  try dsimp only at hn ⊢
  have hmd : ((G n).maxDegree : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h0' : (0 : ℝ) ≤ ((G n).maxDegree : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg h0', Real.norm_of_nonneg h0] at hn
    exact hn
  obtain ⟨H0, hle, hcf, hbound⟩ := hN n hnN (G n) (hG n) hmd
  obtain ⟨H, hGH, hHcf, hdiam, hcard⟩ :=
    erdos_33134_hyp_greedy_completion n (G n) H0 hle hcf
  have hh2 : h2 (G n) ≤ (H.edgeFinset \ (G n).edgeFinset).card := by
    unfold h2
    apply Nat.sInf_le
    rw [Set.mem_setOf_eq]
    exact ⟨H, hGH, hHcf, hdiam, rfl⟩
  have hc : (h2 (G n) : ℝ) ≤
      (((H0.edgeFinset \ (G n).edgeFinset).card + farPairs33134 H0 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (hh2.trans hcard)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (h2 (G n))),
    Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
  exact hc.trans hbound