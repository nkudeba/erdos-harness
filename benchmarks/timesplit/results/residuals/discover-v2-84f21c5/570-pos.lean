namespace SimpleGraph
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }
end SimpleGraph

open Filter

def erdos_32140_HasIndepOfSize {n : ℕ} (C : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = r ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ C.Adj x y

-- Handshake lemma: sum of degrees = 2 * #edges, each degree ≥ 1, so |V(H)| ≤ 2m.
-- (Checked on all 28263 labelled graphs on 1..6 vertices.)
theorem erdos_32140_hyp_card :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v, 0 < H.degree v) → Fintype.card W ≤ 2 * H.edgeSet.ncard := by
  sorry

-- An independent set of size |W| in C is a clique of size |W| in Cᶜ; any H on W
-- embeds into that clique via a bijection W ≃ s.
namespace erdos_32140_hyp_indep_ns
open Filter

theorem erdos_32140_hyp_indep :
    ∀ (n : ℕ) (C : SimpleGraph (Fin n)) (W : Type) [Fintype W] (H : SimpleGraph W),
      erdos_32140_HasIndepOfSize C (Fintype.card W) → H.IsContained Cᶜ := by
  intro n C W _ H h
  obtain ⟨s, hs, hind⟩ := h
  have hc : Fintype.card W = Fintype.card s := by
    rw [Fintype.card_coe, hs]
  let e : W ≃ s := Fintype.equivOfCardEq hc
  refine ⟨⟨⟨fun w => ((e w : s) : Fin n), ?_⟩, ?_⟩⟩
  · intro a b hab
    have hne : a ≠ b := H.ne_of_adj hab
    have hne' : ((e a : s) : Fin n) ≠ ((e b : s) : Fin n) := by
      intro heq
      apply hne
      exact e.injective (Subtype.ext heq)
    rw [SimpleGraph.compl_adj]
    exact ⟨hne', hind _ (e a).2 _ (e b).2 hne'⟩
  · intro a b heq
    exact e.injective (Subtype.ext heq)
end erdos_32140_hyp_indep_ns

theorem erdos_32140_hyp_indep :
    ∀ (n : ℕ) (C : SimpleGraph (Fin n)) (W : Type) [Fintype W] (H : SimpleGraph W),
      erdos_32140_HasIndepOfSize C (Fintype.card W) → H.IsContained Cᶜ := by
  exact erdos_32140_hyp_indep_ns.erdos_32140_hyp_indep



-- Hard core (the open content, after R1 and the independence-number reduction):
-- only C_k-free C on exactly N = 2m + ⌊(k-1)/2⌋ vertices with α(C) < |V(H)| ≤ 2m remain.
theorem erdos_32140_hyp_core :
    ∀ (k : ℕ), 3 ≤ k →
      ∀ᶠ (m : ℕ) in atTop,
        ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          Fintype.card W ≤ 2 * m →
          ∀ (C : SimpleGraph (Fin (2 * m + (k - 1) / 2))),
            ¬ erdos_32140_HasIndepOfSize C (Fintype.card W) →
            (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

theorem erdos_32140 :
    ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ᶠ (m : ℕ) in atTop,
        ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ 2 * m + (k - 1) / 2 := by
  intro k hk
  filter_upwards [erdos_32140_hyp_core k hk] with m hm
  intro W _ H _ hdeg hE
  have hc : Fintype.card W ≤ 2 * m := by
    have h0 := erdos_32140_hyp_card W H hdeg
    rw [hE] at h0
    exact h0
  unfold SimpleGraph.graphRamsey
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq]
  intro C
  by_cases hC : erdos_32140_HasIndepOfSize C (Fintype.card W)
  · right
    exact erdos_32140_hyp_indep _ C W H hC
  · exact hm W H hdeg hE hc C hC