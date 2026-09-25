-- PUBLISHED: A. F. Sidorenko, "The Ramsey number of an N-edge graph versus triangle is at most 2N+1", J. Combin. Theory Ser. B 58 (1993), main theorem; independently W. Goddard and D. J. Kleitman, Discrete Math. (1994). Stated in the single-size form: every graph on 2m+1 vertices contains a triangle or its complement contains H.
theorem erdos_62774_hyp_sidorenko :
    ∀ (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v, 0 < H.degree v) →
      H.edgeSet.ncard = m →
      ∀ (C : SimpleGraph (Fin (2 * m + 1))),
        (SimpleGraph.cycleGraph 3).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

-- CONJECTURE (the open core, k ≥ 4): this is reduction R1 (the upward-closed Ramsey set, so a single vertex count
-- N = 2m + ⌊(k-1)/2⌋ suffices), stated in contrapositive form: a C_k-free graph on exactly N vertices has H in its
-- complement. The case k = 3 is removed because it is covered by Sidorenko's theorem.
-- A counterexample must be a C_k-free C on exactly N vertices with H ⋢ Cᶜ, where Fintype.card W ≤ 2m by the handshake lemma.
theorem erdos_62774_hyp_core :
    ∀ (k : ℕ), 4 ≤ k → ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
      ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        (∀ v, 0 < H.degree v) →
        H.edgeSet.ncard = m →
        ∀ (C : SimpleGraph (Fin (2 * m + (k - 1) / 2))),
          ¬ (SimpleGraph.cycleGraph k).IsContained C → H.IsContained Cᶜ := by
  sorry

namespace SimpleGraph
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }
end SimpleGraph

open Filter

theorem erdos_62774 :
    ∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ᶠ (m : ℕ) in atTop,
        ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ 2 * m + (k - 1) / 2 := by
  intro k hk
  rcases Nat.lt_or_ge k 4 with h | h
  · have hk3 : k = 3 := by omega
    subst hk3
    refine Filter.eventually_atTop.2 ⟨0, ?_⟩
    intro m _ W _ H _ hdeg hcard
    unfold SimpleGraph.graphRamsey
    apply Nat.sInf_le
    exact erdos_62774_hyp_sidorenko m W H hdeg hcard
  · obtain ⟨M, hM⟩ := erdos_62774_hyp_core k h
    refine Filter.eventually_atTop.2 ⟨M, ?_⟩
    intro m hm W _ H _ hdeg hcard
    unfold SimpleGraph.graphRamsey
    apply Nat.sInf_le
    simp only [Set.mem_setOf_eq]
    intro C
    by_cases hC : (SimpleGraph.cycleGraph k).IsContained C
    · exact Or.inl hC
    · exact Or.inr (hM m hm W H hdeg hcard C hC)