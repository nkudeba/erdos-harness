namespace SimpleGraph
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }
end SimpleGraph

-- Finite Ramsey theorem for (C_k, H): take n ≥ R(k, |W|); an independent set of size |W|
-- in C makes Cᶜ contain K_|W| ⊇ H, and a k-clique in C contains C_k.
theorem erdos_62774_neg_hyp_finite :
    ∀ (k : ℕ), 3 ≤ k → ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      ∃ n : ℕ, ∀ C : SimpleGraph (Fin n),
        (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  sorry

-- Upward closure: a bad colouring on Fin N restricts (via Fin.castLE) to a bad colouring on Fin n,
-- since containment in the restriction (or in its complement) lifts to C (or Cᶜ).
namespace erdos_62774_neg_hyp_mono_ns
open Filter

private lemma copy_push {α β γ : Type*} (A : SimpleGraph α) (B : SimpleGraph β)
    (D : SimpleGraph γ) (f : β → γ) (hf : Function.Injective f)
    (hadj : ∀ a b, B.Adj a b → D.Adj (f a) (f b)) (h : A.IsContained B) :
    A.IsContained D := by
  obtain ⟨c⟩ := h
  exact ⟨⟨⟨fun x => f (c.toHom x), fun {a b} hab => hadj _ _ (c.toHom.map_rel' hab)⟩,
    fun a b hab => c.injective' (hf hab)⟩⟩

theorem erdos_62774_neg_hyp_mono :
    ∀ (k : ℕ), 3 ≤ k → ∀ (W : Type) (H : SimpleGraph W) (n N : ℕ), n ≤ N →
      (∀ C : SimpleGraph (Fin n), (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ) →
      ∀ C : SimpleGraph (Fin N), (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  intro k _ W H n N hnN hP C
  rcases hP (C.comap (Fin.castLE hnN)) with h | h
  · left
    exact copy_push _ _ _ (Fin.castLE hnN) (Fin.castLE_injective hnN)
      (fun a b hab => hab) h
  · right
    refine copy_push _ _ _ (Fin.castLE hnN) (Fin.castLE_injective hnN) ?_ h
    intro a b hab
    rw [SimpleGraph.compl_adj] at hab ⊢
    exact ⟨fun e => hab.1 (Fin.castLE_injective hnN e), hab.2⟩
end erdos_62774_neg_hyp_mono_ns

theorem erdos_62774_neg_hyp_mono :
    ∀ (k : ℕ), 3 ≤ k → ∀ (W : Type) (H : SimpleGraph W) (n N : ℕ), n ≤ N →
      (∀ C : SimpleGraph (Fin n), (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ) →
      ∀ C : SimpleGraph (Fin N), (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ := by
  exact erdos_62774_neg_hyp_mono_ns.erdos_62774_neg_hyp_mono



-- Core open hypothesis: a counterexample must supply, for infinitely many m, a colouring on
-- exactly 2m + (k-1)/2 vertices avoiding C_k in C and H in Cᶜ (derived necessary condition).
theorem erdos_62774_neg_hyp_core :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧
      ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj),
        (∀ v, 0 < H.degree v) ∧ H.edgeSet.ncard = m ∧
        ∃ C : SimpleGraph (Fin (2 * m + (k - 1) / 2)),
          ¬ (SimpleGraph.cycleGraph k).IsContained C ∧ ¬ H.IsContained Cᶜ := by
  sorry

open Filter

theorem erdos_62774_neg :
    ¬ (∀ (k : ℕ) (hk : 3 ≤ k),
      ∀ᶠ (m : ℕ) in atTop,
        ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ 2 * m + (k - 1) / 2) := by
  intro h
  obtain ⟨k, hk, hcore⟩ := erdos_62774_neg_hyp_core
  have hev := h k hk
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  obtain ⟨m, hmM, W, instW, H, instH, hdeg, hcard, C, hC1, hC2⟩ := hcore M
  have hle := hM m hmM W H hdeg hcard
  have hne : Set.Nonempty {n : ℕ | ∀ C : SimpleGraph (Fin n),
      (SimpleGraph.cycleGraph k).IsContained C ∨ H.IsContained Cᶜ} := by
    obtain ⟨n0, hn0⟩ := erdos_62774_neg_hyp_finite k hk W H
    exact ⟨n0, hn0⟩
  have hmem := Nat.sInf_mem hne
  have hall := erdos_62774_neg_hyp_mono k hk W H
    (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H) (2 * m + (k - 1) / 2) hle hmem
  rcases hall C with h1 | h2
  · exact hC1 h1
  · exact hC2 h2