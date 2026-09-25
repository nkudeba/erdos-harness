open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- CONJECTURE (hard core). Known facts: liminf c(n)^{1/n} ≥ 3^{1/3} and limsup < 2 (Fomin–Villanger bound on minimal separators).
-- With those facts, the frozen target holds exactly when the sequence c(n)^{1/n} fails to converge.
-- This hypothesis asserts that failure in an explicit form: the sequence is frequently ≤ a and frequently ≥ b, for some a < b.
-- It is strictly stronger than the target, since it rules out convergence to any real limit.
-- Given the known bounds, it is equivalent to the target.
theorem erdos_26015_neg_hyp_oscillation :
    ∃ a b : ℝ, a < b ∧
      (∃ᶠ n in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ a) ∧
      (∃ᶠ n in atTop, b ≤ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) := by
  sorry

theorem erdos_26015_neg :
    ¬ (∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) := by
  rintro ⟨α, -, hα⟩
  obtain ⟨a, b, hab, ha, hb⟩ := erdos_26015_neg_hyp_oscillation
  rcases lt_or_ge α b with h | h
  · obtain ⟨n, h1, h2⟩ := (hb.and_eventually (hα.eventually (gt_mem_nhds h))).exists
    exact (not_lt.mpr h1) h2
  · obtain ⟨n, h1, h2⟩ :=
      (ha.and_eventually (hα.eventually (lt_mem_nhds (lt_of_lt_of_le hab h)))).exists
    exact (not_lt.mpr h1) h2