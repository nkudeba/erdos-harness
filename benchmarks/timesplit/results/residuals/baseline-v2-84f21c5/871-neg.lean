def erdos_34364_locallyObstructed (A : Set ℕ) (N : ℕ) : Prop :=
  ∃ S T : Finset ℕ, (∀ n ∈ T, N ≤ n) ∧
    (∀ n ∈ T, ∀ a ∈ A, ∀ b ∈ A, a + b = n → a ∈ S ∧ b ∈ S) ∧
    ∀ X ∈ S.powerset, ∃ n ∈ T,
      (∀ a ∈ X, ∀ b ∈ X, a + b ≠ n) ∨ (∀ a ∈ S \ X, ∀ b ∈ S \ X, a + b ≠ n)

-- Conjecture (derived): a counterexample built in blocks. For every threshold N there is a finite
-- gadget (S, T): targets T ⊆ [N, ∞) whose representations in A lie inside S, such that every
-- 2-colouring of S leaves some n ∈ T unrepresented in one colour class.
-- A random colouring fails each n ∈ T with probability ≤ 2(3/4)^{r(n)}. So such a gadget
-- forces |T| ≳ (4/3)^{min r}/2, and min over T of r must be O(log |T|). This is consistent with the
-- necessary condition ¬ Summable (3/4)^{r(n)}.
theorem erdos_34364_neg_hyp_block_obstruction :
    ∃ A : Set ℕ,
      (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) ∧
      ∀ N, erdos_34364_locallyObstructed A N := by
  sorry

theorem erdos_34364_neg :
    ¬ (∀ (A : Set ℕ),
        (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
        (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
        ∃ (B C : Set ℕ),
          (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
          Disjoint B C ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n)) := by
  classical
  intro h
  obtain ⟨A, hbasis, hgrowth, hobs⟩ := erdos_34364_neg_hyp_block_obstruction
  obtain ⟨B, C, hiff, hdisj, hB, hC⟩ := h A ⟨hbasis, hgrowth⟩
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hB
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hC
  obtain ⟨S, T, hTN, hloc, hX⟩ := hobs (max N1 N2)
  obtain ⟨n, hnT, hn⟩ :=
    hX (S.filter (fun x => x ∈ B)) (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (hTN n hnT)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (hTN n hnT)
  rcases hn with hn | hn
  · obtain ⟨a, ha, b, hb, hab⟩ := hN1 n hn1
    have haA : a ∈ A := (hiff a).2 (Or.inl ha)
    have hbA : b ∈ A := (hiff b).2 (Or.inl hb)
    obtain ⟨haS, hbS⟩ := hloc n hnT a haA b hbA hab
    exact hn a (Finset.mem_filter.2 ⟨haS, ha⟩) b (Finset.mem_filter.2 ⟨hbS, hb⟩) hab
  · obtain ⟨a, ha, b, hb, hab⟩ := hN2 n hn2
    have haA : a ∈ A := (hiff a).2 (Or.inr ha)
    have hbA : b ∈ A := (hiff b).2 (Or.inr hb)
    obtain ⟨haS, hbS⟩ := hloc n hnT a haA b hbA hab
    have haB : a ∉ B := fun h' => Set.disjoint_left.1 hdisj h' ha
    have hbB : b ∉ B := fun h' => Set.disjoint_left.1 hdisj h' hb
    exact hn a (Finset.mem_sdiff.2 ⟨haS, fun h' => haB (Finset.mem_filter.1 h').2⟩)
      b (Finset.mem_sdiff.2 ⟨hbS, fun h' => hbB (Finset.mem_filter.1 h').2⟩) hab