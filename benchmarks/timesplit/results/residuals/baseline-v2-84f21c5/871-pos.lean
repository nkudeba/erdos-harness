def IsAsymBasis2 (S : Set ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, ∃ a ∈ S, ∃ b ∈ S, a + b = n

def GrowthHyp (A : Set ℕ) : Prop :=
  ∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
    pairs.card ≥ t ∧
      ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2

def HasDisjointSubBases (A : Set ℕ) : Prop :=
  ∃ B C : Set ℕ, B ⊆ A ∧ C ⊆ A ∧ Disjoint B C ∧ IsAsymBasis2 B ∧ IsAsymBasis2 C

noncomputable def roff (A : Set ℕ) (n : ℕ) : ℕ :=
  {a : ℕ | a ∈ A ∧ n - a ∈ A ∧ 2 * a < n}.ncard

-- Derived (first-moment / Borel–Cantelli, the Erdős–Nathanson route): colour A by fair coins;
-- the off-diagonal pairs {a, n-a} are disjoint, so P(n not represented in one class) ≤ (3/4)^(roff A n).
-- If Σ (3/4)^roff < ∞, then choose N₀ with the tail sum over n > N₀ of 2(3/4)^roff less than 1.
-- A counting argument on finite windows, plus compactness, gives a colouring with both classes bases.
theorem erdos_34364_hyp_summable :
    ∀ A : Set ℕ, GrowthHyp A →
      Summable (fun n : ℕ => (3/4 : ℝ) ^ roff A n) → HasDisjointSubBases A := by
  sorry

-- Open core: the slow-growth regime. Every counterexample must satisfy GrowthHyp A and the
-- non-summability of (3/4)^roff (checked invariant). This is the part the published results do not cover.
theorem erdos_34364_hyp_slow :
    ∀ A : Set ℕ, GrowthHyp A →
      ¬ Summable (fun n : ℕ => (3/4 : ℝ) ^ roff A n) → HasDisjointSubBases A := by
  sorry

theorem erdos_34364 :
    ∀ (A : Set ℕ),
        (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
        (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
        ∃ (B C : Set ℕ),
          (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
          Disjoint B C ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  intro A hA
  obtain ⟨_, hg⟩ := hA
  have hd : HasDisjointSubBases A := by
    by_cases hs : Summable (fun n : ℕ => (3/4 : ℝ) ^ roff A n)
    · exact erdos_34364_hyp_summable A hg hs
    · exact erdos_34364_hyp_slow A hg hs
  unfold HasDisjointSubBases IsAsymBasis2 at hd
  obtain ⟨B, C, hBA, hCA, hBC, hB, hC⟩ := hd
  refine ⟨A \ C, C, ?_, ?_, ?_, hC⟩
  · intro x
    constructor
    · intro hx
      by_cases h : x ∈ C
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    · rintro (h | h)
      · exact h.1
      · exact hCA h
  · exact Set.disjoint_left.mpr (fun x hx hxC => hx.2 hxC)
  · filter_upwards [hB] with n hn
    obtain ⟨a, ha, b, hb, hab⟩ := hn
    exact ⟨a, ⟨hBA ha, fun h => Set.disjoint_left.mp hBC ha h⟩,
      b, ⟨hBA hb, fun h => Set.disjoint_left.mp hBC hb h⟩, hab⟩