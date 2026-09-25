theorem erdos_94894_neg_hyp_infinite_sidon_interval :
    ∃ a K : ℕ, 1 ≤ a ∧ 1 ≤ K ∧ ∃ B : ℕ → ℕ, B 0 = a ∧ (∀ i, B i < B (i + 1)) ∧
      (∀ i, B (i + 1) - B i ≤ K) ∧
      ∀ u v x y : ℕ, u < v → x < y → (u, v) ≠ (x, y) →
        ∑ i ∈ Finset.Ico u v, B i ≠ ∑ i ∈ Finset.Ico x y, B i := by
  sorry

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

theorem erdos_94894_neg :
    ¬ (∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s) := by
  intro h
  obtain ⟨a, K, ha, hK, B, hB0, hBmono, hBgap, hdist⟩ := erdos_94894_neg_hyp_infinite_sidon_interval
  obtain ⟨f, hf⟩ := h a K ha hK
  have hsm : StrictMono B := strictMono_nat_of_lt_succ hBmono
  have hge : ∀ i, i ≤ B i := by
    intro i
    induction i with
    | zero => omega
    | succ n ih => have := hBmono n; omega
  have hlast : f < B (f + 2 - 1) := by
    have e : f + 2 - 1 = f + 1 := by omega
    rw [e]
    have := hge (f + 1)
    omega
  obtain ⟨u, v, x, y, huv, _, hxy, _, hne, hsum⟩ :=
    hf (f + 2) B (by omega) hB0 (hsm.strictMonoOn _) (fun i _ => hBgap i) hlast
  exact hdist u v x y huv hxy hne hsum