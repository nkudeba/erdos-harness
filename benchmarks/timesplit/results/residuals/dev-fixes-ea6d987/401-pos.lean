-- CHECK: Finset.prod_dvd_prod_of_subset Finset.range_mono Real.log_natCast_nonneg Set.Ioi_infinite Nat.findGreatest_spec Nat.le_findGreatest Nat.le_ceil
open Filter

noncomputable def P39531 (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i

def GoodSet39531 (r : ℕ) (c : ℝ) : Set ℕ :=
  {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
    (a₁ : ℝ) + a₂ > n + c * Real.log n ∧
    a₁.factorial * a₂.factorial ∣ n.factorial * (P39531 r) ^ n}

-- CONJECTURE (the open core, in weakened form): for every constant K, SOME r has infinitely many
-- n whose gain exceeds K log n. With L_r = limsup T_r(n)/log n, this says sup_r L_r = ∞.
-- The derivation in the cycle output shows that sup_r L_r = ∞ is exactly the negation of a
-- counterexample. This is weaker than the target: it asks for one r per K, not every r
-- simultaneously with a single f.
theorem erdos_39531_hyp_unbounded :
    ∀ K : ℕ, ∃ r : ℕ, (GoodSet39531 r (K : ℝ)).Infinite := by
  sorry

theorem erdos_39531 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  classical
  have hmono : ∀ r r' : ℕ, r ≤ r' → ∀ c : ℝ, GoodSet39531 r c ⊆ GoodSet39531 r' c := by
    intro r r' hrr c n hn
    simp only [GoodSet39531, Set.mem_setOf_eq] at hn ⊢
    obtain ⟨a₁, a₂, h1, h2, h3, h4⟩ := hn
    refine ⟨a₁, a₂, h1, h2, h3, h4.trans ?_⟩
    apply Nat.mul_dvd_mul_left
    apply pow_dvd_pow_of_dvd
    unfold P39531
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hrr)
  have hzero : ∀ r : ℕ, (GoodSet39531 r 0).Infinite := by
    intro r
    refine Set.Infinite.mono ?_ (Set.Ioi_infinite 0)
    intro n hn
    simp only [Set.mem_Ioi] at hn
    simp only [GoodSet39531, Set.mem_setOf_eq]
    refine ⟨n, 1, hn, one_pos, ?_, ?_⟩
    · norm_num
    · rw [Nat.factorial_one, mul_one]
      exact dvd_mul_right _ _
  have H := erdos_39531_hyp_unbounded
  let g : ℕ → ℕ := fun r =>
    Nat.findGreatest (fun K : ℕ => (GoodSet39531 r (K : ℝ)).Infinite) r
  refine ⟨fun r => (g r : ℝ), ?_, ?_⟩
  · rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨r0, hr0⟩ := H ⌈b⌉₊
    rw [Filter.eventually_atTop]
    refine ⟨max r0 ⌈b⌉₊, fun r hr => ?_⟩
    have h1 : r0 ≤ r := le_trans (le_max_left _ _) hr
    have h2 : ⌈b⌉₊ ≤ r := le_trans (le_max_right _ _) hr
    have hinf : (GoodSet39531 r (⌈b⌉₊ : ℝ)).Infinite := hr0.mono (hmono r0 r h1 _)
    have hle : ⌈b⌉₊ ≤ g r := Nat.le_findGreatest h2 hinf
    show b ≤ (g r : ℝ)
    calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      _ ≤ (g r : ℝ) := by exact_mod_cast hle
  · intro r _hr
    have hspec : (GoodSet39531 r (g r : ℝ)).Infinite :=
      Nat.findGreatest_spec (P := fun K : ℕ => (GoodSet39531 r (K : ℝ)).Infinite)
        (Nat.zero_le r) (by simpa using hzero r)
    exact hspec