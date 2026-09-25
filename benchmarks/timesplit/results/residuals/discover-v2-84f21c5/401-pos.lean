open Filter

def erdos_49172_good (r : ℕ) (c : ℝ) : Prop :=
  {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
    (a₁ : ℝ) + a₂ > n + c * Real.log n ∧
    a₁.factorial * a₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite

-- Core (R1 form): for each integer K, some r works. Should follow from the random
-- Kummer/Legendre construction: s = a₁+a₂-n ≈ 2K log X, with p_{r+1} ≫ K log p_{r+1}.
theorem erdos_49172_hyp_core :
    ∀ K : ℕ, ∃ r : ℕ, 1 ≤ r ∧ erdos_49172_good r (K : ℝ) := by
  sorry

-- R1 fact (2): the product over range r divides the product over range r', so P_r^n ∣ P_{r'}^n.
namespace erdos_49172_hyp_mono_r_ns
open Filter

theorem erdos_49172_hyp_mono_r :
    ∀ (r r' : ℕ) (c : ℝ), r ≤ r' → erdos_49172_good r c → erdos_49172_good r' c := by
  intro r r' c hrr' h
  unfold erdos_49172_good at *
  have hsub : Finset.range r ⊆ Finset.range r' := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hprod : (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ∣
      ∏ i ∈ Finset.range r', Nat.nth Nat.Prime i :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  refine Set.Infinite.mono ?_ h
  intro n hn
  obtain ⟨a₁, a₂, h1, h2, h3, h4⟩ := hn
  exact ⟨a₁, a₂, h1, h2, h3, h4.trans (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hprod n))⟩
end erdos_49172_hyp_mono_r_ns

theorem erdos_49172_hyp_mono_r :
    ∀ (r r' : ℕ) (c : ℝ), r ≤ r' → erdos_49172_good r c → erdos_49172_good r' c := by
  exact erdos_49172_hyp_mono_r_ns.erdos_49172_hyp_mono_r



-- R1 fact (3): for c ≤ 0 the witness (a₁,a₂) = (n,1) works for every n ≥ 1,
-- since n+1 > n ≥ n + c·log n and n!·1! ∣ n!·P^n.
namespace erdos_49172_hyp_nonpos_ns
open Filter

private lemma erdos_49172_mem (r : ℕ) (c : ℝ) (hc : c ≤ 0) (n : ℕ) (hn : 0 < n) :
    ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
      (a₁ : ℝ) + a₂ > n + c * Real.log n ∧
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
  refine ⟨n, 1, hn, one_pos, ?_, ?_⟩
  · have hl : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have h2 : c * Real.log (n : ℝ) ≤ 0 := by nlinarith
    push_cast
    linarith
  · rw [Nat.factorial_one, mul_one]
    exact Nat.dvd_mul_right _ _

theorem erdos_49172_hyp_nonpos :
    ∀ (r : ℕ) (c : ℝ), c ≤ 0 → erdos_49172_good r c := by
  intro r c hc
  unfold erdos_49172_good
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  have hmem : M + 1 ∈ {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
      (a₁ : ℝ) + a₂ > n + c * Real.log n ∧
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n} :=
    erdos_49172_mem r c hc (M + 1) (Nat.succ_pos M)
  have := hM hmem
  omega
end erdos_49172_hyp_nonpos_ns

theorem erdos_49172_hyp_nonpos :
    ∀ (r : ℕ) (c : ℝ), c ≤ 0 → erdos_49172_good r c := by
  exact erdos_49172_hyp_nonpos_ns.erdos_49172_hyp_nonpos



theorem erdos_49172 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  classical
  choose rK hrK1 hrK using erdos_49172_hyp_core
  let S : ℕ → Finset ℕ := fun r => (Finset.range (r + 1)).filter (fun K => rK K ≤ r)
  refine ⟨fun r => (((S r).sup id : ℕ) : ℝ), ?_, ?_⟩
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max ⌈b⌉₊ (rK ⌈b⌉₊), ?_⟩
    intro a ha
    have h1 : ⌈b⌉₊ ≤ a := le_trans (le_max_left _ _) ha
    have h2 : rK ⌈b⌉₊ ≤ a := le_trans (le_max_right _ _) ha
    have hmem : ⌈b⌉₊ ∈ S a :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩
    have h3 : ⌈b⌉₊ ≤ (S a).sup id := Finset.le_sup (f := id) hmem
    show b ≤ (((S a).sup id : ℕ) : ℝ)
    calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      _ ≤ (((S a).sup id : ℕ) : ℝ) := by exact_mod_cast h3
  · intro r hr
    show erdos_49172_good r (((S r).sup id : ℕ) : ℝ)
    by_cases hs : (S r).Nonempty
    · obtain ⟨K, hK, hKeq⟩ := Finset.exists_mem_eq_sup (S r) hs id
      rw [hKeq]
      have hK' : rK K ≤ r := (Finset.mem_filter.mp hK).2
      exact erdos_49172_hyp_mono_r (rK K) r (K : ℝ) hK' (hrK K)
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      exact erdos_49172_hyp_nonpos r _ (by simp [hs])