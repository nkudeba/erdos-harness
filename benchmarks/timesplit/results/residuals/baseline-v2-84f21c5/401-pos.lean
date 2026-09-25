-- CHECK: Nat.findGreatest_eq_iff Nat.le_findGreatest tendsto_natCast_atTop_atTop Filter.tendsto_atTop_atTop Finset.single_le_sum Set.Infinite.mono
open Filter

/-- `n` is good for level `r` and constant `C`: admissible pair normalised by R3 (a₂ ≤ a₁)
and by the R2/Bertrand bound (a₁ < 2n), with excess > C·log n. -/
def ErdosGood (r : ℕ) (C : ℝ) (n : ℕ) : Prop :=
  ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧ a₂ ≤ a₁ ∧ a₁ < 2 * n ∧
    (a₁ : ℝ) + a₂ > n + C * Real.log n ∧
    a₁.factorial * a₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n

-- R1(1): the product over range r divides the product over range r', so the RHS for r
-- divides the RHS for r'; all other conditions are independent of r.
namespace erdos_86376_hyp_mono_ns
open Filter

/-- `n` is good for level `r` and constant `C`: admissible pair normalised by R3 (a₂ ≤ a₁)
and by the R2/Bertrand bound (a₁ < 2n), with excess > C·log n. -/

theorem erdos_86376_hyp_mono :
    ∀ (r r' : ℕ) (C : ℝ) (n : ℕ), r ≤ r' → ErdosGood r C n → ErdosGood r' C n := by
  intro r r' C n hr h
  unfold ErdosGood at h ⊢
  obtain ⟨a₁, a₂, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨a₁, a₂, h1, h2, h3, h4, h5, h6.trans ?_⟩
  apply mul_dvd_mul_left
  apply pow_dvd_pow_of_dvd
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega
end erdos_86376_hyp_mono_ns

theorem erdos_86376_hyp_mono :
    ∀ (r r' : ℕ) (C : ℝ) (n : ℕ), r ≤ r' → ErdosGood r C n → ErdosGood r' C n := by
  exact erdos_86376_hyp_mono_ns.erdos_86376_hyp_mono



-- R1(2): for every n ≥ 1 take a₁ = n, a₂ = 1: n!·1! ∣ n!·P^n, 1 ≤ n < 2n, n+1 > n + 0·log n.
namespace erdos_86376_hyp_zero_ns
-- CHECK: Set.infinite_of_forall_exists_gt
open Filter

/-- `n` is good for level `r` and constant `C`: admissible pair normalised by R3 (a₂ ≤ a₁)
and by the R2/Bertrand bound (a₁ < 2n), with excess > C·log n. -/

theorem erdos_86376_hyp_zero :
    ∀ r : ℕ, {n : ℕ | ErdosGood r 0 n}.Infinite := by
  intro r
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨a + 1, ?_, by omega⟩
  show ErdosGood r 0 (a + 1)
  refine ⟨a + 1, 1, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · simp only [zero_mul, add_zero]
    push_cast
    linarith
  · rw [Nat.factorial_one, mul_one]
    exact dvd_mul_right _ _
end erdos_86376_hyp_zero_ns

theorem erdos_86376_hyp_zero :
    ∀ r : ℕ, {n : ℕ | ErdosGood r 0 n}.Infinite := by
  exact erdos_86376_hyp_zero_ns.erdos_86376_hyp_zero



-- Hard core (R1 equivalent form, with the R2/R3 normalisations built in): for every natural
-- constant k some level r ≥ 1 has infinitely many good n. This is the carry/CRT construction.
theorem erdos_86376_hyp_core :
    ∀ k : ℕ, ∃ r : ℕ, 1 ≤ r ∧ {n : ℕ | ErdosGood r (k : ℝ) n}.Infinite := by
  sorry

theorem erdos_86376 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  classical
  choose R hR1 hRinf using erdos_86376_hyp_core
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ r, g r = Nat.findGreatest (fun k => ∀ j ≤ k, R j ≤ r) r :=
    ⟨fun r => Nat.findGreatest (fun k => ∀ j ≤ k, R j ≤ r) r, fun r => rfl⟩
  have hgt : Tendsto g atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro K
    refine ⟨K + ∑ j ∈ Finset.range (K + 1), R j, ?_⟩
    intro r hr
    rw [hg r]
    apply Nat.le_findGreatest
    · omega
    · intro j hj
      have hs : R j ≤ ∑ i ∈ Finset.range (K + 1), R i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (R i)) (Finset.mem_range.2 (by omega))
      omega
  refine ⟨fun r => ((g r : ℕ) : ℝ), tendsto_natCast_atTop_atTop.comp hgt, ?_⟩
  intro r hr
  by_cases hP : ∀ j ≤ g r, R j ≤ r
  · refine Set.Infinite.mono ?_ (hRinf (g r))
    intro n hn
    obtain ⟨a₁, a₂, h1, h2, -, -, h5, h6⟩ :=
      erdos_86376_hyp_mono (R (g r)) r _ n (hP _ le_rfl) hn
    exact ⟨a₁, a₂, h1, h2, h5, h6⟩
  · have hg0 : g r = 0 := by
      by_contra hne
      apply hP
      exact (Nat.findGreatest_eq_iff.1 (hg r).symm).2.1 hne
    refine Set.Infinite.mono ?_ (erdos_86376_hyp_zero r)
    intro n hn
    obtain ⟨a₁, a₂, h1, h2, -, -, h5, h6⟩ := hn
    refine ⟨a₁, a₂, h1, h2, ?_, h6⟩
    show (a₁ : ℝ) + a₂ > n + ((g r : ℕ) : ℝ) * Real.log n
    rw [hg0]
    simpa using h5