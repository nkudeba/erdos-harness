open Filter

noncomputable def erdos56143_P (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i

noncomputable def erdos56143_BlockAbsorbed (r n k a : ℕ) : Prop :=
  0 < a ∧ a < n + k ∧
    ∀ q : ℕ, q.Prime → ¬ q ∣ erdos56143_P r →
      padicValNat q ((n + k).descFactorial k) ≤ padicValNat q ((n + k).choose a)

namespace erdos_56143_hyp_absorb_suff_ns
open Filter

private lemma erdos56143_val_bound (q n m : ℕ) (hq : q.Prime) (hm : m ≤ 2 * n) :
    padicValNat q m.factorial ≤ padicValNat q n.factorial + n := by
  haveI := Fact.mk hq
  have h1 : m.factorial ∣ (q * n).factorial :=
    Nat.factorial_dvd_factorial (le_trans hm (Nat.mul_le_mul_right n hq.two_le))
  have h2 : padicValNat q m.factorial ≤ padicValNat q (q * n).factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp
      (dvd_trans pow_padicValNat_dvd h1)
  rw [padicValNat_factorial_mul] at h2
  exact h2

theorem erdos_56143_hyp_absorb_suff :
    ∀ r n k a : ℕ, 1 ≤ r → 0 < k → k ≤ n → erdos56143_BlockAbsorbed r n k a →
      a.factorial * (n + k - a).factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
  intro r n k a hr hk hkn hB
  obtain ⟨ha0, ham, hq⟩ := hB
  have hC : ((n + k).choose a) * a.factorial * (n + k - a).factorial = (n + k).factorial :=
    Nat.choose_mul_factorial_mul_factorial ham.le
  have hD : n.factorial * (n + k).descFactorial k = (n + k).factorial := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rwa [show n + k - k = n by omega] at this
  have hP : (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (Nat.prime_nth_prime i).ne_zero
  have hCne : (n + k).choose a ≠ 0 := (Nat.choose_pos ham.le).ne'
  have hDne : (n + k).descFactorial k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hD
    exact Nat.factorial_ne_zero _ hD.symm
  have hL : a.factorial * (n + k - a).factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hR : n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero n) (pow_ne_zero _ hP)
  rw [← Nat.factorization_prime_le_iff_dvd hL hR]
  intro q hqp
  haveI := Fact.mk hqp
  rw [Nat.factorization_def _ hqp, Nat.factorization_def _ hqp]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ hP)]
  have e1 : padicValNat q ((n + k).choose a) + padicValNat q a.factorial
      + padicValNat q (n + k - a).factorial = padicValNat q (n + k).factorial := by
    rw [← hC, padicValNat.mul (mul_ne_zero hCne (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), padicValNat.mul hCne (Nat.factorial_ne_zero _)]
  have e2 : padicValNat q n.factorial + padicValNat q ((n + k).descFactorial k)
      = padicValNat q (n + k).factorial := by
    rw [← hD, padicValNat.mul (Nat.factorial_ne_zero _) hDne]
  by_cases hqP : q ∣ ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i
  · have hv : n ≤ padicValNat q ((∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n) :=
      (padicValNat_dvd_iff_le (pow_ne_zero _ hP)).mp (pow_dvd_pow_of_dvd hqP n)
    have hb := erdos56143_val_bound q n (n + k) hqp (by omega)
    omega
  · have h3 := hq q hqp hqP
    omega
end erdos_56143_hyp_absorb_suff_ns

theorem erdos_56143_hyp_absorb_suff :
    ∀ r n k a : ℕ, 1 ≤ r → 0 < k → k ≤ n → erdos56143_BlockAbsorbed r n k a →
      a.factorial * (n + k - a).factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
  exact erdos_56143_hyp_absorb_suff_ns.erdos_56143_hyp_absorb_suff



theorem erdos_56143_hyp_core :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧
      ∀ r : ℕ, 1 ≤ r →
        {n : ℕ | ∃ k a : ℕ, 0 < k ∧ k ≤ n ∧ (k : ℝ) > g r * Real.log n ∧
          erdos56143_BlockAbsorbed r n k a}.Infinite := by
  sorry

theorem erdos_56143 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  obtain ⟨g, hg, hcore⟩ := erdos_56143_hyp_core
  refine ⟨g, hg, fun r hr => ?_⟩
  refine Set.Infinite.mono ?_ (hcore r hr)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  obtain ⟨k, a, hk0, hkn, hgt, hab⟩ := hn
  have ha0 : 0 < a := hab.1
  have hlt : a < n + k := hab.2.1
  have hsum : a + (n + k - a) = n + k := by omega
  have hcast : ((a : ℝ) + ((n + k - a : ℕ) : ℝ)) = (n : ℝ) + (k : ℝ) := by
    exact_mod_cast hsum
  refine ⟨a, n + k - a, ha0, by omega, ?_, ?_⟩
  · rw [hcast]
    linarith
  · exact erdos_56143_hyp_absorb_suff r n k a hr hk0 hkn hab