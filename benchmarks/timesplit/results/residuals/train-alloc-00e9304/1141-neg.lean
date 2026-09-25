-- CHECK: Nat.prime_mul_iff Nat.coprime_one_right Nat.sub_mod_eq_zero_of_mod_eq Nat.prime_dvd_prime_iff_eq Set.finite_lt_nat Nat.Prime.eq_one_or_self_of_dvd
open Nat Set

def TSProp (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (TSProp n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [TSProp]
    | succ n' =>
      simp [TSProp, le_sqrt, pow_two]

-- Core (deferred, hard): Linnik–Vinogradov least split prime for the real character of Q(√n),
-- via Burgess and Siegel, weakened to p ≤ n^{1/3}. n is even, so such p is odd and p ∤ n.
theorem erdos_93184_hyp_lv_split :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n % 6 = 0 ∨ n % 6 = 2) → ¬ IsSquare n →
      ∃ p r : ℕ, p.Prime ∧ ¬ p ∣ n ∧ p ^ 3 ≤ n ∧ r ^ 2 % p = n % p := by
  sorry

-- Jacobsthal / Möbius count: k = r0 + p j over ≥ n^{1/6} consecutive j.
-- Coprimality to n removes one class of j mod each prime q ∣ n.
-- The survivors number ≥ L·φ(n)/n - 2^ω(n) > 0 for large n.
theorem erdos_93184_hyp_coprime_in_class :
    ∃ N : ℕ, ∀ n p r : ℕ, N ≤ n → p.Prime → ¬ p ∣ n → p ^ 3 ≤ n →
      ∃ k : ℕ, k % p = r % p ∧ Coprime n k ∧ k ^ 2 + p < n := by
  sorry

theorem erdos_93184 :
    ¬ (Infinite { n | TSProp n }) := by
  intro hinf
  obtain ⟨N2, hlv⟩ := erdos_93184_hyp_lv_split
  obtain ⟨N3, hcnt⟩ := erdos_93184_hyp_coprime_in_class
  have hfin : Set.Finite { n | TSProp n } := by
    apply (Set.finite_lt_nat (N2 + N3 + 10)).subset
    intro n hn
    change TSProp n at hn
    show n < N2 + N3 + 10
    by_contra hlt
    push_neg at hlt
    have h1 : (n - 1).Prime := by
      have h1' : (n - 1 ^ 2).Prime := hn 1 (by rw [one_pow]; omega) (Nat.coprime_one_right n)
      rw [one_pow] at h1'
      exact h1'
    have h2 : ¬ 2 ∣ n - 1 := by
      intro hd
      rcases h1.eq_one_or_self_of_dvd 2 hd with h | h <;> omega
    have h3 : ¬ 3 ∣ n - 1 := by
      intro hd
      rcases h1.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
    have h6 : n % 6 = 0 ∨ n % 6 = 2 := by omega
    by_cases hs : IsSquare n
    · obtain ⟨m, hm⟩ := hs
      have hm3 : 3 ≤ m := by
        by_contra h
        push_neg at h
        have hmm : m * m ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
        generalize m * m = M at hm hmm
        omega
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
      have hfac : n - 1 = (t + 2) * (t + 4) := by
        have e : (t + 3) * (t + 3) = (t + 2) * (t + 4) + 1 := by ring
        generalize (t + 3) * (t + 3) = A at hm e
        generalize (t + 2) * (t + 4) = B at e ⊢
        omega
      have h1b := h1
      rw [hfac] at h1b
      rcases Nat.prime_mul_iff.mp h1b with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    · obtain ⟨p, r, hp, hpn, hp3, hr⟩ := hlv n (by omega) h6 hs
      obtain ⟨k, hk, hcop, hkn⟩ := hcnt n p r (by omega) hp hpn hp3
      have hklt : k ^ 2 < n := by
        have h' := hkn
        generalize k ^ 2 = K at h' ⊢
        omega
      unfold TSProp at hn
      have hprime : (n - k ^ 2).Prime := hn k hklt hcop
      have hmod : k ^ 2 % p = n % p := by
        rw [Nat.pow_mod, hk, ← Nat.pow_mod]
        exact hr
      have hdvd : p ∣ n - k ^ 2 :=
        Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
      have heq : p = n - k ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
      have hkn' := hkn
      generalize k ^ 2 = K at heq hkn' hklt
      omega
  exact (Set.infinite_coe_iff.mp hinf) hfin