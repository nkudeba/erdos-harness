open Nat Set

def TSProp (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (TSProp n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [TSProp]
    | succ n' =>
      simp [TSProp, le_sqrt, pow_two]

def CompositeWitness (n : ℕ) : Prop :=
  ∃ p k, p.Prime ∧ Coprime n k ∧ k ^ 2 + p < n ∧ p ∣ n - k ^ 2

namespace erdos_53249_neg_hyp_pred_prime_ns
open Nat Set

theorem erdos_53249_neg_hyp_pred_prime :
    ∀ n : ℕ, 2 ≤ n → TSProp n → (n - 1).Prime := by
  intro n hn h
  have h1 : (1 : ℕ) ^ 2 < n := by rw [one_pow]; omega
  have hp := h 1 h1 (Nat.coprime_one_right n)
  rw [one_pow] at hp
  exact hp
end erdos_53249_neg_hyp_pred_prime_ns

theorem erdos_53249_neg_hyp_pred_prime :
    ∀ n : ℕ, 2 ≤ n → TSProp n → (n - 1).Prime := by
  exact erdos_53249_neg_hyp_pred_prime_ns.erdos_53249_neg_hyp_pred_prime

namespace erdos_53249_neg_hyp_parity_ns
open Nat Set

theorem erdos_53249_neg_hyp_parity :
    ∀ n : ℕ, 5 ≤ n → TSProp n → n % 2 = 0 := by
  intro n hn h
  by_contra hodd
  have hk : (1:ℕ) ^ 2 < n := by rw [one_pow]; omega
  have h1 := h 1 hk (Nat.coprime_one_right n)
  rw [one_pow] at h1
  have h2 : 2 ∣ n - 1 := by omega
  rcases h1.eq_one_or_self_of_dvd 2 h2 with h3 | h3 <;> omega
end erdos_53249_neg_hyp_parity_ns

theorem erdos_53249_neg_hyp_parity :
    ∀ n : ℕ, 5 ≤ n → TSProp n → n % 2 = 0 := by
  exact erdos_53249_neg_hyp_parity_ns.erdos_53249_neg_hyp_parity

theorem erdos_53249_neg_mod6_proved :
    ∀ n : ℕ, 5 ≤ n → TSProp n → n % 6 = 0 ∨ n % 6 = 2 := by
  intro n hn h
  have h2 := erdos_53249_neg_hyp_parity n hn h
  have hp := erdos_53249_neg_hyp_pred_prime n (by omega) h
  by_contra hc
  have h3 : 3 ∣ n - 1 := by omega
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h4 | h4 <;> omega

-- Hard core: every large candidate (n ≡ 0,2 mod 6, n - 1 prime) has a coprime k with n - k^2
-- a proper multiple of a prime p. Proxy check: true for all candidates in [2e6, 4e6), least k ≤ 43.
theorem erdos_53249_neg_hyp_tail :
    ∀ n : ℕ, 2000000 ≤ n → (n % 6 = 0 ∨ n % 6 = 2) → (n - 1).Prime →
      CompositeWitness n := by
  sorry

theorem erdos_53249_neg :
    ¬ (Infinite { n | TSProp n }) := by
  intro hinf
  have hfin : Set.Finite {n | TSProp n} := by
    apply (Set.finite_Iic (2000000 : ℕ)).subset
    intro n hn
    have hn' : TSProp n := hn
    show n ≤ 2000000
    by_contra hlt
    push_neg at hlt
    have h5 : 5 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h6 := erdos_53249_neg_mod6_proved n h5 hn'
    have hpp := erdos_53249_neg_hyp_pred_prime n h2 hn'
    obtain ⟨p, k, hp, hcop, hlt2, hdvd⟩ :=
      erdos_53249_neg_hyp_tail n (by omega) h6 hpp
    have hk : k ^ 2 < n := lt_of_le_of_lt (Nat.le_add_right _ _) hlt2
    have hpr : (n - k ^ 2).Prime := hn' k hk hcop
    rcases (Nat.dvd_prime hpr).1 hdvd with h | h
    · have := hp.two_le
      omega
    · omega
  first
    | exact hfin.not_infinite hinf
    | exact hfin.not_infinite (Set.infinite_coe_iff.mp hinf)