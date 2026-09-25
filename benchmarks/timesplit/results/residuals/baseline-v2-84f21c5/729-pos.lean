namespace erdos_83986_hyp_den_of_factorization_ns
private lemma den_val_zero_of_nonneg (p : ℕ) (hp : p.Prime) (q : ℚ)
    (hq : 0 ≤ padicValRat p q) : padicValNat p q.den = 0 := by
  by_contra hne
  have hpd : p ∣ q.den := (dvd_pow_self p hne).trans pow_padicValNat_dvd
  have hnum : padicValInt p q.num = 0 := by
    unfold padicValInt
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hd hpd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have hdef : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
  omega

theorem erdos_83986_hyp_den_of_factorization :
    ∀ (a b n p : ℕ), p.Prime →
      (a.factorial * b.factorial).factorization p ≤ n.factorial.factorization p →
      padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 := by
  intro a b n p hp h
  haveI := Fact.mk hp
  apply den_val_zero_of_nonneg p hp
  have hx : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hy : ((a.factorial : ℚ) * (b.factorial : ℚ)) ≠ 0 := by positivity
  have hcast : (((a.factorial * b.factorial : ℕ)) : ℚ) = (a.factorial : ℚ) * (b.factorial : ℚ) := by
    push_cast; ring
  rw [padicValRat.div hx hy, ← hcast, padicValRat.of_nat, padicValRat.of_nat]
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp] at h
  omega
end erdos_83986_hyp_den_of_factorization_ns

-- CHECK: Set.Infinite.of_image Set.infinite_of_not_bddAbove Nat.factorization Rat.den padicValNat
-- Elementary: den (n!/(a!b!)) = a!b!/gcd(n!,a!b!). If v_p(a!b!) ≤ v_p(n!), then p does not divide the
-- reduced denominator. Follows from Rat.den_div_eq_of_coprime / Rat.divInt and padicValRat of a quotient.
theorem erdos_83986_hyp_den_of_factorization :
    ∀ (a b n p : ℕ), p.Prime →
      (a.factorial * b.factorial).factorization p ≤ n.factorial.factorization p →
      padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 := by
  exact erdos_83986_hyp_den_of_factorization_ns.erdos_83986_hyp_den_of_factorization

-- CHECK: Set.Infinite.of_image Set.infinite_of_not_bddAbove erdos_83986_hyp_den_of_factorization_ns.erdos_83986_hyp_den_of_factorization

-- Hard core (the arithmetic content of the problem, with the R1/R2 constraints a ≤ b ≤ n asserted).
-- Weakened relative to cycle 1: K ≥ 3, b > 0 and n > 0 are dropped, because the glue recovers them
-- (K ↦ max K 3; b ≥ a > 0; n > N ≥ 0).
-- Derived shape: for every prime p > K, v_p(a!) + v_p(b!) ≤ v_p(n!).
-- Via Kummer/R3 this is v_p((n+1)⋯(n+k)) ≤ carries_p(a,b), where k = a+b-n.
-- Large primes p > k need only digit-size conditions on a.
-- Medium primes K < p ≤ k have room because C/(p-1) < 1/log p once p > K(C).
-- A counting/CRT choice of (n, b) is expected to meet all p at once (literature route).
-- A termwise per-prime-power strengthening is FALSE: for q = p < k/2 it would need a%p + b%p ≥ k.
-- So the Legendre sums must be compared in aggregate.
theorem erdos_83986_hyp_core :
    ∀ (C : ℝ), C > 0 →
      ∃ K : ℕ, ∀ N : ℕ, ∃ a b n : ℕ, N < n ∧ a > 0 ∧
        a ≤ b ∧ b ≤ n ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          (a.factorial * b.factorial).factorization p ≤ n.factorial.factorization p := by
  sorry

theorem erdos_83986 :
    ∀ (C : ℝ) (hC : C > 0),
      ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
  intro C hC
  obtain ⟨K, hcore⟩ := erdos_83986_hyp_core C hC
  refine ⟨max K 3, le_max_right K 3, ?_⟩
  apply Set.Infinite.of_image (fun T : ℕ × ℕ × ℕ => T.2.2)
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨a, b, n, hn, ha, hab, _hbn, hlog, hpf⟩ := hcore M
  have hb : b > 0 := by omega
  have hn0 : n > 0 := by omega
  have h2 : n ≤ M := hM ⟨(a, b, n), by
      simp only [Set.mem_setOf_eq]
      exact ⟨ha, hb, hn0, hlog, fun p hp hpK =>
        erdos_83986_hyp_den_of_factorization_ns.erdos_83986_hyp_den_of_factorization a b n p hp
          (hpf p hp (lt_of_le_of_lt (le_max_left K 3) hpK))⟩, rfl⟩
  omega