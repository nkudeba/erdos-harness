-- CHECK: Set.Infinite.exists_gt Prime.dvd_finset_prod_iff Nat.Prime.prime Nat.mul_mod_right Nat.add_mod Nat.mod_eq_of_lt
-- Derived from R2: a counterexample-free world (target true) is equivalent to: for every eps>0,
-- all large n have a window prime p in (floor(log n), (2+eps) log n] whose residue n mod p
-- misses the admissible window [p - floor(log n), p - 1].  Believed FALSE (random-model heuristic
-- gives e^{k - O(k/log k)} good n near e^k for every fixed constant).
theorem erdos_32534_neg_hyp_window_miss :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∃ p : ℕ, p.Prime ∧ ⌊Real.log n⌋₊ < p ∧ (p : ℝ) ≤ (2 + ε) * Real.log n ∧
        n % p < p - ⌊Real.log n⌋₊ := by
  sorry

theorem erdos_32534_neg :
    ¬ (∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite) := by
  rintro ⟨ε, hε, hinf⟩
  obtain ⟨N, hN⟩ := erdos_32534_neg_hyp_window_miss ε hε
  obtain ⟨n, hn, hNn⟩ := hinf.exists_gt N
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨p, hp, hkp, hple, hmod⟩ := hN n hNn
  have hdvd := hn p hple hp
  obtain ⟨i, hi, hdiv⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hdvd
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨c, hc⟩ := hdiv
  have h0 : (n + i) % p = 0 := by
    rw [hc]
    exact Nat.mul_mod_right p c
  have hip : i < p := by omega
  have hsum : n % p + i < p := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hsum] at h0
  omega