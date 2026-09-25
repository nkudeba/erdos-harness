def ADAP (n : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ x : ℤ, ∃ d ∈ {d : ℕ | d ∣ n ∧ d > 1}, x ≡ a d [ZMOD d]) ∧
  (∀ d ∈ {d : ℕ | d ∣ n ∧ d > 1}, ∀ d' ∈ {d : ℕ | d ∣ n ∧ d > 1}, d ≠ d' →
    (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) → Nat.gcd d d' = 1)

-- DERIVED: for n = 0 the moduli 2, 4, 6 all lie in D with pairwise gcd 2; disjointness
-- forces a 2, a 4, a 6 pairwise distinct mod 2, impossible by pigeonhole.
namespace erdos_99794_hyp_zero_ns
theorem erdos_99794_hyp_zero : ∀ a : ℕ → ℤ, ¬ ADAP 0 a := by
  intro a hA
  obtain ⟨-, h⟩ := hA
  have m : ∀ k : ℕ, 1 < k → k ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := fun k hk => ⟨dvd_zero _, hk⟩
  by_cases h24 : a 2 % 2 = a 4 % 2
  · have := h 2 (m 2 (by norm_num)) 4 (m 4 (by norm_num)) (by decide)
      ⟨a 4, by unfold Int.ModEq; push_cast; omega, by unfold Int.ModEq; push_cast; omega⟩
    norm_num at this
  by_cases h26 : a 2 % 2 = a 6 % 2
  · have := h 2 (m 2 (by norm_num)) 6 (m 6 (by norm_num)) (by decide)
      ⟨a 6, by unfold Int.ModEq; push_cast; omega, by unfold Int.ModEq; push_cast; omega⟩
    norm_num at this
  · have hk : a 6 - a 4 = 2 * ((a 6 - a 4) / 2) := by omega
    have hx : 4 * a 6 - 3 * a 4 = a 6 + 6 * ((a 6 - a 4) / 2) := by omega
    have := h 4 (m 4 (by norm_num)) 6 (m 6 (by norm_num)) (by decide)
      ⟨4 * a 6 - 3 * a 4, by unfold Int.ModEq; push_cast; omega,
        by unfold Int.ModEq; push_cast; rw [hx, Int.add_mul_emod_self_left]⟩
    norm_num at this
end erdos_99794_hyp_zero_ns

theorem erdos_99794_hyp_zero : ∀ a : ℕ → ℤ, ¬ ADAP 0 a := by
  exact erdos_99794_hyp_zero_ns.erdos_99794_hyp_zero



-- DERIVED: covering Z is equivalent to covering Z/n; the class mod d ∣ n has n/d residues,
-- so n ≤ ∑_{d ∣ n, d > 1} n/d = σ(n) - n.
namespace erdos_99794_hyp_sigma_ns
theorem erdos_99794_hyp_sigma : ∀ (n : ℕ) (a : ℕ → ℤ), 1 ≤ n → ADAP n a →
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  intro n a hn h
  have hn0 : n ≠ 0 := by omega
  classical
  set D := n.divisors.erase 1 with hD
  let S : ℕ → Finset ℕ := fun d => (Finset.range n).filter (fun x => (x:ℤ) ≡ a d [ZMOD d])
  have hcov : Finset.range n ⊆ D.biUnion S := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := h.1 (x:ℤ)
    simp only [Set.mem_setOf_eq] at hd
    rw [Finset.mem_biUnion]
    refine ⟨d, ?_, ?_⟩
    · rw [hD, Finset.mem_erase, Nat.mem_divisors]
      exact ⟨by omega, hd.1, hn0⟩
    · simp only [S, Finset.mem_filter]
      exact ⟨hx, hxd⟩
  have hclass : ∀ d ∈ D, (S d).card ≤ n / d := by
    intro d hd
    rw [hD, Finset.mem_erase, Nat.mem_divisors] at hd
    obtain ⟨_, ⟨k, hk⟩, _⟩ := hd
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; simp at hk; omega
      · exact h0
    have hnd : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ hdpos]
    rw [hnd]
    have := Finset.card_le_card_of_injOn (fun x => x / d) (s := S d) (t := Finset.range k)
      ?_ ?_
    · simpa using this
    · intro x hx
      simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
      simp only [Finset.coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul hdpos]
      rw [hk] at hx
      nlinarith [hx.1]
    · intro x hx y hy hxy
      simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx hy
      have h1 : (x:ℤ) ≡ (y:ℤ) [ZMOD (d:ℤ)] := hx.2.trans hy.2.symm
      have h2 : x ≡ y [MOD d] := Int.natCast_modEq_iff.1 h1
      have h3 : x / d = y / d := hxy
      unfold Nat.ModEq at h2
      have e1 := Nat.div_add_mod x d
      have e2 := Nat.div_add_mod y d
      rw [h3, h2] at e1
      omega
  have hsplit : n + ∑ d ∈ D, n / d = ∑ d ∈ n.divisors, d := by
    have h1 : (1:ℕ) ∈ n.divisors := Nat.mem_divisors.2 ⟨one_dvd n, hn0⟩
    have := Finset.add_sum_erase n.divisors (fun d => n / d) h1
    simp only [Nat.div_one] at this
    rw [hD, this]
    exact Nat.sum_div_divisors n id
  have hle : n ≤ ∑ d ∈ D, n / d := by
    calc n = (Finset.range n).card := (Finset.card_range n).symm
      _ ≤ (D.biUnion S).card := Finset.card_le_card hcov
      _ ≤ ∑ d ∈ D, (S d).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ D, n / d := Finset.sum_le_sum hclass
  omega
end erdos_99794_hyp_sigma_ns

theorem erdos_99794_hyp_sigma : ∀ (n : ℕ) (a : ℕ → ℤ), 1 ≤ n → ADAP n a →
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  exact erdos_99794_hyp_sigma_ns.erdos_99794_hyp_sigma



-- DERIVED: with p = minFac n, the set {p} ∪ {p*q : q prime, q ∣ n, q ≠ p} (∪ {p^2} if p^2 ∣ n)
-- has pairwise gcd exactly p, so (CRT meet criterion) the residues mod p are pairwise distinct.
theorem erdos_99794_hyp_kbound : ∀ (n : ℕ) (a : ℕ → ℤ), 1 ≤ n → ADAP n a →
    n.primeFactors.card ≤ n.minFac ∧
    (n.minFac ^ 2 ∣ n → n.primeFactors.card + 1 ≤ n.minFac) := by
  sorry

-- DERIVED: for odd n with least prime p and k ≤ p primes, σ(n)/n < ∏ q/(q-1) over the
-- k smallest odd numbers ≥ p (improved when p ∥ n or p^2 ∣ n), which is < 2
-- (explicit for p = 3, 5, 7, analytic tail for p ≥ 11).
theorem erdos_99794_hyp_odd : ∀ n : ℕ, Odd n →
    n.primeFactors.card ≤ n.minFac →
    (n.minFac ^ 2 ∣ n → n.primeFactors.card + 1 ≤ n.minFac) →
    ∑ d ∈ n.divisors, d < 2 * n := by
  sorry

-- DERIVED: for even n, k ≤ 2 and 4 ∣ n → k = 1. The case 2^a has σ = 2n - 1; for 2q^b,
-- σ/n < (3/2)·q/(q-1) < 2 unless q = 3; n = 2 has σ = 3 < 4.
theorem erdos_99794_hyp_even : ∀ n : ℕ, 1 ≤ n → Even n →
    2 * n ≤ ∑ d ∈ n.divisors, d →
    n.primeFactors.card ≤ n.minFac →
    (n.minFac ^ 2 ∣ n → n.primeFactors.card + 1 ≤ n.minFac) →
    ∃ b : ℕ, 1 ≤ b ∧ n = 2 * 3 ^ b := by
  sorry

-- DERIVED: for n = 2·3^b the classes mod 3^j are pairwise disjoint, each meets the class
-- mod 2 in n/(2·3^j) residues (CRT), so class 2 together with the classes mod 3^j covers at
-- most n/2 + nG/2 residues, G = ∑_{j=1}^b 3^{-j} < 1/2; the classes mod 2·3^j add at most
-- nG/2 more, so fewer than n residues are covered.
theorem erdos_99794_hyp_two_three_pow : ∀ b : ℕ, 1 ≤ b → ∀ a : ℕ → ℤ,
    ¬ ADAP (2 * 3 ^ b) a := by
  sorry

theorem erdos_99794 :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  rintro ⟨n, a, h⟩
  have hA : ADAP n a := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact erdos_99794_hyp_zero a hA
  have h1 := erdos_99794_hyp_sigma n a hn hA
  obtain ⟨hk1, hk2⟩ := erdos_99794_hyp_kbound n a hn hA
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨b, hb, rfl⟩ := erdos_99794_hyp_even n hn he h1 hk1 hk2
    exact erdos_99794_hyp_two_three_pow b hb a hA
  · have h2 := erdos_99794_hyp_odd n ho hk1 hk2
    omega