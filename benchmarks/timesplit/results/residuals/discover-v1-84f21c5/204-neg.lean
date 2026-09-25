def erdos_53704_Valid (n : ℕ) (a : ℕ → ℤ) : Prop :=
  let D := {d : ℕ | d ∣ n ∧ d > 1}
  (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
  (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
    Nat.gcd d d' = 1)

-- n = 1: D is empty, so x = 0 is uncovered.
-- n = 0: the moduli 2, 4, 6 have pairwise gcd 2. Two of a_2, a_4, a_6 agree mod 2,
-- so by generalized CRT their classes meet although the gcd is 2 ≠ 1.
namespace erdos_53704_hyp_small_ns
theorem erdos_53704_hyp_small :
    ∀ a : ℕ → ℤ, ¬ erdos_53704_Valid 0 a ∧ ¬ erdos_53704_Valid 1 a := by
  intro a
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := h.2
    have m2 : (2:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 2, by norm_num⟩
    have m4 : (4:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 4, by norm_num⟩
    have m6 : (6:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 6, by norm_num⟩
    have key : a 2 % 2 = a 4 % 2 ∨ a 2 % 2 = a 6 % 2 ∨ a 4 % 2 = a 6 % 2 := by omega
    rcases key with k | k | k
    · have := h2 2 m2 4 m4 (by norm_num) ⟨a 4, by
        unfold Int.ModEq; push_cast; omega, by unfold Int.ModEq; push_cast; omega⟩
      norm_num at this
    · have := h2 2 m2 6 m6 (by norm_num) ⟨a 6, by
        unfold Int.ModEq; push_cast; omega, by unfold Int.ModEq; push_cast; omega⟩
      norm_num at this
    · have := h2 4 m4 6 m6 (by norm_num) ⟨4 * a 6 - 3 * a 4, by
        unfold Int.ModEq; push_cast; omega, by unfold Int.ModEq; push_cast; omega⟩
      norm_num at this
  · obtain ⟨d, ⟨hd1, hd2⟩, -⟩ := h.1 0
    have := Nat.le_of_dvd one_pos hd1
    omega
end erdos_53704_hyp_small_ns

theorem erdos_53704_hyp_small :
    ∀ a : ℕ → ℤ, ¬ erdos_53704_Valid 0 a ∧ ¬ erdos_53704_Valid 1 a := by
  exact erdos_53704_hyp_small_ns.erdos_53704_hyp_small



-- Union bound: coverage depends only on x mod n. The class a_d mod d contains n/d residues
-- mod n, so n ≤ Σ_{d|n, d>1} n/d = σ(n) - n.
namespace erdos_53704_hyp_abundant_ns
theorem erdos_53704_hyp_abundant :
    ∀ (n : ℕ) (a : ℕ → ℤ), 2 ≤ n → erdos_53704_Valid n a →
      2 * n ≤ ∑ d ∈ n.divisors, d := by
  intro n a hn h
  simp only [erdos_53704_Valid, Set.mem_setOf_eq] at h
  obtain ⟨hcov, -⟩ := h
  have hn0 : n ≠ 0 := by omega
  set S := n.divisors.filter (fun d => 1 < d) with hS
  have hsub : Finset.range n ⊆ S.biUnion
      (fun d => (Finset.range n).filter (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d])) := by
    intro x hx
    obtain ⟨d, ⟨hd, hd1⟩, hxd⟩ := hcov (x : ℤ)
    rw [Finset.mem_biUnion]
    refine ⟨d, ?_, ?_⟩
    · rw [hS, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hd, hn0⟩, hd1⟩
    · rw [Finset.mem_filter]
      exact ⟨hx, hxd⟩
  have hfib : ∀ d ∈ S, ((Finset.range n).filter
      (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d])).card ≤ n / d := by
    intro d hdS
    rw [hS, Finset.mem_filter, Nat.mem_divisors] at hdS
    obtain ⟨⟨⟨k, hk⟩, -⟩, hd1⟩ := hdS
    have hnd : n / d = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k (by omega)
    rw [hnd]
    have := Finset.card_le_card_of_injOn (fun x => x / d)
      (s := (Finset.range n).filter (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d]))
      (t := Finset.range k) ?_ ?_
    · simpa using this
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
      simp only [Finset.coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      rw [hk] at hx
      nlinarith [hx.1]
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
      have h1 : (x : ℤ) ≡ y [ZMOD d] := hx.2.trans hy.2.symm
      unfold Int.ModEq at h1
      have h2 : ((x % d : ℕ) : ℤ) = ((y % d : ℕ) : ℤ) := by push_cast; exact h1
      have h3 : x % d = y % d := by exact_mod_cast h2
      have h4 : x / d = y / d := hxy
      rw [← Nat.div_add_mod x d, ← Nat.div_add_mod y d, h3, h4]
  have hcount : n ≤ ∑ d ∈ S, n / d := by
    calc n = (Finset.range n).card := (Finset.card_range n).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum hfib
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 1 < d) (fun d => n / d)
  have hone : n.divisors.filter (fun d => ¬ 1 < d) = {1} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hd1⟩
      have : d ≠ 0 := by rintro rfl; simp at hd; omega
      omega
    · rintro rfl
      exact ⟨⟨one_dvd n, hn0⟩, by omega⟩
  rw [hone, Finset.sum_singleton, Nat.div_one, Nat.sum_div_divisors n (fun d => d)] at hsplit
  rw [← hS] at hsplit
  omega
end erdos_53704_hyp_abundant_ns

theorem erdos_53704_hyp_abundant :
    ∀ (n : ℕ) (a : ℕ → ℤ), 2 ≤ n → erdos_53704_Valid n a →
      2 * n ≤ ∑ d ∈ n.divisors, d := by
  exact erdos_53704_hyp_abundant_ns.erdos_53704_hyp_abundant



-- Pigeonhole: let p = minFac n. The family {p} ∪ {pq : q ≠ p prime, q | n} ∪ ({p^2} if p^2 | n)
-- has all pairwise gcds equal to p. By generalized CRT the residues a_d mod p are pairwise
-- distinct, so the family has at most p members.
theorem erdos_53704_hyp_pigeon :
    ∀ (n : ℕ) (a : ℕ → ℤ), 2 ≤ n → erdos_53704_Valid n a →
      n.primeFactors.card ≤ n.minFac ∧
      (n.minFac ^ 2 ∣ n → n.primeFactors.card + 1 ≤ n.minFac) := by
  sorry

-- Pure number theory: casework on p = minFac n.
-- p = 2, 3, 5, 7 use explicit bounds on the product of q/(q-1); p ≥ 11 uses an integral bound.
-- Every n satisfying the pigeonhole constraints is deficient, except n = 2·3^b.
theorem erdos_53704_hyp_numerics :
    ∀ n : ℕ, 2 ≤ n → 2 * n ≤ ∑ d ∈ n.divisors, d →
      n.primeFactors.card ≤ n.minFac →
      (n.minFac ^ 2 ∣ n → n.primeFactors.card + 1 ≤ n.minFac) →
      ∃ b : ℕ, 1 ≤ b ∧ n = 2 * 3 ^ b := by
  sorry

-- For n = 2·3^b the class of 2·3^j is disjoint from the class of 2 (gcd 2).
-- The class of 3^j meets the class of 2 in n/(2·3^j) residues (CRT).
-- So at most n/2 + (n/2)(1 - 3^{-b}) < n residues are covered.
theorem erdos_53704_hyp_two_three :
    ∀ b : ℕ, 1 ≤ b → ∀ a : ℕ → ℤ, ¬ erdos_53704_Valid (2 * 3 ^ b) a := by
  sorry

theorem erdos_53704 :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  rintro ⟨n, a, h⟩
  have hv : erdos_53704_Valid n a := h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact (erdos_53704_hyp_small a).1 hv
    · exact (erdos_53704_hyp_small a).2 hv
  · have hab := erdos_53704_hyp_abundant n a hn hv
    have hpg := erdos_53704_hyp_pigeon n a hn hv
    obtain ⟨b, hb, rfl⟩ := erdos_53704_hyp_numerics n hn hab hpg.1 hpg.2
    exact erdos_53704_hyp_two_three b hb a hv