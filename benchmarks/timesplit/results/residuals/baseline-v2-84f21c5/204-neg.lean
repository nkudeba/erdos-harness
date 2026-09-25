-- CHECK: Nat.Coprime.sum_divisors_mul_sum_divisors_eq Nat.sum_divisors_prime_pow Int.modEq_and_modEq_iff_modEq_mul
-- LOOGLE: Int.ModEq, Int.gcd, ∃ x, Int.ModEq _ x _ ∧ Int.ModEq _ x _

def Erdos67538IsDAP (n : ℕ) (a : ℕ → ℤ) : Prop :=
  let D := {d : ℕ | d ∣ n ∧ d > 1}
  (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
  (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)

def PerPrimeBound (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n →
    n.primeFactors.card + (if p ^ 2 ∣ n then 1 else 0) ≤ p

def CRTCriterion : Prop :=
  ∀ (d d' : ℕ) (u v : ℤ), 0 < d → 0 < d' →
    u ≡ v [ZMOD ((Nat.gcd d d' : ℕ) : ℤ)] →
    ∃ x : ℤ, x ≡ u [ZMOD (d : ℤ)] ∧ x ≡ v [ZMOD (d' : ℤ)]

def AbundancyProdBound : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∑ d ∈ n.divisors, d) * (∏ q ∈ n.primeFactors, (q - 1)) <
      n * ∏ q ∈ n.primeFactors, q

def OddProdBound : Prop :=
  ∀ (p : ℕ) (S : Finset ℕ), 5 ≤ p → (∀ q ∈ S, q.Prime ∧ p ≤ q) → S.card ≤ p →
    ∏ q ∈ S, q < 2 * ∏ q ∈ S, (q - 1)

namespace erdos_67538_neg_hyp_zero_ns
theorem erdos_67538_neg_hyp_zero :
    ∀ a : ℕ → ℤ, ¬ Erdos67538IsDAP 0 a := by
  intro a h
  obtain ⟨_, h2⟩ := h
  have m2 : (2:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 2, by norm_num⟩
  have m4 : (4:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 4, by norm_num⟩
  have m6 : (6:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 6, by norm_num⟩
  have h24 : a 4 % 2 ≠ a 2 % 2 := by
    intro heq
    have hx1 : a 4 ≡ a 2 [ZMOD ((2:ℕ):ℤ)] := by
      unfold Int.ModEq; push_cast; omega
    have hx2 : a 4 ≡ a 4 [ZMOD ((4:ℕ):ℤ)] := Int.ModEq.refl _
    have := h2 2 m2 4 m4 (by norm_num) ⟨a 4, hx1, hx2⟩
    norm_num at this
  have h26 : a 6 % 2 ≠ a 2 % 2 := by
    intro heq
    have hx1 : a 6 ≡ a 2 [ZMOD ((2:ℕ):ℤ)] := by
      unfold Int.ModEq; push_cast; omega
    have hx2 : a 6 ≡ a 6 [ZMOD ((6:ℕ):ℤ)] := Int.ModEq.refl _
    have := h2 2 m2 6 m6 (by norm_num) ⟨a 6, hx1, hx2⟩
    norm_num at this
  have hp : a 4 % 2 = a 6 % 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k, a 6 - a 4 = 2 * k := ⟨(a 6 - a 4) / 2, by omega⟩
  have hx4 : 4 * a 6 - 3 * a 4 ≡ a 4 [ZMOD ((4:ℕ):ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨a 4 - a 6, by push_cast; ring⟩
  have hx6 : 4 * a 6 - 3 * a 4 ≡ a 6 [ZMOD ((6:ℕ):ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨-k, by push_cast; linarith⟩
  have := h2 4 m4 6 m6 (by norm_num) ⟨4 * a 6 - 3 * a 4, hx4, hx6⟩
  norm_num at this
end erdos_67538_neg_hyp_zero_ns

-- n = 0: 2, 4 and 6 all lie in D with pairwise gcd 2. Classes can meet only if the
-- residues agree mod 2, so disjointness forces a_2, a_4, a_6 pairwise distinct mod 2
-- (pigeonhole). A common solution is x = a_4 + 4*t for a suitable t.
theorem erdos_67538_neg_hyp_zero :
    ∀ a : ℕ → ℤ, ¬ Erdos67538IsDAP 0 a := by
  exact erdos_67538_neg_hyp_zero_ns.erdos_67538_neg_hyp_zero

namespace erdos_67538_neg_hyp_sigma_ns
theorem erdos_67538_neg_hyp_sigma :
    ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos67538IsDAP n a →
      2 * n ≤ ∑ d ∈ n.divisors, d := by
  intro n a hn h
  unfold Erdos67538IsDAP at h
  dsimp only at h
  obtain ⟨hcov, -⟩ := h
  have h1mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  have hsub : Finset.range n ⊆ (n.divisors.erase 1).biUnion
      (fun d => (Finset.range n).filter (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d])) := by
    intro x hx
    obtain ⟨d, ⟨hdn, hd1⟩, hxd⟩ := hcov (x : ℤ)
    rw [Finset.mem_biUnion]
    refine ⟨d, ?_, ?_⟩
    · rw [Finset.mem_erase, Nat.mem_divisors]
      exact ⟨by omega, hdn, hn.ne'⟩
    · rw [Finset.mem_filter]
      exact ⟨hx, hxd⟩
  have hbound : ∀ d ∈ n.divisors.erase 1,
      ((Finset.range n).filter (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d])).card ≤ n / d := by
    intro d hd
    rw [Finset.mem_erase, Nat.mem_divisors] at hd
    obtain ⟨hd1, hdn, -⟩ := hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    calc ((Finset.range n).filter (fun x : ℕ => (x : ℤ) ≡ a d [ZMOD d])).card
        ≤ (Finset.range (n / d)).card := by
          apply Finset.card_le_card_of_injOn (· / d)
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
            rw [Finset.mem_coe, Finset.mem_range]
            exact Nat.div_lt_div_of_lt_of_dvd hdn hx.1
          · intro x hx y hy hxy
            rw [Finset.mem_coe, Finset.mem_filter] at hx hy
            have hm : (x : ℤ) ≡ (y : ℤ) [ZMOD d] := hx.2.trans hy.2.symm
            have hm' : x % d = y % d := by
              unfold Int.ModEq at hm
              exact_mod_cast hm
            simp only at hxy
            rw [← Nat.div_add_mod x d, ← Nat.div_add_mod y d, hxy, hm']
      _ = n / d := Finset.card_range _
  have key : n ≤ ∑ d ∈ n.divisors.erase 1, n / d := by
    calc n = (Finset.range n).card := (Finset.card_range n).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsum : ∑ d ∈ n.divisors, n / d = ∑ d ∈ n.divisors, d :=
    Nat.sum_div_divisors n (fun d => d)
  rw [← Finset.add_sum_erase _ _ h1mem, Nat.div_one] at hsum
  omega
end erdos_67538_neg_hyp_sigma_ns

-- Union bound in ZMod n: class a_d mod d has n/d elements; covering forces
-- ∑_{d|n,d>1} n/d ≥ n, i.e. σ(n) ≥ 2n.
theorem erdos_67538_neg_hyp_sigma :
    ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos67538IsDAP n a →
      2 * n ≤ ∑ d ∈ n.divisors, d := by
  exact erdos_67538_neg_hyp_sigma_ns.erdos_67538_neg_hyp_sigma

-- Generalised CRT (R1, converse direction): if g = gcd(d,d') divides u - v, then
-- Bezout u - v = s*d + t*d' gives x = u - s*d solving both congruences.
namespace erdos_67538_neg_hyp_crt_ns
theorem erdos_67538_neg_hyp_crt : CRTCriterion := by
  intro d d' u v _ _ h
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hb := Nat.gcd_eq_gcd_ab d d'
  refine ⟨u + (d : ℤ) * Nat.gcdA d d' * k, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨-(Nat.gcdA d d' * k), by ring⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨Nat.gcdB d d' * k, by linear_combination hk + k * hb⟩
end erdos_67538_neg_hyp_crt_ns

theorem erdos_67538_neg_hyp_crt : CRTCriterion := by
  exact erdos_67538_neg_hyp_crt_ns.erdos_67538_neg_hyp_crt



-- sigma(p^k)*(p-1) = p^(k+1) - 1 < p^k * p for each prime power; sigma is multiplicative,
-- so the product of these strict inequalities (at least one factor since n ≥ 2) gives this.
theorem erdos_67538_neg_hyp_abund : AbundancyProdBound := by
  sorry

-- The i-th smallest element of S (0-indexed) is ≥ p + 2i, being an odd prime ≥ p.
-- Put P = prod m/(m-1) over odd m, p ≤ m ≤ 3p-2. Since m/(m-1) < (m-1)/(m-2), the square
-- P^2 is < the telescoping product (3p-2)/(p-2), which is < 4 for p ≥ 7.
-- For p = 5, 6 the bound is checked directly: 5/4*7/6*11/10*13/12*17/16 < 2.
theorem erdos_67538_neg_hyp_oddprod : OddProdBound := by
  sorry

-- For prime p | n, the moduli p, p^2 (if p^2 | n) and p*q (q another prime factor of n)
-- have pairwise gcd exactly p, so they are pairwise disjoint. By CRTCriterion their residues
-- are pairwise distinct mod p, and pigeonhole gives omega(n) + [p^2 | n] ≤ p.
theorem erdos_67538_neg_hyp_pigeon :
    CRTCriterion → ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos67538IsDAP n a →
      PerPrimeBound n := by
  sorry

-- At p = 2: omega(n) ≤ 2 and 4 ∤ n, so n = 2*m with m odd and omega(m) ≤ 1.
-- m = 1 gives sigma = 3 < 4. Otherwise m = q^k, sigma(n) = 3*sigma(m) and
-- sigma(m)*(q-1) < m*q, so 4m(q-1) < 3mq, i.e. q < 4, hence q = 3.
theorem erdos_67538_neg_hyp_even :
    AbundancyProdBound → ∀ n : ℕ, 0 < n → Even n → 2 * n ≤ ∑ d ∈ n.divisors, d →
      PerPrimeBound n → ∃ k : ℕ, 1 ≤ k ∧ n = 2 * 3 ^ k := by
  sorry

-- Least prime 3. If 9 | n then omega ≤ 2 and sigma/n < (3/2)(5/4) = 15/8.
-- Otherwise n = 3m with 3 ∤ m, omega(m) ≤ 2 and all primes of m ≥ 5;
-- sigma(n) = 4 sigma(m) and sigma(m)/m < (5/4)(7/6) (or m = 1), so sigma/n < 35/18 < 2.
theorem erdos_67538_neg_hyp_odd_three :
    AbundancyProdBound → ∀ n : ℕ, 0 < n → Odd n → 3 ∣ n →
      2 * n ≤ ∑ d ∈ n.divisors, d → PerPrimeBound n → False := by
  sorry

-- Odd n with 3 ∤ n: n = 1 is deficient. Otherwise p = minFac n ≥ 5 and omega(n) ≤ p
-- by PerPrimeBound. AbundancyProdBound and OddProdBound (with S = primeFactors n)
-- then give sigma(n) < 2n.
theorem erdos_67538_neg_hyp_odd_ge5 :
    AbundancyProdBound → OddProdBound → ∀ n : ℕ, 0 < n → Odd n → ¬ 3 ∣ n →
      2 * n ≤ ∑ d ∈ n.divisors, d → PerPrimeBound n → False := by
  sorry

-- n = 2*3^k: a_2 misses one parity class of 3^k residues mod n. Inside it, only moduli
-- 3^j and 2*3^j contribute, and these are pairwise disjoint (all divisible by 3).
-- They cover at most sum_j 2*3^(k-j) = 3^k - 1 residues of the class, so one is uncovered.
theorem erdos_67538_neg_hyp_two_three :
    ∀ k : ℕ, 1 ≤ k → ∀ a : ℕ → ℤ, ¬ Erdos67538IsDAP (2 * 3 ^ k) a := by
  sorry

theorem erdos_67538_neg :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  rintro ⟨n, a, h⟩
  have h' : Erdos67538IsDAP n a := h
  have hC := erdos_67538_neg_hyp_crt
  have hA := erdos_67538_neg_hyp_abund
  have hB := erdos_67538_neg_hyp_oddprod
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact erdos_67538_neg_hyp_zero_ns.erdos_67538_neg_hyp_zero a h'
  · have hs : 2 * n ≤ ∑ d ∈ n.divisors, d :=
      erdos_67538_neg_hyp_sigma_ns.erdos_67538_neg_hyp_sigma n a hn h'
    have hp : PerPrimeBound n := erdos_67538_neg_hyp_pigeon hC n a hn h'
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk, rfl⟩ := erdos_67538_neg_hyp_even hA n hn he hs hp
      exact erdos_67538_neg_hyp_two_three k hk a h'
    · by_cases h3 : 3 ∣ n
      · exact erdos_67538_neg_hyp_odd_three hA n hn ho h3 hs hp
      · exact erdos_67538_neg_hyp_odd_ge5 hA hB n hn ho h3 hs hp