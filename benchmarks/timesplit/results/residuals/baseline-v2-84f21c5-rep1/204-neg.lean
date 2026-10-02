def Erdos74498Valid (n : ℕ) (a : ℕ → ℤ) : Prop :=
  let D := {d : ℕ | d ∣ n ∧ d > 1}
  (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
  (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
    Nat.gcd d d' = 1)

def Erdos74498R1Cond (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → n.primeFactors.card + (if p ^ 2 ∣ n then 1 else 0) ≤ p

-- n = 0: the divisors 2, 4, 6 of 0 have pairwise gcd 2 (not 1), so by CRT their classes
-- must be pairwise incongruent mod 2 -- three distinct parities, impossible.
namespace erdos_74498_neg_hyp_zero_ns
theorem erdos_74498_neg_hyp_zero : ∀ a : ℕ → ℤ, ¬ Erdos74498Valid 0 a := by
  intro a h
  obtain ⟨-, hdisj⟩ := h
  have m : ∀ k : ℕ, 1 < k → k ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := fun k hk => ⟨dvd_zero k, hk⟩
  have h24 : ¬ (a 4 % 2 = a 2 % 2) := fun hc =>
    absurd (hdisj 2 (m 2 (by norm_num)) 4 (m 4 (by norm_num)) (by norm_num)
      ⟨a 4, by unfold Int.ModEq; push_cast; omega, Int.ModEq.refl _⟩) (by norm_num)
  have h26 : ¬ (a 6 % 2 = a 2 % 2) := fun hc =>
    absurd (hdisj 2 (m 2 (by norm_num)) 6 (m 6 (by norm_num)) (by norm_num)
      ⟨a 6, by unfold Int.ModEq; push_cast; omega, Int.ModEq.refl _⟩) (by norm_num)
  have h46 : ¬ (a 4 % 2 = a 6 % 2) := fun hc =>
    absurd (hdisj 4 (m 4 (by norm_num)) 6 (m 6 (by norm_num)) (by norm_num)
      ⟨4 * a 6 - 3 * a 4, by unfold Int.ModEq; push_cast; omega,
        by unfold Int.ModEq; push_cast; omega⟩) (by norm_num)
  omega
end erdos_74498_neg_hyp_zero_ns

theorem erdos_74498_neg_hyp_zero : ∀ a : ℕ → ℤ, ¬ Erdos74498Valid 0 a := by
  exact erdos_74498_neg_hyp_zero_ns.erdos_74498_neg_hyp_zero



-- R1: for prime p | n, S_p = {p} ∪ {p^2 if p^2 | n} ∪ {p*q : q | n prime, q ≠ p} are divisors
-- of n with pairwise gcd exactly p; by CRT the a_d mod p (d ∈ S_p) are pairwise distinct,
-- so |S_p| = omega(n) + [p^2 | n] ≤ p (pigeonhole).
namespace erdos_74498_neg_hyp_r1_ns
private lemma e74498_key (n p : ℕ) (a : ℕ → ℤ) (hp : p.Prime) (hv : Erdos74498Valid n a)
    (e e' : ℕ) (he : p * e ∣ n) (he' : p * e' ∣ n) (h1 : 1 ≤ e) (h1' : 1 ≤ e')
    (hne : e ≠ e') (hcop : Nat.Coprime e e')
    (hcong : ((a (p * e) : ℤ) : ZMod p) = ((a (p * e') : ℤ) : ZMod p)) : False := by
  obtain ⟨-, hdis⟩ := id hv
  have hp2 := hp.two_le
  have hgt : p * e > 1 := by nlinarith
  have hgt' : p * e' > 1 := by nlinarith
  have hne2 : p * e ≠ p * e' := fun h => hne (Nat.eq_of_mul_eq_mul_left hp.pos h)
  have hdvd : (p : ℤ) ∣ a (p * e') - a (p * e) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcong
  obtain ⟨t, ht⟩ := hdvd
  have hb := Nat.gcd_eq_gcd_ab e e'
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  have hx : ∃ x : ℤ, x ≡ a (p * e) [ZMOD ((p * e : ℕ) : ℤ)] ∧
      x ≡ a (p * e') [ZMOD ((p * e' : ℕ) : ℤ)] := by
    refine ⟨a (p * e) + (p : ℤ) * (e : ℤ) * (Nat.gcdA e e' * t), ?_, ?_⟩
    · rw [Int.modEq_iff_dvd]
      exact ⟨-(Nat.gcdA e e' * t), by push_cast; ring⟩
    · rw [Int.modEq_iff_dvd]
      exact ⟨t * Nat.gcdB e e', by push_cast; linear_combination ht + ((p : ℤ) * t) * hb⟩
  have hg := hdis (p * e) (by show p * e ∣ n ∧ p * e > 1; exact ⟨he, hgt⟩)
    (p * e') (by show p * e' ∣ n ∧ p * e' > 1; exact ⟨he', hgt'⟩) hne2 hx
  have hpd : p ∣ Nat.gcd (p * e) (p * e') :=
    Nat.dvd_gcd (dvd_mul_right p e) (dvd_mul_right p e')
  rw [hg] at hpd
  have := Nat.le_of_dvd one_pos hpd
  omega

private lemma e74498_cardA (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    (insert 1 (n.primeFactors.erase p)).card = n.primeFactors.card := by
  have h1 : (1 : ℕ) ∉ n.primeFactors.erase p := by
    intro h
    rw [Finset.mem_erase, Nat.mem_primeFactors] at h
    exact Nat.not_prime_one h.2.1
  have hpm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
  have hpos := Finset.card_pos.mpr ⟨p, hpm⟩
  rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_erase_of_mem hpm]
  omega

private lemma e74498_cardE (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    (if p ^ 2 ∣ n then insert p (insert 1 (n.primeFactors.erase p))
      else insert 1 (n.primeFactors.erase p)).card
      = n.primeFactors.card + (if p ^ 2 ∣ n then 1 else 0) := by
  have hA := e74498_cardA n p hp hpn hn
  have hpA : p ∉ insert 1 (n.primeFactors.erase p) := by
    intro h
    rw [Finset.mem_insert, Finset.mem_erase] at h
    rcases h with h | h
    · exact hp.one_lt.ne' h
    · exact h.1 rfl
  split_ifs with h
  · rw [Finset.card_insert_eq_ite, if_neg hpA, hA]
  · rw [hA, add_zero]

private lemma e74498_memA (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (e : ℕ)
    (he : e ∈ insert 1 (n.primeFactors.erase p)) : (e = 1 ∨ e.Prime) ∧ p * e ∣ n := by
  rw [Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors] at he
  rcases he with h | ⟨hne, hq, hqn, _⟩
  · subst h
    exact ⟨Or.inl rfl, by rw [mul_one]; exact hpn⟩
  · exact ⟨Or.inr hq, Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hp hq).mpr (Ne.symm hne)) hpn hqn⟩

private lemma e74498_memE (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (e : ℕ)
    (he : e ∈ (if p ^ 2 ∣ n then insert p (insert 1 (n.primeFactors.erase p))
      else insert 1 (n.primeFactors.erase p))) : (e = 1 ∨ e.Prime) ∧ p * e ∣ n := by
  split_ifs at he with h2
  · rw [Finset.mem_insert] at he
    rcases he with h | he
    · subst h
      exact ⟨Or.inr hp, by rw [← sq]; exact h2⟩
    · exact e74498_memA n p hp hpn e he
  · exact e74498_memA n p hp hpn e he

private lemma e74498_one_le {e : ℕ} (h : e = 1 ∨ e.Prime) : 1 ≤ e := by
  rcases h with h | h
  · omega
  · exact h.one_lt.le

private lemma e74498_cop {e e' : ℕ} (h : e = 1 ∨ e.Prime) (h' : e' = 1 ∨ e'.Prime)
    (hne : e ≠ e') : Nat.Coprime e e' := by
  rcases h with h | he
  · subst h; exact Nat.coprime_one_left _
  rcases h' with h' | he'
  · subst h'; exact Nat.coprime_one_right _
  exact (Nat.coprime_primes he he').mpr hne

theorem erdos_74498_neg_hyp_r1 : ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos74498Valid n a →
    Erdos74498R1Cond n := by
  intro n a hn hv
  unfold Erdos74498R1Cond
  intro p hp hpn
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← e74498_cardE n p hp hpn hn]
  calc _ ≤ (Finset.univ : Finset (ZMod p)).card := by
        apply Finset.card_le_card_of_injOn (fun e => ((a (p * e) : ℤ) : ZMod p))
        · intro x _
          exact Finset.mem_univ _
        · intro e he e' he' heq
          by_contra hne
          have hm := e74498_memE n p hp hpn e (Finset.mem_coe.mp he)
          have hm' := e74498_memE n p hp hpn e' (Finset.mem_coe.mp he')
          exact e74498_key n p a hp hv e e' hm.2 hm'.2 (e74498_one_le hm.1)
            (e74498_one_le hm'.1) hne (e74498_cop hm.1 hm'.1 hne) heq
    _ = p := by rw [Finset.card_univ, ZMod.card]
end erdos_74498_neg_hyp_r1_ns

theorem erdos_74498_neg_hyp_r1 : ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos74498Valid n a →
    Erdos74498R1Cond n := by
  exact erdos_74498_neg_hyp_r1_ns.erdos_74498_neg_hyp_r1



-- R2: the classes cover Z/nZ; class a_d mod d hits n/d residues, so
-- n ≤ Σ_{d|n,d>1} n/d = σ(n) - n.
theorem erdos_74498_neg_hyp_r2 : ∀ (n : ℕ) (a : ℕ → ℤ), 0 < n → Erdos74498Valid n a →
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  sorry

-- R3 (pure arithmetic): R1Cond together with σ(n) ≥ 2n forces n = 2*3^j, j ≥ 1.
-- Even n: p = 2 gives n = 2^k (deficient) or 2*q^j with ratio < (3/2) q/(q-1), < 2 unless q = 3.
-- Odd n: the product of q/(q-1) over at most p primes ≥ p stays < 2. n = 1 fails σ(1) = 1 < 2.
theorem erdos_74498_neg_hyp_arith : ∀ n : ℕ, 0 < n → Erdos74498R1Cond n →
    2 * n ≤ ∑ d ∈ n.divisors, d → ∃ j : ℕ, 1 ≤ j ∧ n = 2 * 3 ^ j := by
  sorry

-- R4: for n = 2*3^j, each modulus 2*3^i shares the factor 2 with modulus 2, so it lies in the
-- parity opposite to a_2; each 3^i puts at most half its density there. The opposite parity
-- gets total density (1/2)(1 - 3^{-j}) < 1/2, so it is not covered.
theorem erdos_74498_neg_hyp_r4 : ∀ j : ℕ, 1 ≤ j → ∀ a : ℕ → ℤ,
    ¬ Erdos74498Valid (2 * 3 ^ j) a := by
  sorry

theorem erdos_74498_neg :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  rintro ⟨n, a, h⟩
  have hv : Erdos74498Valid n a := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact erdos_74498_neg_hyp_zero a hv
  · have h1 := erdos_74498_neg_hyp_r1 n a hn hv
    have h2 := erdos_74498_neg_hyp_r2 n a hn hv
    obtain ⟨j, hj, rfl⟩ := erdos_74498_neg_hyp_arith n hn h1 h2
    exact erdos_74498_neg_hyp_r4 j hj a hv