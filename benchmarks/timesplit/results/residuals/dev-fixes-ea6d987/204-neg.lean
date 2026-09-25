def Erdos30169CoversRange (n : ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ x : ℤ, 0 ≤ x → x < n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ x ≡ a d [ZMOD d]

def Erdos30169HasClash (n : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ d d' : ℕ, d ∣ n ∧ 1 < d ∧ d' ∣ n ∧ 1 < d' ∧ d ≠ d' ∧ 1 < Nat.gcd d d' ∧
    a d ≡ a d' [ZMOD (Nat.gcd d d')]

-- Generalised CRT (R1, the direction needed): if a ≡ b mod gcd(d,d'), write a - b = g*t and
-- g = u*d + v*d' (Bezout); then x = a - t*u*d = b + t*v*d' lies in both classes.
namespace erdos_30169_neg_hyp_crt_ns
theorem erdos_30169_neg_hyp_crt :
    ∀ (d d' : ℕ) (a b : ℤ), a ≡ b [ZMOD (Nat.gcd d d')] →
      ∃ x : ℤ, x ≡ a [ZMOD d] ∧ x ≡ b [ZMOD d'] := by
  intro d d' a b h
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp h)
  have hg := Nat.gcd_eq_gcd_ab d d'
  refine ⟨a + (d : ℤ) * Nat.gcdA d d' * k, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨-(Nat.gcdA d d' * k), by ring⟩
  · rw [Int.modEq_iff_dvd]
    refine ⟨Nat.gcdB d d' * k, ?_⟩
    linear_combination hk + k * hg
end erdos_30169_neg_hyp_crt_ns

theorem erdos_30169_neg_hyp_crt :
    ∀ (d d' : ℕ) (a b : ℤ), a ≡ b [ZMOD (Nat.gcd d d')] →
      ∃ x : ℤ, x ≡ a [ZMOD d] ∧ x ≡ b [ZMOD d'] := by
  exact erdos_30169_neg_hyp_crt_ns.erdos_30169_neg_hyp_crt



-- R2: for n = 0 every d > 1 divides 0; the classes mod 2,4,6,8 occupy 12+6+4+3 = 25 > 24
-- residues of Z/24, so two of them meet, i.e. agree modulo their gcd (which is > 1).
namespace erdos_30169_neg_hyp_zero_ns
private lemma key (a : ℕ → ℤ) (d d' : ℕ) (hd : 1 < d) (hd' : 1 < d') (hne : d ≠ d')
    (hg : Nat.gcd d d' = 2) (h : a d % 2 = a d' % 2) : Erdos30169HasClash 0 a := by
  refine ⟨d, d', dvd_zero _, hd, dvd_zero _, hd', hne, by rw [hg]; norm_num, ?_⟩
  rw [hg]
  unfold Int.ModEq
  exact_mod_cast h

theorem erdos_30169_neg_hyp_zero :
    ∀ a : ℕ → ℤ, Erdos30169HasClash 0 a := by
  intro a
  have h2 := Int.emod_two_eq_zero_or_one (a 2)
  have h4 := Int.emod_two_eq_zero_or_one (a 4)
  have h6 := Int.emod_two_eq_zero_or_one (a 6)
  by_cases h24 : a 2 % 2 = a 4 % 2
  · exact key a 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h24
  · by_cases h26 : a 2 % 2 = a 6 % 2
    · exact key a 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h26
    · exact key a 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
end erdos_30169_neg_hyp_zero_ns

theorem erdos_30169_neg_hyp_zero :
    ∀ a : ℕ → ℤ, Erdos30169HasClash 0 a := by
  exact erdos_30169_neg_hyp_zero_ns.erdos_30169_neg_hyp_zero



-- Prime powers: all divisors > 1 of p^k are pairwise non-coprime. Without a clash, the classes
-- are pairwise disjoint in Z/p^k with total size sigma(p^k) - p^k < p^k, so the covering fails.
namespace erdos_30169_neg_hyp_primepow_ns
private lemma greedy (p : ℕ) (hp : 1 < p) (a : ℕ → ℤ) :
    ∀ j : ℕ, ∃ x : ℤ, 0 ≤ x ∧ x < ((p ^ j : ℕ) : ℤ) ∧
      ∀ i, 1 ≤ i → i ≤ j → ¬ x ≡ a (p ^ i) [ZMOD ((p ^ i : ℕ) : ℤ)] := by
  intro j
  induction j with
  | zero => exact ⟨0, le_refl _, by simp, fun i h1 h2 => by omega⟩
  | succ j ih =>
    obtain ⟨x, hx0, hxl, hx⟩ := ih
    have hpj : ((p ^ (j+1) : ℕ) : ℤ) = ((p ^ j : ℕ) : ℤ) * (p : ℤ) := by
      push_cast; ring
    have hp' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    have hpos : (0 : ℤ) < ((p ^ j : ℕ) : ℤ) := by
      have : 0 < p ^ j := by positivity
      exact_mod_cast this
    by_cases hc : x ≡ a (p ^ (j+1)) [ZMOD ((p ^ (j+1) : ℕ) : ℤ)]
    · refine ⟨x + ((p ^ j : ℕ) : ℤ), by linarith, by rw [hpj]; nlinarith, ?_⟩
      intro i h1 h2
      rcases Nat.lt_or_ge i (j+1) with hi | hi
      · intro h
        apply hx i h1 (by omega)
        have hd : ((p ^ i : ℕ) : ℤ) ∣ ((p ^ j : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p (by omega))
        have : x + ((p ^ j : ℕ) : ℤ) ≡ x [ZMOD ((p ^ i : ℕ) : ℤ)] :=
          (Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr hd)).symm
        exact this.symm.trans h
      · have hij : i = j + 1 := by omega
        subst hij
        intro h
        have h3 := Int.modEq_iff_dvd.mp (hc.trans h.symm)
        have h4 : ((p ^ (j+1) : ℕ) : ℤ) ∣ ((p ^ j : ℕ) : ℤ) := by
          simpa using h3
        have h5 : p ^ (j+1) ∣ p ^ j := Int.natCast_dvd_natCast.mp h4
        have := (Nat.pow_dvd_pow_iff_le_right hp).mp h5
        omega
    · refine ⟨x, hx0, by rw [hpj]; nlinarith, ?_⟩
      intro i h1 h2
      rcases Nat.lt_or_ge i (j+1) with hi | hi
      · exact hx i h1 (by omega)
      · have hij : i = j + 1 := by omega
        subst hij
        exact hc

theorem erdos_30169_neg_hyp_primepow :
    ∀ (n : ℕ) (a : ℕ → ℤ), IsPrimePow n → Erdos30169CoversRange n a →
      Erdos30169HasClash n a := by
  intro n a hn hcov
  exfalso
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  obtain ⟨x, hx0, hxl, hx⟩ := greedy p hp.one_lt a k
  obtain ⟨d, hd, hd1, hxd⟩ := hcov x hx0 hxl
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hi : i ≠ 0 := by
    rintro rfl
    simp at hd1
  exact hx i (by omega) hik hxd
end erdos_30169_neg_hyp_primepow_ns

theorem erdos_30169_neg_hyp_primepow :
    ∀ (n : ℕ) (a : ℕ → ℤ), IsPrimePow n → Erdos30169CoversRange n a →
      Erdos30169HasClash n a := by
  exact erdos_30169_neg_hyp_primepow_ns.erdos_30169_neg_hyp_primepow



-- Hard core (Erdős–Graham problem, reportedly resolved negatively by Adenwalla): no n with at
-- least two distinct prime factors admits a covering of Z/n by classes a_d mod d (d | n, d > 1)
-- with non-coprime pairs disagreeing modulo their gcd. Exhaustive search excludes n <= 3000.
theorem erdos_30169_neg_hyp_core :
    ∀ (n : ℕ) (a : ℕ → ℤ), 2 ≤ n → ¬ IsPrimePow n → Erdos30169CoversRange n a →
      Erdos30169HasClash n a := by
  sorry

theorem erdos_30169_neg :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  intro h
  obtain ⟨n, a, hcov, hdisj⟩ := h
  have hcr : Erdos30169CoversRange n a := by
    intro x _ _
    obtain ⟨d, ⟨h1, h2⟩, hx⟩ := hcov x
    exact ⟨d, h1, h2, hx⟩
  have hclash : Erdos30169HasClash n a := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact erdos_30169_neg_hyp_zero a
      · exfalso
        obtain ⟨d, ⟨h1, h2⟩, _⟩ := hcov 0
        have := Nat.le_of_dvd one_pos h1
        omega
    · by_cases hpp : IsPrimePow n
      · exact erdos_30169_neg_hyp_primepow n a hpp hcr
      · exact erdos_30169_neg_hyp_core n a hn hpp hcr
  obtain ⟨d, d', h1, h2, h3, h4, hne, hg, hmod⟩ := hclash
  have hx := erdos_30169_neg_hyp_crt d d' (a d) (a d') hmod
  have := hdisj d ⟨h1, h2⟩ d' ⟨h3, h4⟩ hne hx
  omega