def ErdosValid (n : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ x : ℤ, ∃ d ∈ {d : ℕ | d ∣ n ∧ d > 1}, x ≡ a d [ZMOD d]) ∧
  (∀ d ∈ {d : ℕ | d ∣ n ∧ d > 1}, ∀ d' ∈ {d : ℕ | d ∣ n ∧ d > 1}, d ≠ d' →
    (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) → Nat.gcd d d' = 1)

def FinValid (n : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ x : ℕ, x < n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ (x : ℤ) ≡ a d [ZMOD (d : ℤ)]) ∧
  (∀ d d' : ℕ, d ∣ n → d' ∣ n → 1 < d → 1 < d' → d ≠ d' → 1 < Nat.gcd d d' →
    ¬ (a d ≡ a d' [ZMOD ((Nat.gcd d d' : ℕ) : ℤ)]))

-- Derived (R2 / C1): for n = 0 the moduli 2, 4, 6, 8 all lie in D with pairwise gcd ≥ 2.
-- Disjointness forces their classes to be pairwise disjoint. Reduced mod 24 they would have
-- sizes 12 + 6 + 4 + 3 = 25 > 24, which is impossible. A shorter route uses 2, 4, 6: pairwise
-- different parities among only two parity classes.
namespace erdos_68434_neg_hyp_zero_ns
theorem erdos_68434_neg_hyp_zero : ∀ a : ℕ → ℤ, ¬ ErdosValid 0 a := by
  intro a hv
  obtain ⟨_, h⟩ := hv
  have m2 : (2:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 2, by norm_num⟩
  have m4 : (4:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 4, by norm_num⟩
  have m6 : (6:ℕ) ∈ {d : ℕ | d ∣ 0 ∧ d > 1} := ⟨dvd_zero 6, by norm_num⟩
  have e1 := h 2 m2 4 m4 (by norm_num)
  have e2 := h 2 m2 6 m6 (by norm_num)
  have e3 := h 4 m4 6 m6 (by norm_num)
  have g1 : Nat.gcd 2 4 ≠ 1 := by decide
  have g2 : Nat.gcd 2 6 ≠ 1 := by decide
  have g3 : Nat.gcd 4 6 ≠ 1 := by decide
  have p1 : a 4 % 2 ≠ a 2 % 2 := by
    intro hc
    apply g1 (e1 ⟨a 4, ?_, ?_⟩)
    · simp only [Int.ModEq, Nat.cast_ofNat]; omega
    · exact Int.ModEq.refl _
  have p2 : a 6 % 2 ≠ a 2 % 2 := by
    intro hc
    apply g2 (e2 ⟨a 6, ?_, ?_⟩)
    · simp only [Int.ModEq, Nat.cast_ofNat]; omega
    · exact Int.ModEq.refl _
  apply g3 (e3 ⟨3 * a 4 - 2 * a 6, ?_, ?_⟩)
  · simp only [Int.ModEq, Nat.cast_ofNat]; omega
  · simp only [Int.ModEq, Nat.cast_ofNat]; omega
end erdos_68434_neg_hyp_zero_ns

theorem erdos_68434_neg_hyp_zero : ∀ a : ℕ → ℤ, ¬ ErdosValid 0 a := by
  exact erdos_68434_neg_hyp_zero_ns.erdos_68434_neg_hyp_zero



-- Derived (R1): the covering of ℤ restricts to the residues 0 ≤ x < n. For a non-coprime
-- pair, a ≡ b (mod gcd) would yield, by Bezout/CRT, a common point x of the two classes.
-- The disjointness clause would then give gcd = 1, contradicting gcd > 1.
namespace erdos_68434_neg_hyp_reduce_ns
theorem erdos_68434_neg_hyp_reduce :
    ∀ n : ℕ, 0 < n → ∀ a : ℕ → ℤ, ErdosValid n a → FinValid n a := by
  intro n hn a h
  obtain ⟨hcov, hdisj⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, hx'⟩ := hcov (x : ℤ)
    exact ⟨d, hd.1, hd.2, hx'⟩
  · intro d d' hd hd' h1 h1' hne hg hmod
    have key : ∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d'] := by
      obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
      have hb := Nat.gcd_eq_gcd_ab d d'
      refine ⟨a d + (d : ℤ) * Nat.gcdA d d' * k, ?_, ?_⟩
      · apply Int.modEq_iff_dvd.mpr
        exact ⟨-(Nat.gcdA d d' * k), by ring⟩
      · apply Int.modEq_iff_dvd.mpr
        refine ⟨Nat.gcdB d d' * k, ?_⟩
        linear_combination hk + k * hb
    have := hdisj d ⟨hd, h1⟩ d' ⟨hd', h1'⟩ hne key
    omega
end erdos_68434_neg_hyp_reduce_ns

theorem erdos_68434_neg_hyp_reduce :
    ∀ n : ℕ, 0 < n → ∀ a : ℕ → ℤ, ErdosValid n a → FinValid n a := by
  exact erdos_68434_neg_hyp_reduce_ns.erdos_68434_neg_hyp_reduce



-- Core: the finite residue formulation on ℤ/n has no solution. This is believed to be true
-- (attributed to Adenwalla 2025, Erdős #204, unverified). The cases n = 1, prime powers and
-- pq are handled by R3/R4, and exhaustive search rules out every n ≤ 600. The general case
-- is the open core of this program.
theorem erdos_68434_neg_hyp_core :
    ∀ n : ℕ, 0 < n → ∀ a : ℕ → ℤ, ¬ FinValid n a := by
  sorry

theorem erdos_68434_neg :
    ¬ (∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1)) := by
  rintro ⟨n, a, h⟩
  have hv : ErdosValid n a := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact erdos_68434_neg_hyp_zero a hv
  · exact erdos_68434_neg_hyp_core n hn a (erdos_68434_neg_hyp_reduce n hn a hv)