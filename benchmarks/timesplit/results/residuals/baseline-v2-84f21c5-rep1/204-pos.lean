-- This hypothesis asserts a finite, residue-level form of a witness. Its truth is equivalent to the frozen
-- target given CRT and periodicity mod n, but the glue below does real work (periodicity reduction and
-- the CRT necessity direction). It is believed FALSE: the case analysis in reductions R2 and R3, plus the
-- parity-complement argument for n = 2*3^j (reduction R4), rules out every n.
theorem erdos_74498_hyp_witness_residue :
    ∃ (n : ℕ) (a : ℕ → ℤ), 0 < n ∧
      (∀ x : ℕ, x < n → ∃ d : ℕ, d ∣ n ∧ d > 1 ∧ (x : ℤ) ≡ a d [ZMOD d]) ∧
      (∀ d d' : ℕ, d ∣ n → d > 1 → d' ∣ n → d' > 1 → d ≠ d' →
        Nat.gcd d d' = 1 ∨ ¬ ((Nat.gcd d d' : ℤ) ∣ a d - a d')) := by
  sorry

theorem erdos_74498 :
    ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  obtain ⟨n, a, hn, hcov, hdisj⟩ := erdos_74498_hyp_witness_residue
  refine ⟨n, a, ?_⟩
  intro D
  have hD : ∀ d, d ∈ D ↔ d ∣ n ∧ d > 1 := fun d => Iff.rfl
  constructor
  · intro x
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnn : 0 ≤ x % (n : ℤ) := Int.emod_nonneg x hn'
    have hlt : x % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos x (by exact_mod_cast hn)
    have hcast : (((x % (n : ℤ)).toNat : ℕ) : ℤ) = x % (n : ℤ) := Int.toNat_of_nonneg hnn
    have hr : (x % (n : ℤ)).toNat < n := by omega
    obtain ⟨d, hd, hd1, hmod⟩ := hcov _ hr
    refine ⟨d, (hD d).mpr ⟨hd, hd1⟩, ?_⟩
    rw [hcast] at hmod
    have hxn : x ≡ x % (n : ℤ) [ZMOD n] := (Int.mod_modEq x n).symm
    exact (hxn.of_dvd (Int.natCast_dvd_natCast.mpr hd)).trans hmod
  · intro d hdD d' hd'D hne hx
    obtain ⟨hd, hd1⟩ := (hD d).mp hdD
    obtain ⟨hd', hd'1⟩ := (hD d').mp hd'D
    rcases hdisj d d' hd hd1 hd' hd'1 hne with h | h
    · exact h
    · exfalso
      obtain ⟨x, h1, h2⟩ := hx
      have hg1 : ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d d')
      have hg2 : ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d' : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d d')
      exact h ((h2.of_dvd hg2).symm.trans (h1.of_dvd hg1)).dvd