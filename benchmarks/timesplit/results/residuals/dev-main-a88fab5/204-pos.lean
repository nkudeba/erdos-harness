-- CHECK: Int.mod_modEq Int.ModEq.of_dvd Int.natCast_dvd_natCast Int.emod_nonneg Int.emod_lt_of_pos
-- Finite-residue reformulation of a witness (reductions R1, R2 plus covering of Z/nZ).
-- This is believed FALSE: Erdős–Graham #204 was answered negatively (Adenwalla, 2025),
-- and exhaustive search finds no system for all filtered n up to 246.
theorem erdos_68434_hyp_finite_witness :
    ∃ (n : ℕ) (a : ℕ → ℤ), 0 < n ∧
      (∀ x : ℤ, 0 ≤ x → x < (n : ℤ) → ∃ d : ℕ, d ∣ n ∧ d > 1 ∧ x ≡ a d [ZMOD d]) ∧
      (∀ d d' : ℕ, d ∣ n → d > 1 → d' ∣ n → d' > 1 → d ≠ d' → Nat.gcd d d' ≠ 1 →
        ¬ (a d ≡ a d' [ZMOD (Nat.gcd d d')])) := by
  sorry

theorem erdos_68434 :
    ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  obtain ⟨n, a, hn, hcov, hdis⟩ := erdos_68434_hyp_finite_witness
  refine ⟨n, a, ?_⟩
  intro D
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  refine ⟨fun x => ?_, fun d hd d' hd' hne hx => ?_⟩
  · obtain ⟨d, hdn, hd1, hy⟩ :=
      hcov (x % (n : ℤ)) (Int.emod_nonneg x hpos.ne') (Int.emod_lt_of_pos x hpos)
    have hdvd : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdn
    have hmem : d ∈ D := ⟨hdn, hd1⟩
    exact ⟨d, hmem, ((Int.mod_modEq x (n : ℤ)).symm.of_dvd hdvd).trans hy⟩
  · have hd2 : d ∣ n ∧ d > 1 := hd
    have hd2' : d' ∣ n ∧ d' > 1 := hd'
    by_contra hg
    obtain ⟨x, h1, h2⟩ := hx
    have h3 : ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d d')
    have h4 : ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d' : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d d')
    exact hdis d d' hd2.1 hd2.2 hd2'.1 hd2'.2 hne hg
      ((h1.symm.of_dvd h3).trans (h2.of_dvd h4))