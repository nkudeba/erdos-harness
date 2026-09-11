import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ChineseRemainder

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Data.Set.Card
-- IMPORTS: Mathlib.Analysis.SpecificLimits.Basic
-- IMPORTS: Mathlib.NumberTheory.LSeries.PrimesInAP

private lemma erdos_16_cast_zero {q d : ℕ} (h : q ∣ d) : ((d : ℕ) : ZMod q) = 0 := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  simp

private lemma erdos_16_bcast (a d j m : ℕ) (hd : 1 ≤ d) (hdm : ((d : ℕ) : ZMod m) = 0) :
    ((a + (d - 1) * 2 ^ j : ℕ) : ZMod m) = (a : ZMod m) - 2 ^ j := by
  push_cast [Nat.cast_sub hd, hdm]
  ring

/-- Dirichlet case: if `a - 2 ^ k` is a unit mod `d`, the progression contains `2 ^ k + p`. -/
private lemma erdos_16_unit (a d : ℕ) (hd : 0 < d) (k : ℕ)
    (hu : IsUnit ((a : ZMod d) - 2 ^ k))
    (hA : ∀ m : ℕ, ¬ ∃ (k p : ℕ), p.Prime ∧ a + m * d = 2 ^ k + p) : False := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨p, hpgt, hp, hpeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (a + 2 ^ k)
  have h0 : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hcast : ((2 ^ k + p : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) := by
    push_cast
    rw [hpeq]
    ring
  have hmod : (2 ^ k + p) ≡ a [MOD d] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hle : a ≤ 2 ^ k + p := by omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  refine hA t ⟨k, p, hp, ?_⟩
  rw [Nat.mul_comm t d]
  omega

/-- From the failure of the unit condition we read off, for each `k`, an odd prime `q ∣ d`
with `a ≡ 2 ^ (k+1)` mod `q`. -/
private lemma erdos_16_cover (a d : ℕ) (hd : 0 < d) (hodda : Odd a)
    (hnu : ∀ k : ℕ, ¬ IsUnit ((a : ZMod d) - 2 ^ k)) (k : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∣ d ∧ (a : ZMod q) = 2 ^ (k + 1) ∧ q ≠ 2 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hbcast : ((a + (d - 1) * 2 ^ (k + 1) : ℕ) : ZMod d) = (a : ZMod d) - 2 ^ (k + 1) :=
    erdos_16_bcast a d (k + 1) d hd (ZMod.natCast_self d)
  have hnc : ¬ Nat.Coprime (a + (d - 1) * 2 ^ (k + 1)) d := by
    rw [← ZMod.isUnit_iff_coprime, hbcast]
    exact hnu (k + 1)
  have hg : Nat.gcd (a + (d - 1) * 2 ^ (k + 1)) d ≠ 1 := hnc
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hg
  have hqb : q ∣ a + (d - 1) * 2 ^ (k + 1) := hqg.trans (Nat.gcd_dvd_left _ _)
  have hqd : q ∣ d := hqg.trans (Nat.gcd_dvd_right _ _)
  have hbq : ((a + (d - 1) * 2 ^ (k + 1) : ℕ) : ZMod q) = (a : ZMod q) - 2 ^ (k + 1) :=
    erdos_16_bcast a d (k + 1) q hd (erdos_16_cast_zero hqd)
  have hzero : ((a + (d - 1) * 2 ^ (k + 1) : ℕ) : ZMod q) = 0 := erdos_16_cast_zero hqb
  rw [hbq, sub_eq_zero] at hzero
  refine ⟨q, hq, hqd, hzero, ?_⟩
  rintro rfl
  have hae : ((a : ℕ) : ZMod 2) = 0 := by
    rw [hzero]
    have : ((2 : ℕ) : ZMod 2) = 0 := erdos_16_cast_zero dvd_rfl
    push_cast at this
    rw [pow_succ, this, mul_zero]
  have : (2 : ℕ) ∣ a := by
    have h1 : ((a : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2) := by simpa using hae
    exact (Nat.modEq_zero_iff_dvd).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1)
  rw [Nat.odd_iff] at hodda
  omega

/-- The value of a member of the new class modulo a covering prime. -/
private lemma erdos_16_nval (d' inv2 a n q k : ℕ) (hq : q.Prime) (hqd' : q ∣ d')
    (h2inv : 2 * inv2 = d' + 1) (hmod : n ≡ a * inv2 [MOD d'])
    (hqa : (a : ZMod q) = 2 ^ (k + 1)) : ((n : ℕ) : ZMod q) = 2 ^ k := by
  have hnq : n ≡ a * inv2 [MOD q] := hmod.of_dvd hqd'
  have h1 : ((n : ℕ) : ZMod q) = ((a * inv2 : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hnq
  have hd'0 : ((d' : ℕ) : ZMod q) = 0 := erdos_16_cast_zero hqd'
  have hinv : (2 : ZMod q) * ((inv2 : ℕ) : ZMod q) = 1 := by
    have h3 : ((2 * inv2 : ℕ) : ZMod q) = ((d' + 1 : ℕ) : ZMod q) := by rw [h2inv]
    push_cast at h3
    rw [hd'0, zero_add] at h3
    exact h3
  rw [h1]
  push_cast
  rw [hqa, pow_succ]
  calc (2 : ZMod q) ^ k * 2 * ((inv2 : ℕ) : ZMod q)
      = 2 ^ k * (2 * ((inv2 : ℕ) : ZMod q)) := by ring
    _ = 2 ^ k := by rw [hinv, mul_one]

/-- Every member of the new residue class is odd, non-representable, and outside the AP. -/
private lemma erdos_16_mem (a d d' inv2 s : ℕ) (hd : 0 < d) (hodda : Odd a)
    (hdeq : d = 2 ^ s * d') (hodd' : Odd d')
    (hcov : ∀ k : ℕ, ∃ q : ℕ, q.Prime ∧ q ∣ d ∧ (a : ZMod q) = 2 ^ (k + 1) ∧ q ≠ 2)
    (h2inv : 2 * inv2 = d' + 1)
    (n : ℕ) (hn1 : n ≡ 1 [MOD 2 ^ d]) (hnd' : n ≡ a * inv2 [MOD d'])
    (hbig : d + 2 ^ d < n) :
    (Odd n ∧ ¬ ∃ (k p : ℕ), p.Prime ∧ n = 2 ^ k + p) ∧
      n ∉ Set.range (fun m : ℕ => a + m * d) := by
  have hdlt : d < 2 ^ d := Nat.lt_two_pow_self
  have hqdvd' : ∀ q : ℕ, q.Prime → q ∣ d → q ≠ 2 → q ∣ d' := by
    intro q hq hqd hq2
    rw [hdeq] at hqd
    have hcop : Nat.Coprime q (2 ^ s) := by
      refine Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr ?_)
      intro hcon
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hcon)
    exact hcop.dvd_of_dvd_mul_left hqd
  have hval : ∀ q k : ℕ, q.Prime → q ∣ d → q ≠ 2 → (a : ZMod q) = 2 ^ (k + 1) →
      ((n : ℕ) : ZMod q) = 2 ^ k := by
    intro q k hq hqd hq2 hqa
    exact erdos_16_nval d' inv2 a n q k hq (hqdvd' q hq hqd hq2) h2inv hnd' hqa
  constructor
  · constructor
    · have h2 : n ≡ 1 [MOD 2] := hn1.of_dvd (dvd_pow_self 2 (by omega : d ≠ 0))
      rw [Nat.odd_iff]
      simpa [Nat.ModEq] using h2
    · rintro ⟨k, p, hp, hnkp⟩
      obtain ⟨q, hq, hqd, hqa, hq2⟩ := hcov k
      have hnq : ((n : ℕ) : ZMod q) = 2 ^ k := hval q k hq hqd hq2 hqa
      have hp0 : ((p : ℕ) : ZMod q) = 0 := by
        have hc : ((n : ℕ) : ZMod q) = 2 ^ k + ((p : ℕ) : ZMod q) := by
          rw [hnkp]; push_cast; ring
        rw [hnq] at hc
        linear_combination -hc
      have hqp : q ∣ p := by
        have h1 : ((p : ℕ) : ZMod q) = ((0 : ℕ) : ZMod q) := by simpa using hp0
        exact (Nat.modEq_zero_iff_dvd).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1)
      have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      have hqled : q ≤ d := Nat.le_of_dvd hd hqd
      have hpled : p ≤ d := by omega
      by_cases hk : d ≤ k
      · have hdvd : (2 : ℕ) ^ d ∣ 2 ^ k := pow_dvd_pow 2 hk
        have h1 : (2 : ℕ) ^ k + p ≡ 0 + p [MOD 2 ^ d] :=
          Nat.ModEq.add_right p ((Nat.modEq_zero_iff_dvd).mpr hdvd)
        have h2 : n ≡ p [MOD 2 ^ d] := by
          rw [hnkp]; simpa using h1
        have h3 : p ≡ 1 [MOD 2 ^ d] := h2.symm.trans hn1
        have h4 : p % 2 ^ d = 1 % 2 ^ d := h3
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h4
        have := hp.two_le
        omega
      · push_neg at hk
        have h5 : (2 : ℕ) ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hk.le
        omega
  · rintro ⟨j, hj⟩
    obtain ⟨q, hq, hqd, hqa, hq2⟩ := hcov 0
    have hnq : ((n : ℕ) : ZMod q) = 2 ^ 0 := hval q 0 hq hqd hq2 hqa
    have hna : ((n : ℕ) : ZMod q) = ((a : ℕ) : ZMod q) := by
      rw [← hj]
      push_cast
      rw [erdos_16_cast_zero hqd]
      ring
    rw [hna, hqa] at hnq
    have e1 : ((2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      push_cast
      simpa using hnq
    have h12 : (2 : ℕ) ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp e1
    have hq1 : q ∣ 1 := by
      simpa using (Nat.modEq_iff_dvd' (by norm_num : (1 : ℕ) ≤ 2)).mp h12.symm
    exact hq.ne_one (Nat.dvd_one.mp hq1)

theorem erdos_16
    (U : Set ℕ)
    (hU : U = {n : ℕ | Odd n ∧ ¬ ∃ (k p : ℕ), p.Prime ∧ n = 2 ^ k + p})
    (a d : ℕ) (hd : 0 < d)
    (B : Set ℕ)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ((B ∩ Set.Iic x).ncard : ℝ) ≤ ε * (x : ℝ)) :
    U ≠ Set.range (fun m : ℕ => a + m * d) ∪ B := by
  intro h
  have hAU : Set.range (fun m : ℕ => a + m * d) ⊆ U := by
    rw [h]; exact Set.subset_union_left
  have hUA : U \ Set.range (fun m : ℕ => a + m * d) ⊆ B := by
    intro n hn
    have h1 := hn.1
    rw [h] at h1
    rcases h1 with h2 | h2
    · exact absurd h2 hn.2
    · exact h2
  by_cases hcase : ∃ k : ℕ, IsUnit ((a : ZMod d) - 2 ^ k)
  · obtain ⟨k, hk⟩ := hcase
    refine erdos_16_unit a d hd k hk ?_
    intro m hex
    have hm := hAU (Set.mem_range_self m)
    rw [hU] at hm
    exact hm.2 hex
  · push_neg at hcase
    have hodda : Odd a := by
      have hm := hAU (Set.mem_range_self 0)
      rw [hU] at hm
      simpa using hm.1
    obtain ⟨s, d', hodd', hdeq⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
    obtain ⟨jj, hjj⟩ := hodd'
    have hd'pos : 0 < d' := by omega
    have h2inv : 2 * (jj + 1) = d' + 1 := by omega
    have hcov : ∀ k : ℕ, ∃ q : ℕ, q.Prime ∧ q ∣ d ∧ (a : ZMod q) = 2 ^ (k + 1) ∧ q ≠ 2 :=
      erdos_16_cover a d hd hodda hcase
    have hcop : Nat.Coprime (2 ^ d) d' := by
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      omega
    obtain ⟨ν, hν1, hν2⟩ := Nat.chineseRemainder hcop 1 (a * (jj + 1))
    have h2dpos : 0 < 2 ^ d := pow_pos (by norm_num) d
    have hLpos : 0 < 2 ^ d * d' := Nat.mul_pos h2dpos hd'pos
    set L := 2 ^ d * d' with hL
    set C := ν + L * (d + 2 ^ d + 1) with hC
    set f : ℕ → ℕ := fun t => C + L * t with hf
    have hkey1 : ∀ u : ℕ, (ν + L * u) ≡ 1 [MOD 2 ^ d] := by
      intro u
      have hz : L * u ≡ 0 [MOD 2 ^ d] :=
        (Nat.modEq_zero_iff_dvd).mpr ⟨d' * u, by rw [hL]; ring⟩
      calc ν + L * u ≡ ν + 0 [MOD 2 ^ d] := Nat.ModEq.add_left ν hz
        _ = ν := by ring
        _ ≡ 1 [MOD 2 ^ d] := hν1
    have hkey2 : ∀ u : ℕ, (ν + L * u) ≡ a * (jj + 1) [MOD d'] := by
      intro u
      have hz : L * u ≡ 0 [MOD d'] :=
        (Nat.modEq_zero_iff_dvd).mpr ⟨2 ^ d * u, by rw [hL]; ring⟩
      calc ν + L * u ≡ ν + 0 [MOD d'] := Nat.ModEq.add_left ν hz
        _ = ν := by ring
        _ ≡ a * (jj + 1) [MOD d'] := hν2
    have hfeq : ∀ t : ℕ, f t = ν + L * (d + 2 ^ d + 1 + t) := by
      intro t
      simp only [hf, hC]
      ring
    have hfbig : ∀ t : ℕ, d + 2 ^ d < f t := by
      intro t
      have h1 : d + 2 ^ d + 1 ≤ L * (d + 2 ^ d + 1 + t) :=
        le_trans (Nat.le_add_right _ t) (Nat.le_mul_of_pos_left _ hLpos)
      rw [hfeq t]
      omega
    have hfB : ∀ t : ℕ, f t ∈ B := by
      intro t
      have hm := erdos_16_mem a d d' (jj + 1) s hd hodda hdeq ⟨jj, hjj⟩ hcov h2inv (f t)
        (by rw [hfeq t]; exact hkey1 _) (by rw [hfeq t]; exact hkey2 _) (hfbig t)
      refine hUA ⟨?_, hm.2⟩
      rw [hU]
      exact hm.1
    have hfinj : Function.Injective f := by
      intro x y hxy
      simp only [hf] at hxy
      have : L * x = L * y := by omega
      exact Nat.eq_of_mul_eq_mul_left hLpos this
    have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
    obtain ⟨N, hN⟩ := hB (2 * (L : ℝ))⁻¹ (by positivity)
    set J := max N C with hJ
    set x := f J with hx
    have hxN : N ≤ x := by
      have h1 : N ≤ J := le_max_left _ _
      have h2 : J ≤ x := by
        simp only [hx, hf]
        have := Nat.le_mul_of_pos_left J hLpos
        omega
      omega
    have hsub : ((Finset.range (J + 1)).image f : Set ℕ) ⊆ B ∩ Set.Iic x := by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      refine ⟨hfB t, ?_⟩
      simp only [Set.mem_Iic, hx, hf]
      have : L * t ≤ L * J := Nat.mul_le_mul_left L (by omega)
      omega
    have hfin : (B ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
    have hcard : (J + 1 : ℕ) ≤ (B ∩ Set.Iic x).ncard := by
      have h1 := Set.ncard_le_ncard hsub hfin
      rwa [Set.ncard_coe_finset, Finset.card_image_of_injective _ hfinj,
        Finset.card_range] at h1
    have hineq := hN x hxN
    have hcardR : ((J : ℝ) + 1) ≤ ((B ∩ Set.Iic x).ncard : ℝ) := by exact_mod_cast hcard
    have hxR : (x : ℝ) = (C : ℝ) + (L : ℝ) * (J : ℝ) := by
      simp only [hx, hf]
      push_cast
      ring
    have h2L : (0 : ℝ) < 2 * (L : ℝ) := by linarith
    have hfinal : ((J : ℝ) + 1) ≤ (2 * (L : ℝ))⁻¹ * (x : ℝ) := le_trans hcardR hineq
    rw [inv_mul_eq_div, le_div_iff₀ h2L, hxR] at hfinal
    have hCJ : (C : ℝ) ≤ (J : ℝ) := by
      have : C ≤ J := le_max_right _ _
      exact_mod_cast this
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
    have hJL : (J : ℝ) ≤ (L : ℝ) * (J : ℝ) := le_mul_of_one_le_left hJ0 hLR
    nlinarith [hfinal, hCJ, hJL, hLR]
