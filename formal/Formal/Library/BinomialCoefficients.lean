import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

/-!
# Binomial coefficients — shared machinery for the Erdős binomial-coefficient cluster

This module is a *library*, not a solution to any problem. It collects facts about prime divisors
of binomial coefficients that recur across the 22 catalogue problems tagged `binomial coefficients`
(#175, #376-#379, #384, #386, #387, #396, #397, #683-#685, #698-#700, #730, #731, #849, #1093-#1095).

## Provenance and honesty

**Nothing here is new mathematics.**

* `choose_mul_choose` is the Erdős–Szekeres identity used in [ErSz78]; it is classical.
* `digit_carry` / `small_index_carry` are immediate consequences of **Lucas's theorem** (1878), taken
  from Mathlib's published `Choose.choose_modEq_choose_mod_mul_choose_div_nat`.
* `exists_shared_prime` is the Erdős–Szekeres result that `C(n,i)` and `C(n,j)` are never coprime —
  published in [ErSz78]. It carries **no lower bound on the prime**, and is therefore strictly weaker
  than Erdős #699.
* The `Erdos699` section migrates lemmas certified by harness runs
  (`runs/20260911-195529-727426-erdos699`, `programs/erdos_699/`) and the operator-assisted Codex
  continuation (`experiments/699-continuation/`).

**Erdős #699 is OPEN and nothing here resolves it.** `counterexample_forces_smooth_block` is a
*necessary* condition on a counterexample, one-way only: it does not show smooth blocks are
impossible and yields no finite cutoff.

## The limitation that matters

`block_prime` only ever produces a prime `p > j`. The residue route is **sufficient, not necessary**:
at `(n,i,j) = (10,3,5)` the shared prime is `p = 3 = i`, which divides both binomials through a carry
at a *higher* base-`p` digit, and `residue_route_fails` records that the units-digit criterion finds
nothing there. Any full attack on #699 must separately handle primes in `[i, j]`, including `p = i`.
-/

namespace Formal.Library.BinomialCoefficients


-- certified in sub-0 (2026-09-12T00:18:18Z)
namespace erdos_699_sub1_1_ns
-- CHECK: Nat.choose_mul_factorial_mul_factorial Nat.eq_of_mul_eq_mul_right Nat.factorial_pos
-- LOOGLE: Nat.choose ?n ?k * Nat.choose ?k ?m = _
-- GREP: choose_mul_choose

private lemma erdos_699_sub1_1_lhs (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    Nat.choose n j * Nat.choose j i *
        (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))
      = Nat.factorial n := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hij
  have h2 := Nat.choose_mul_factorial_mul_factorial hjn
  calc Nat.choose n j * Nat.choose j i *
        (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))
      = (Nat.choose j i * Nat.factorial i * Nat.factorial (j - i)) *
          (Nat.choose n j * Nat.factorial (n - j)) := by ring
    _ = Nat.factorial j * (Nat.choose n j * Nat.factorial (n - j)) := by rw [h1]
    _ = Nat.choose n j * Nat.factorial j * Nat.factorial (n - j) := by ring
    _ = Nat.factorial n := h2

private lemma erdos_699_sub1_1_rhs (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    Nat.choose n i * Nat.choose (n - i) (j - i) *
        (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))
      = Nat.factorial n := by
  have hin : i ≤ n := le_trans hij hjn
  have hji : j - i ≤ n - i := by omega
  have h3 := Nat.choose_mul_factorial_mul_factorial hji
  rw [show n - i - (j - i) = n - j by omega] at h3
  have h4 := Nat.choose_mul_factorial_mul_factorial hin
  calc Nat.choose n i * Nat.choose (n - i) (j - i) *
        (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))
      = (Nat.choose (n - i) (j - i) * Nat.factorial (j - i) * Nat.factorial (n - j)) *
          (Nat.choose n i * Nat.factorial i) := by ring
    _ = Nat.factorial (n - i) * (Nat.choose n i * Nat.factorial i) := by rw [h3]
    _ = Nat.choose n i * Nat.factorial i * Nat.factorial (n - i) := by ring
    _ = Nat.factorial n := h4

theorem erdos_699_sub1_1 (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    Nat.choose n j * Nat.choose j i = Nat.choose n i * Nat.choose (n - i) (j - i) := by
  have hpos : 0 < Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)) :=
    Nat.mul_pos (Nat.factorial_pos i)
      (Nat.mul_pos (Nat.factorial_pos (j - i)) (Nat.factorial_pos (n - j)))
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [erdos_699_sub1_1_lhs n i j hij hjn, erdos_699_sub1_1_rhs n i j hij hjn]
end erdos_699_sub1_1_ns

-- certified in sub-1 (2026-09-12T00:25:25Z)
namespace erdos_699_sub2_1_ns
-- CHECK: Nat.choose_pos Nat.choose_succ_succ Nat.choose_succ_succ' Nat.choose_le_choose
-- LOOGLE: Nat.choose ?a ?k < Nat.choose ?b ?k

private lemma choose_lt_choose_succ_aux (m i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    Nat.choose m i < Nat.choose (m + 1) i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : Nat.choose (m + 1) (k + 1) = Nat.choose m k + Nat.choose m (k + 1) := rfl
  have hpos : 0 < Nat.choose m k := Nat.choose_pos (by omega)
  omega

private lemma choose_lt_choose_add (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    ∀ d : ℕ, Nat.choose j i < Nat.choose (j + d + 1) i := by
  intro d
  induction d with
  | zero =>
      have h := choose_lt_choose_succ_aux j i hi hij
      have he : j + 0 + 1 = j + 1 := by omega
      rw [he]
      exact h
  | succ e ih =>
      have h2 := choose_lt_choose_succ_aux (j + e + 1) i hi (by omega)
      have he : j + (e + 1) + 1 = (j + e + 1) + 1 := by omega
      rw [he]
      exact lt_trans ih h2

theorem erdos_699_sub2_1 (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    Nat.choose j i < Nat.choose n i := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d + 1 := ⟨n - j - 1, by omega⟩
  exact choose_lt_choose_add i j hi hij d
end erdos_699_sub2_1_ns

-- certified in sub-2 (2026-09-12T00:37:25Z)
namespace erdos_699_sub3_1_ns
-- CHECK: Nat.choose_mul Nat.choose_le_choose Nat.choose_succ_succ Nat.choose_pos
-- CHECK: Nat.Coprime.dvd_of_dvd_mul_left Nat.exists_prime_and_dvd Nat.le_of_dvd
private lemma choose_lt_choose_of_lt {i j n : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    Nat.choose j i < Nat.choose n i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have h1 : Nat.choose j (i' + 1) ≤ Nat.choose m (i' + 1) := by
    apply Nat.choose_le_choose
    omega
  have h2 : 0 < Nat.choose m i' := Nat.choose_pos (by omega)
  have h3 : Nat.choose (m + 1) (i' + 1) = Nat.choose m i' + Nat.choose m (i' + 1) :=
    Nat.choose_succ_succ m i'
  omega

theorem erdos_699_sub3_1 (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j := by
  have hne : Nat.gcd (Nat.choose n i) (Nat.choose n j) ≠ 1 := by
    intro h
    have hcop : Nat.Coprime (Nat.choose n i) (Nat.choose n j) := h
    have hid : Nat.choose n j * Nat.choose j i
        = Nat.choose n i * Nat.choose (n - i) (j - i) := by
      apply Nat.choose_mul <;> omega
    have hdvd : Nat.choose n i ∣ Nat.choose n j * Nat.choose j i :=
      ⟨Nat.choose (n - i) (j - i), hid⟩
    have hdvd2 : Nat.choose n i ∣ Nat.choose j i := hcop.dvd_of_dvd_mul_left hdvd
    have hpos : 0 < Nat.choose j i := Nat.choose_pos hij
    have hle := Nat.le_of_dvd hpos hdvd2
    have hlt := choose_lt_choose_of_lt hi hij hjn
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left _ _), hpd.trans (Nat.gcd_dvd_right _ _)⟩
end erdos_699_sub3_1_ns

-- certified in sub-3 (2026-09-12T00:44:27Z)
namespace erdos_699_sub4_1_ns
-- CHECK: Nat.succ_mul_choose_eq Nat.choose_one_right Nat.Coprime.dvd_of_dvd_mul_left
-- CHECK: Nat.exists_prime_and_dvd Nat.gcd_dvd_left Nat.gcd_dvd_right
private lemma erdos_699_sub4_1_absorb (n j : ℕ) (hj : 1 ≤ j) (hjn : j < n) :
    n ∣ Nat.choose n j * j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨Nat.choose m k, (Nat.succ_mul_choose_eq m k).symm⟩

theorem erdos_699_sub4_1 (n j : ℕ) (hj : 1 ≤ j) (hjn : j < n) :
    ∃ p : ℕ, p.Prime ∧ 1 ≤ p ∧ p ∣ Nat.choose n 1 ∧ p ∣ Nat.choose n j := by
  have hkey : n ∣ Nat.choose n j * j := erdos_699_sub4_1_absorb n j hj hjn
  have hgne : Nat.gcd n (Nat.choose n j) ≠ 1 := by
    intro h
    have hcop : Nat.Coprime n (Nat.choose n j) := h
    have hnj : n ∣ j := hcop.dvd_of_dvd_mul_left hkey
    have hle : n ≤ j := Nat.le_of_dvd (by omega) hnj
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgne
  refine ⟨p, hp, hp.one_lt.le, ?_, hpd.trans (Nat.gcd_dvd_right _ _)⟩
  rw [Nat.choose_one_right]
  exact hpd.trans (Nat.gcd_dvd_left _ _)
end erdos_699_sub4_1_ns

-- certified in sub-4 (2026-09-12T00:50:11Z)
namespace erdos_699_sub5_1_ns
-- IMPORTS: Mathlib.Data.Nat.Choose.Dvd
-- CHECK: Nat.Prime.dvd_choose Nat.Prime.dvd_choose_add Nat.Prime.dvd_factorial
theorem erdos_699_sub5_1 (n i j p : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjn : 2 * j ≤ n)
    (hp : Nat.Prime p) (hlo : n - i < p) (hhi : p ≤ n) :
    i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j := by
  have hip : i < p := by omega
  have hjp : j < p := by omega
  have hlj : n - j < p := by omega
  refine ⟨hip.le, ?_, ?_⟩
  · exact hp.dvd_choose hip hlo hhi
  · exact hp.dvd_choose hjp hlj hhi
end erdos_699_sub5_1_ns

/-! ## Lucas-theorem consequences and the smoothness reduction (Codex continuation) -/

theorem digit_carry {n k p : ℕ} (hp : p.Prime)
    (h : n % p < k % p) : p ∣ Nat.choose n k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hm
  exact Nat.dvd_of_mod_eq_zero hm

theorem small_index_carry {n k p : ℕ} (hp : p.Prime)
    (hkp : k < p) (h : n % p < k) : p ∣ Nat.choose n k := by
  apply digit_carry hp
  simpa [Nat.mod_eq_of_lt hkp] using h

theorem block_prime {n i j t p : ℕ} (hij : i < j) (hjn : 2 * j ≤ n)
    (ht : t < i) (hp : p.Prime) (hjp : j < p) (hd : p ∣ n - t) :
    i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j := by
  have htn : t ≤ n := by omega
  have he : n = (n - t) + t := by omega
  have hm : n % p = t := by
    conv_lhs => rw [he]
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.mod_eq_of_lt (show t < p by omega)]
  exact ⟨by omega, small_index_carry hp (by omega) (by omega),
    small_index_carry hp hjp (by omega)⟩

theorem counterexample_forces_smooth_block {n i j : ℕ}
    (hij : i < j) (hjn : 2 * j ≤ n)
    (hfail : ¬ ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j) :
    ∀ t < i, ∀ p : ℕ, p.Prime → p ∣ n - t → p ≤ j := by
  intro t ht p hp hd
  by_contra h
  have hb := block_prime hij hjn ht hp (by omega) hd
  exact hfail ⟨p, hp, hb⟩

-- The proposed Conjecture D fails at a known strict-variant exception.
theorem residue_route_fails :
    ¬ ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ 10 % p < 3 % p ∧ 10 % p < 5 % p := by
  rintro ⟨p, hp, hlo, hi, hj⟩
  have hd := digit_carry hp hi
  have he := digit_carry hp hj
  have hg : p ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) := Nat.dvd_gcd hd he
  norm_num at hg
  have hple := Nat.le_of_dvd (by decide : 0 < 12) hg
  -- `norm_num at hp hi hj` closed each goal from `hp` and then kept going with no goals left,
  -- which Lean reported as 9 errors and patched with sorryAx. Revert and decide each literal case.
  interval_cases p <;> revert hp hi hj <;> decide

theorem same_example_satisfies_target :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.choose 10 3 ∧ p ∣ Nat.choose 10 5 := by
  exact ⟨3, by decide, by decide, by decide, by decide⟩


end Formal.Library.BinomialCoefficients
