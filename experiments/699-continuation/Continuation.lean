import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Lucas

/- Operator-assisted Codex continuation of Claude's #699 program.
   These are consequences of published Lucas theory, not a resolution of #699. -/
namespace Erdos699Continuation

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

theorem block_prime {n i j t p : ℕ} (hij : i < j) (hjn : 2*j ≤ n)
    (ht : t < i) (hp : p.Prime) (hjp : j < p) (hd : p ∣ n-t) :
    i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j := by
  have htn : t ≤ n := by omega
  have he : n = (n-t)+t := by omega
  have hm : n % p = t := by
    conv_lhs => rw [he]
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.mod_eq_of_lt (show t < p by omega)]
  exact ⟨by omega, small_index_carry hp (by omega) (by omega),
    small_index_carry hp hjp (by omega)⟩

theorem counterexample_forces_smooth_block {n i j : ℕ}
    (hij : i < j) (hjn : 2*j ≤ n)
    (hfail : ¬ ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j) :
    ∀ t < i, ∀ p : ℕ, p.Prime → p ∣ n-t → p ≤ j := by
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

#print axioms digit_carry
#print axioms small_index_carry
#print axioms block_prime
#print axioms counterexample_forces_smooth_block
#print axioms residue_route_fails
#print axioms same_example_satisfies_target
end Erdos699Continuation
