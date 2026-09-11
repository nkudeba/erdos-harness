import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

/-! # Checked structural facts about Erdős #273, formalised

#273 asks for a covering system of `ℤ` all of whose (distinct) moduli have the form `p - 1` for a prime
`p ≥ 5`.  It is OPEN.  Nothing here resolves it.  These are the elementary facts the reduction stage
proposed and checked empirically, now proved.  A modulus is written `m` with `m + 1 = p`, which avoids
truncated natural subtraction. -/

/-- **The sieve.** For every prime `q`, an admissible modulus `m` with `q < m + 1` is never `≡ q - 1`
mod `q` — equivalently `q ∤ m + 1`.  Taking `q = 3` with evenness gives "no admissible modulus is
`2 mod 6`", which deletes 8, 14, 20, 26, …; every prime `q` contributes its own exclusion. -/
theorem erdos_273_sieve {q m : ℕ} (hq : q.Prime) (hp : (m + 1).Prime) (hgt : q < m + 1) :
    ¬ (q ∣ m + 1) := by
  intro hdvd
  exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd) (by omega)

/-- Every admissible modulus is even: `p ≥ 5` prime is odd, so `m = p - 1` is even. -/
theorem erdos_273_even {m : ℕ} (hp : (m + 1).Prime) (h5 : 5 ≤ m + 1) : 2 ∣ m := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · omega
  · obtain ⟨k, hk⟩ := hodd
    omega

/-- **Parity confinement**, the engine of the decomposition: a congruence class with an even modulus
lies entirely inside one parity class.  So a covering system with all moduli even must cover the evens
and the odds by two families that share no modulus. -/
theorem erdos_273_parity {m a n : ℤ} (hm : 2 ∣ m) (h : m ∣ n - a) : n % 2 = a % 2 := by
  have h2 : (2 : ℤ) ∣ n - a := dvd_trans hm h
  omega

/-- The 17 smallest halved admissible moduli have reciprocal sum `< 2`.  With the density bound
(`Σ 1/mᵢ ≥ 1` per covering family, hence `≥ 2` over the two disjoint halved families), this forces any
solution to use **at least 18** congruences. -/
theorem erdos_273_seventeen_insufficient :
    (1/2 + 1/3 + 1/5 + 1/6 + 1/8 + 1/9 + 1/11 + 1/14 + 1/15 + 1/18 + 1/20 + 1/21 + 1/23 + 1/26
      + 1/29 + 1/30 + 1/33 : ℚ) < 2 := by
  norm_num

/-- …and they are genuinely the 17 smallest: each is `(p-1)/2` for a prime `p ≥ 5`. -/
theorem erdos_273_halved_admissible :
    ∀ h ∈ [2, 3, 5, 6, 8, 9, 11, 14, 15, 18, 20, 21, 23, 26, 29, 30, 33],
      Nat.Prime (2 * h + 1) ∧ 5 ≤ 2 * h + 1 := by
  decide

