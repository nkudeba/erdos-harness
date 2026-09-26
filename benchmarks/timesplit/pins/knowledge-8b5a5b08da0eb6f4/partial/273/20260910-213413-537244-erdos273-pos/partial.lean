import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

private lemma erdos_273_count_le (L m : ℕ) (a : ℤ) (hm : 0 < m) (hmL : m ∣ L) :
    ((Finset.range L).filter (fun n : ℕ => (m : ℤ) ∣ ((n : ℤ) - a))).card ≤ L / m := by
  classical
  rw [← Finset.card_range (L / m)]
  refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    obtain ⟨c, rfl⟩ := hmL
    rw [Nat.mul_div_cancel_left c hm]
    exact (Nat.div_lt_iff_lt_mul hm).mpr (by rw [Nat.mul_comm c m]; exact hn.1)
  · intro n hn n' hn' h
    rw [Finset.mem_coe, Finset.mem_filter] at hn hn'
    have hmodeq : Nat.ModEq m n n' := by
      refine Nat.modEq_iff_dvd.mpr ?_
      obtain ⟨k, hk⟩ := hn.2
      obtain ⟨k', hk'⟩ := hn'.2
      exact ⟨k' - k, by linarith [hk, hk']⟩
    have hmod : n % m = n' % m := hmodeq
    have e1 := Nat.div_add_mod n m
    have e2 := Nat.div_add_mod n' m
    rw [show n / m = n' / m from h, hmod] at e1
    exact e1.symm.trans e2

/-- The density necessary condition for covering systems: if the classes `aᵢ mod mᵢ`
(`i` ranging over a finite set `S`, all `mᵢ` dividing a positive `L`) cover `ℤ`, then
`∑ᵢ 1/mᵢ ≥ 1`. -/

private lemma erdos_273_density (S : Finset (ℤ × ℕ)) (L : ℕ) (hL : 0 < L)
    (hpos : ∀ x ∈ S, 0 < x.2) (hdvd : ∀ x ∈ S, x.2 ∣ L)
    (hcov : ∀ n : ℤ, ∃ x ∈ S, ((x.2 : ℤ)) ∣ (n - x.1)) :
    (1 : ℚ) ≤ ∑ x ∈ S, (1 : ℚ) / (x.2 : ℚ) := by
  classical
  have hsub : Finset.range L ⊆
      S.biUnion (fun x => (Finset.range L).filter (fun n : ℕ => (x.2 : ℤ) ∣ ((n : ℤ) - x.1))) := by
    intro n hn
    obtain ⟨x, hx, hd⟩ := hcov (n : ℤ)
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hn, hd⟩⟩
  have h1 : L ≤ ∑ x ∈ S, L / x.2 := by
    calc L = (Finset.range L).card := (Finset.card_range L).symm
      _ ≤ (S.biUnion (fun x =>
            (Finset.range L).filter (fun n : ℕ => (x.2 : ℤ) ∣ ((n : ℤ) - x.1)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ S, ((Finset.range L).filter (fun n : ℕ => (x.2 : ℤ) ∣ ((n : ℤ) - x.1))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S, L / x.2 :=
          Finset.sum_le_sum (fun x hx => erdos_273_count_le L x.2 x.1 (hpos x hx) (hdvd x hx))
  have hLQ : (0 : ℚ) < (L : ℚ) := by exact_mod_cast hL
  have h2 : (L : ℚ) ≤ ∑ x ∈ S, (L : ℚ) / (x.2 : ℚ) := by
    have hc := (Nat.cast_le (α := ℚ)).mpr h1
    refine hc.trans (le_of_eq ?_)
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx0 : ((x.2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hpos x hx).ne'
    exact Nat.cast_div (hdvd x hx) hx0
  have h3 : ∑ x ∈ S, (L : ℚ) / (x.2 : ℚ) = (L : ℚ) * ∑ x ∈ S, (1 : ℚ) / (x.2 : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [h3] at h2
  exact le_of_mul_le_mul_left (by rw [mul_one]; exact h2) hLQ

/-- Every admissible modulus is even and at least `4`. -/

private lemma erdos_273_even (m : ℕ) (h : ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ m = p - 1) :
    Even m ∧ 4 ≤ m := by
  obtain ⟨p, hp, h5, rfl⟩ := h
  exact ⟨hp.even_sub_one (by omega), by omega⟩

/-- **Pool bound.**  If the classes `aᵢ mod mᵢ` cover `ℤ`, the moduli `mᵢ` are distinct, positive,
all divide `L > 0`, and all belong to a finite pool `P`, then `∑_{d ∈ P} 1/d ≥ 1`.

This is the screen that rules out a candidate lcm: one only has to add up the reciprocals of the
*eligible* moduli dividing `L`, with no reference to the covering itself. -/

private theorem erdos_273_pool_bound (S : Finset (ℤ × ℕ)) (L : ℕ) (hL : 0 < L) (P : Finset ℕ)
    (hpos : ∀ x ∈ S, 0 < x.2)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 → x = y)
    (hdvd : ∀ x ∈ S, x.2 ∣ L)
    (hmem : ∀ x ∈ S, x.2 ∈ P)
    (hcov : ∀ n : ℤ, ∃ x ∈ S, ((x.2 : ℤ)) ∣ (n - x.1)) :
    (1 : ℚ) ≤ ∑ d ∈ P, (1 : ℚ) / (d : ℚ) := by
  have hdens := erdos_273_density S L hL hpos hdvd hcov
  have hsum : ∑ d ∈ S.image (fun x : ℤ × ℕ => x.2), (1 : ℚ) / (d : ℚ)
      = ∑ x ∈ S, (1 : ℚ) / (x.2 : ℚ) :=
    Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)
  have hsub : S.image (fun x : ℤ × ℕ => x.2) ⊆ P := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact hmem x hx
  have hle : ∑ d ∈ S.image (fun x : ℤ × ℕ => x.2), (1 : ℚ) / (d : ℚ)
      ≤ ∑ d ∈ P, (1 : ℚ) / (d : ℚ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  rw [hsum] at hle
  linarith

/-- The admissible moduli dividing `360`: divisors `d ∣ 360` with `d ≥ 4` and `d + 1` prime. -/

private lemma erdos_273_mem_allowed (d : ℕ) (h4 : 4 ≤ d) (hd : d ∣ 360)
    (hp : Nat.Prime (d + 1)) :
    d ∈ ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) := by
  have hle : d ≤ 360 := Nat.le_of_dvd (by norm_num) hd
  have hmem : d ∈ ({4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90, 120, 180,
      360} : Finset ℕ) := by
    interval_cases d <;> revert hd <;> decide
  fin_cases hmem <;> first
    | decide
    | exact absurd hp (by norm_num)

/-- **Selfridge's covering needs the prime `3`.**  No covering system of `ℤ` whose moduli are
distinct numbers of the form `p - 1` (`p ≥ 5` prime) can have all its moduli dividing `360`:
the reciprocals of the eligible moduli `{4,6,10,12,18,30,36,40,60,72,180}` sum to `7/9 < 1`. -/

private theorem erdos_273_not_selfridge (S : Finset (ℤ × ℕ))
    (hform : ∀ x ∈ S, ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ x.2 = p - 1)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 → x = y)
    (h360 : ∀ x ∈ S, x.2 ∣ 360) :
    ¬ (∀ n : ℤ, ∃ x ∈ S, ((x.2 : ℤ)) ∣ (n - x.1)) := by
  intro hcov
  have hpos : ∀ x ∈ S, 0 < x.2 := by
    intro x hx
    have := (erdos_273_even x.2 (hform x hx)).2
    omega
  have hmem : ∀ x ∈ S, x.2 ∈ ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) := by
    intro x hx
    obtain ⟨p, hp, h5, hx2⟩ := hform x hx
    have h4 := (erdos_273_even x.2 (hform x hx)).2
    refine erdos_273_mem_allowed x.2 h4 (h360 x hx) ?_
    have hxp : x.2 + 1 = p := by omega
    rw [hxp]
    exact hp
  have hpool := erdos_273_pool_bound S 360 (by norm_num)
    ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) hpos hinj h360 hmem hcov
  have hval : ∑ d ∈ ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ), (1 : ℚ) / (d : ℚ)
      = 7 / 9 := by
    norm_num [Finset.sum_insert, Finset.mem_insert]
  rw [hval] at hpool
  linarith


-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
/-! ### Certified partial results towards Erdős #273

Erdős #273 asks for a covering system of `ℤ` all of whose (distinct) moduli have the form `p - 1`
for a prime `p ≥ 5`.  No such system is known and the problem is open, so the theorem
`erdos_273` below is *not* proved here.  What is proved here is the exact structural content that
is available:

* `erdos_273_count_le`     : a residue class `a mod m` meets `{0, …, L-1}` in at most `L / m` points;
* `erdos_273_density`      : **every** finite covering system with moduli dividing `L` satisfies
  `∑ 1/mᵢ ≥ 1` (the density necessary condition);
* `erdos_273_even`         : every admissible modulus `p - 1` (`p ≥ 5` prime) is even and `≥ 4`;
* `erdos_273_pool_bound`   : if moreover the (distinct) moduli all lie in a finite pool `P`, then
  `∑_{d ∈ P} 1/d ≥ 1` — the reciprocal screen that eliminates a candidate lcm without reference to
  the covering itself;
* `erdos_273_not_selfridge`: no such covering has all its moduli dividing `360`, because the
  eligible moduli there are `{4,6,10,12,18,30,36,40,60,72,180}` with reciprocal sum `7/9 < 1`.
  (This is the precise sense in which Selfridge's covering by divisors of `360` needs the modulus
  `2 = 3 - 1`, which `p ≥ 5` forbids.)
-/

/-- A residue class modulo `m` meets `{0, 1, …, L-1}` in at most `L / m` points. -/

private lemma erdos_273_cast_sub (p : ℕ) (hp : 5 ≤ p) :
    ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
  omega
