import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.GCDMonoid.Finset

set_option autoImplicit false

/-!
# Covering systems of `ℤ` — shared machinery for the Erdős covering-system cluster

This module is a *library*, not a solution to any problem.  It collects the elementary and
classical facts about finite families of congruence classes that recur across the covering-system
problems in the Erdős catalogue (#2, #7, #8, #27, #202-#204, #273-#281, #586, #947, #1113,
#1188-#1190).

## Provenance and honesty

**Nothing here is new mathematics.**

* `density` / `pool_bound` are the textbook density necessary condition for a covering system.
* `exact_cover_max_modulus_repeats` is the **Mirsky–Newman / Davenport–Rado theorem** (1950),
  a published result; the generating-function proof reconstructed here is the standard one.
  Reconstructing a published theorem in Lean is *mechanical verification*, not a new result.
* `norm_excess_eq` / `le_excess` are the root-of-unity necessary condition for a covering with
  excess; it is the same generating-function argument run with a nonzero excess term, and is
  likewise standard.  It was derived and numerically validated before formalisation
  (`knowledge/reductions/273/rootofunity_validation.py`, `.../STRUCTURE.md`).
* The `Erdos273` section migrates lemmas certified by earlier harness runs
  (`knowledge/partial/273/`).  **Erdős #273 is OPEN and nothing here resolves it.**

Mathlib (v4.32.0-rc1) has no `CoveringSystem` / `StrictCoveringSystem`; those live in
`google-deepmind/formal-conjectures`, not in Mathlib.  `CongruenceFamily` below is therefore
defined here, deliberately shaped so that a `StrictCoveringSystem` is the special case
`Covers ∧ DistinctModuli` (with `injective_moduli` becoming `DistinctModuli`).

## The analytic argument, made finite

The classical proofs evaluate `∑ᵢ zᵃⁱ/(1 − z^mᵢ) = 1/(1−z)` near a root of unity and compare
poles.  Working instead inside `{0, …, L−1}` for `L` a common multiple of the moduli, the same
argument becomes a finite character sum with no analysis at all:

* a class `a mod m` meets `{0,…,L−1}` in exactly `L/m` points (`card_class`);
* summing `ζⁿ` over that class gives `(L/μ)·ζᵃ` when `ζ^μ = 1`, and `0` otherwise
  (`sum_class_zpow`, `sum_class_pow_eq_zero`) — this is the pole/no-pole dichotomy;
* `∑_{n<L} ζⁿ = 0` replaces "the right-hand side is finite at `ζ`".

`rootOfUnity_identity` is the resulting identity, and everything else is read off from it.

## Main results

* `CongruenceFamily.density` — `∑ 1/mᵢ ≥ 1` for a covering with moduli dividing `L`.
* `CongruenceFamily.pool_bound` — the reciprocal screen over a pool of eligible moduli.
* `CongruenceFamily.rootOfUnity_identity` — the finite form of the generating-function identity.
* `CongruenceFamily.norm_excess_eq` — `‖∑_{r∈E} ζʳ‖ = L/m` at a divisibility-maximal `m`.
* `CongruenceFamily.le_excess` — hence `L/m ≤ k`, the root-of-unity condition.
* `CongruenceFamily.exact_cover_max_modulus_repeats` — Mirsky–Newman / Davenport–Rado.
* `CongruenceFamily.not_exact_of_distinctModuli` — distinct moduli have no exact cover.
-/

namespace Erdos.Covering

open Finset

universe u

/-- A finite family of congruence classes `res i mod modulus i` in `ℤ`, indexed by a `Finset`.

A *covering system* in the sense of Erdős–Graham is a `CongruenceFamily` satisfying `Covers`
together with `DistinctModuli` and `1 < modulus i`; separating the conditions lets the same
lemmas serve families with repeated moduli (which Mirsky–Newman is *about*). -/
structure CongruenceFamily (ι : Type u) where
  /-- The index set of the family. -/
  idx : Finset ι
  /-- The residue of each class. -/
  res : ι → ℤ
  /-- The modulus of each class. -/
  modulus : ι → ℕ
  /-- Moduli are positive. -/
  modulus_pos : ∀ i ∈ idx, 0 < modulus i

/-! ### Single congruence classes inside `{0, …, L-1}` -/

section SingleClass

variable {M : Type*} [AddCommMonoid M]

/-- Reindexing a residue class: the elements of `{0,…,L−1}` congruent to `a mod m` are exactly
`a₀ + m·t` for `t < L/m`, where `a₀ = a mod m`. -/
theorem sum_class_reindex {L m : ℕ} (a : ℤ) (hm : 0 < m) (hmL : m ∣ L) (f : ℕ → M) :
    ∑ n ∈ (range L).filter (fun n : ℕ => (m : ℤ) ∣ ((n : ℤ) - a)), f n
      = ∑ t ∈ range (L / m), f ((a % (m : ℤ)).toNat + m * t) := by
  have hm0 : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  set a₀ : ℕ := (a % (m : ℤ)).toNat with ha₀def
  have ha₀ : (a₀ : ℤ) = a % (m : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg a hm0)
  have ha₀lt : a₀ < m := by
    have h := Int.emod_lt_of_pos a hmz
    rw [← ha₀] at h
    exact_mod_cast h
  have hdvd₀ : (m : ℤ) ∣ ((a₀ : ℤ) - a) := by
    refine ⟨-(a / (m : ℤ)), ?_⟩
    rw [ha₀, Int.emod_def]; ring
  have hLc : m * (L / m) = L := Nat.mul_div_cancel' hmL
  have hcm : (L / m) * m = L := by rw [Nat.mul_comm]; exact hLc
  have hmod : ∀ n : ℕ, (m : ℤ) ∣ ((n : ℤ) - a) → n % m = a₀ := by
    intro n hn
    have h1 : (a : ℤ) % (m : ℤ) = (n : ℤ) % (m : ℤ) := Int.modEq_iff_dvd.mpr hn
    have h2 : ((n % m : ℕ) : ℤ) = (a₀ : ℤ) := by rw [Int.natCast_mod, ← h1, ha₀]
    exact_mod_cast h2
  refine Finset.sum_nbij' (fun n => n / m) (fun t => a₀ + m * t) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]
    refine (Nat.div_lt_iff_lt_mul hm).mpr ?_
    rw [hcm]; exact hn.1
  · intro t ht
    rw [Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have h2 : m * t + m ≤ L := by
        calc m * t + m = m * (t + 1) := by ring
          _ ≤ m * (L / m) := Nat.mul_le_mul le_rfl ht
          _ = L := hLc
      omega
    · have hcast : ((a₀ + m * t : ℕ) : ℤ) - a = ((a₀ : ℤ) - a) + (m : ℤ) * t := by push_cast; ring
      rw [hcast]
      exact dvd_add hdvd₀ ⟨(t : ℤ), rfl⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [← hmod n hn.2]
    exact Nat.mod_add_div n m
  · intro t _
    rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ha₀lt, Nat.zero_add]
  · intro n hn
    rw [Finset.mem_filter] at hn
    have h3 : a₀ + m * (n / m) = n := by rw [← hmod n hn.2]; exact Nat.mod_add_div n m
    rw [h3]

/-- A residue class `a mod m` meets `{0,…,L−1}` in exactly `L/m` points. -/
theorem card_class {L m : ℕ} (a : ℤ) (hm : 0 < m) (hmL : m ∣ L) :
    ((range L).filter (fun n : ℕ => (m : ℤ) ∣ ((n : ℤ) - a))).card = L / m := by
  have h := sum_class_reindex (M := ℕ) a hm hmL (fun _ => 1)
  simpa using h

/-- `∑ zⁿ` over a residue class, factored as `z^{a mod m}` times a geometric sum. -/
theorem sum_class_pow {L m : ℕ} (a : ℤ) (z : ℂ) (hm : 0 < m) (hmL : m ∣ L) :
    ∑ n ∈ (range L).filter (fun n : ℕ => (m : ℤ) ∣ ((n : ℤ) - a)), z ^ n
      = z ^ (a % (m : ℤ)).toNat * ∑ t ∈ range (L / m), (z ^ m) ^ t := by
  rw [sum_class_reindex a hm hmL (fun n => z ^ n), Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [pow_add, pow_mul]

/-- **No pole.**  If `z^L = 1` but `z^m ≠ 1`, the class sum vanishes. -/
theorem sum_class_pow_eq_zero {L m : ℕ} (a : ℤ) {z : ℂ} (hm : 0 < m) (hmL : m ∣ L)
    (hzL : z ^ L = 1) (hzm : z ^ m ≠ 1) :
    ∑ n ∈ (range L).filter (fun n : ℕ => (m : ℤ) ∣ ((n : ℤ) - a)), z ^ n = 0 := by
  rw [sum_class_pow a z hm hmL, geom_sum_eq hzm]
  have h : (z ^ m) ^ (L / m) = 1 := by rw [← pow_mul, Nat.mul_div_cancel' hmL, hzL]
  rw [h]
  simp

/-- If `z ≠ 0`, `z^m = 1` and `x ≡ y (mod m)`, then `z^x = z^y` (integer exponents). -/
theorem zpow_eq_zpow_of_dvd {z : ℂ} (hz : z ≠ 0) {m : ℕ} (hzm : z ^ m = 1) {x y : ℤ}
    (h : (m : ℤ) ∣ x - y) : z ^ x = z ^ y := by
  obtain ⟨c, hc⟩ := h
  have hx : x = y + (m : ℤ) * c := by linarith
  subst hx
  rw [zpow_add₀ hz, zpow_mul, zpow_natCast, hzm, one_zpow, mul_one]

/-- **The pole term.**  If `z^μ = 1` then the class `a mod μ` contributes `(L/μ)·z^a`. -/
theorem sum_class_zpow {L μ : ℕ} (a : ℤ) {z : ℂ} (hz : z ≠ 0) (hμ : 0 < μ) (hμL : μ ∣ L)
    (hzμ : z ^ μ = 1) :
    ∑ n ∈ (range L).filter (fun n : ℕ => (μ : ℤ) ∣ ((n : ℤ) - a)), z ^ n
      = ((L / μ : ℕ) : ℂ) * z ^ a := by
  have hμ0 : (μ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hμ.ne'
  have h1 : z ^ ((a % (μ : ℤ)).toNat : ℕ) = z ^ a := by
    rw [← zpow_natCast z]
    refine zpow_eq_zpow_of_dvd hz hzμ ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hμ0), Int.emod_def]
    exact ⟨-(a / (μ : ℤ)), by ring⟩
  rw [sum_class_pow a z hμ hμL, hzμ]
  simp [h1, mul_comm]

end SingleClass

namespace CongruenceFamily

variable {ι : Type u} (F : CongruenceFamily ι)

/-- `n` lies in the `i`-th congruence class. -/
def Covered (i : ι) (n : ℤ) : Prop := (F.modulus i : ℤ) ∣ (n - F.res i)

instance decidableCovered (i : ι) (n : ℤ) : Decidable (F.Covered i n) :=
  inferInstanceAs (Decidable ((F.modulus i : ℤ) ∣ (n - F.res i)))

/-- The family covers `ℤ`. -/
def Covers : Prop := ∀ n : ℤ, ∃ i ∈ F.idx, F.Covered i n

/-- How many classes of the family contain `n`. -/
def mult (n : ℤ) : ℕ := (F.idx.filter (fun i => F.Covered i n)).card

/-- The family is an *exact* (disjoint) covering system: every integer is covered once. -/
def Exact : Prop := ∀ n : ℤ, F.mult n = 1

/-- All moduli of the family are distinct (Erdős–Graham's requirement; `injective_moduli`). -/
def DistinctModuli : Prop := Set.InjOn F.modulus F.idx

/-- `i` is *divisibility-maximal*: no other class of the family has a modulus that `modulus i`
divides.  (For distinct moduli, the largest modulus always is.) -/
def DivMaximal (i : ι) : Prop := ∀ j ∈ F.idx, F.modulus i ∣ F.modulus j → j = i

/-- The least common multiple of the family's moduli. -/
def lcmModuli : ℕ := F.idx.lcm F.modulus

theorem modulus_dvd_lcmModuli : ∀ i ∈ F.idx, F.modulus i ∣ F.lcmModuli :=
  fun _ hi => Finset.dvd_lcm hi

theorem lcmModuli_pos : 0 < F.lcmModuli := by
  refine Nat.pos_of_ne_zero fun h => ?_
  obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
  exact absurd hx0 (F.modulus_pos x hx).ne'

theorem one_le_mult_of_covers (hcov : F.Covers) (n : ℤ) : 1 ≤ F.mult n := by
  obtain ⟨i, hi, hin⟩ := hcov n
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hin⟩⟩

/-! ### Counting: the density necessary condition -/

/-- Summing any weight over all classes counts each point with its multiplicity. -/
theorem sum_over_classes {M : Type*} [AddCommMonoid M] (L : ℕ) (f : ℕ → M) :
    ∑ i ∈ F.idx, ∑ n ∈ (range L).filter (fun n : ℕ => F.Covered i (n : ℤ)), f n
      = ∑ n ∈ range L, F.mult (n : ℤ) • f n := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const]
  rfl

/-- **Double counting.**  `∑_{n<L} mult n = ∑_i L/mᵢ`. -/
theorem sum_mult (L : ℕ) (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) :
    ∑ n ∈ range L, F.mult (n : ℤ) = ∑ i ∈ F.idx, L / F.modulus i := by
  have h := F.sum_over_classes (M := ℕ) L (fun _ => 1)
  simp only [smul_eq_mul, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := card_class (L := L) (F.res i) (F.modulus_pos i hi) (hdvd i hi)
  simpa [CongruenceFamily.Covered] using this

/-- **The density necessary condition.**  A covering whose moduli all divide `L > 0` satisfies
`∑ᵢ 1/mᵢ ≥ 1`. -/
theorem density (L : ℕ) (hL : 0 < L) (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) (hcov : F.Covers) :
    (1 : ℚ) ≤ ∑ i ∈ F.idx, (1 : ℚ) / (F.modulus i : ℚ) := by
  have h1 : L ≤ ∑ i ∈ F.idx, L / F.modulus i := by
    rw [← F.sum_mult L hdvd]
    calc L = ∑ _n ∈ range L, 1 := by simp
      _ ≤ ∑ n ∈ range L, F.mult (n : ℤ) :=
          Finset.sum_le_sum fun n _ => F.one_le_mult_of_covers hcov (n : ℤ)
  have hLQ : (0 : ℚ) < (L : ℚ) := by exact_mod_cast hL
  have h2 : (L : ℚ) ≤ ∑ i ∈ F.idx, (L : ℚ) / (F.modulus i : ℚ) := by
    have hc := (Nat.cast_le (α := ℚ)).mpr h1
    refine hc.trans (le_of_eq ?_)
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hx0 : ((F.modulus i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (F.modulus_pos i hi).ne'
    exact Nat.cast_div (hdvd i hi) hx0
  have h3 : ∑ i ∈ F.idx, (L : ℚ) / (F.modulus i : ℚ)
      = (L : ℚ) * ∑ i ∈ F.idx, (1 : ℚ) / (F.modulus i : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3] at h2
  exact le_of_mul_le_mul_left (by rw [mul_one]; exact h2) hLQ

/-- **The pool bound / reciprocal screen.**  If the (distinct) moduli of a covering all lie in a
finite pool `P`, then `∑_{d∈P} 1/d ≥ 1` — a test on `P` alone, with no reference to the covering. -/
theorem pool_bound (L : ℕ) (hL : 0 < L) (P : Finset ℕ)
    (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) (hinj : F.DistinctModuli)
    (hmem : ∀ i ∈ F.idx, F.modulus i ∈ P) (hcov : F.Covers) :
    (1 : ℚ) ≤ ∑ d ∈ P, (1 : ℚ) / (d : ℚ) := by
  classical
  have hdens := F.density L hL hdvd hcov
  have hsum : ∑ d ∈ F.idx.image F.modulus, (1 : ℚ) / (d : ℚ)
      = ∑ i ∈ F.idx, (1 : ℚ) / (F.modulus i : ℚ) :=
    Finset.sum_image fun x hx y hy h => hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
  have hsub : F.idx.image F.modulus ⊆ P := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    exact hmem i hi
  have hle : ∑ d ∈ F.idx.image F.modulus, (1 : ℚ) / (d : ℚ) ≤ ∑ d ∈ P, (1 : ℚ) / (d : ℚ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => by positivity
  rw [hsum] at hle
  linarith

/-! ### The root-of-unity identity and its consequences -/

/-- **The root-of-unity identity** (the finite form of `∑ᵢ z^{aᵢ}/(1−z^{mᵢ}) = 1/(1−z) +
∑_{r∈E} z^r/(1−z^L)`).

For `ζ` a primitive `m`-th root of unity with `m ∣ L`, only the classes whose modulus is a
multiple of `m` survive, and what they add up to is the excess. -/
theorem rootOfUnity_identity (L : ℕ) (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L)
    {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) (hmL : m ∣ L) :
    ∑ i ∈ F.idx.filter (fun i => m ∣ F.modulus i), ((L / F.modulus i : ℕ) : ℂ) * ζ ^ (F.res i)
      = ∑ n ∈ range L, ((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n := by
  have hm0 : m ≠ 0 := by omega
  have hζpow : ζ ^ m = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hm0] at hζpow
    exact zero_ne_one hζpow
  have hζL : ζ ^ L = 1 := by
    obtain ⟨c, hc⟩ := hmL
    rw [hc, pow_mul, hζpow, one_pow]
  have hζne : ζ ≠ 1 := hζ.ne_one hm
  have htot : ∑ n ∈ range L, ζ ^ n = 0 := by
    rw [geom_sum_eq hζne, hζL]
    simp
  have key : ∑ i ∈ F.idx, ∑ n ∈ (range L).filter (fun n : ℕ => F.Covered i (n : ℤ)), ζ ^ n
      = ∑ n ∈ range L, (F.mult (n : ℤ) : ℂ) * ζ ^ n := by
    rw [F.sum_over_classes L fun n => ζ ^ n]
    exact Finset.sum_congr rfl fun n _ => by rw [nsmul_eq_mul]
  have hclass : ∀ i ∈ F.idx, ∑ n ∈ (range L).filter (fun n : ℕ => F.Covered i (n : ℤ)), ζ ^ n
      = if m ∣ F.modulus i then ((L / F.modulus i : ℕ) : ℂ) * ζ ^ (F.res i) else 0 := by
    intro i hi
    by_cases h : m ∣ F.modulus i
    · rw [if_pos h]
      have hzμ : ζ ^ F.modulus i = 1 := (hζ.pow_eq_one_iff_dvd _).mpr h
      exact sum_class_zpow (F.res i) hζ0 (F.modulus_pos i hi) (hdvd i hi) hzμ
    · rw [if_neg h]
      have hzμ : ζ ^ F.modulus i ≠ 1 := fun hc => h ((hζ.pow_eq_one_iff_dvd _).mp hc)
      exact sum_class_pow_eq_zero (F.res i) (F.modulus_pos i hi) (hdvd i hi) hζL hzμ
  calc ∑ i ∈ F.idx.filter (fun i => m ∣ F.modulus i),
          ((L / F.modulus i : ℕ) : ℂ) * ζ ^ (F.res i)
      = ∑ i ∈ F.idx, (if m ∣ F.modulus i then ((L / F.modulus i : ℕ) : ℂ) * ζ ^ (F.res i)
          else 0) := Finset.sum_filter _ _
    _ = ∑ i ∈ F.idx, ∑ n ∈ (range L).filter (fun n : ℕ => F.Covered i (n : ℤ)), ζ ^ n :=
        (Finset.sum_congr rfl hclass).symm
    _ = ∑ n ∈ range L, (F.mult (n : ℤ) : ℂ) * ζ ^ n := key
    _ = ∑ n ∈ range L, ((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n := by
        have hsplit : ∑ n ∈ range L, ((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n
            = (∑ n ∈ range L, (F.mult (n : ℤ) : ℂ) * ζ ^ n) - ∑ n ∈ range L, ζ ^ n := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [hsplit, htot, sub_zero]

/-- **The root-of-unity condition, equality form.**  At a divisibility-maximal modulus `m`, the
excess sum `∑_{r∈E} ζʳ` has modulus exactly `L/m`. -/
theorem norm_excess_eq (L : ℕ) (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L)
    {i : ι} (hi : i ∈ F.idx) (hmax : F.DivMaximal i) (hm : 1 < F.modulus i)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (F.modulus i)) :
    ‖∑ n ∈ range L, ((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n‖ = ((L / F.modulus i : ℕ) : ℝ) := by
  have hid := F.rootOfUnity_identity L hdvd hζ hm (hdvd i hi)
  have hfilter : F.idx.filter (fun j => F.modulus i ∣ F.modulus j) = {i} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hi, dvd_rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hmax x hx.1 hx.2
  rw [← hid, hfilter, Finset.sum_singleton, norm_mul, Complex.norm_natCast, norm_zpow,
    hζ.norm'_eq_one (by omega), one_zpow, mul_one]

/-- **The root-of-unity condition.**  For a covering with total excess `k` (so that
`∑ᵢ L/mᵢ = L + k`) and any divisibility-maximal `i` with `mᵢ > 1`, one has `L/mᵢ ≤ k`.

This subsumes Mirsky–Newman: an exact cover has `k = 0` and demands `L/mᵢ ≤ 0`. -/
theorem le_excess (L : ℕ) (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) (hcov : F.Covers)
    {i : ι} (hi : i ∈ F.idx) (hmax : F.DivMaximal i) (hm : 1 < F.modulus i)
    (k : ℕ) (hk : ∑ j ∈ F.idx, L / F.modulus j = L + k) :
    L / F.modulus i ≤ k := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (F.modulus i) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ (by omega)⟩
  have heq := F.norm_excess_eq L hdvd hi hmax hm hζ
  have hmult : ∀ n : ℕ, 1 ≤ F.mult (n : ℤ) := fun n => F.one_le_mult_of_covers hcov (n : ℤ)
  have hsum : ∑ n ∈ range L, (F.mult (n : ℤ) - 1) = k := by
    have h2 := F.sum_mult L hdvd
    have h3 : ∑ n ∈ range L, ((F.mult (n : ℤ) - 1) + 1) = ∑ n ∈ range L, F.mult (n : ℤ) :=
      Finset.sum_congr rfl fun n _ => by have := hmult n; omega
    rw [Finset.sum_add_distrib] at h3
    have h4 : ∑ _n ∈ range L, 1 = L := by simp
    rw [h4] at h3
    omega
  have hterm : ∀ n ∈ range L,
      ‖((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n‖ = ((F.mult (n : ℤ) - 1 : ℕ) : ℝ) := by
    intro n _
    rw [norm_mul, norm_pow, hζ.norm'_eq_one (by omega), one_pow, mul_one]
    have h1 : ((F.mult (n : ℤ) : ℂ) - 1) = ((F.mult (n : ℤ) - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (hmult n)]
      norm_num
    rw [h1, Complex.norm_natCast]
  have hbound : ‖∑ n ∈ range L, ((F.mult (n : ℤ) : ℂ) - 1) * ζ ^ n‖ ≤ (k : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, hsum]
  rw [heq] at hbound
  exact_mod_cast hbound

/-! ### Mirsky–Newman / Davenport–Rado

The theorem that a disjoint covering system of `ℤ` by at least two congruences must repeat its
largest modulus.  **This is a published theorem (Mirsky–Newman, Davenport–Rado, 1950);** the
proof below is the standard generating-function argument, reconstructed, not discovered. -/

/-- **Mirsky–Newman / Davenport–Rado.**  An exact cover of `ℤ` by `≥ 2` congruences repeats its
largest modulus. -/
theorem exact_cover_max_modulus_repeats (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) (hexact : F.Exact) (hcard : 2 ≤ F.idx.card)
    {i : ι} (hi : i ∈ F.idx) (hgreatest : ∀ j ∈ F.idx, F.modulus j ≤ F.modulus i) :
    ∃ j ∈ F.idx, j ≠ i ∧ F.modulus j = F.modulus i := by
  by_contra hcon
  have hcon' : ∀ j ∈ F.idx, j ≠ i → F.modulus j ≠ F.modulus i := fun j hj hne heq =>
    hcon ⟨j, hj, hne, heq⟩
  have hm1 : 1 < F.modulus i := by
    rcases Nat.lt_or_ge 1 (F.modulus i) with hgt | h
    · exact hgt
    exfalso
    have hall : ∀ j ∈ F.idx, F.modulus j = 1 := fun j hj =>
      le_antisymm ((hgreatest j hj).trans h) (F.modulus_pos j hj)
    have hfull : F.mult 0 = F.idx.card := by
      have : F.idx.filter (fun j => F.Covered j 0) = F.idx := by
        refine Finset.filter_true_of_mem fun j hj => ?_
        change (F.modulus j : ℤ) ∣ (0 - F.res j)
        rw [hall j hj]
        simp
      rw [CongruenceFamily.mult, this]
    rw [hexact 0] at hfull
    omega
  have hmax : F.DivMaximal i := by
    intro j hj hdj
    by_contra hne
    exact hcon' j hj hne (le_antisymm (hgreatest j hj) (Nat.le_of_dvd (F.modulus_pos j hj) hdj))
  have hcov : F.Covers := by
    intro n
    have hn : 0 < F.mult n := by rw [hexact n]; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hn
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
    exact ⟨j, hj1, hj2⟩
  have hk : ∑ j ∈ F.idx, L / F.modulus j = L + 0 := by
    rw [← F.sum_mult L hdvd]
    have hone : ∀ n ∈ range L, F.mult (n : ℤ) = 1 := fun n _ => hexact (n : ℤ)
    rw [Finset.sum_congr rfl hone]
    simp
  have hle := F.le_excess L hdvd hcov hi hmax hm1 0 hk
  have hpos : 0 < L / F.modulus i := Nat.div_pos (Nat.le_of_dvd hL (hdvd i hi)) (by omega)
  omega

/-- **Distinct moduli have no exact cover** (`L` supplied). -/
theorem not_exact_of_distinctModuli (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ i ∈ F.idx, F.modulus i ∣ L) (hinj : F.DistinctModuli) (hcard : 2 ≤ F.idx.card) :
    ¬ F.Exact := by
  intro hexact
  obtain ⟨i, hi, hgreatest⟩ :=
    F.idx.exists_max_image F.modulus (Finset.card_pos.mp (by omega))
  obtain ⟨j, hj, hne, heq⟩ :=
    F.exact_cover_max_modulus_repeats L hL hdvd hexact hcard hi hgreatest
  exact hne (hinj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hi) heq)

/-- **Distinct moduli have no exact cover** — the form with no `L` to supply. -/
theorem not_exact_of_distinctModuli' (hinj : F.DistinctModuli) (hcard : 2 ≤ F.idx.card) :
    ¬ F.Exact :=
  F.not_exact_of_distinctModuli F.lcmModuli F.lcmModuli_pos F.modulus_dvd_lcmModuli hinj hcard

/-- **The root-of-unity condition** with the lcm supplied automatically. -/
theorem le_excess' (hcov : F.Covers) {i : ι} (hi : i ∈ F.idx) (hmax : F.DivMaximal i)
    (hm : 1 < F.modulus i) (k : ℕ)
    (hk : ∑ j ∈ F.idx, F.lcmModuli / F.modulus j = F.lcmModuli + k) :
    F.lcmModuli / F.modulus i ≤ k :=
  F.le_excess F.lcmModuli F.modulus_dvd_lcmModuli hcov hi hmax hm k hk

end CongruenceFamily

/-! ### Erdős #273 — certified partial facts

**#273 is OPEN.**  It asks for a covering system of `ℤ` all of whose (distinct) moduli have the
form `p − 1` for a prime `p ≥ 5`.  Nothing below resolves it; these are the structural facts that
earlier harness runs certified, restated against `CongruenceFamily`. -/

namespace Erdos273

open CongruenceFamily

/-- **The sieve.**  For every prime `q`, an admissible modulus `m` (i.e. `m + 1` prime) with
`q < m + 1` satisfies `q ∤ m + 1`.  With `q = 3` and evenness this deletes `8, 14, 20, 26, …`. -/
theorem sieve {q m : ℕ} (hq : q.Prime) (hp : (m + 1).Prime) (hgt : q < m + 1) : ¬ (q ∣ m + 1) := by
  intro hdvd
  exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd) (by omega)

/-- Every admissible modulus is even: `p ≥ 5` prime is odd, so `m = p − 1` is even. -/
theorem even_modulus {m : ℕ} (hp : (m + 1).Prime) (h5 : 5 ≤ m + 1) : 2 ∣ m := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · omega
  · obtain ⟨k, hk⟩ := hodd
    omega

/-- **Parity confinement.**  A congruence class with an even modulus lies inside one parity class,
so a covering with all moduli even splits into two disjoint coverings sharing no modulus. -/
theorem parity {m a n : ℤ} (hm : 2 ∣ m) (h : m ∣ n - a) : n % 2 = a % 2 := by
  have h2 : (2 : ℤ) ∣ n - a := dvd_trans hm h
  omega

/-- Admissible moduli are even and at least `4`. -/
theorem even_and_four_le (m : ℕ) (h : ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ m = p - 1) :
    Even m ∧ 4 ≤ m := by
  obtain ⟨p, hp, h5, rfl⟩ := h
  exact ⟨hp.even_sub_one (by omega), by omega⟩

/-- The 17 smallest halved admissible moduli have reciprocal sum `< 2`.  With the density bound
applied to each parity class, any solution needs **at least 18** congruences. -/
theorem seventeen_insufficient :
    (1/2 + 1/3 + 1/5 + 1/6 + 1/8 + 1/9 + 1/11 + 1/14 + 1/15 + 1/18 + 1/20 + 1/21 + 1/23 + 1/26
      + 1/29 + 1/30 + 1/33 : ℚ) < 2 := by
  norm_num

/-- …and they are genuinely halved admissible moduli: each is `(p−1)/2` for a prime `p ≥ 5`. -/
theorem halved_admissible :
    ∀ h ∈ [2, 3, 5, 6, 8, 9, 11, 14, 15, 18, 20, 21, 23, 26, 29, 30, 33],
      Nat.Prime (2 * h + 1) ∧ 5 ≤ 2 * h + 1 := by
  decide

set_option maxHeartbeats 1000000 in
-- `interval_cases d` below splits 361 cases, each discharged by `decide`, which exceeds the
-- default heartbeat budget.
/-- The admissible moduli dividing `360`: divisors `d ∣ 360` with `d ≥ 4` and `d + 1` prime. -/
theorem mem_allowed_360 (d : ℕ) (h4 : 4 ≤ d) (hd : d ∣ 360) (hp : Nat.Prime (d + 1)) :
    d ∈ ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) := by
  have hle : d ≤ 360 := Nat.le_of_dvd (by norm_num) hd
  have hmem : d ∈ ({4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90, 120, 180,
      360} : Finset ℕ) := by
    interval_cases d <;> revert hd <;> decide
  fin_cases hmem <;> first
    | decide
    | exact absurd hp (by norm_num)

/-- **Selfridge's covering needs the prime `3`.**  No covering system of `ℤ` whose (distinct)
moduli all have the form `p − 1` with `p ≥ 5` prime can have every modulus dividing `360`: the
eligible moduli `{4,6,10,12,18,30,36,40,60,72,180}` have reciprocal sum `7/9 < 1`. -/
theorem not_dvd_360 {ι : Type u} (F : CongruenceFamily ι)
    (hform : ∀ i ∈ F.idx, ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ F.modulus i = p - 1)
    (hinj : F.DistinctModuli) (h360 : ∀ i ∈ F.idx, F.modulus i ∣ 360) :
    ¬ F.Covers := by
  intro hcov
  have hmem : ∀ i ∈ F.idx, F.modulus i ∈
      ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) := by
    intro i hi
    obtain ⟨p, hp, h5, hx2⟩ := hform i hi
    have h4 := (even_and_four_le (F.modulus i) (hform i hi)).2
    refine mem_allowed_360 (F.modulus i) h4 (h360 i hi) ?_
    have hxp : F.modulus i + 1 = p := by omega
    rw [hxp]
    exact hp
  have hpool := F.pool_bound 360 (by norm_num)
    ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ) h360 hinj hmem hcov
  have hval : ∑ d ∈ ({4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} : Finset ℕ), (1 : ℚ) / (d : ℚ)
      = 7 / 9 := by
    norm_num [Finset.sum_insert, Finset.mem_insert]
  rw [hval] at hpool
  linarith

end Erdos273

end Erdos.Covering
