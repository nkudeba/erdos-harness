import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Nat.Prime.Factorial

set_option maxHeartbeats 1000000
set_option autoImplicit false

open MvPolynomial

private lemma single_pair_eq (a b i j : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j
      = Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) ↔ (i = a ∧ j = b) := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
    norm_num at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma coeff_two_var {R : Type*} [CommRing R] (a b i j : ℕ) (c : R) :
    coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
      ((X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) * MvPolynomial.C c)
      = if (i = a ∧ j = b) then c else 0 := by
  have h : ((X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) * MvPolynomial.C c)
      = monomial (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) c := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_apply, monomial_mul]
    simp
  rw [h, coeff_monomial]
  simp only [single_pair_eq]

private lemma coeff_add_pow_two {R : Type*} [CommRing R] (n a b : ℕ) (hab : a + b = n) :
    coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
      ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) = (n.choose a : R) := by
  rw [add_pow, coeff_sum]
  have key : ∀ i ∈ Finset.range (n + 1),
      coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
        ((X 0 ^ i * X 1 ^ (n - i) : MvPolynomial (Fin 2) R)
          * (n.choose i : MvPolynomial (Fin 2) R))
      = if i = a then (n.choose a : R) else 0 := by
    intro i _
    rw [show ((n.choose i : MvPolynomial (Fin 2) R))
        = MvPolynomial.C ((n.choose i : ℕ) : R) from (map_natCast MvPolynomial.C _).symm,
      coeff_two_var]
    by_cases h : i = a
    · subst h
      rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (by tauto), if_neg h]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (Finset.range (n + 1)) a
    (fun _ => (n.choose a : R)), if_pos (Finset.mem_range.mpr (by omega))]

private lemma coeff_key {R : Type*} [CommRing R] (n a b : ℕ) (hab : a + b + 2 = n + 1) :
    coeff (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      (((X 0 - X 1) * (X 0 + X 1) ^ n : MvPolynomial (Fin 2) R))
      = (n.choose a : R) - (n.choose (a + 1) : R) := by
  have hs0 : Finsupp.single (0 : Fin 2) (a + 1)
      = Finsupp.single (0 : Fin 2) a + Finsupp.single (0 : Fin 2) 1 := by
    rw [← Finsupp.single_add]
  have hs1 : Finsupp.single (1 : Fin 2) (b + 1)
      = Finsupp.single (1 : Fin 2) b + Finsupp.single (1 : Fin 2) 1 := by
    rw [← Finsupp.single_add]
  have e0 : (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      = (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) (b + 1))
        + Finsupp.single (0 : Fin 2) 1 := by
    rw [hs0]; abel
  have e1 : (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      = (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) b)
        + Finsupp.single (1 : Fin 2) 1 := by
    rw [hs1]; abel
  have hsplit : ((X 0 - X 1) * (X 0 + X 1) ^ n : MvPolynomial (Fin 2) R)
      = ((X 0 + X 1) ^ n) * X 0 - ((X 0 + X 1) ^ n) * X 1 := by ring
  rw [hsplit, coeff_sub]
  have h0 : coeff (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      (((X 0 + X 1) ^ n : MvPolynomial (Fin 2) R) * X 0) = (n.choose a : R) := by
    rw [e0, coeff_mul_X, coeff_add_pow_two n a (b + 1) (by omega)]
  have h1 : coeff (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      (((X 0 + X 1) ^ n : MvPolynomial (Fin 2) R) * X 1) = (n.choose (a + 1) : R) := by
    rw [e1, coeff_mul_X, coeff_add_pow_two n (a + 1) b (by omega)]
  rw [h0, h1]

private lemma degree_pair (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b).degree = a + b := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

private lemma totalDegree_XaddX {R : Type*} [CommRing R] [Nontrivial R] :
    ((X 0 + X 1 : MvPolynomial (Fin 2) R)).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_add _ _) ?_
  rw [totalDegree_X, totalDegree_X]
  simp

private lemma totalDegree_XsubX {R : Type*} [CommRing R] [Nontrivial R] :
    ((X 0 - X 1 : MvPolynomial (Fin 2) R)).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_X, totalDegree_X]
  simp

private lemma totalDegree_pow_XaddX {R : Type*} [CommRing R] [Nontrivial R] (m : ℕ) :
    ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ m).totalDegree ≤ m := by
  refine le_trans (totalDegree_pow _ _) ?_
  have := totalDegree_XaddX (R := R)
  calc m * ((X 0 + X 1 : MvPolynomial (Fin 2) R)).totalDegree ≤ m * 1 :=
        Nat.mul_le_mul_left _ this
    _ = m := by ring

private lemma totalDegree_lin {R : Type*} [CommRing R] [Nontrivial R] (c : R) :
    ((X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) R)).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_C]
  simpa using totalDegree_XaddX (R := R)

private lemma prod_struct {R : Type*} [CommRing R] [Nontrivial R] (C0 : Finset R) :
    ∃ r : MvPolynomial (Fin 2) R,
      (∏ c ∈ C0, (X 0 + X 1 - MvPolynomial.C c)) = (X 0 + X 1) ^ C0.card + r ∧
        (r.totalDegree + 1 ≤ C0.card ∨ r = 0) := by
  classical
  refine Finset.induction_on C0 ⟨0, by simp, Or.inr rfl⟩ ?_
  intro c s hcs ih
  obtain ⟨r, hr, hdeg⟩ := ih
  refine ⟨-(MvPolynomial.C c * (X 0 + X 1) ^ s.card)
      + (X 0 + X 1 - MvPolynomial.C c) * r, ?_, ?_⟩
  · rw [Finset.prod_insert hcs, hr, Finset.card_insert_of_notMem hcs]
    ring
  · left
    rw [Finset.card_insert_of_notMem hcs]
    have h1 : (-(MvPolynomial.C c * (X 0 + X 1) ^ s.card)
        : MvPolynomial (Fin 2) R).totalDegree ≤ s.card := by
      rw [totalDegree_neg]
      refine le_trans (totalDegree_mul _ _) ?_
      rw [totalDegree_C]
      simpa using totalDegree_pow_XaddX (R := R) s.card
    have hsc : ((X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) R)).totalDegree ≤ 1 := by
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_C]
      simpa using totalDegree_XaddX (R := R)
    have h2 : ((X 0 + X 1 - MvPolynomial.C c) * r : MvPolynomial (Fin 2) R).totalDegree
        ≤ s.card := by
      rcases hdeg with h | h
      · have := totalDegree_mul (X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) R) r
        omega
      · rw [h, mul_zero, totalDegree_zero]
        exact Nat.zero_le _
    have h3 := totalDegree_add (-(MvPolynomial.C c * (X 0 + X 1) ^ s.card)
      : MvPolynomial (Fin 2) R) ((X 0 + X 1 - MvPolynomial.C c) * r)
    omega

private lemma coeff_f {R : Type*} [CommRing R] [Nontrivial R] (C0 : Finset R) (a b : ℕ)
    (hab : a + b + 2 = C0.card + 1) :
    coeff (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      ((X 0 - X 1) * ∏ c ∈ C0, (X 0 + X 1 - MvPolynomial.C c))
      = (C0.card.choose a : R) - (C0.card.choose (a + 1) : R) := by
  obtain ⟨r, hr, hdeg⟩ := prod_struct C0
  rw [hr, mul_add, coeff_add, coeff_key C0.card a b hab]
  have hz : coeff (Finsupp.single (0 : Fin 2) (a + 1) + Finsupp.single (1 : Fin 2) (b + 1))
      ((X 0 - X 1) * r : MvPolynomial (Fin 2) R) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    rw [← Finsupp.degree_apply, degree_pair]
    have hd := totalDegree_mul (X 0 - X 1 : MvPolynomial (Fin 2) R) r
    have hd2 := totalDegree_XsubX (R := R)
    rcases hdeg with h | h
    · omega
    · rw [h, mul_zero, totalDegree_zero]
      omega
  rw [hz, add_zero]

private lemma choose_identity (m : ℕ) :
    (m + 1) * ((2 * m).choose (m + 1)) = m * ((2 * m).choose m) := by
  have key := Nat.add_one_mul_choose_eq (2 * m) m
  rw [Nat.choose_succ_succ] at key
  simp only [Nat.succ_eq_add_one] at key
  have keyz : (2 * (m : ℤ) + 1) * (((2 * m).choose m : ℕ) : ℤ)
      = ((((2 * m).choose m : ℕ) : ℤ) + (((2 * m).choose (m + 1) : ℕ) : ℤ)) * ((m : ℤ) + 1) := by
    exact_mod_cast key
  have : ((m : ℤ) + 1) * (((2 * m).choose (m + 1) : ℕ) : ℤ)
      = (m : ℤ) * (((2 * m).choose m : ℕ) : ℤ) := by linear_combination -keyz
  exact_mod_cast this

private lemma central_ne_zero (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (hm : 2 * m < p) :
    ((((2 * m).choose m : ℕ) : ZMod p)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hfac : ((2 * m).choose m) * Nat.factorial m * Nat.factorial (2 * m - m)
      = Nat.factorial (2 * m) :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have hdvd : p ∣ Nat.factorial (2 * m) := by
    rw [← hfac]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  have := (Nat.Prime.dvd_factorial hp).mp hdvd
  omega

private lemma choose_diff_ne_zero (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (hm : 2 * m < p) :
    ((((2 * m).choose m : ℕ) : ZMod p) - (((2 * m).choose (m + 1) : ℕ) : ZMod p)) ≠ 0 := by
  intro hzero
  have hcc : (((2 * m).choose m : ℕ) : ZMod p) = (((2 * m).choose (m + 1) : ℕ) : ZMod p) :=
    eq_of_sub_eq_zero hzero
  have h1z : ((m : ZMod p) + 1) * (((2 * m).choose (m + 1) : ℕ) : ZMod p)
      = (m : ZMod p) * (((2 * m).choose m : ℕ) : ZMod p) := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) (choose_identity m)
    push_cast at this
    linear_combination this
  exact central_ne_zero p hp m hm (by linear_combination h1z + ((m : ZMod p) + 1) * hcc)

private def sumset {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  ((A ×ˢ A).filter (fun q : ZMod p × ZMod p => q.1 ≠ q.2)).image
    (fun q : ZMod p × ZMod p => q.1 + q.2)

private lemma mem_sumset {p : ℕ} {A : Finset (ZMod p)} {x y : ZMod p}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) : x + y ∈ sumset A := by
  refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hx, hy⟩, hxy⟩

private lemma sumset_mono {p : ℕ} {A B : Finset (ZMod p)} (h : A ⊆ B) :
    sumset A ⊆ sumset B :=
  Finset.image_subset_image (Finset.filter_subset_filter _ (Finset.product_subset_product h h))

private lemma erdos_476_core (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (A : Finset (ZMod p))
    (hk : A.card = k + 3) (hkp : 2 * k + 2 < p) :
    2 * k + 3 ≤ (sumset A).card := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  by_contra hcon
  obtain ⟨C0, hDC, hC0card⟩ := Finset.exists_superset_card_eq
    (s := sumset A) (n := 2 * k + 2) (by omega) (by rw [ZMod.card]; omega)
  set f : MvPolynomial (Fin 2) (ZMod p) :=
    (X 0 - X 1) * ∏ c ∈ C0, (X 0 + X 1 - MvPolynomial.C c) with hf
  set t : Fin 2 →₀ ℕ :=
    Finsupp.single (0 : Fin 2) (k + 2) + Finsupp.single (1 : Fin 2) (k + 1) with ht
  have hcoeff : coeff t f ≠ 0 := by
    rw [ht, hf, coeff_f C0 (k + 1) k (by omega), hC0card,
      show 2 * k + 2 = 2 * (k + 1) by ring]
    exact choose_diff_ne_zero p hp (k + 1) (by omega)
  have htdeg : t.degree = 2 * k + 3 := by rw [ht, degree_pair]; ring
  have htot : f.totalDegree = t.degree := by
    refine le_antisymm ?_ ?_
    · have hprod : (∏ c ∈ C0, (X 0 + X 1 - MvPolynomial.C c)
          : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ C0.card := by
        refine le_trans (totalDegree_finsetProd _ _) ?_
        refine le_trans (Finset.sum_le_sum (fun c _ => totalDegree_lin c)) ?_
        simp
      have h2 := totalDegree_XsubX (R := ZMod p)
      have h3 : f.totalDegree ≤ (X 0 - X 1 : MvPolynomial (Fin 2) (ZMod p)).totalDegree
          + (∏ c ∈ C0, (X 0 + X 1 - MvPolynomial.C c)
              : MvPolynomial (Fin 2) (ZMod p)).totalDegree := by
        rw [hf]; exact totalDegree_mul _ _
      omega
    · have hmem : t ∈ f.support := mem_support_iff.mpr hcoeff
      have hle := MvPolynomial.le_totalDegree hmem
      simpa [Finsupp.degree_apply, Finsupp.sum] using hle
  have hSt : ∀ i : Fin 2, t i < A.card := by
    intro i
    rw [hk, ht]
    fin_cases i <;> simp
  obtain ⟨sv, hsv, hne⟩ := MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
    f t hcoeff htot (fun _ => A) hSt
  have heval : eval sv f = (sv 0 - sv 1) * ∏ c ∈ C0, (sv 0 + sv 1 - c) := by
    rw [hf]
    simp
  rw [heval] at hne
  have hd : sv 0 ≠ sv 1 := by
    intro h
    apply hne
    rw [h, sub_self, zero_mul]
  have hmemC : sv 0 + sv 1 ∈ C0 := hDC (mem_sumset (hsv 0) (hsv 1) hd)
  exact hne (by rw [Finset.prod_eq_zero hmemC (sub_self _), mul_zero])

theorem erdos_476 (p : ℕ) (hp : Nat.Prime p) (A : Finset (ZMod p)) :
    min (2 * (A.card : ℤ) - 3) (p : ℤ) ≤
      ((((A ×ˢ A).filter (fun q : ZMod p × ZMod p => q.1 ≠ q.2)).image
          (fun q : ZMod p × ZMod p => q.1 + q.2)).card : ℤ) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  show min (2 * (A.card : ℤ) - 3) (p : ℤ) ≤ ((sumset A).card : ℤ)
  have hnn : (0 : ℤ) ≤ ((sumset A).card : ℤ) := by exact_mod_cast Nat.zero_le _
  rcases Nat.lt_or_ge A.card 3 with hsmall | hbig
  · rcases Nat.lt_or_ge A.card 2 with h1 | h1
    · refine le_trans (min_le_left _ _) ?_
      have hc : (A.card : ℤ) ≤ 1 := by exact_mod_cast (by omega : A.card ≤ 1)
      linarith
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      have hpos : 1 ≤ (sumset A).card := Finset.card_pos.mpr ⟨_, mem_sumset ha hb hab⟩
      refine le_trans (min_le_left _ _) ?_
      have hc : (A.card : ℤ) = 2 := by exact_mod_cast (by omega : A.card = 2)
      have hc3 : (1 : ℤ) ≤ ((sumset A).card : ℤ) := by exact_mod_cast hpos
      linarith
  · obtain ⟨k, hk⟩ : ∃ k, A.card = k + 3 := ⟨A.card - 3, by omega⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hcard_le : A.card ≤ p := by
      have hcu := Finset.card_le_univ A
      rwa [ZMod.card] at hcu
    rcases Nat.lt_or_ge (2 * k + 2) p with hkp | hkp
    · have hcore := erdos_476_core p hp k A hk hkp
      refine le_trans (min_le_left _ _) ?_
      have hcz : (2 * (k : ℤ) + 3) ≤ ((sumset A).card : ℤ) := by exact_mod_cast hcore
      have hkz : (A.card : ℤ) = (k : ℤ) + 3 := by exact_mod_cast hk
      linarith
    · have hpne2 : p ≠ 2 := by
        rintro rfl
        omega
      obtain ⟨j, hj⟩ : ∃ j, p = 2 * j + 1 := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h hpne2
        · exact h
      obtain ⟨A', hA'sub, hA'card⟩ :=
        Finset.exists_subset_card_eq (s := A) (n := j + 2) (by omega)
      have hcore := erdos_476_core p hp (j - 1) A' (by omega) (by omega)
      have h1 : 2 * (j - 1) + 3 ≤ (sumset A).card :=
        le_trans hcore (Finset.card_le_card (sumset_mono hA'sub))
      refine le_trans (min_le_right _ _) ?_
      have hfin : p ≤ (sumset A).card := by omega
      exact_mod_cast hfin
