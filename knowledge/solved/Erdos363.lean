import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Totient

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-- Product of the block `[x, x+3]`. -/
private def blk (x : ℕ) : ℕ := ∏ m ∈ Finset.Icc x (x + 3), m

private lemma blk_ne_zero {x : ℕ} (hx : 1 ≤ x) : blk x ≠ 0 := by
  unfold blk
  rw [Finset.prod_ne_zero_iff]
  intro m hm
  rw [Finset.mem_Icc] at hm
  omega

private lemma prime_dvd_blk {p x : ℕ} (hx : 1 ≤ x) (hp : p.Prime) (h : p ∣ blk x) :
    p ≤ x + 3 := by
  unfold blk at h
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  rw [Finset.mem_Icc] at hm
  exact (Nat.le_of_dvd (by omega) hpm).trans hm.2

private lemma prod_blk_ne_zero {U : Finset ℕ} (hU : ∀ x ∈ U, 1 ≤ x) :
    ∏ x ∈ U, blk x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun x hx => blk_ne_zero (hU x hx)

private lemma prime_dvd_prod_blk {p : ℕ} {U : Finset ℕ} {B : ℕ} (hp : p.Prime)
    (hU1 : ∀ x ∈ U, 1 ≤ x) (hU : ∀ x ∈ U, x ≤ B) (h : p ∣ ∏ x ∈ U, blk x) : p ≤ B + 3 := by
  obtain ⟨x, hx, hpx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  exact (prime_dvd_blk (hU1 x hx) hp hpx).trans (by have := hU x hx; omega)

private lemma isSquare_of_even_factorization (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod (fun p k => p ^ (k / 2)), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro p _
  show p ^ n.factorization p = p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

private lemma even_symmdiff {S T : Finset ℕ} (hS : ∀ x ∈ S, 1 ≤ x) (hT : ∀ x ∈ T, 1 ≤ x)
    (p : ℕ)
    (hpar : Odd ((∏ x ∈ S, blk x).factorization p) ↔ Odd ((∏ x ∈ T, blk x).factorization p)) :
    Even ((∏ x ∈ (S \ T) ∪ (T \ S), blk x).factorization p) := by
  have h1 : ∏ x ∈ S, blk x = (∏ x ∈ S \ T, blk x) * ∏ x ∈ S ∩ T, blk x := by
    rw [← Finset.sdiff_inter_self_left S T, Finset.prod_sdiff Finset.inter_subset_left]
  have h2 : ∏ x ∈ T, blk x = (∏ x ∈ T \ S, blk x) * ∏ x ∈ S ∩ T, blk x := by
    rw [← Finset.sdiff_inter_self_right T S, Finset.prod_sdiff Finset.inter_subset_right]
  have h3 : ∏ x ∈ (S \ T) ∪ (T \ S), blk x = (∏ x ∈ S \ T, blk x) * ∏ x ∈ T \ S, blk x :=
    Finset.prod_union disjoint_sdiff_sdiff
  have nST : ∏ x ∈ S \ T, blk x ≠ 0 :=
    prod_blk_ne_zero fun x hx => hS x (Finset.mem_sdiff.mp hx).1
  have nTS : ∏ x ∈ T \ S, blk x ≠ 0 :=
    prod_blk_ne_zero fun x hx => hT x (Finset.mem_sdiff.mp hx).1
  have nI : ∏ x ∈ S ∩ T, blk x ≠ 0 :=
    prod_blk_ne_zero fun x hx => hS x (Finset.mem_inter.mp hx).1
  rw [h1, Nat.factorization_mul nST nI, h2, Nat.factorization_mul nTS nI] at hpar
  rw [h3, Nat.factorization_mul nST nTS]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.odd_iff, Nat.even_iff] at hpar ⊢
  omega

private lemma exists_square_collection (n : ℕ) :
    ∃ U : Finset ℕ, U.Nonempty ∧ (∀ x ∈ U, n < x ∧ x % 4 = 1) ∧
      IsSquare (∏ x ∈ U, blk x) := by
  set m := 3 * n + 5000 with hm
  set a := n / 4 + 1 with ha
  set X : Finset ℕ := (Finset.Ico a m).image (fun k => 4 * k + 1) with hX
  have hXmem : ∀ x ∈ X, n < x ∧ x % 4 = 1 ∧ x ≤ 4 * m := by
    intro x hx
    rw [hX, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_Ico] at hk
    omega
  have hXcard : X.card = m - a := by
    rw [hX, Finset.card_image_of_injective _ (fun k l h => by simpa using h), Nat.card_Ico]
  set Pr : Finset ℕ := (Finset.range (4 * m + 4)).filter Nat.Prime with hPr
  have hPrcard : Pr.card = Nat.primeCounting' (4 * m + 4) := by
    rw [hPr, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hpi : Nat.primeCounting' (4 * m + 4) < m - a := by
    have h1 := Nat.primeCounting'_add_le (a := 210) (k := 211) (by norm_num) (by norm_num)
      (4 * m + 4 - 211)
    have h2 : 211 + (4 * m + 4 - 211) = 4 * m + 4 := by omega
    rw [h2] at h1
    have h3 : Nat.primeCounting' 211 ≤ 211 := by
      rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
      exact (Finset.card_filter_le _ _).trans (Finset.card_range 211).le
    have h4 : Nat.totient 210 = 48 := by decide +kernel
    rw [h4] at h1
    omega
  have hlt : Pr.powerset.card < X.powerset.card := by
    rw [Finset.card_powerset, Finset.card_powerset, hXcard, hPrcard]
    exact Nat.pow_lt_pow_right (by norm_num) hpi
  set v : Finset ℕ → Finset ℕ :=
    fun S => Pr.filter (fun p => Odd ((∏ x ∈ S, blk x).factorization p)) with hv
  obtain ⟨S, hS, T, hT, hne, hvST⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := v) (fun S _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  rw [Finset.mem_powerset] at hS hT
  have hS1 : ∀ x ∈ S, 1 ≤ x := fun x hx => by have := hXmem x (hS hx); omega
  have hT1 : ∀ x ∈ T, 1 ≤ x := fun x hx => by have := hXmem x (hT hx); omega
  have hUX : ∀ x ∈ (S \ T) ∪ (T \ S), x ∈ X := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hx
    rcases hx with h | h
    · exact hS h.1
    · exact hT h.1
  refine ⟨(S \ T) ∪ (T \ S), ?_, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset,
      Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (Finset.Subset.antisymm h.1 h.2)
  · intro x hx
    exact ⟨(hXmem x (hUX x hx)).1, (hXmem x (hUX x hx)).2.1⟩
  · have hU1 : ∀ x ∈ (S \ T) ∪ (T \ S), 1 ≤ x := fun x hx => by
      have := hXmem x (hUX x hx); omega
    have hUB : ∀ x ∈ (S \ T) ∪ (T \ S), x ≤ 4 * m := fun x hx => (hXmem x (hUX x hx)).2.2
    apply isSquare_of_even_factorization _ (prod_blk_ne_zero hU1)
    intro p
    by_cases hp : p.Prime
    · by_cases hpm : p < 4 * m + 4
      · apply even_symmdiff hS1 hT1
        have hpPr : p ∈ Pr := by
          rw [hPr, Finset.mem_filter, Finset.mem_range]
          exact ⟨hpm, hp⟩
        have := congrArg (fun A => p ∈ A) hvST
        simp only [hv, Finset.mem_filter, hpPr, true_and, eq_iff_iff] at this
        exact this
      · rw [Nat.factorization_eq_zero_of_not_dvd]
        · exact ⟨0, rfl⟩
        · intro hdvd
          have := prime_dvd_prod_blk hp hU1 hUB hdvd
          omega
    · rw [(Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hp)]
      exact ⟨0, rfl⟩

theorem erdos_363 :
    Set.Infinite {𝓘 : Finset (Finset ℕ) |
      (∀ I ∈ 𝓘, 4 ≤ I.card ∧ 0 ∉ I ∧ ∃ a b : ℕ, I = Finset.Icc a b) ∧
      (𝓘 : Set (Finset ℕ)).PairwiseDisjoint id ∧
      IsSquare (∏ I ∈ 𝓘, ∏ m ∈ I, m)} := by
  intro hfin
  set N := hfin.toFinset.sup (fun 𝓙 : Finset (Finset ℕ) => 𝓙.sup (fun I => I.sup id)) with hN
  obtain ⟨U, hUne, hU, hsq⟩ := exists_square_collection N
  set 𝓘 : Finset (Finset ℕ) := U.image (fun x => Finset.Icc x (x + 3)) with h𝓘
  have hle1 : 𝓘.sup (fun I => I.sup id) ≤ N := by
    refine Finset.le_sup (f := fun 𝓙 : Finset (Finset ℕ) => 𝓙.sup (fun I => I.sup id)) ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro I hI
      rw [h𝓘, Finset.mem_image] at hI
      obtain ⟨x, hx, rfl⟩ := hI
      have := hU x hx
      refine ⟨?_, ?_, x, x + 3, rfl⟩
      · rw [Nat.card_Icc]; omega
      · rw [Finset.mem_Icc]; omega
    · intro I hI J hJ hne
      rw [Finset.mem_coe, h𝓘, Finset.mem_image] at hI hJ
      obtain ⟨x, hx, rfl⟩ := hI
      obtain ⟨y, hy, rfl⟩ := hJ
      have hxy : x ≠ y := fun h => hne (by rw [h])
      have h1 := hU x hx
      have h2 := hU y hy
      show Disjoint (Finset.Icc x (x + 3)) (Finset.Icc y (y + 3))
      rw [Finset.disjoint_left]
      intro z hz hz'
      rw [Finset.mem_Icc] at hz hz'
      omega
    · rw [h𝓘, Finset.prod_image]
      · exact hsq
      · intro x hx y hy h
        have h' : Finset.Icc x (x + 3) = Finset.Icc y (y + 3) := h
        have h1 := Finset.left_mem_Icc.mpr (show x ≤ x + 3 by omega)
        rw [h', Finset.mem_Icc] at h1
        have h2 := Finset.left_mem_Icc.mpr (show y ≤ y + 3 by omega)
        rw [← h', Finset.mem_Icc] at h2
        omega
  obtain ⟨x, hx⟩ := hUne
  have hxN := (hU x hx).1
  have hle2 : (Finset.Icc x (x + 3)).sup id ≤ 𝓘.sup (fun I => I.sup id) := by
    rw [h𝓘]
    exact Finset.le_sup (f := fun I : Finset ℕ => I.sup id)
      (Finset.mem_image_of_mem (fun x => Finset.Icc x (x + 3)) hx)
  have hle3 : x ≤ (Finset.Icc x (x + 3)).sup id :=
    Finset.le_sup (f := id) (Finset.left_mem_Icc.mpr (by omega))
  omega
