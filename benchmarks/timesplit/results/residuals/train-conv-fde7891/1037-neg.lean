namespace erdos_25820_neg_hyp_construction_ns
-- IMPORTS: Mathlib.Data.Fin.Tuple.Sort
open Filter

private def auxAdj (m : ℕ) (P Q : SimpleGraph (Fin m)) : Fin m ⊕ Fin m → Fin m ⊕ Fin m → Prop
  | Sum.inl i, Sum.inl j => P.Adj i j
  | Sum.inr i, Sum.inr j => Q.Adj i j
  | Sum.inl i, Sum.inr j => m ≤ i.val + j.val + 1
  | Sum.inr i, Sum.inl j => m ≤ i.val + j.val + 1

private def auxG (m : ℕ) (P Q : SimpleGraph (Fin m)) : SimpleGraph (Fin m ⊕ Fin m) where
  Adj := auxAdj m P Q
  symm := by
    refine ⟨fun x y h => ?_⟩
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        change P.Adj i j at h
        exact (show P.Adj j i from h.symm)
      | inr j =>
        change m ≤ i.val + j.val + 1 at h
        change m ≤ j.val + i.val + 1
        omega
    | inr i =>
      cases y with
      | inl j =>
        change m ≤ i.val + j.val + 1 at h
        change m ≤ j.val + i.val + 1
        omega
      | inr j =>
        change Q.Adj i j at h
        exact (show Q.Adj j i from h.symm)
  loopless := by
    refine ⟨fun x h => ?_⟩
    cases x with
    | inl i =>
      change P.Adj i i at h
      exact h.ne rfl
    | inr i =>
      change Q.Adj i i at h
      exact h.ne rfl

private lemma ncard_preimage_equiv {V W : Type*} (e : V ≃ W) (s : Set W) :
    (e ⁻¹' s).ncard = s.ncard := by
  have h : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      show e (e.symm y) ∈ s
      rw [e.apply_symm_apply]
      exact hy
  rw [h, Set.ncard_image_of_injective _ e.symm.injective]

private lemma ncard_nbr_comap {V W : Type*} (e : V ≃ W) (K : SimpleGraph W) (v : V) :
    ((K.comap e).neighborSet v).ncard = (K.neighborSet (e v)).ncard := by
  have h : (K.comap e).neighborSet v = e ⁻¹' K.neighborSet (e v) := by
    ext w
    exact Iff.rfl
  rw [h, ncard_preimage_equiv]

private lemma trivial_comap_equiv {V W : Type*} (e : V ≃ W) (K : SimpleGraph W) (s : Set V)
    (h : (K.comap e).IsIndepSet s ∨ (K.comap e).IsClique s) :
    K.IsIndepSet (e '' s) ∨ K.IsClique (e '' s) := by
  rcases h with h | h
  · left
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact h ha hb (fun hh => hab (by rw [hh]))
  · right
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact h ha hb (fun hh => hab (by rw [hh]))

private lemma trivial_compl {V : Type*} (K : SimpleGraph V) (u : Set V)
    (h : Kᶜ.IsIndepSet u ∨ Kᶜ.IsClique u) : K.IsIndepSet u ∨ K.IsClique u := by
  rcases h with h | h
  · right
    intro x hx y hy hxy
    by_contra hc
    exact h hx hy hxy (by rw [SimpleGraph.compl_adj]; exact ⟨hxy, hc⟩)
  · left
    intro x hx y hy hxy
    have h2 := h hx hy hxy
    rw [SimpleGraph.compl_adj] at h2
    exact h2.2

private lemma ncard_sum_split {α β : Type*} [Finite α] [Finite β] (T : Set (α ⊕ β)) :
    T.ncard = (Sum.inl ⁻¹' T).ncard + (Sum.inr ⁻¹' T).ncard := by
  have h1 : T = Sum.inl '' (Sum.inl ⁻¹' T) ∪ Sum.inr '' (Sum.inr ⁻¹' T) := by
    ext x
    rcases x with a | b <;> simp
  have hd : Disjoint (Sum.inl '' (Sum.inl ⁻¹' T) : Set (α ⊕ β)) (Sum.inr '' (Sum.inr ⁻¹' T)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
    cases hb
  calc T.ncard = (Sum.inl '' (Sum.inl ⁻¹' T) ∪ Sum.inr '' (Sum.inr ⁻¹' T)).ncard := by
        rw [← h1]
    _ = (Sum.inl '' (Sum.inl ⁻¹' T)).ncard + (Sum.inr '' (Sum.inr ⁻¹' T)).ncard :=
        Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
    _ = _ := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]

private lemma crossCount (m : ℕ) (i : Fin m) :
    {j : Fin m | m ≤ i.val + j.val + 1}.ncard = i.val + 1 := by
  have hi := i.isLt
  have h : (Fin.val '' {j : Fin m | m ≤ i.val + j.val + 1}) =
      ↑(Finset.Ico (m - 1 - i.val) m) := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have := j.isLt
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, show m ≤ i.val + x + 1 by omega, rfl⟩
  have h2 := Set.ncard_image_of_injective {j : Fin m | m ≤ i.val + j.val + 1} Fin.val_injective
  rw [← h2, h, Set.ncard_coe_finset, Nat.card_Ico]
  omega

private lemma auxG_deg_inl {m : ℕ} (P Q : SimpleGraph (Fin m)) (i : Fin m) :
    ((auxG m P Q).neighborSet (Sum.inl i)).ncard = (P.neighborSet i).ncard + i.val + 1 := by
  rw [ncard_sum_split]
  have h1 : Sum.inl ⁻¹' (auxG m P Q).neighborSet (Sum.inl i) = P.neighborSet i := by
    ext j
    exact Iff.rfl
  have h2 : Sum.inr ⁻¹' (auxG m P Q).neighborSet (Sum.inl i) =
      {j : Fin m | m ≤ i.val + j.val + 1} := by
    ext j
    exact Iff.rfl
  have h3 := crossCount m i
  rw [h1, h2]
  omega

private lemma auxG_deg_inr {m : ℕ} (P Q : SimpleGraph (Fin m)) (j : Fin m) :
    ((auxG m P Q).neighborSet (Sum.inr j)).ncard = (Q.neighborSet j).ncard + j.val + 1 := by
  rw [ncard_sum_split]
  have h1 : Sum.inl ⁻¹' (auxG m P Q).neighborSet (Sum.inr j) =
      {i : Fin m | m ≤ j.val + i.val + 1} := by
    ext i
    exact Iff.rfl
  have h2 : Sum.inr ⁻¹' (auxG m P Q).neighborSet (Sum.inr j) = Q.neighborSet j := by
    ext i
    exact Iff.rfl
  have h3 := crossCount m j
  rw [h1, h2]
  omega

private lemma auxG_trivial {m : ℕ} (P Q : SimpleGraph (Fin m)) (s : Set (Fin m ⊕ Fin m))
    (h : (auxG m P Q).IsIndepSet s ∨ (auxG m P Q).IsClique s) :
    (P.IsIndepSet (Sum.inl ⁻¹' s) ∨ P.IsClique (Sum.inl ⁻¹' s)) ∧
    (Q.IsIndepSet (Sum.inr ⁻¹' s) ∨ Q.IsClique (Sum.inr ⁻¹' s)) := by
  rcases h with h | h
  · refine ⟨Or.inl ?_, Or.inl ?_⟩
    · intro i hi j hj hij
      have hi' : (Sum.inl i : Fin m ⊕ Fin m) ∈ s := hi
      have hj' : (Sum.inl j : Fin m ⊕ Fin m) ∈ s := hj
      exact h hi' hj' (fun hh => hij (Sum.inl_injective hh))
    · intro i hi j hj hij
      have hi' : (Sum.inr i : Fin m ⊕ Fin m) ∈ s := hi
      have hj' : (Sum.inr j : Fin m ⊕ Fin m) ∈ s := hj
      exact h hi' hj' (fun hh => hij (Sum.inr_injective hh))
  · refine ⟨Or.inr ?_, Or.inr ?_⟩
    · intro i hi j hj hij
      have hi' : (Sum.inl i : Fin m ⊕ Fin m) ∈ s := hi
      have hj' : (Sum.inl j : Fin m ⊕ Fin m) ∈ s := hj
      exact h hi' hj' (fun hh => hij (Sum.inl_injective hh))
    · intro i hi j hj hij
      have hi' : (Sum.inr i : Fin m ⊕ Fin m) ∈ s := hi
      have hj' : (Sum.inr j : Fin m ⊕ Fin m) ∈ s := hj
      exact h hi' hj' (fun hh => hij (Sum.inr_injective hh))

private lemma compl_deg (m : ℕ) (H : SimpleGraph (Fin m)) (v : Fin m) :
    (Hᶜ.neighborSet v).ncard + (H.neighborSet v).ncard + 1 = m := by
  have hU : (Set.univ : Set (Fin m)) = (Hᶜ.neighborSet v ∪ H.neighborSet v) ∪ {v} := by
    ext w
    constructor
    · intro _
      simp only [Set.mem_union, Set.mem_singleton_iff]
      by_cases h1 : w = v
      · exact Or.inr h1
      · by_cases h2 : H.Adj v w
        · exact Or.inl (Or.inr h2)
        · refine Or.inl (Or.inl ?_)
          rw [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj]
          exact ⟨fun h => h1 h.symm, h2⟩
    · intro _
      exact Set.mem_univ _
  have hd1 : Disjoint (Hᶜ.neighborSet v) (H.neighborSet v) := by
    rw [Set.disjoint_left]
    intro w h1 h2
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj] at h1
    exact h1.2 h2
  have hd2 : Disjoint (Hᶜ.neighborSet v ∪ H.neighborSet v) {v} := by
    rw [Set.disjoint_right]
    intro w hw h
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rcases h with h | h <;> (rw [SimpleGraph.mem_neighborSet] at h; exact h.ne rfl)
  have := congrArg Set.ncard hU
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton] at this
  omega

private lemma fiber_le_one {m : ℕ} (f : Fin m → ℕ) (hf : StrictMono f) (d : ℕ) :
    {i | f i = d}.ncard ≤ 1 := by
  by_cases h : ∃ i, f i = d
  · obtain ⟨i0, hi0⟩ := h
    have hsub : {i | f i = d} ⊆ {i0} := by
      intro i hi
      rw [Set.mem_setOf_eq] at hi
      rw [Set.mem_singleton_iff]
      exact hf.injective (hi.trans hi0.symm)
    calc {i | f i = d}.ncard ≤ ({i0} : Set (Fin m)).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
  · push_neg at h
    have h' : {i | f i = d} = ∅ := by
      ext i
      simp [h i]
    rw [h', Set.ncard_empty]
    exact Nat.zero_le _

theorem erdos_25820_neg_hyp_construction :
    ∀ m : ℕ, 6 ≤ m → ∀ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 10 * (H.neighborSet v).ncard ≤ 3 * m) →
      ∃ G : SimpleGraph (Fin (2 * m)),
        (∀ d : ℕ, {v : Fin (2 * m) | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
        ((1 / 2 + 1 / 10) * ((2 * m : ℕ) : ℝ) <
          ((Set.range fun v : Fin (2 * m) => (G.neighborSet v).ncard).ncard : ℝ)) ∧
        ∀ s : Set (Fin (2 * m)), (G.IsIndepSet s ∨ G.IsClique s) →
          ∃ t u : Set (Fin m), (H.IsIndepSet t ∨ H.IsClique t) ∧
            (H.IsIndepSet u ∨ H.IsClique u) ∧ s.ncard ≤ t.ncard + u.ncard := by
  intro m hm H hH
  classical
  obtain ⟨σ, hσm⟩ : ∃ σ : Equiv.Perm (Fin m),
      Monotone (fun i => (H.neighborSet (σ i)).ncard) :=
    ⟨Tuple.sort (fun a => (H.neighborSet a).ncard),
      Tuple.monotone_sort (fun a => (H.neighborSet a).ncard)⟩
  obtain ⟨τ, hτm⟩ : ∃ τ : Equiv.Perm (Fin m),
      Monotone (fun i => (Hᶜ.neighborSet (τ i)).ncard) :=
    ⟨Tuple.sort (fun a => (Hᶜ.neighborSet a).ncard),
      Tuple.monotone_sort (fun a => (Hᶜ.neighborSet a).ncard)⟩
  have hfA : StrictMono (fun i : Fin m => (H.neighborSet (σ i)).ncard + i.val + 1) := by
    intro i j hij
    have h1 : (H.neighborSet (σ i)).ncard ≤ (H.neighborSet (σ j)).ncard := hσm hij.le
    have h2 : i.val < j.val := hij
    show (H.neighborSet (σ i)).ncard + i.val + 1 < (H.neighborSet (σ j)).ncard + j.val + 1
    omega
  have hfB : StrictMono (fun i : Fin m => (Hᶜ.neighborSet (τ i)).ncard + i.val + 1) := by
    intro i j hij
    have h1 : (Hᶜ.neighborSet (τ i)).ncard ≤ (Hᶜ.neighborSet (τ j)).ncard := hτm hij.le
    have h2 : i.val < j.val := hij
    show (Hᶜ.neighborSet (τ i)).ncard + i.val + 1 < (Hᶜ.neighborSet (τ j)).ncard + j.val + 1
    omega
  obtain ⟨G', hA, hB, hT⟩ : ∃ G' : SimpleGraph (Fin m ⊕ Fin m),
      (∀ i, (G'.neighborSet (Sum.inl i)).ncard = (H.neighborSet (σ i)).ncard + i.val + 1) ∧
      (∀ j, (G'.neighborSet (Sum.inr j)).ncard = (Hᶜ.neighborSet (τ j)).ncard + j.val + 1) ∧
      (∀ s : Set (Fin m ⊕ Fin m), (G'.IsIndepSet s ∨ G'.IsClique s) →
        (H.IsIndepSet (σ '' (Sum.inl ⁻¹' s)) ∨ H.IsClique (σ '' (Sum.inl ⁻¹' s))) ∧
        (H.IsIndepSet (τ '' (Sum.inr ⁻¹' s)) ∨ H.IsClique (τ '' (Sum.inr ⁻¹' s)))) := by
    refine ⟨auxG m (H.comap σ) (Hᶜ.comap τ), ?_, ?_, ?_⟩
    · intro i
      rw [auxG_deg_inl, ncard_nbr_comap]
    · intro j
      rw [auxG_deg_inr, ncard_nbr_comap]
    · intro s hs
      obtain ⟨h1, h2⟩ := auxG_trivial _ _ s hs
      exact ⟨trivial_comap_equiv σ H _ h1, trivial_compl H _ (trivial_comap_equiv τ Hᶜ _ h2)⟩
  obtain ⟨e⟩ : Nonempty (Fin (2 * m) ≃ Fin m ⊕ Fin m) :=
    ⟨(finCongr (two_mul m)).trans finSumFinEquiv.symm⟩
  have hdeg : ∀ v, ((G'.comap e).neighborSet v).ncard = (G'.neighborSet (e v)).ncard :=
    fun v => ncard_nbr_comap e G' v
  refine ⟨G'.comap e, ?_, ?_, ?_⟩
  · intro d
    have h1 : {v : Fin (2 * m) | ((G'.comap e).neighborSet v).ncard = d}
        = e ⁻¹' {x | (G'.neighborSet x).ncard = d} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hdeg]
    have h2 : Sum.inl ⁻¹' {x | (G'.neighborSet x).ncard = d}
        = {i : Fin m | (H.neighborSet (σ i)).ncard + i.val + 1 = d} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hA]
    have h3 : Sum.inr ⁻¹' {x | (G'.neighborSet x).ncard = d}
        = {j : Fin m | (Hᶜ.neighborSet (τ j)).ncard + j.val + 1 = d} := by
      ext j
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hB]
    have hA1 : {i : Fin m | (H.neighborSet (σ i)).ncard + i.val + 1 = d}.ncard ≤ 1 :=
      fiber_le_one _ hfA d
    have hB1 : {j : Fin m | (Hᶜ.neighborSet (τ j)).ncard + j.val + 1 = d}.ncard ≤ 1 :=
      fiber_le_one _ hfB d
    rw [h1, ncard_preimage_equiv, ncard_sum_split, h2, h3]
    exact le_trans (add_le_add hA1 hB1) (by norm_num)
  · have hrange : (Set.range fun v : Fin (2 * m) => ((G'.comap e).neighborSet v).ncard)
        = Set.range fun x => (G'.neighborSet x).ncard := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨e v, (hdeg v).symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e.symm x, by simp only [hdeg, Equiv.apply_symm_apply]⟩
    have hcount : 6 * m < 5 * (Set.range fun x => (G'.neighborSet x).ncard).ncard := by
      set SA : Finset ℕ :=
        Finset.univ.image (fun i : Fin m => (H.neighborSet (σ i)).ncard + i.val + 1) with hSA
      set SB : Finset ℕ :=
        Finset.univ.image (fun j : Fin m => (Hᶜ.neighborSet (τ j)).ncard + j.val + 1) with hSB
      have hcA : SA.card = m := by
        rw [hSA, Finset.card_image_of_injective _ hfA.injective, Finset.card_univ,
          Fintype.card_fin]
      have hcB : SB.card = m := by
        rw [hSB, Finset.card_image_of_injective _ hfB.injective, Finset.card_univ,
          Fintype.card_fin]
      have hsub : ((SA ∪ SB : Finset ℕ) : Set ℕ) ⊆ Set.range fun x => (G'.neighborSet x).ncard := by
        intro y hy
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hSA, hSB, Finset.mem_image,
          Finset.mem_univ, true_and] at hy
        rcases hy with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact ⟨Sum.inl i, hA i⟩
        · exact ⟨Sum.inr j, hB j⟩
      have hle : (SA ∪ SB).card ≤ (Set.range fun x => (G'.neighborSet x).ncard).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      have hinter : SA ∩ SB ⊆ Finset.Icc ((7 * m + 9) / 10) (13 * m / 10) := by
        intro y hy
        rw [Finset.mem_inter] at hy
        obtain ⟨hy1, hy2⟩ := hy
        simp only [hSA, Finset.mem_image, Finset.mem_univ, true_and] at hy1
        simp only [hSB, Finset.mem_image, Finset.mem_univ, true_and] at hy2
        obtain ⟨i, hi⟩ := hy1
        obtain ⟨j, hj⟩ := hy2
        have b1 := hH (σ i)
        have b2 := hH (τ j)
        have c2 := compl_deg m H (τ j)
        have li := i.isLt
        have lj := j.isLt
        rw [Finset.mem_Icc]
        omega
      have hic := Finset.card_le_card hinter
      rw [Nat.card_Icc] at hic
      have hu := Finset.card_union_add_card_inter SA SB
      omega
    rw [hrange]
    have hc : (6 * m : ℝ) < 5 * ((Set.range fun x => (G'.neighborSet x).ncard).ncard : ℝ) := by
      exact_mod_cast hcount
    push_cast
    linarith
  · intro s hs
    have hs' := trivial_comap_equiv e G' s hs
    obtain ⟨ht, hu⟩ := hT _ hs'
    refine ⟨σ '' (Sum.inl ⁻¹' (e '' s)), τ '' (Sum.inr ⁻¹' (e '' s)), ht, hu, ?_⟩
    have hcard : s.ncard = (σ '' (Sum.inl ⁻¹' (e '' s))).ncard +
        (τ '' (Sum.inr ⁻¹' (e '' s))).ncard := by
      rw [Set.ncard_image_of_injective _ σ.injective, Set.ncard_image_of_injective _ τ.injective,
        ← ncard_sum_split, Set.ncard_image_of_injective _ e.injective]
    exact hcard.le
end erdos_25820_neg_hyp_construction_ns

-- Derived from R3 and R4, the deterministic half-graph construction.
-- Put H on A = first copy of Fin m and Hᶜ on B = second copy.
-- Sort each class by nondecreasing internal degree and join a_i ~ b_j iff i + j ≥ m+1.
-- Then deg(a_i) = α_i + i and deg(b_j) = β_j + j, each strictly increasing within its class,
-- so every degree fibre has size ≤ 2.
-- A-degrees are ≤ m + Δ and B-degrees are ≥ m - Δ, with Δ ≤ 0.3m.
-- Hence the overlap is ≤ 2Δ+1 values and D ≥ 2m - 2Δ - 1 ≥ 1.4m - 1 > 1.2m once m ≥ 6.
-- R3: a trivial s of G meets A in a trivial set of H and B in a trivial set of Hᶜ,
-- which is also trivial in H since the roles of clique and independent set swap.
theorem erdos_25820_neg_hyp_construction :
    ∀ m : ℕ, 6 ≤ m → ∀ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 10 * (H.neighborSet v).ncard ≤ 3 * m) →
      ∃ G : SimpleGraph (Fin (2 * m)),
        (∀ d : ℕ, {v : Fin (2 * m) | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
        ((1 / 2 + 1 / 10) * ((2 * m : ℕ) : ℝ) <
          ((Set.range fun v : Fin (2 * m) => (G.neighborSet v).ncard).ncard : ℝ)) ∧
        ∀ s : Set (Fin (2 * m)), (G.IsIndepSet s ∨ G.IsClique s) →
          ∃ t u : Set (Fin m), (H.IsIndepSet t ∨ H.IsClique t) ∧
            (H.IsIndepSet u ∨ H.IsClique u) ∧ s.ncard ≤ t.ncard + u.ncard := by
  exact erdos_25820_neg_hyp_construction_ns.erdos_25820_neg_hyp_construction

-- CHECK: Set.ncard_le_ncard_of_injOn Set.ncard_image_of_injOn SimpleGraph.isIndepSet_iff SimpleGraph.isClique_iff SimpleGraph.boxProd_adj Set.ncard_univ Set.ncard_union_le

-- Derived conjecture (first-moment / Erdős 1947 counting): for t = ⌊3 ln k⌋ + 1 the expected number of
-- trivial t-sets in G(k,1/2) is at most 2 (k 2^{-(t-1)/2})^t / t! < 1 once t ≥ 2 log₂ k + 1, which holds for
-- t > 3 ln k ≥ 2.886 ln k + 1, i.e. for all k ≥ e^9. Hence some graph on Fin k has all trivial sets ≤ 3 ln k.
theorem erdos_25820_neg_hyp_ramsey_lower :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ k → ∃ R : SimpleGraph (Fin k),
      ∀ s : Set (Fin k), (R.IsIndepSet s ∨ R.IsClique s) →
        (s.ncard : ℝ) ≤ 3 * Real.log (k : ℝ) := by
  sorry

open Filter

def IsTrivialSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∨ G.IsClique s

theorem erdos_25820_neg :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) →
      ((1 / 2 + ε) * (n : ℝ) <
        ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) →
      ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ))) := by
  intro h
  obtain ⟨M1, hM1⟩ := erdos_25820_neg_hyp_ramsey_lower
  have hev := h (1 / 10) (by norm_num) 25
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨k, hk1, hk2, hkN⟩ : ∃ k : ℕ, M1 ≤ k ∧ 2 ≤ k ∧ N ≤ k :=
    ⟨M1 + N + 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := hM1 k hk1
  obtain ⟨e⟩ : Nonempty (Fin (4 * k) ≃ Fin 4 × Fin k) := ⟨finProdFinEquiv.symm⟩
  obtain ⟨H, hHadj⟩ : ∃ H : SimpleGraph (Fin (4 * k)), ∀ x y,
      H.Adj x y ↔ (R.Adj (e x).2 (e y).2 ∧ (e x).1 = (e y).1) :=
    ⟨SimpleGraph.comap e (SimpleGraph.boxProd (⊥ : SimpleGraph (Fin 4)) R),
      by intro x y; simp [SimpleGraph.boxProd_adj]⟩
  have hHdeg : ∀ v : Fin (4 * k), 10 * (H.neighborSet v).ncard ≤ 3 * (4 * k) := by
    intro v
    have hinj : Set.InjOn (fun w => (e w).2) (H.neighborSet v) := by
      intro a ha b hb hab
      rw [SimpleGraph.mem_neighborSet, hHadj] at ha
      rw [SimpleGraph.mem_neighborSet, hHadj] at hb
      apply e.injective
      exact Prod.ext (ha.2.symm.trans hb.2) hab
    have hle : (H.neighborSet v).ncard ≤ (Set.univ : Set (Fin k)).ncard :=
      Set.ncard_le_ncard_of_injOn (fun w => (e w).2) (fun a _ => Set.mem_univ _) hinj
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega
  have hlayer : ∀ t : Set (Fin (4 * k)), (H.IsIndepSet t ∨ H.IsClique t) → ∀ r : Fin 4,
      ((t ∩ {w | (e w).1 = r}).ncard : ℝ) ≤ 3 * Real.log (k : ℝ) := by
    intro t ht r
    have hinj : Set.InjOn (fun w => (e w).2) (t ∩ {w | (e w).1 = r}) := by
      intro a ha b hb hab
      have h1 : (e a).1 = r := ha.2
      have h2 : (e b).1 = r := hb.2
      apply e.injective
      exact Prod.ext (h1.trans h2.symm) hab
    have hkey : ∀ a ∈ t ∩ {w | (e w).1 = r}, ∀ b ∈ t ∩ {w | (e w).1 = r},
        (H.Adj a b ↔ R.Adj (e a).2 (e b).2) := by
      intro a ha b hb
      have h1 : (e a).1 = r := ha.2
      have h2 : (e b).1 = r := hb.2
      rw [hHadj]
      constructor
      · intro hab
        exact hab.1
      · intro hab
        exact ⟨hab, h1.trans h2.symm⟩
    have himg : R.IsIndepSet ((fun w => (e w).2) '' (t ∩ {w | (e w).1 = r})) ∨
        R.IsClique ((fun w => (e w).2) '' (t ∩ {w | (e w).1 = r})) := by
      rcases ht with hI | hC
      · left
        rw [SimpleGraph.isIndepSet_iff] at hI ⊢
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
        have hab : a ≠ b := fun h' => hne (by rw [h'])
        show ¬ R.Adj (e a).2 (e b).2
        exact fun hRab => hI ha.1 hb.1 hab ((hkey a ha b hb).mpr hRab)
      · right
        rw [SimpleGraph.isClique_iff] at hC ⊢
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
        have hab : a ≠ b := fun h' => hne (by rw [h'])
        show R.Adj (e a).2 (e b).2
        exact (hkey a ha b hb).mp (hC ha.1 hb.1 hab)
    have hb := hR _ himg
    rw [Set.ncard_image_of_injOn hinj] at hb
    exact hb
  have htot : ∀ t : Set (Fin (4 * k)), (H.IsIndepSet t ∨ H.IsClique t) →
      (t.ncard : ℝ) ≤ 12 * Real.log (k : ℝ) := by
    intro t ht
    have hcov : t ⊆ ((t ∩ {w | (e w).1 = 0} ∪ t ∩ {w | (e w).1 = 1}) ∪
        t ∩ {w | (e w).1 = 2}) ∪ t ∩ {w | (e w).1 = 3} := by
      intro w hw
      have h4 : ∀ r : Fin 4, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by decide
      rcases h4 (e w).1 with h' | h' | h' | h' <;> simp [hw, h']
    have hA0 := hlayer t ht 0
    have hA1 := hlayer t ht 1
    have hA2 := hlayer t ht 2
    have hA3 := hlayer t ht 3
    have hu1 := Set.ncard_union_le (t ∩ {w | (e w).1 = 0}) (t ∩ {w | (e w).1 = 1})
    have hu2 := Set.ncard_union_le (t ∩ {w | (e w).1 = 0} ∪ t ∩ {w | (e w).1 = 1})
      (t ∩ {w | (e w).1 = 2})
    have hu3 := Set.ncard_union_le ((t ∩ {w | (e w).1 = 0} ∪ t ∩ {w | (e w).1 = 1}) ∪
      t ∩ {w | (e w).1 = 2}) (t ∩ {w | (e w).1 = 3})
    have hsub := Set.ncard_le_ncard hcov
    have hnat : t.ncard ≤ (t ∩ {w | (e w).1 = 0}).ncard + (t ∩ {w | (e w).1 = 1}).ncard +
        (t ∩ {w | (e w).1 = 2}).ncard + (t ∩ {w | (e w).1 = 3}).ncard := by
      omega
    have hreal : (t.ncard : ℝ) ≤ ((t ∩ {w | (e w).1 = 0}).ncard : ℝ) +
        ((t ∩ {w | (e w).1 = 1}).ncard : ℝ) + ((t ∩ {w | (e w).1 = 2}).ncard : ℝ) +
        ((t ∩ {w | (e w).1 = 3}).ncard : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hm6 : 6 ≤ 4 * k := by omega
  obtain ⟨G, hGdeg, hGD, hGsub⟩ := erdos_25820_neg_hyp_construction (4 * k) hm6 H hHdeg
  obtain ⟨s, hs, hlt⟩ := hN (2 * (4 * k)) (by omega) G hGdeg hGD
  obtain ⟨t, u, ht, hu, hle⟩ := hGsub s hs
  have ht' := htot t ht
  have hu' := htot u hu
  have hle' : (s.ncard : ℝ) ≤ (t.ncard : ℝ) + (u.ncard : ℝ) := by exact_mod_cast hle
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hlogk := Real.log_nonneg hk'
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hcast : ((2 * (4 * k) : ℕ) : ℝ) = 8 * (k : ℝ) := by push_cast; ring
  rw [hcast, Real.log_mul (by norm_num) hk0] at hlt
  have h8 : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  linarith