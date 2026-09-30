open Filter

-- Follows from the Erdős first-moment argument on G(m, 0.9) plus Hoeffding and a union bound
-- (operator's Lemma 1); C = 21 suffices since ceil(20 ln 2m) <= 21 ln 2m for m >= 2.
-- Homogeneous sets are written out as IsIndepSet ∨ IsClique (defeq to IsTrivialSet).
namespace erdos_95105_hyp_dense_ramsey_ns
open Filter

-- PUBLISHED: P. Erdős, "Some remarks on the theory of graphs", Bull. Amer. Math. Soc. 53 (1947), 292–294
-- (probabilistic lower bound for diagonal Ramsey numbers R(k,k) > 2^{k/2}). Stated form: there is C such that
-- for all large r some graph on r vertices has every clique and every independent set of size at most C log r.
-- This is the p = 1/2 case of the first-moment argument; it has no degree condition, unlike the target.
theorem erdos_95105_hyp_dense_ramsey_hyp_erdos_ramsey :
    ∃ C : ℝ, ∀ᶠ r : ℕ in atTop, ∃ R : SimpleGraph (Fin r),
      ∀ s : Set (Fin r), (R.IsIndepSet s ∨ R.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log (r : ℝ) := by
  sorry

-- CONJECTURE (derived, deterministic blow-up): split Fin m into the 6 residue classes mod 6. Put a Ramsey
-- graph R_i on class i; the class has floor(m/6) or ceil(m/6) vertices, and both are large when m is large.
-- Let F be the disjoint union of the R_i, and let H be the complement of F.
-- Degrees: deg_F ≤ ceil(m/6) - 1, so deg_H ≥ m - ceil(m/6), which is ≥ 4m/5 once m ≥ 25.
-- Homogeneous sets: a clique of H is independent in F, so it is a union of 6 independent sets, one per
-- R_i, and has size ≤ 6 C log(ceil(m/6)). An independent set of H is a clique of F, so it lies in one class
-- and has size ≤ C log(ceil(m/6)). Both bounds are ≤ 6|C| log(2m).
-- If C < 0 the premise fails for large r (singletons), so the implication holds vacuously.
namespace erdos_95105_hyp_dense_ramsey_hyp_blowup_ns

open Filter

open Filter

open Filter

private lemma deg_bound (m : ℕ) (hm : 10 ≤ m) (G : SimpleGraph (Fin m))
    (hG : ∀ u v : Fin m, u.val % 10 ≠ v.val % 10 → G.Adj u v) (v : Fin m) :
    4 * m ≤ 5 * (G.neighborSet v).ncard := by
  have hsub : {u : Fin m | u.val % 10 ≠ v.val % 10} ⊆ G.neighborSet v := by
    intro u hu
    exact hG v u (Ne.symm hu)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_add_ncard_compl {u : Fin m | u.val % 10 ≠ v.val % 10}
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h3 : ({u : Fin m | u.val % 10 ≠ v.val % 10}ᶜ).ncard ≤ m / 10 + 1 := by
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun u : Fin m => u.val / 10)
      (s := {u : Fin m | u.val % 10 ≠ v.val % 10}ᶜ)
      (t := ((Finset.range (m / 10 + 1) : Finset ℕ) : Set ℕ)) ?_ ?_ (Set.toFinite _)) ?_
    · intro u _
      have := u.isLt
      have hlt : u.val / 10 < m / 10 + 1 := by omega
      exact Finset.mem_coe.2 (Finset.mem_range.2 hlt)
    · intro a ha b hb hab
      have ha' : a.val % 10 = v.val % 10 := by
        by_contra h
        exact ha h
      have hb' : b.val % 10 = v.val % 10 := by
        by_contra h
        exact hb h
      have hab' : a.val / 10 = b.val / 10 := hab
      apply Fin.ext
      omega
    · rw [Set.ncard_coe_finset, Finset.card_range]
  omega

private lemma clique_bound (m : ℕ) (G R : SimpleGraph (Fin m)) (B : ℝ)
    (hG : ∀ u v : Fin m, G.Adj u v → u.val % 10 = v.val % 10 → R.Adj u v)
    (hR : ∀ t : Set (Fin m), R.IsClique t → (t.ncard : ℝ) ≤ B)
    (s : Set (Fin m)) (hs : G.IsClique s) : (s.ncard : ℝ) ≤ 10 * B := by
  have hfin : s.Finite := Set.toFinite s
  rw [Set.ncard_eq_toFinset_card s hfin]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun u : Fin m => u.val % 10)
    (s := hfin.toFinset) (t := Finset.range 10) (by
      intro x _
      exact Finset.mem_range.2 (Nat.mod_lt _ (by norm_num : (0:ℕ) < 10)))
  have hfib : ∀ c ∈ Finset.range 10,
      (((hfin.toFinset.filter (fun u : Fin m => u.val % 10 = c)).card : ℕ) : ℝ) ≤ B := by
    intro c _
    have hcl : R.IsClique
        ((hfin.toFinset.filter (fun u : Fin m => u.val % 10 = c) : Finset (Fin m)) :
          Set (Fin m)) := by
      intro u hu w hw huw
      rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hu hw
      exact hG u w (hs hu.1 hw.1 huw) (hu.2.trans hw.2.symm)
    have := hR _ hcl
    rwa [Set.ncard_coe_finset] at this
  rw [hsum, Nat.cast_sum]
  calc ∑ c ∈ Finset.range 10,
        (((hfin.toFinset.filter (fun u : Fin m => u.val % 10 = c)).card : ℕ) : ℝ)
      ≤ ∑ c ∈ Finset.range 10, B := Finset.sum_le_sum hfib
    _ = 10 * B := by simp

theorem erdos_95105_hyp_dense_ramsey_hyp_blowup :
    ∀ C : ℝ, (∀ᶠ r : ℕ in atTop, ∃ R : SimpleGraph (Fin r),
      ∀ s : Set (Fin r), (R.IsIndepSet s ∨ R.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log (r : ℝ)) →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∃ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) ∧
      ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log ((2 * m : ℕ) : ℝ) := by
  intro C hC
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hC
  refine ⟨10 * |C|, Filter.eventually_atTop.2 ⟨max N 10, fun m hm => ?_⟩⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm10 : 10 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨R, hR⟩ := hN m hmN
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlogle : Real.log (m : ℝ) ≤ Real.log ((2 * m : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < m)
    · exact_mod_cast (by omega : m ≤ 2 * m)
  have hkey : C * Real.log (m : ℝ) ≤ |C| * Real.log ((2 * m : ℕ) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
      (mul_le_mul_of_nonneg_left hlogle (abs_nonneg C))
  have hnn : 0 ≤ |C| * Real.log ((2 * m : ℕ) : ℝ) :=
    mul_nonneg (abs_nonneg C) (le_trans hlog0 hlogle)
  refine ⟨{ Adj := fun u v => u ≠ v ∧ (u.val % 10 ≠ v.val % 10 ∨ R.Adj u v),
            symm := ?_, loopless := ?_ }, ?_, ?_⟩
  · constructor
    intro u v h
    rcases h with ⟨h1, h2 | h2⟩
    · exact ⟨Ne.symm h1, Or.inl (Ne.symm h2)⟩
    · exact ⟨Ne.symm h1, Or.inr h2.symm⟩
  · constructor
    intro u h
    rcases h with ⟨h1, _⟩
    exact h1 rfl
  · intro v
    apply deg_bound m hm10
    intro u w h
    exact ⟨fun e => h (congrArg (fun x : Fin m => x.val % 10) e), Or.inl h⟩
  · intro s hs
    rcases hs with hs | hs
    · have hRi : R.IsIndepSet s := by
        intro u hu w hw huw hadj
        exact hs hu hw huw ⟨huw, Or.inr hadj⟩
      have := hR s (Or.inl hRi)
      linarith
    · have := clique_bound m _ R (C * Real.log (m : ℝ))
        (fun u w h e => by
          rcases h with ⟨_, h2 | h2⟩
          · exact absurd e h2
          · exact h2)
        (fun t ht => hR t (Or.inr ht)) s hs
      linarith

end erdos_95105_hyp_dense_ramsey_hyp_blowup_ns

theorem erdos_95105_hyp_dense_ramsey_hyp_blowup :
    ∀ C : ℝ, (∀ᶠ r : ℕ in atTop, ∃ R : SimpleGraph (Fin r),
      ∀ s : Set (Fin r), (R.IsIndepSet s ∨ R.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log (r : ℝ)) →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∃ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) ∧
      ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log ((2 * m : ℕ) : ℝ) := by
  exact erdos_95105_hyp_dense_ramsey_hyp_blowup_ns.erdos_95105_hyp_dense_ramsey_hyp_blowup

open Filter

open Filter

theorem erdos_95105_hyp_dense_ramsey :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∃ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) ∧
      ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log ((2 * m : ℕ) : ℝ) := by
  obtain ⟨C, hC⟩ := erdos_95105_hyp_dense_ramsey_hyp_erdos_ramsey
  exact erdos_95105_hyp_dense_ramsey_hyp_blowup C hC
end erdos_95105_hyp_dense_ramsey_ns

theorem erdos_95105_hyp_dense_ramsey :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∃ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) ∧
      ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) →
        (s.ncard : ℝ) ≤ C * Real.log ((2 * m : ℕ) : ℝ) := by
  exact erdos_95105_hyp_dense_ramsey_ns.erdos_95105_hyp_dense_ramsey



-- Half-graph gadget (reduction R3): A = H sorted by degree, B = complement of H sorted by degree,
-- a_i ~ b_j iff i + j > m. Then deg(a_i) = d_H(a_i) + i and deg(b_j) = d_Hbar(b_j) + j are strictly
-- increasing within each part, so every degree fibre has size <= 2.
-- With min degree >= 0.8m, fewer than 0.4m values are shared, so distinct >= 1.6m + 1 > 0.75 * 2m.
-- A homogeneous set of G meets each part in a homogeneous set of H, so its size is <= 2K.
namespace erdos_95105_hyp_gadget_ns
-- IMPORTS: Mathlib.Data.Fin.Tuple.Sort
open Filter

open Filter

private def gAdj {m : ℕ} (P Q : SimpleGraph (Fin m)) (σ τ : Equiv.Perm (Fin m)) :
    Fin m ⊕ Fin m → Fin m ⊕ Fin m → Prop
  | Sum.inl a, Sum.inl b => P.Adj (σ a) (σ b)
  | Sum.inr a, Sum.inr b => Q.Adj (τ a) (τ b)
  | Sum.inl i, Sum.inr j => m ≤ i.val + j.val + 1
  | Sum.inr j, Sum.inl i => m ≤ i.val + j.val + 1

private def mkG {m : ℕ} (P Q : SimpleGraph (Fin m)) (σ τ : Equiv.Perm (Fin m)) :
    SimpleGraph (Fin m ⊕ Fin m) where
  Adj := gAdj P Q σ τ
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact ((show P.Adj (σ a) (σ b) from h).symm : P.Adj (σ b) (σ a))
    · exact (show m ≤ a.val + b.val + 1 from h)
    · exact (show m ≤ b.val + a.val + 1 from h)
    · exact ((show Q.Adj (τ a) (τ b) from h).symm : Q.Adj (τ b) (τ a))⟩
  loopless := ⟨by
    rintro (a | a) h
    · exact (show P.Adj (σ a) (σ a) from h).ne rfl
    · exact (show Q.Adj (τ a) (τ a) from h).ne rfl⟩

private lemma ncard_sum_split {α β : Type*} [Finite α] [Finite β] (S : Set (α ⊕ β)) :
    S.ncard = (Sum.inl ⁻¹' S).ncard + (Sum.inr ⁻¹' S).ncard := by
  have h1 : S = Sum.inl '' (Sum.inl ⁻¹' S) ∪ Sum.inr '' (Sum.inr ⁻¹' S) := by
    ext x
    rcases x with a | b
    · constructor
      · intro h
        exact Set.mem_union_left _ ⟨a, h, rfl⟩
      · rintro (⟨a', h, e⟩ | ⟨b', h, e⟩)
        · cases e
          exact h
        · cases e
    · constructor
      · intro h
        exact Set.mem_union_right _ ⟨b, h, rfl⟩
      · rintro (⟨a', h, e⟩ | ⟨b', h, e⟩)
        · cases e
        · cases e
          exact h
  have hd : Disjoint (Sum.inl '' (Sum.inl ⁻¹' S) : Set (α ⊕ β)) (Sum.inr '' (Sum.inr ⁻¹' S)) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    cases hb
  calc S.ncard = (Sum.inl '' (Sum.inl ⁻¹' S) ∪ Sum.inr '' (Sum.inr ⁻¹' S)).ncard :=
        congrArg Set.ncard h1
    _ = (Sum.inl '' (Sum.inl ⁻¹' S)).ncard + (Sum.inr '' (Sum.inr ⁻¹' S)).ncard :=
        Set.ncard_union_eq hd
    _ = _ := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]

private lemma ncard_le_one_of {α : Type*} [Finite α] (s : Set α)
    (h : ∀ a ∈ s, ∀ b ∈ s, a = b) : s.ncard ≤ 1 := by
  rcases s.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · rw [he, Set.ncard_empty]
    omega
  · have hs : s ⊆ {a} := fun b hb => by
      rw [Set.mem_singleton_iff]
      exact h b hb a ha
    calc s.ncard ≤ ({a} : Set α).ncard := Set.ncard_le_ncard hs
      _ = 1 := Set.ncard_singleton a

private lemma ncard_preimage_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (S : Set (Fin m)) :
    (σ ⁻¹' S).ncard = S.ncard := by
  rw [← Set.ncard_image_of_injective (σ ⁻¹' S) σ.injective, Set.image_preimage_eq S σ.surjective]

private lemma card_half1 (m k : ℕ) (hk : k < m) :
    ({x : Fin m | m ≤ x.val + k + 1} : Set (Fin m)).ncard = k + 1 := by
  have h : (Fin.val '' ({x : Fin m | m ≤ x.val + k + 1} : Set (Fin m)))
      = ((Finset.Ico (m - 1 - k) m : Finset ℕ) : Set ℕ) := by
    ext n
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by omega, x.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n, h2⟩, by show m ≤ n + k + 1; omega, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, h, Set.ncard_coe_finset, Nat.card_Ico]
  omega

private lemma card_half2 (m k : ℕ) (hk : k < m) :
    ({x : Fin m | m ≤ k + x.val + 1} : Set (Fin m)).ncard = k + 1 := by
  have h : (Fin.val '' ({x : Fin m | m ≤ k + x.val + 1} : Set (Fin m)))
      = ((Finset.Ico (m - 1 - k) m : Finset ℕ) : Set ℕ) := by
    ext n
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by omega, x.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n, h2⟩, by show m ≤ k + n + 1; omega, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, h, Set.ncard_coe_finset, Nat.card_Ico]
  omega

private lemma compl_bound {m : ℕ} (H : SimpleGraph (Fin m)) (v : Fin m) :
    (Hᶜ.neighborSet v).ncard + (H.neighborSet v).ncard + 1 ≤ m := by
  have d1 : Disjoint (Hᶜ.neighborSet v) (H.neighborSet v) := by
    rw [Set.disjoint_left]
    intro w h1 h2
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj] at h1
    exact h1.2 h2
  have d2 : Disjoint (Hᶜ.neighborSet v ∪ H.neighborSet v) {v} := by
    rw [Set.disjoint_left]
    intro w hw hwv
    rw [Set.mem_singleton_iff] at hwv
    rw [hwv] at hw
    rcases hw with h | h
    · exact (show Hᶜ.Adj v v from h).ne rfl
    · exact (show H.Adj v v from h).ne rfl
  have hsub : Hᶜ.neighborSet v ∪ H.neighborSet v ∪ {v} ⊆ Set.univ := Set.subset_univ _
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq d2, Set.ncard_union_eq d1, Set.ncard_singleton, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin] at this
  exact this

private lemma img_bound {m : ℕ} (H : SimpleGraph (Fin m)) (K : ℝ)
    (hK : ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) → (s.ncard : ℝ) ≤ K)
    (σ : Equiv.Perm (Fin m)) (S : Set (Fin m))
    (h : (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ H.Adj (σ a) (σ b)) ∨
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj (σ a) (σ b))) :
    (S.ncard : ℝ) ≤ K := by
  have hhom : H.IsIndepSet (σ '' S) ∨ H.IsClique (σ '' S) := by
    rcases h with h | h
    · left
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact h a ha b hb (fun e => hxy (by rw [e]))
    · right
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact h a ha b hb (fun e => hxy (by rw [e]))
  have := hK _ hhom
  rwa [Set.ncard_image_of_injective _ σ.injective] at this

private lemma core (m : ℕ) (K : ℝ) (hm : 1 ≤ m) (H : SimpleGraph (Fin m))
    (hdeg : ∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard)
    (hK : ∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) → (s.ncard : ℝ) ≤ K) :
    ∃ G' : SimpleGraph (Fin m ⊕ Fin m),
      (∀ d : ℕ, {w | (G'.neighborSet w).ncard = d}.ncard ≤ 2) ∧
      3 * m < 2 * (Set.range fun w => (G'.neighborSet w).ncard).ncard ∧
      ∀ t : Set (Fin m ⊕ Fin m), (G'.IsIndepSet t ∨ G'.IsClique t) → (t.ncard : ℝ) ≤ 2 * K := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin m), Monotone (fun i => (H.neighborSet (σ i)).ncard) :=
    ⟨Tuple.sort (fun v => (H.neighborSet v).ncard),
      Tuple.monotone_sort (fun v => (H.neighborSet v).ncard)⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin m), Monotone (fun i => (Hᶜ.neighborSet (τ i)).ncard) :=
    ⟨Tuple.sort (fun v => (Hᶜ.neighborSet v).ncard),
      Tuple.monotone_sort (fun v => (Hᶜ.neighborSet v).ncard)⟩
  have hA : ∀ i : Fin m, ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard
      = (H.neighborSet (σ i)).ncard + (i.val + 1) := by
    intro i
    have e1 : (Sum.inl ⁻¹' ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)) : Set (Fin m))
        = σ ⁻¹' H.neighborSet (σ i) := by
      ext a; exact Iff.rfl
    have e2 : (Sum.inr ⁻¹' ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)) : Set (Fin m))
        = {x : Fin m | m ≤ i.val + x.val + 1} := by
      ext a; exact Iff.rfl
    rw [ncard_sum_split ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)), e1, e2,
      ncard_preimage_perm, card_half2 m i.val i.isLt]
  have hB : ∀ j : Fin m, ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard
      = (Hᶜ.neighborSet (τ j)).ncard + (j.val + 1) := by
    intro j
    have e1 : (Sum.inl ⁻¹' ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)) : Set (Fin m))
        = {x : Fin m | m ≤ x.val + j.val + 1} := by
      ext a; exact Iff.rfl
    have e2 : (Sum.inr ⁻¹' ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)) : Set (Fin m))
        = τ ⁻¹' Hᶜ.neighborSet (τ j) := by
      ext a; exact Iff.rfl
    rw [ncard_sum_split ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)), e1, e2,
      ncard_preimage_perm, card_half1 m j.val j.isLt]
    omega
  have injA : ∀ a b : Fin m, ((mkG H Hᶜ σ τ).neighborSet (Sum.inl a)).ncard
      = ((mkG H Hᶜ σ τ).neighborSet (Sum.inl b)).ncard → a = b := by
    intro a b h
    rw [hA, hA] at h
    rcases lt_trichotomy a b with hl | he | hl
    · have h2 : (H.neighborSet (σ a)).ncard ≤ (H.neighborSet (σ b)).ncard := hσ hl.le
      have h3 : a.val < b.val := hl
      omega
    · exact he
    · have h2 : (H.neighborSet (σ b)).ncard ≤ (H.neighborSet (σ a)).ncard := hσ hl.le
      have h3 : b.val < a.val := hl
      omega
  have injB : ∀ a b : Fin m, ((mkG H Hᶜ σ τ).neighborSet (Sum.inr a)).ncard
      = ((mkG H Hᶜ σ τ).neighborSet (Sum.inr b)).ncard → a = b := by
    intro a b h
    rw [hB, hB] at h
    rcases lt_trichotomy a b with hl | he | hl
    · have h2 : (Hᶜ.neighborSet (τ a)).ncard ≤ (Hᶜ.neighborSet (τ b)).ncard := hτ hl.le
      have h3 : a.val < b.val := hl
      omega
    · exact he
    · have h2 : (Hᶜ.neighborSet (τ b)).ncard ≤ (Hᶜ.neighborSet (τ a)).ncard := hτ hl.le
      have h3 : b.val < a.val := hl
      omega
  refine ⟨mkG H Hᶜ σ τ, ?_, ?_, ?_⟩
  · intro d
    rw [ncard_sum_split {w | ((mkG H Hᶜ σ τ).neighborSet w).ncard = d}]
    have a1 : (Sum.inl ⁻¹' {w | ((mkG H Hᶜ σ τ).neighborSet w).ncard = d} :
        Set (Fin m)).ncard ≤ 1 := by
      apply ncard_le_one_of
      intro a ha b hb
      have ha' : ((mkG H Hᶜ σ τ).neighborSet (Sum.inl a)).ncard = d := ha
      have hb' : ((mkG H Hᶜ σ τ).neighborSet (Sum.inl b)).ncard = d := hb
      exact injA a b (ha'.trans hb'.symm)
    have a2 : (Sum.inr ⁻¹' {w | ((mkG H Hᶜ σ τ).neighborSet w).ncard = d} :
        Set (Fin m)).ncard ≤ 1 := by
      apply ncard_le_one_of
      intro a ha b hb
      have ha' : ((mkG H Hᶜ σ τ).neighborSet (Sum.inr a)).ncard = d := ha
      have hb' : ((mkG H Hᶜ σ τ).neighborSet (Sum.inr b)).ncard = d := hb
      exact injB a b (ha'.trans hb'.symm)
    omega
  · have hJ : ({j : Fin m | 2 * j.val ≤ m} : Set (Fin m)).ncard = m / 2 + 1 := by
      have h : Fin.val '' ({j : Fin m | 2 * j.val ≤ m} : Set (Fin m))
          = ((Finset.range (m / 2 + 1) : Finset ℕ) : Set ℕ) := by
        ext n
        simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
        constructor
        · rintro ⟨x, hx, rfl⟩
          omega
        · intro hn
          exact ⟨⟨n, by omega⟩, by show 2 * n ≤ m; omega, rfl⟩
      rw [← Set.ncard_image_of_injective _ Fin.val_injective, h, Set.ncard_coe_finset,
        Finset.card_range]
    have injA' : Function.Injective
        (fun i : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard) := by
      intro a b h
      exact injA a b h
    have injB' : Function.Injective
        (fun j : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard) := by
      intro a b h
      exact injB a b h
    have hSA : ((fun i : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard) ''
        Set.univ).ncard = m := by
      rw [Set.ncard_image_of_injective _ injA', Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hSB : ((fun j : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard) ''
        {j : Fin m | 2 * j.val ≤ m}).ncard = m / 2 + 1 := by
      rw [Set.ncard_image_of_injective _ injB', hJ]
    have hdisj : Disjoint
        ((fun i : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard) '' Set.univ)
        ((fun j : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard) ''
          {j : Fin m | 2 * j.val ≤ m}) := by
      rw [Set.disjoint_left]
      rintro x ⟨i, -, rfl⟩ ⟨j, hj, hji⟩
      have hji' : ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard
          = ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard := hji
      rw [hA, hB] at hji'
      have hj' : 2 * j.val ≤ m := hj
      have c1 := hdeg (σ i)
      have c2 := hdeg (τ j)
      have c3 := compl_bound H (τ j)
      omega
    have hsub : ((fun i : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inl i)).ncard) ''
        Set.univ) ∪
        ((fun j : Fin m => ((mkG H Hᶜ σ τ).neighborSet (Sum.inr j)).ncard) ''
          {j : Fin m | 2 * j.val ≤ m}) ⊆
        Set.range fun w => ((mkG H Hᶜ σ τ).neighborSet w).ncard := by
      rintro x (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
    have hle := Set.ncard_le_ncard hsub (Set.finite_range _)
    rw [Set.ncard_union_eq hdisj (Set.finite_univ.image _) ((Set.toFinite _).image _),
      hSA, hSB] at hle
    omega
  · intro t ht
    rw [ncard_sum_split t]
    have hL : ((Sum.inl ⁻¹' t : Set (Fin m)).ncard : ℝ) ≤ K := by
      apply img_bound H K hK σ
      rcases ht with ht | ht
      · left
        intro a ha b hb hab
        have ha' : (Sum.inl a : Fin m ⊕ Fin m) ∈ t := ha
        have hb' : (Sum.inl b : Fin m ⊕ Fin m) ∈ t := hb
        exact ht ha' hb' (fun e => hab (Sum.inl_injective e))
      · right
        intro a ha b hb hab
        have ha' : (Sum.inl a : Fin m ⊕ Fin m) ∈ t := ha
        have hb' : (Sum.inl b : Fin m ⊕ Fin m) ∈ t := hb
        exact ht ha' hb' (fun e => hab (Sum.inl_injective e))
    have hR : ((Sum.inr ⁻¹' t : Set (Fin m)).ncard : ℝ) ≤ K := by
      apply img_bound H K hK τ
      rcases ht with ht | ht
      · right
        intro a ha b hb hab
        have ha' : (Sum.inr a : Fin m ⊕ Fin m) ∈ t := ha
        have hb' : (Sum.inr b : Fin m ⊕ Fin m) ∈ t := hb
        have h1 : ¬ Hᶜ.Adj (τ a) (τ b) := ht ha' hb' (fun e => hab (Sum.inr_injective e))
        rw [SimpleGraph.compl_adj] at h1
        by_contra h2
        exact h1 ⟨fun e => hab (τ.injective e), h2⟩
      · left
        intro a ha b hb hab
        have ha' : (Sum.inr a : Fin m ⊕ Fin m) ∈ t := ha
        have hb' : (Sum.inr b : Fin m ⊕ Fin m) ∈ t := hb
        have h1 : Hᶜ.Adj (τ a) (τ b) := ht ha' hb' (fun e => hab (Sum.inr_injective e))
        rw [SimpleGraph.compl_adj] at h1
        exact h1.2
    push_cast
    linarith

private lemma transfer {V W : Type*} (e : V ≃ W) (G' : SimpleGraph V) (B : ℝ)
    (h1 : ∀ d : ℕ, {v | (G'.neighborSet v).ncard = d}.ncard ≤ 2)
    (h3 : ∀ t : Set V, (G'.IsIndepSet t ∨ G'.IsClique t) → (t.ncard : ℝ) ≤ B) :
    ∃ G : SimpleGraph W,
      (∀ d : ℕ, {w | (G.neighborSet w).ncard = d}.ncard ≤ 2) ∧
      (Set.range fun w => (G.neighborSet w).ncard) =
        (Set.range fun v => (G'.neighborSet v).ncard) ∧
      ∀ s : Set W, (G.IsIndepSet s ∨ G.IsClique s) → (s.ncard : ℝ) ≤ B := by
  let G : SimpleGraph W :=
    { Adj := fun x y => G'.Adj (e.symm x) (e.symm y)
      symm := ⟨by
        intro x y h
        exact (show G'.Adj (e.symm x) (e.symm y) from h).symm⟩
      loopless := ⟨by
        intro x h
        exact (show G'.Adj (e.symm x) (e.symm x) from h).ne rfl⟩ }
  have hN : ∀ w, G.neighborSet w = e '' G'.neighborSet (e.symm w) := by
    intro w
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      show G'.Adj (e.symm w) (e.symm (e z))
      rw [e.symm_apply_apply]
      exact hz
  have hdeg : ∀ w, (G.neighborSet w).ncard = (G'.neighborSet (e.symm w)).ncard := by
    intro w
    rw [hN w, Set.ncard_image_of_injective _ e.injective]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro d
    have hset : {w | (G.neighborSet w).ncard = d} = e '' {v | (G'.neighborSet v).ncard = d} := by
      ext w
      simp only [Set.mem_setOf_eq, hdeg, Set.mem_image]
      constructor
      · intro h
        exact ⟨e.symm w, h, e.apply_symm_apply w⟩
      · rintro ⟨v, hv, rfl⟩
        rw [e.symm_apply_apply]
        exact hv
    rw [hset, Set.ncard_image_of_injective _ e.injective]
    exact h1 d
  · ext d
    simp only [Set.mem_range, hdeg]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨e.symm w, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨e v, by rw [e.symm_apply_apply]⟩
  · intro s hs
    have hhom : G'.IsIndepSet (e.symm '' s) ∨ G'.IsClique (e.symm '' s) := by
      rcases hs with hs | hs
      · left
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        exact hs ha hb hab
      · right
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        exact hs ha hb hab
    have := h3 _ hhom
    rwa [Set.ncard_image_of_injective _ e.symm.injective] at this

theorem erdos_95105_hyp_gadget :
    ∀ (m : ℕ) (K : ℝ), 1 ≤ m → ∀ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) →
      (∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) → (s.ncard : ℝ) ≤ K) →
      ∃ G : SimpleGraph (Fin (2 * m)),
        (∀ d : ℕ, {v : Fin (2 * m) | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
        ((1 / 2 + 1 / 4) * ((2 * m : ℕ) : ℝ) <
          ((Set.range fun v : Fin (2 * m) => (G.neighborSet v).ncard).ncard : ℝ)) ∧
        ∀ s : Set (Fin (2 * m)), (G.IsIndepSet s ∨ G.IsClique s) → (s.ncard : ℝ) ≤ 2 * K := by
  intro m K hm H hdeg hK
  obtain ⟨G', h1, h2, h3⟩ := core m K hm H hdeg hK
  obtain ⟨G, g1, g2, g3⟩ :=
    transfer (finSumFinEquiv.trans (finCongr (two_mul m).symm)) G' (2 * K) h1 h3
  refine ⟨G, g1, ?_, g3⟩
  rw [g2]
  have h2' : (3 * m : ℝ) < 2 * ((Set.range fun w => (G'.neighborSet w).ncard).ncard : ℝ) := by
    exact_mod_cast h2
  push_cast
  linarith
end erdos_95105_hyp_gadget_ns

theorem erdos_95105_hyp_gadget :
    ∀ (m : ℕ) (K : ℝ), 1 ≤ m → ∀ H : SimpleGraph (Fin m),
      (∀ v : Fin m, 4 * m ≤ 5 * (H.neighborSet v).ncard) →
      (∀ s : Set (Fin m), (H.IsIndepSet s ∨ H.IsClique s) → (s.ncard : ℝ) ≤ K) →
      ∃ G : SimpleGraph (Fin (2 * m)),
        (∀ d : ℕ, {v : Fin (2 * m) | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
        ((1 / 2 + 1 / 4) * ((2 * m : ℕ) : ℝ) <
          ((Set.range fun v : Fin (2 * m) => (G.neighborSet v).ncard).ncard : ℝ)) ∧
        ∀ s : Set (Fin (2 * m)), (G.IsIndepSet s ∨ G.IsClique s) → (s.ncard : ℝ) ≤ 2 * K := by
  exact erdos_95105_hyp_gadget_ns.erdos_95105_hyp_gadget



open Filter

def IsTrivialSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∨ G.IsClique s

theorem erdos_95105 :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) →
      ((1 / 2 + ε) * (n : ℝ) <
        ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) →
      ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ))) := by
  intro h
  obtain ⟨C, hC⟩ := erdos_95105_hyp_dense_ramsey
  have hP := h (1 / 4) (by norm_num) (2 * C)
  rw [Filter.eventually_atTop] at hP hC
  obtain ⟨N, hN⟩ := hP
  obtain ⟨M, hM⟩ := hC
  obtain ⟨H, hdeg, htriv⟩ := hM (N + M + 1) (by omega)
  obtain ⟨G, hfib, hdist, hG⟩ :=
    erdos_95105_hyp_gadget (N + M + 1) (C * Real.log ((2 * (N + M + 1) : ℕ) : ℝ))
      (by omega) H hdeg htriv
  obtain ⟨s, hs, hlt⟩ := hN (2 * (N + M + 1)) (by omega) G hfib hdist
  have h3 := hG s hs
  have h4 : 2 * C * Real.log ((2 * (N + M + 1) : ℕ) : ℝ)
      = 2 * (C * Real.log ((2 * (N + M + 1) : ℕ) : ℝ)) := by ring
  linarith