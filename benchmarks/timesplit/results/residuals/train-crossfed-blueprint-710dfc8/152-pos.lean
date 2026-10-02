open scoped Pointwise

def SidonN (A : Set ℕ) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

noncomputable def isoCount (A : Set ℕ) : ℕ :=
  {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard

def diffSet (A : Set ℕ) : Set ℤ :=
  {u : ℤ | ∃ a ∈ A, ∃ b ∈ A, u = (a : ℤ) - (b : ℤ)}

noncomputable def diffRuns (A : Set ℕ) : ℕ :=
  {u : ℤ | u ∈ diffSet A ∧ u + 1 ∉ diffSet A}.ncard

-- Sidon sets of every size exist, e.g. {2^i : i < n}; elementary.
namespace erdos_92759_hyp_exists_ns
open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

private lemma sidon_insert (A : Set ℕ) (m x : ℕ) (hA : SidonN A)
    (hm : ∀ a ∈ A, a ≤ m) (hx : 2 * m < x) : SidonN (insert x A) := by
  unfold SidonN at hA ⊢
  intro i₁ h1 j₁ h2 i₂ h3 j₂ h4 heq
  have b1 : i₁ = x ∨ (i₁ ∈ A ∧ i₁ ≤ m) := by
    rcases Set.mem_insert_iff.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have b2 : j₁ = x ∨ (j₁ ∈ A ∧ j₁ ≤ m) := by
    rcases Set.mem_insert_iff.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have b3 : i₂ = x ∨ (i₂ ∈ A ∧ i₂ ≤ m) := by
    rcases Set.mem_insert_iff.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have b4 : j₂ = x ∨ (j₂ ∈ A ∧ j₂ ≤ m) := by
    rcases Set.mem_insert_iff.mp h4 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  rcases b1 with e1 | ⟨m1, l1⟩ <;> rcases b2 with e2 | ⟨m2, l2⟩ <;>
    rcases b3 with e3 | ⟨m3, l3⟩ <;> rcases b4 with e4 | ⟨m4, l4⟩
  all_goals first
    | exact hA _ m1 _ m2 _ m3 _ m4 heq
    | (left; constructor <;> omega)
    | (right; constructor <;> omega)

private lemma exists_finset_sidon (n : ℕ) : ∃ A : Finset ℕ, A.card = n ∧ SidonN (↑A : Set ℕ) := by
  induction n with
  | zero =>
    refine ⟨∅, rfl, ?_⟩
    unfold SidonN
    intro i₁ h1
    simp at h1
  | succ k ih =>
    obtain ⟨A, hc, hS⟩ := ih
    have hnot : (2 * A.sup id + 1) ∉ A := by
      intro h
      have := Finset.le_sup (f := id) h
      simp only [id] at this
      omega
    refine ⟨insert (2 * A.sup id + 1) A, ?_, ?_⟩
    · rw [Finset.card_insert_eq_ite, if_neg hnot, hc]
    · rw [Finset.coe_insert]
      apply sidon_insert (↑A : Set ℕ) (A.sup id) _ hS
      · intro a ha
        have := Finset.le_sup (f := id) (Finset.mem_coe.mp ha)
        simpa using this
      · omega

theorem erdos_92759_hyp_exists : ∀ n : ℕ, ∃ A : Set ℕ, A.ncard = n ∧ SidonN A := by
  intro n
  obtain ⟨A, hc, hS⟩ := exists_finset_sidon n
  refine ⟨(↑A : Set ℕ), ?_, hS⟩
  rw [Set.ncard_coe_finset]
  exact hc
end erdos_92759_hyp_exists_ns

theorem erdos_92759_hyp_exists : ∀ n : ℕ, ∃ A : Set ℕ, A.ncard = n ∧ SidonN A := by
  exact erdos_92759_hyp_exists_ns.erdos_92759_hyp_exists



-- Derived (L1-L4 of the discovery stage): parity bias beta >= n/2, run accounting
-- r_1 >= beta/2 + |S|/2 - P, quadruple identity 4P - 2B = n(n-1)+1-R_D+2eps(n-1), B <= 2n,
-- giving 4 I_Z >= R_D - 3n + 1; Lean count >= I_Z - 1 (truncation only affects s = 0).
namespace erdos_92759_hyp_reduce_ns
open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

noncomputable def evenCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s % 2 = 0}.ncard

noncomputable def oddCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s % 2 = 1}.ncard

noncomputable def adjCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s + 1 ∈ S}.ncard

noncomputable def isoInt (S : Set ℕ) : ℕ :=
  {s : ℕ | s ∈ S ∧ s + 1 ∉ S ∧ (s = 0 ∨ s - 1 ∉ S)}.ncard

noncomputable def quadCnt (A : Set ℕ) : ℕ :=
  {x : ℕ × ℕ × ℕ × ℕ | x.1 ∈ A ∧ x.2.1 ∈ A ∧ x.2.2.1 ∈ A ∧ x.2.2.2 ∈ A ∧
    x.2.2.1 + x.2.2.2 = x.1 + x.2.1 + 1}.ncard

-- Run decomposition of the finite set S = A+A: summing (L-2) over maximal runs gives
-- |S| - 2*(#runs) >= -#(len 1) + #(odd len >= 3), #runs = |S| - adj, #odd-length runs >= |even - odd|.
namespace erdos_92759_hyp_reduce_hyp_runs_ns

open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

open Classical in

private noncomputable def gfun (S : Set ℕ) (s : ℕ) : ℕ :=
  if s ≠ 0 ∧ s - 1 ∈ S ∧ s + 1 ∉ S then s - 1 else s

private lemma card_split_aux (S : Set ℕ) (hS : S.Finite) :
    S.ncard = evenCnt S + oddCnt S := by
  unfold evenCnt oddCnt
  have hU : {s : ℕ | s ∈ S ∧ s % 2 = 0} ∪ {s : ℕ | s ∈ S ∧ s % 2 = 1} = S := by
    ext s
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases Nat.mod_two_eq_zero_or_one s with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hd : Disjoint {s : ℕ | s ∈ S ∧ s % 2 = 0} {s : ℕ | s ∈ S ∧ s % 2 = 1} := by
    rw [Set.disjoint_left]
    intro s h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    obtain ⟨_, h1'⟩ := h1
    obtain ⟨_, h2'⟩ := h2
    omega
  rw [← Set.ncard_union_eq hd (hS.subset fun x hx => hx.1) (hS.subset fun x hx => hx.1), hU]

private lemma even_le_aux (S : Set ℕ) (hS : S.Finite) :
    evenCnt S ≤ isoInt S + adjCnt S := by
  unfold evenCnt isoInt adjCnt
  have h1 : {s : ℕ | s ∈ S ∧ s % 2 = 0}.ncard ≤
      ({s : ℕ | s ∈ S ∧ s + 1 ∉ S ∧ (s = 0 ∨ s - 1 ∉ S)} ∪
        {s : ℕ | s ∈ S ∧ s + 1 ∈ S}).ncard := by
    refine Set.ncard_le_ncard_of_injOn (gfun S) ?_ ?_ ?_
    · intro s hs
      simp only [Set.mem_setOf_eq] at hs
      obtain ⟨hsS, _⟩ := hs
      unfold gfun
      by_cases hc : s ≠ 0 ∧ s - 1 ∈ S ∧ s + 1 ∉ S
      · rw [if_pos hc]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        right
        refine ⟨hc.2.1, ?_⟩
        have hh : s - 1 + 1 = s := by have := hc.1; omega
        rw [hh]
        exact hsS
      · rw [if_neg hc]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        by_cases h3 : s + 1 ∈ S
        · right
          exact ⟨hsS, h3⟩
        · left
          refine ⟨hsS, h3, ?_⟩
          by_cases h0 : s = 0
          · exact Or.inl h0
          · right
            intro h4
            exact hc ⟨h0, h4, h3⟩
    · intro s hs t ht hst
      simp only [Set.mem_setOf_eq] at hs ht
      obtain ⟨_, hs2⟩ := hs
      obtain ⟨_, ht2⟩ := ht
      unfold gfun at hst
      by_cases hc : s ≠ 0 ∧ s - 1 ∈ S ∧ s + 1 ∉ S
      · by_cases hd : t ≠ 0 ∧ t - 1 ∈ S ∧ t + 1 ∉ S
        · rw [if_pos hc, if_pos hd] at hst
          have := hc.1
          have := hd.1
          omega
        · rw [if_pos hc, if_neg hd] at hst
          have := hc.1
          omega
      · by_cases hd : t ≠ 0 ∧ t - 1 ∈ S ∧ t + 1 ∉ S
        · rw [if_neg hc, if_pos hd] at hst
          have := hd.1
          omega
        · rw [if_neg hc, if_neg hd] at hst
          exact hst
    · exact (hS.subset fun x hx => hx.1).union (hS.subset fun x hx => hx.1)
  exact h1.trans (Set.ncard_union_le _ _)

theorem erdos_92759_hyp_reduce_hyp_runs : ∀ A : Set ℕ, A.Finite →
    (A + A).ncard + evenCnt (A + A) ≤
      2 * isoInt (A + A) + 2 * adjCnt (A + A) + oddCnt (A + A) := by
  intro A hA
  have hfin : (A + A).Finite := hA.add hA
  have h1 := even_le_aux (A + A) hfin
  have h2 := card_split_aux (A + A) hfin
  omega

end erdos_92759_hyp_reduce_hyp_runs_ns

theorem erdos_92759_hyp_reduce_hyp_runs : ∀ A : Set ℕ, A.Finite →
    (A + A).ncard + evenCnt (A + A) ≤
      2 * isoInt (A + A) + 2 * adjCnt (A + A) + oddCnt (A + A) := by
  exact erdos_92759_hyp_reduce_hyp_runs_ns.erdos_92759_hyp_reduce_hyp_runs

-- Parity character: #even(A+A) - #odd(A+A) = ((e-o)^2 + n)/2 >= n/2 by unique representation.
namespace erdos_92759_hyp_reduce_hyp_parity_ns

open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

private lemma odd_le_aux (F : Finset ℕ) :
    ((F+F).filter (fun s => s % 2 = 1)).card ≤
      (F.filter (fun a => a % 2 = 0)).card * (F.filter (fun a => a % 2 = 1)).card := by
  have hsub : (F+F).filter (fun s => s % 2 = 1) ⊆
      ((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 1))).image
        (fun p : ℕ × ℕ => p.1 + p.2) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_add] at hs
    obtain ⟨⟨x, hx, y, hy, rfl⟩, hodd⟩ := hs
    rw [Finset.mem_image]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · refine ⟨(x, y), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_filter]
      exact ⟨⟨hx, h⟩, hy, by omega⟩
    · refine ⟨(y, x), ?_, Nat.add_comm y x⟩
      simp only [Finset.mem_product, Finset.mem_filter]
      exact ⟨⟨hy, by omega⟩, hx, h⟩
  calc ((F+F).filter (fun s => s % 2 = 1)).card
      ≤ (((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 1))).image
        (fun p : ℕ × ℕ => p.1 + p.2)).card := Finset.card_le_card hsub
    _ ≤ ((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 1))).card :=
        Finset.card_image_le
    _ = _ := Finset.card_product _ _

private lemma even_ge_aux (F : Finset ℕ) (hS : SidonN (F : Set ℕ)) :
    (F.filter (fun a => a % 2 = 0)).card * (F.filter (fun a => a % 2 = 0)).card +
      (F.filter (fun a => a % 2 = 1)).card * (F.filter (fun a => a % 2 = 1)).card + F.card ≤
      2 * ((F+F).filter (fun s => s % 2 = 0)).card := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (ℕ × ℕ),
      T = (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 % 2 = p.2 % 2) := ⟨_, rfl⟩
  have hmemT : ∀ a b : ℕ, a ∈ F → b ∈ F → a ≤ b → a % 2 = b % 2 → (a, b) ∈ T := by
    intro a b ha hb hab hp
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ha, hb⟩, hab, hp⟩
  have h1 : T.card ≤ ((F+F).filter (fun s => s % 2 = 0)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + p.2)
    · intro p hp
      have hp' : p ∈ T := hp
      rw [hT] at hp'
      simp only [Finset.mem_filter, Finset.mem_product] at hp'
      obtain ⟨⟨g1, g2⟩, _, g4⟩ := hp'
      show p.1 + p.2 ∈ (F+F).filter (fun s => s % 2 = 0)
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_add.mpr ⟨p.1, g1, p.2, g2, rfl⟩, by omega⟩
    · intro p hp q hq hpq
      have hp' : p ∈ T := hp
      have hq' : q ∈ T := hq
      rw [hT] at hp' hq'
      simp only [Finset.mem_filter, Finset.mem_product] at hp' hq'
      obtain ⟨⟨g1, g2⟩, g3, _⟩ := hp'
      obtain ⟨⟨k1, k2⟩, k3, _⟩ := hq'
      have hpq' : p.1 + p.2 = q.1 + q.2 := hpq
      rcases hS p.1 (Finset.mem_coe.mpr g1) q.1 (Finset.mem_coe.mpr k1) p.2
          (Finset.mem_coe.mpr g2) q.2 (Finset.mem_coe.mpr k2) hpq' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext e1 e2
      · exact Prod.ext (by omega) (by omega)
  have hswap : (T.image Prod.swap).card = T.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have hUI := Finset.card_union_add_card_inter T (T.image Prod.swap)
  have hXY : ((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 0))) ∪
      ((F.filter (fun a => a % 2 = 1)) ×ˢ (F.filter (fun a => a % 2 = 1))) ⊆
        T ∪ T.image Prod.swap := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter] at hp
    have hab : a ∈ F ∧ b ∈ F ∧ a % 2 = b % 2 := by
      rcases hp with ⟨⟨ha, h1⟩, hb, h2⟩ | ⟨⟨ha, h1⟩, hb, h2⟩
      · exact ⟨ha, hb, by omega⟩
      · exact ⟨ha, hb, by omega⟩
    obtain ⟨ha, hb, hpar⟩ := hab
    rw [Finset.mem_union]
    rcases le_total a b with h | h
    · exact Or.inl (hmemT a b ha hb h hpar)
    · exact Or.inr (Finset.mem_image.mpr ⟨(b, a), hmemT b a hb ha h hpar.symm, rfl⟩)
  have hD : F.image (fun a => (a, a)) ⊆ T ∩ T.image Prod.swap := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    have hT0 : (a, a) ∈ T := hmemT a a ha ha le_rfl rfl
    exact Finset.mem_inter.mpr ⟨hT0, Finset.mem_image.mpr ⟨(a, a), hT0, rfl⟩⟩
  have hDcard : (F.image (fun a => (a, a))).card = F.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have hX := Finset.card_union_add_card_inter
    ((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 0)))
    ((F.filter (fun a => a % 2 = 1)) ×ˢ (F.filter (fun a => a % 2 = 1)))
  have hXI : (((F.filter (fun a => a % 2 = 0)) ×ˢ (F.filter (fun a => a % 2 = 0))) ∩
      ((F.filter (fun a => a % 2 = 1)) ×ˢ (F.filter (fun a => a % 2 = 1)))).card = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc _ ≤ (∅ : Finset (ℕ × ℕ)).card := Finset.card_le_card (by
          intro p hp
          simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_filter] at hp
          obtain ⟨⟨⟨_, h1⟩, _⟩, ⟨_, h2⟩, _⟩ := hp
          exfalso
          omega)
      _ = 0 := Finset.card_empty
  rw [Finset.card_product, Finset.card_product] at hX
  have c1 := Finset.card_le_card hXY
  have c2 := Finset.card_le_card hD
  linarith

theorem erdos_92759_hyp_reduce_hyp_parity : ∀ A : Set ℕ, A.Finite → SidonN A →
    2 * oddCnt (A + A) + A.ncard ≤ 2 * evenCnt (A + A) := by
  intro A hA hS
  obtain ⟨F, rfl⟩ := hA.exists_finset_coe
  have hodd : oddCnt ((F : Set ℕ) + (F : Set ℕ)) =
      ((F+F).filter (fun s => s % 2 = 1)).card := by
    unfold oddCnt
    rw [← Finset.coe_add, ← Set.ncard_coe_finset]
    congr 1
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  have hev : evenCnt ((F : Set ℕ) + (F : Set ℕ)) =
      ((F+F).filter (fun s => s % 2 = 0)).card := by
    unfold evenCnt
    rw [← Finset.coe_add, ← Set.ncard_coe_finset]
    congr 1
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  rw [hodd, hev, Set.ncard_coe_finset]
  have h1 := odd_le_aux F
  have h2 := even_ge_aux F hS
  have key : ∀ e o : ℕ, 2 * (e * o) ≤ e * e + o * o := by
    intro e o
    have : (2:ℤ) * (e * o) ≤ e * e + o * o := by nlinarith [sq_nonneg ((e:ℤ) - o)]
    exact_mod_cast this
  have h3 := key (F.filter (fun a => a % 2 = 0)).card (F.filter (fun a => a % 2 = 1)).card
  linarith

end erdos_92759_hyp_reduce_hyp_parity_ns

theorem erdos_92759_hyp_reduce_hyp_parity : ∀ A : Set ℕ, A.Finite → SidonN A →
    2 * oddCnt (A + A) + A.ncard ≤ 2 * evenCnt (A + A) := by
  exact erdos_92759_hyp_reduce_hyp_parity_ns.erdos_92759_hyp_reduce_hyp_parity

-- Unique representation of sums: |A+A| = n(n+1)/2.
namespace erdos_92759_hyp_reduce_hyp_card_ns

open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

private lemma sidon_key : ∀ s : Finset ℕ, SidonN (↑s : Set ℕ) →
    2 * (s + s).card = s.card * s.card + s.card := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro m t hm ih h
    have ht : SidonN (↑t : Set ℕ) := by
      intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ he
      exact h i₁ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hi₁)))
        j₁ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hj₁)))
        i₂ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hi₂)))
        j₂ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hj₂))) he
    have hS : insert m t + insert m t
        = (t + t) ∪ (insert m t).image (fun x => m + x) := by
      ext y
      simp only [Finset.mem_add, Finset.mem_union, Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases ha with rfl | ha
        · right; exact ⟨b, hb, rfl⟩
        · rcases hb with rfl | hb
          · right; exact ⟨a, Or.inr ha, add_comm _ _⟩
          · left; exact ⟨a, ha, b, hb, rfl⟩
      · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨a, Or.inr ha, b, Or.inr hb, rfl⟩
        · exact ⟨m, Or.inl rfl, x, hx, rfl⟩
    have hdisj : Disjoint (t + t) ((insert m t).image (fun x => m + x)) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      rw [Finset.mem_add] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [Finset.mem_image] at hy'
      obtain ⟨x, hx, hxe⟩ := hy'
      have hh := h m (Finset.mem_coe.2 (Finset.mem_insert_self m t))
        a (Finset.mem_coe.2 (Finset.mem_insert_of_mem ha))
        x (Finset.mem_coe.2 hx)
        b (Finset.mem_coe.2 (Finset.mem_insert_of_mem hb)) hxe
      rcases hh with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at hm; exact hm ha
      · rw [h1] at hm; exact hm hb
    have hinj : Function.Injective (fun x : ℕ => m + x) := by
      intro x y hxy
      simpa using hxy
    have hc : (insert m t).card = t.card + 1 := by simp [hm]
    rw [hS, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, hc]
    have := ih ht
    nlinarith

theorem erdos_92759_hyp_reduce_hyp_card : ∀ A : Set ℕ, A.Finite → SidonN A →
    2 * (A + A).ncard = A.ncard * A.ncard + A.ncard := by
  intro A hA hS
  obtain ⟨s, rfl⟩ : ∃ s : Finset ℕ, A = ↑s := ⟨hA.toFinset, hA.coe_toFinset.symm⟩
  rw [← Finset.coe_add, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact sidon_key s hS

end erdos_92759_hyp_reduce_hyp_card_ns

theorem erdos_92759_hyp_reduce_hyp_card : ∀ A : Set ℕ, A.Finite → SidonN A →
    2 * (A + A).ncard = A.ncard * A.ncard + A.ncard := by
  exact erdos_92759_hyp_reduce_hyp_card_ns.erdos_92759_hyp_reduce_hyp_card

-- Q = sum_x r(x) r(x+1) = 4P - 2B with B = #{a : 2a+1 ∈ S} + #{a : 2a-1 ∈ S} <= 2n.
theorem erdos_92759_hyp_reduce_hyp_adj : ∀ A : Set ℕ, A.Finite → SidonN A →
    4 * adjCnt (A + A) ≤ quadCnt A + 4 * A.ncard := by
  sorry

-- Q = |A-A| - diffRuns A + 2*eps*(n-1), with |A-A| = n^2 - n + 1 and eps <= 1.
namespace erdos_92759_hyp_reduce_hyp_diff_ns
open scoped Pointwise

-- Derived (L1-L4 of the discovery stage): parity bias beta >= n/2, run accounting
-- r_1 >= beta/2 + |S|/2 - P, quadruple identity 4P - 2B = n(n-1)+1-R_D+2eps(n-1), B <= 2n,
-- giving 4 I_Z >= R_D - 3n + 1; Lean count >= I_Z - 1 (truncation only affects s = 0).
open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

noncomputable def evenCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s % 2 = 0}.ncard

noncomputable def oddCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s % 2 = 1}.ncard

noncomputable def adjCnt (S : Set ℕ) : ℕ := {s : ℕ | s ∈ S ∧ s + 1 ∈ S}.ncard

noncomputable def isoInt (S : Set ℕ) : ℕ :=
  {s : ℕ | s ∈ S ∧ s + 1 ∉ S ∧ (s = 0 ∨ s - 1 ∉ S)}.ncard

noncomputable def quadCnt (A : Set ℕ) : ℕ :=
  {x : ℕ × ℕ × ℕ × ℕ | x.1 ∈ A ∧ x.2.1 ∈ A ∧ x.2.2.1 ∈ A ∧ x.2.2.2 ∈ A ∧
    x.2.2.1 + x.2.2.2 = x.1 + x.2.1 + 1}.ncard

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

-- CHECK: Finset.filter_card_add_filter_neg_card_eq_card Finset.card_le_card_of_injOn Set.ncard_coe_finset Set.Finite.exists_finset_coe
theorem erdos_92759_hyp_reduce_hyp_diff : ∀ A : Set ℕ, A.Finite → SidonN A → 1 ≤ A.ncard →
    quadCnt A + diffRuns A + 1 ≤ A.ncard * A.ncard + A.ncard := by
  intro A hA hS hn
  obtain ⟨F, rfl⟩ := hA.exists_finset_coe
  have hS' : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F, a + c = b + d →
      (a = b ∧ c = d) ∨ (a = d ∧ c = b) := by
    intro a ha b hb c hc d hd h
    exact hS a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb) c (Finset.mem_coe.mpr hc)
      d (Finset.mem_coe.mpr hd) h
  obtain ⟨Df, hDf⟩ : ∃ D : Finset ℤ,
      D = (F ×ˢ F).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) := ⟨_, rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Q : Finset (ℕ × ℕ × ℕ × ℕ),
      Q = (F ×ˢ F ×ˢ F ×ˢ F).filter (fun x => x.2.2.1 + x.2.2.2 = x.1 + x.2.1 + 1) :=
    ⟨_, rfl⟩
  obtain ⟨Rf, hRf⟩ : ∃ R : Finset ℤ, R = Df.filter (fun u => u + 1 ∉ Df) := ⟨_, rfl⟩
  obtain ⟨good, hgood⟩ : ∃ G : Finset (ℕ × ℕ),
      G = (F ×ˢ F).filter (fun p => (p.1 : ℤ) - p.2 + 1 ∈ Df) := ⟨_, rfl⟩
  obtain ⟨bad, hbad⟩ : ∃ G : Finset (ℕ × ℕ),
      G = (F ×ˢ F).filter (fun p => ¬ ((p.1 : ℤ) - p.2 + 1 ∈ Df)) := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ Q : Finset (ℕ × ℕ × ℕ × ℕ),
      Q = Qf.filter (fun x => ¬ (x.2.2.2 = x.2.1 + 1)) := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q : Finset (ℕ × ℕ × ℕ × ℕ),
      Q = Qf.filter (fun x => x.2.2.2 = x.2.1 + 1) := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ G : Finset (ℕ × ℕ),
      G = good.filter (fun p => ¬ (p.2 = p.1 + 1)) := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ G : Finset (ℕ × ℕ),
      G = good.filter (fun p => p.2 = p.1 + 1) := ⟨_, rfl⟩
  -- translate the set-level counts
  have hQcard : quadCnt (↑F : Set ℕ) = Qf.card := by
    rw [← Set.ncard_coe_finset Qf]
    unfold quadCnt
    congr 1
    ext x
    rw [hQf]
    simp [Finset.mem_product, and_assoc]
  have hD : diffSet (↑F : Set ℕ) = (↑Df : Set ℤ) := by
    ext u
    simp only [diffSet, Set.mem_setOf_eq, Finset.mem_coe]
    rw [hDf, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hp, rfl⟩
      rw [Finset.mem_product] at hp
      exact ⟨a, hp.1, b, hp.2, rfl⟩
  have hRcard : diffRuns (↑F : Set ℕ) = Rf.card := by
    rw [← Set.ncard_coe_finset Rf]
    unfold diffRuns
    rw [hD]
    congr 1
    ext u
    rw [hRf]
    simp
  -- splitting counts
  have c1 : good.card + bad.card = F.card * F.card := by
    rw [hgood, hbad, ← Finset.card_product]
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq]
  have c2 : g2.card + g1.card = good.card := by
    rw [hg2, hg1]
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq]
  have c3 : Q2.card + Q1.card = Qf.card := by
    rw [hQ2, hQ1]
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq]
  -- runs bounded by bad pairs
  have c4 : Rf.card ≤ bad.card := by
    calc Rf.card ≤ (bad.image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)).card := by
          apply Finset.card_le_card
          intro u hu
          rw [hRf, Finset.mem_filter] at hu
          obtain ⟨huD, hu1⟩ := hu
          have huD' := huD
          rw [hDf, Finset.mem_image] at huD'
          obtain ⟨p, hp, hpu⟩ := huD'
          have hpu' : (p.1 : ℤ) - p.2 = u := hpu
          rw [Finset.mem_image]
          refine ⟨p, ?_, hpu⟩
          rw [hbad, Finset.mem_filter]
          refine ⟨hp, ?_⟩
          show ¬ ((p.1 : ℤ) - p.2 + 1 ∈ Df)
          rw [hpu']
          exact hu1
      _ ≤ bad.card := Finset.card_image_le
  -- quadruples with d ≠ b+1
  have c5 : Q1.card ≤ g1.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ × ℕ × ℕ => (x.2.1, x.2.2.2))
    · intro x hx
      obtain ⟨a, b, c, d⟩ := x
      have hx' : (a, b, c, d) ∈ Q1 := hx
      simp only [hQ1, hQf, Finset.mem_filter, Finset.mem_product] at hx'
      obtain ⟨⟨⟨ha, hb, hc, hd⟩, heq⟩, hne⟩ := hx'
      show (b, d) ∈ g1
      rw [hg1, Finset.mem_filter, hgood, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hb, hd⟩, ?_⟩, hne⟩
      show (b : ℤ) - d + 1 ∈ Df
      rw [hDf, Finset.mem_image]
      exact ⟨(c, a), Finset.mem_product.mpr ⟨hc, ha⟩,
        by show (c : ℤ) - a = b - d + 1; omega⟩
    · intro x hx y hy hxy
      obtain ⟨a, b, c, d⟩ := x
      obtain ⟨a', b', c', d'⟩ := y
      have hx' : (a, b, c, d) ∈ Q1 := hx
      have hy' : (a', b', c', d') ∈ Q1 := hy
      simp only [hQ1, hQf, Finset.mem_filter, Finset.mem_product] at hx' hy'
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨⟨⟨ha, hb, hc, hd⟩, heq⟩, hne⟩ := hx'
      obtain ⟨⟨⟨ha', hb', hc', hd'⟩, heq'⟩, hne'⟩ := hy'
      obtain ⟨rfl, rfl⟩ := hxy
      have key := hS' c hc c' hc' a' ha' a ha (by omega)
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        rfl
      · exact absurd (by omega : d = b + 1) hne
  -- quadruples with d = b+1
  have c6 : Q2.card ≤ F.card * g2.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ × ℕ × ℕ => (x.1, (x.2.1, x.2.2.2)))
    · intro x hx
      obtain ⟨a, b, c, d⟩ := x
      have hx' : (a, b, c, d) ∈ Q2 := hx
      simp only [hQ2, hQf, Finset.mem_filter, Finset.mem_product] at hx'
      obtain ⟨⟨⟨ha, hb, hc, hd⟩, heq⟩, hdq⟩ := hx'
      show (a, (b, d)) ∈ F ×ˢ g2
      rw [Finset.mem_product]
      refine ⟨ha, ?_⟩
      show (b, d) ∈ g2
      rw [hg2, Finset.mem_filter, hgood, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hb, hd⟩, ?_⟩, hdq⟩
      show (b : ℤ) - d + 1 ∈ Df
      rw [hDf, Finset.mem_image]
      exact ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩,
        by show (a : ℤ) - a = b - d + 1; omega⟩
    · intro x hx y hy hxy
      obtain ⟨a, b, c, d⟩ := x
      obtain ⟨a', b', c', d'⟩ := y
      have hx' : (a, b, c, d) ∈ Q2 := hx
      have hy' : (a', b', c', d') ∈ Q2 := hy
      simp only [hQ2, hQf, Finset.mem_filter, Finset.mem_product] at hx' hy'
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨⟨_, heq⟩, hdq⟩ := hx'
      obtain ⟨⟨_, heq'⟩, hdq'⟩ := hy'
      obtain ⟨h1, h2, h3⟩ := hxy
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2, by omega, h3⟩
  -- at most one consecutive pair
  have c7 : g2.card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨b, d⟩ hp ⟨b', d'⟩ hp'
    rw [hg2, Finset.mem_filter, hgood, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨⟨hb, hd⟩, -⟩, hbd⟩ := hp
    obtain ⟨⟨⟨hb', hd'⟩, -⟩, hbd'⟩ := hp'
    have e1 : d = b + 1 := hbd
    have e2 : d' = b' + 1 := hbd'
    have key := hS' b hb b' hb' d' hd' d hd (by omega)
    simp only [Prod.mk.injEq]
    omega
  rw [hQcard, hRcard]
  rw [Set.ncard_coe_finset] at hn ⊢
  rcases (show g2.card = 0 ∨ g2.card = 1 by omega) with h | h
  · rw [h, Nat.mul_zero] at c6
    generalize F.card * F.card = m at c1 ⊢
    omega
  · rw [h, Nat.mul_one] at c6
    generalize F.card * F.card = m at c1 ⊢
    omega
end erdos_92759_hyp_reduce_hyp_diff_ns

theorem erdos_92759_hyp_reduce_hyp_diff : ∀ A : Set ℕ, A.Finite → SidonN A → 1 ≤ A.ncard →
    quadCnt A + diffRuns A + 1 ≤ A.ncard * A.ncard + A.ncard := by
  exact erdos_92759_hyp_reduce_hyp_diff_ns.erdos_92759_hyp_reduce_hyp_diff



-- Truncated subtraction only affects s = 0, so the two isolated-sum counts differ by at most 1.
namespace erdos_92759_hyp_reduce_hyp_iso_ns

open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

theorem erdos_92759_hyp_reduce_hyp_iso : ∀ A : Set ℕ, A.Finite →
    isoInt (A + A) ≤ isoCount A + 1 := by
  intro A hA
  have hS : (A + A).Finite := hA.add hA
  unfold isoInt isoCount
  have hX : {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.Finite :=
    hS.subset (fun s hs => hs.2.1)
  calc _ ≤ (insert 0 {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}).ncard := by
        apply Set.ncard_le_ncard _ (hX.insert 0)
        intro s hs
        simp only [Set.mem_setOf_eq] at hs
        rw [Set.mem_insert_iff, Set.mem_setOf_eq]
        rcases hs with ⟨h1, h2, h3⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨h3, h1, h2⟩
    _ ≤ _ := Set.ncard_insert_le _ _

end erdos_92759_hyp_reduce_hyp_iso_ns

theorem erdos_92759_hyp_reduce_hyp_iso : ∀ A : Set ℕ, A.Finite →
    isoInt (A + A) ≤ isoCount A + 1 := by
  exact erdos_92759_hyp_reduce_hyp_iso_ns.erdos_92759_hyp_reduce_hyp_iso

-- Empty set: diffSet is empty, so it has no runs.
namespace erdos_92759_hyp_reduce_hyp_empty_ns

open scoped Pointwise

open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

theorem erdos_92759_hyp_reduce_hyp_empty : ∀ A : Set ℕ, A.Finite → A.ncard = 0 →
    diffRuns A = 0 := by
  intro A hA h0
  have hAe : A = ∅ := (Set.ncard_eq_zero hA).mp h0
  subst hAe
  have hE : {u : ℤ | u ∈ diffSet (∅ : Set ℕ) ∧ u + 1 ∉ diffSet (∅ : Set ℕ)} = ∅ := by
    ext u
    simp [diffSet]
  rw [diffRuns, hE, Set.ncard_empty]

end erdos_92759_hyp_reduce_hyp_empty_ns

theorem erdos_92759_hyp_reduce_hyp_empty : ∀ A : Set ℕ, A.Finite → A.ncard = 0 →
    diffRuns A = 0 := by
  exact erdos_92759_hyp_reduce_hyp_empty_ns.erdos_92759_hyp_reduce_hyp_empty

theorem erdos_92759_hyp_reduce : ∀ A : Set ℕ, A.Finite → SidonN A →
    diffRuns A + 1 ≤ 4 * isoCount A + 3 * A.ncard + 4 := by
  intro A hA hS
  have h6 := erdos_92759_hyp_reduce_hyp_iso A hA
  by_cases hn : A.ncard = 0
  · have h0 := erdos_92759_hyp_reduce_hyp_empty A hA hn
    rw [h0]
    omega
  · have h1 := erdos_92759_hyp_reduce_hyp_runs A hA
    have h2 := erdos_92759_hyp_reduce_hyp_parity A hA hS
    have h3 := erdos_92759_hyp_reduce_hyp_card A hA hS
    have h4 := erdos_92759_hyp_reduce_hyp_adj A hA hS
    have h5 := erdos_92759_hyp_reduce_hyp_diff A hA hS (Nat.one_le_iff_ne_zero.mpr hn)
    generalize A.ncard * A.ncard = m at h3 h5
    omega
end erdos_92759_hyp_reduce_ns

theorem erdos_92759_hyp_reduce : ∀ A : Set ℕ, A.Finite → SidonN A →
    diffRuns A + 1 ≤ 4 * isoCount A + 3 * A.ncard + 4 := by
  exact erdos_92759_hyp_reduce_ns.erdos_92759_hyp_reduce



-- Open core: A - A is not a union of 3n + O(1) intervals for large Sidon A
-- (equivalently V = sum (r(s+1)-r(s))^2 >= 2n^2 + 6n - 4(n-1)eps + omega(1)).
theorem erdos_92759_hyp_runs : ∀ M : ℕ, ∃ N : ℕ, ∀ A : Set ℕ, A.Finite → SidonN A →
    N ≤ A.ncard → 3 * A.ncard + M ≤ diffRuns A := by
  sorry

open Function Set
open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

open scoped Pointwise Asymptotics
open Filter

noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard

theorem erdos_92759 :
    Tendsto f atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := erdos_92759_hyp_runs (4 * b + 4)
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨A0, hA0c, hA0s⟩ := erdos_92759_hyp_exists n
  haveI : Nonempty {A : Set ℕ | A.ncard = n ∧ IsSidon A} :=
    ⟨⟨A0, show A0.ncard = n ∧ IsSidon A0 from ⟨hA0c, hA0s⟩⟩⟩
  unfold f
  apply le_ciInf
  intro ⟨A, hA⟩
  have hA' : A.ncard = n ∧ IsSidon A := hA
  obtain ⟨hAc, hAs⟩ := hA'
  have hAs' : SidonN A := hAs
  have hfin : A.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have h1 := erdos_92759_hyp_reduce A hfin hAs'
  have h2 := hN A hfin hAs' (by omega)
  change b ≤ isoCount A
  omega