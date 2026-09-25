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

def diffSetZ (A : Set ℕ) : Set ℤ :=
  {x : ℤ | ∃ a ∈ A, ∃ b ∈ A, x = (a : ℤ) - (b : ℤ)}

noncomputable def runsD (A : Set ℕ) : ℕ :=
  {x : ℤ | x ∈ diffSetZ A ∧ x - 1 ∉ diffSetZ A}.ncard

noncomputable def isoCount (A : Set ℕ) : ℕ :=
  {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard

-- Sidon sets of every size exist, e.g. {2^i : i < n}; needed only for nonemptiness of the infimum.
namespace erdos_70264_hyp_exists_ns
open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

private lemma sidon_insert_big (A : Finset ℕ) (m : ℕ) (hA : IsSidon (A : Set ℕ))
    (hm : ∀ y ∈ A, y < m) : IsSidon ((insert (2 * m) A : Finset ℕ) : Set ℕ) := by
  intro i₁ h1 j₁ h2 i₂ h3 j₂ h4 heq
  have k1 : i₁ = 2 * m ∨ (i₁ ∈ A ∧ i₁ < m) := by
    have h1' : i₁ ∈ insert (2 * m) A := h1
    rcases Finset.mem_insert.mp h1' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have k2 : j₁ = 2 * m ∨ (j₁ ∈ A ∧ j₁ < m) := by
    have h2' : j₁ ∈ insert (2 * m) A := h2
    rcases Finset.mem_insert.mp h2' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have k3 : i₂ = 2 * m ∨ (i₂ ∈ A ∧ i₂ < m) := by
    have h3' : i₂ ∈ insert (2 * m) A := h3
    rcases Finset.mem_insert.mp h3' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  have k4 : j₂ = 2 * m ∨ (j₂ ∈ A ∧ j₂ < m) := by
    have h4' : j₂ ∈ insert (2 * m) A := h4
    rcases Finset.mem_insert.mp h4' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm _ h⟩
  clear h1 h2 h3 h4
  rcases k1 with e1 | ⟨m1, b1⟩ <;> rcases k2 with e2 | ⟨m2, b2⟩ <;>
    rcases k3 with e3 | ⟨m3, b3⟩ <;> rcases k4 with e4 | ⟨m4, b4⟩
  all_goals first
    | exact hA i₁ m1 j₁ m2 i₂ m3 j₂ m4 heq
    | omega
    | (left; constructor <;> omega)
    | (right; constructor <;> omega)

theorem erdos_70264_hyp_exists :
    ∀ n : ℕ, ∃ A : Set ℕ, A.ncard = n ∧ IsSidon A := by
  have key : ∀ n : ℕ, ∃ A : Finset ℕ, A.card = n ∧ IsSidon (A : Set ℕ) ∧
      ∃ m, ∀ y ∈ A, y < m := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, rfl, ?_, 0, ?_⟩
      · intro i h
        simp at h
      · intro y hy
        simp at hy
    | succ k ih =>
      obtain ⟨A, hc, hs, m, hm⟩ := ih
      refine ⟨insert (2 * m) A, ?_, sidon_insert_big A m hs hm, 2 * m + 1, ?_⟩
      · rw [Finset.card_insert_eq_ite]
        split_ifs with h
        · exact absurd (hm _ h) (by omega)
        · rw [hc]
      · intro y hy
        rcases Finset.mem_insert.mp hy with h | h
        · omega
        · have := hm _ h
          omega
  intro n
  obtain ⟨A, hc, hs, -⟩ := key n
  exact ⟨(A : Set ℕ), by rw [Set.ncard_coe_finset]; exact hc, hs⟩
end erdos_70264_hyp_exists_ns

theorem erdos_70264_hyp_exists :
    ∀ n : ℕ, ∃ A : Set ℕ, A.ncard = n ∧ IsSidon A := by
  exact erdos_70264_hyp_exists_ns.erdos_70264_hyp_exists



-- Lemma 2 of the discovery stage: adjacencies (s, s+1) in A+A inject (about 4 each, O(n) degenerate)
-- into Z' = {x ∈ D \ {0,1} : x-1 ∈ D}, and the least element of each run of D = A-A lies outside Z'.
-- This gives 2*isoZ ≥ runs(D) - 6n - 1, and formal ≥ isoZ - 1 (R1). Constant loosened to 10n+3.
namespace erdos_70264_hyp_runs_ns
open Function Set

open scoped Pointwise
variable {α : Type*} [AddCommMonoid α]

open scoped Pointwise Asymptotics

open Filter

private lemma runs_core (F : Finset ℕ)
    (hS : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F, a + c = b + d → (a = b ∧ c = d) ∨ (a = d ∧ c = b))
    (D : Finset ℤ) (hD : D = (F ×ˢ F).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2))
    (S : Finset ℕ) (hSS : ∀ s, s ∈ S ↔ ∃ a ∈ F, ∃ b ∈ F, a + b = s) :
    (D.filter (fun z => z - 1 ∉ D)).card ≤
      2 * (S.filter (fun s => s - 1 ∉ S ∧ s + 1 ∉ S)).card + 6 * F.card + 1 := by
  generalize hIdef : S.filter (fun s => s - 1 ∉ S ∧ s + 1 ∉ S) = I
  have hmemI : ∀ s, s ∈ I ↔ s ∈ S ∧ s - 1 ∉ S ∧ s + 1 ∉ S := by
    intro s
    rw [← hIdef, Finset.mem_filter]
  have hmemD : ∀ x : ℤ, x ∈ D ↔ ∃ a ∈ F, ∃ b ∈ F, (a : ℤ) - b = x := by
    intro x
    rw [hD, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hab, h⟩
      rw [Finset.mem_product] at hab
      exact ⟨a, hab.1, b, hab.2, h⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, h⟩
  -- Step A
  have hA1 : D.card ≤ F.offDiag.card + 1 := by
    have hsub : D ⊆ insert (0 : ℤ) (F.offDiag.image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hmemD x).1 hx
      rw [Finset.mem_insert, Finset.mem_image]
      by_cases hab : a = b
      · left; subst hab; simp
      · right; exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
    have e1 := Finset.card_le_card hsub
    have e2 := Finset.card_insert_le (0 : ℤ) (F.offDiag.image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2))
    have e3 := Finset.card_image_le (s := F.offDiag) (f := fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
    omega
  -- partition of D
  have hP : (D.filter (fun z => z - 1 ∉ D)).card + (D.filter (fun z => z - 1 ∈ D)).card
      ≤ D.card := by
    have hdisj : D.filter (fun z => z - 1 ∉ D) ∩ D.filter (fun z => z - 1 ∈ D) = ∅ := by
      ext z
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨_, h1⟩, _, h2⟩
        exact absurd h2 h1
      · intro h
        simp at h
    have e1 := Finset.card_union_add_card_inter (D.filter (fun z => z - 1 ∉ D))
      (D.filter (fun z => z - 1 ∈ D))
    rw [hdisj, Finset.card_empty] at e1
    have e2 : (D.filter (fun z => z - 1 ∉ D) ∪ D.filter (fun z => z - 1 ∈ D)).card ≤ D.card :=
      Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ((ℕ × ℕ) × (ℕ × ℕ)),
      Q = (F.offDiag ×ˢ F.offDiag).filter (fun x => x.2.1 + x.2.2 = x.1.1 + x.1.2 + 1) :=
    ⟨_, rfl⟩
  have hmemQ : ∀ x, x ∈ Q ↔
      x.1 ∈ F.offDiag ∧ x.2 ∈ F.offDiag ∧ x.2.1 + x.2.2 = x.1.1 + x.1.2 + 1 := by
    intro x
    rw [hQ, Finset.mem_filter, Finset.mem_product, and_assoc]
  obtain ⟨Gp, hGp⟩ : ∃ G : Finset (ℕ × ℕ),
      G = F.offDiag.filter (fun p => ∃ q ∈ F.offDiag, q.1 + q.2 = p.1 + p.2 + 1) := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ G : Finset (ℕ × ℕ),
      G = F.offDiag.filter (fun p => ∃ q ∈ F.offDiag, q.1 + q.2 + 1 = p.1 + p.2) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Finset ℕ,
      X = I ∪ F.image (fun e => 2 * e - 1) ∪ F.image (fun e => 2 * e + 1) := ⟨_, rfl⟩
  obtain ⟨Bad, hBad⟩ : ∃ B : Finset (ℕ × ℕ),
      B = F.offDiag.filter (fun p => p.1 + p.2 ∈ X) := ⟨_, rfl⟩
  have hT : F.offDiag.card ≤ Gp.card + Gm.card + Bad.card := by
    have hsub : F.offDiag ⊆ Gp ∪ Gm ∪ Bad := by
      intro p hp
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      rw [Finset.mem_union, Finset.mem_union]
      by_cases h1 : ∃ q ∈ F.offDiag, q.1 + q.2 = p.1 + p.2 + 1
      · left; left; rw [hGp, Finset.mem_filter]; exact ⟨hp, h1⟩
      by_cases h2 : ∃ q ∈ F.offDiag, q.1 + q.2 + 1 = p.1 + p.2
      · left; right; rw [hGm, Finset.mem_filter]; exact ⟨hp, h2⟩
      right
      rw [hBad, Finset.mem_filter]
      refine ⟨hp, ?_⟩
      rw [hX, Finset.mem_union, Finset.mem_union]
      by_cases h3 : p.1 + p.2 + 1 ∈ S
      · obtain ⟨c, hc, d, hd, hcd⟩ := (hSS _).1 h3
        have hcd' : c = d := by
          by_contra hne'
          exact h1 ⟨(c, d), Finset.mem_offDiag.mpr ⟨hc, hd, hne'⟩, hcd⟩
        left; right
        rw [Finset.mem_image]
        exact ⟨c, hc, by show 2 * c - 1 = p.1 + p.2; omega⟩
      · by_cases h4 : p.1 + p.2 - 1 ∈ S
        · obtain ⟨c, hc, d, hd, hcd⟩ := (hSS _).1 h4
          have hcd' : c = d := by
            by_contra hne'
            exact h2 ⟨(c, d), Finset.mem_offDiag.mpr ⟨hc, hd, hne'⟩,
              by show c + d + 1 = p.1 + p.2; omega⟩
          right
          rw [Finset.mem_image]
          exact ⟨c, hc, by show 2 * c + 1 = p.1 + p.2; omega⟩
        · left; left
          rw [hmemI]
          exact ⟨(hSS _).2 ⟨p.1, ha, p.2, hb, rfl⟩, h4, h3⟩
    have e1 := Finset.card_le_card hsub
    have e2 := Finset.card_union_le (Gp ∪ Gm) Bad
    have e3 := Finset.card_union_le Gp Gm
    omega
  have hBadc : Bad.card ≤ X.card * 2 := by
    calc Bad.card ≤ (X ×ˢ (Finset.univ : Finset Bool)).card := by
          apply Finset.card_le_card_of_injOn
            (fun p : ℕ × ℕ => (p.1 + p.2, decide (p.1 < p.2)))
          · intro p hp
            have hp' : p ∈ Bad := hp
            rw [hBad, Finset.mem_filter] at hp'
            show (p.1 + p.2, decide (p.1 < p.2)) ∈ X ×ˢ (Finset.univ : Finset Bool)
            exact Finset.mem_product.mpr ⟨hp'.2, Finset.mem_univ _⟩
          · intro p hp q hq h
            have hp' : p ∈ Bad := hp
            have hq' : q ∈ Bad := hq
            rw [hBad, Finset.mem_filter] at hp' hq'
            obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp'.1
            obtain ⟨hq1, hq2, hqne⟩ := Finset.mem_offDiag.mp hq'.1
            have h' : (p.1 + p.2, decide (p.1 < p.2)) = (q.1 + q.2, decide (q.1 < q.2)) := h
            rw [Prod.mk.injEq] at h'
            obtain ⟨hs, hd⟩ := h'
            rcases hS p.1 hp1 q.1 hq1 p.2 hp2 q.2 hq2 hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact Prod.ext e1 e2
            · exfalso
              by_cases hlt : p.1 < p.2
              · have hq' : ¬ q.1 < q.2 := by omega
                simp [hlt, hq'] at hd
              · have hq' : q.1 < q.2 := by omega
                simp [hlt, hq'] at hd
      _ = X.card * 2 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
  have hXc : X.card ≤ I.card + F.card + F.card := by
    rw [hX]
    have e1 := Finset.card_union_le (I ∪ F.image (fun e => 2 * e - 1)) (F.image (fun e => 2 * e + 1))
    have e2 := Finset.card_union_le I (F.image (fun e => 2 * e - 1))
    have e3 := Finset.card_image_le (s := F) (f := fun e => 2 * e - 1)
    have e4 := Finset.card_image_le (s := F) (f := fun e => 2 * e + 1)
    omega
  have hQp : Gp.card * 2 ≤ Q.card := by
    have hfib : ∀ b ∈ Gp, 2 ≤ (Q.filter (fun x => x.1 = b)).card := by
      intro b hb
      rw [hGp, Finset.mem_filter] at hb
      obtain ⟨hbT, q, hq, hqs⟩ := hb
      obtain ⟨hq1, hq2, hqne⟩ := Finset.mem_offDiag.mp hq
      have hne : (b, q) ≠ (b, (q.2, q.1)) := by
        intro h
        apply hqne
        have h' := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1) h
        exact h'
      have hsub : ({(b, q), (b, (q.2, q.1))} : Finset ((ℕ × ℕ) × (ℕ × ℕ))) ⊆
          Q.filter (fun x => x.1 = b) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_filter, hmemQ]
        rcases hx with rfl | rfl
        · exact ⟨⟨hbT, hq, hqs⟩, rfl⟩
        · exact ⟨⟨hbT, Finset.mem_offDiag.mpr ⟨hq2, hq1, fun h => hqne h.symm⟩,
            by show q.2 + q.1 = b.1 + b.2 + 1; omega⟩, rfl⟩
      exact (Finset.card_pair hne).symm.le.trans (Finset.card_le_card hsub)
    have hmaps : Set.MapsTo Prod.fst (Q : Set ((ℕ × ℕ) × (ℕ × ℕ))) (F.offDiag : Set (ℕ × ℕ)) := by
      intro x hx
      exact ((hmemQ x).1 hx).1
    calc Gp.card * 2 = ∑ b ∈ Gp, 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ Gp, (Q.filter (fun x => x.1 = b)).card := Finset.sum_le_sum hfib
      _ ≤ ∑ b ∈ F.offDiag, (Q.filter (fun x => x.1 = b)).card := by
          apply Finset.sum_le_sum_of_subset
          rw [hGp]; exact Finset.filter_subset _ _
      _ = Q.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hQm : Gm.card * 2 ≤ Q.card := by
    have hfib : ∀ b ∈ Gm, 2 ≤ (Q.filter (fun x => x.2 = b)).card := by
      intro b hb
      rw [hGm, Finset.mem_filter] at hb
      obtain ⟨hbT, q, hq, hqs⟩ := hb
      obtain ⟨hq1, hq2, hqne⟩ := Finset.mem_offDiag.mp hq
      have hne : (q, b) ≠ ((q.2, q.1), b) := by
        intro h
        apply hqne
        have h' := congrArg (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1) h
        exact h'
      have hsub : ({(q, b), ((q.2, q.1), b)} : Finset ((ℕ × ℕ) × (ℕ × ℕ))) ⊆
          Q.filter (fun x => x.2 = b) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_filter, hmemQ]
        rcases hx with rfl | rfl
        · exact ⟨⟨hq, hbT, by show b.1 + b.2 = q.1 + q.2 + 1; omega⟩, rfl⟩
        · exact ⟨⟨Finset.mem_offDiag.mpr ⟨hq2, hq1, fun h => hqne h.symm⟩, hbT,
            by show b.1 + b.2 = q.2 + q.1 + 1; omega⟩, rfl⟩
      exact (Finset.card_pair hne).symm.le.trans (Finset.card_le_card hsub)
    have hmaps : Set.MapsTo Prod.snd (Q : Set ((ℕ × ℕ) × (ℕ × ℕ))) (F.offDiag : Set (ℕ × ℕ)) := by
      intro x hx
      exact ((hmemQ x).1 hx).2.1
    calc Gm.card * 2 = ∑ b ∈ Gm, 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ Gm, (Q.filter (fun x => x.2 = b)).card := Finset.sum_le_sum hfib
      _ ≤ ∑ b ∈ F.offDiag, (Q.filter (fun x => x.2 = b)).card := by
          apply Finset.sum_le_sum_of_subset
          rw [hGm]; exact Finset.filter_subset _ _
      _ = Q.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Finset ((ℕ × ℕ) × (ℕ × ℕ)),
      Q' = Q.filter (fun x => x.2.1 ≠ x.1.1 ∧ x.2.2 ≠ x.1.2) := ⟨_, rfl⟩
  have hE1 : (Q.filter (fun x => x.2.1 = x.1.1)).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1)
    · intro x hx
      have hx' : x ∈ Q.filter (fun x => x.2.1 = x.1.1) := hx
      rw [Finset.mem_filter, hmemQ] at hx'
      exact (Finset.mem_offDiag.mp hx'.1.1).1
    · intro x hx y hy hxy
      have hx' : x ∈ Q.filter (fun x => x.2.1 = x.1.1) := hx
      have hy' : y ∈ Q.filter (fun x => x.2.1 = x.1.1) := hy
      rw [Finset.mem_filter, hmemQ] at hx' hy'
      have hxy' : x.1.1 = y.1.1 := hxy
      obtain ⟨⟨hxT1, hxT2, hxs⟩, hxe⟩ := hx'
      obtain ⟨⟨hyT1, hyT2, hys⟩, hye⟩ := hy'
      obtain ⟨hxa, hxb, -⟩ := Finset.mem_offDiag.mp hxT1
      obtain ⟨hxc, hxd, -⟩ := Finset.mem_offDiag.mp hxT2
      obtain ⟨hya, hyb, -⟩ := Finset.mem_offDiag.mp hyT1
      obtain ⟨hyc, hyd, -⟩ := Finset.mem_offDiag.mp hyT2
      rcases hS x.1.2 hxb y.1.2 hyb y.2.2 hyd x.2.2 hxd (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext (Prod.ext hxy' e1) (Prod.ext (by omega) e2.symm)
      · exfalso; omega
  have hE2 : (Q.filter (fun x => x.2.2 = x.1.2)).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.2)
    · intro x hx
      have hx' : x ∈ Q.filter (fun x => x.2.2 = x.1.2) := hx
      rw [Finset.mem_filter, hmemQ] at hx'
      exact (Finset.mem_offDiag.mp hx'.1.1).2.1
    · intro x hx y hy hxy
      have hx' : x ∈ Q.filter (fun x => x.2.2 = x.1.2) := hx
      have hy' : y ∈ Q.filter (fun x => x.2.2 = x.1.2) := hy
      rw [Finset.mem_filter, hmemQ] at hx' hy'
      have hxy' : x.1.2 = y.1.2 := hxy
      obtain ⟨⟨hxT1, hxT2, hxs⟩, hxe⟩ := hx'
      obtain ⟨⟨hyT1, hyT2, hys⟩, hye⟩ := hy'
      obtain ⟨hxa, hxb, -⟩ := Finset.mem_offDiag.mp hxT1
      obtain ⟨hxc, hxd, -⟩ := Finset.mem_offDiag.mp hxT2
      obtain ⟨hya, hyb, -⟩ := Finset.mem_offDiag.mp hyT1
      obtain ⟨hyc, hyd, -⟩ := Finset.mem_offDiag.mp hyT2
      rcases hS x.1.1 hxa y.1.1 hya y.2.1 hyc x.2.1 hxc (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext (Prod.ext e1 hxy') (Prod.ext e2.symm (by omega))
      · exfalso; omega
  have hE3 : Q'.card ≤ (D.filter (fun z => z - 1 ∈ D)).card := by
    apply Finset.card_le_card_of_injOn
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (x.2.1 : ℤ) - x.1.1)
    · intro x hx
      have hx' : x ∈ Q' := hx
      rw [hQ', Finset.mem_filter, hmemQ] at hx'
      obtain ⟨⟨hxT1, hxT2, hxs⟩, -, -⟩ := hx'
      obtain ⟨hxa, hxb, -⟩ := Finset.mem_offDiag.mp hxT1
      obtain ⟨hxc, hxd, -⟩ := Finset.mem_offDiag.mp hxT2
      show (x.2.1 : ℤ) - x.1.1 ∈ D.filter (fun z => z - 1 ∈ D)
      rw [Finset.mem_filter, hmemD, hmemD]
      exact ⟨⟨x.2.1, hxc, x.1.1, hxa, rfl⟩, ⟨x.1.2, hxb, x.2.2, hxd, by omega⟩⟩
    · intro x hx y hy hxy
      have hx' : x ∈ Q' := hx
      have hy' : y ∈ Q' := hy
      rw [hQ', Finset.mem_filter, hmemQ] at hx' hy'
      have hxy' : (x.2.1 : ℤ) - x.1.1 = (y.2.1 : ℤ) - y.1.1 := hxy
      obtain ⟨⟨hxT1, hxT2, hxs⟩, hxn1, hxn2⟩ := hx'
      obtain ⟨⟨hyT1, hyT2, hys⟩, hyn1, hyn2⟩ := hy'
      obtain ⟨hxa, hxb, -⟩ := Finset.mem_offDiag.mp hxT1
      obtain ⟨hxc, hxd, -⟩ := Finset.mem_offDiag.mp hxT2
      obtain ⟨hya, hyb, -⟩ := Finset.mem_offDiag.mp hyT1
      obtain ⟨hyc, hyd, -⟩ := Finset.mem_offDiag.mp hyT2
      rcases hS x.2.1 hxc y.2.1 hyc y.1.1 hya x.1.1 hxa (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rcases hS x.1.2 hxb y.1.2 hyb y.2.2 hyd x.2.2 hxd (by omega) with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · exact Prod.ext (Prod.ext e2.symm f1) (Prod.ext e1 f2.symm)
        · exfalso; exact hxn2 f1.symm
      · exfalso; exact hxn1 e1
  have hQs : Q.card ≤ Q'.card + (Q.filter (fun x => x.2.1 = x.1.1)).card
      + (Q.filter (fun x => x.2.2 = x.1.2)).card := by
    have hsub : Q ⊆ Q' ∪ Q.filter (fun x => x.2.1 = x.1.1) ∪ Q.filter (fun x => x.2.2 = x.1.2) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_union]
      by_cases h1 : x.2.1 = x.1.1
      · left; right; exact Finset.mem_filter.mpr ⟨hx, h1⟩
      · by_cases h2 : x.2.2 = x.1.2
        · right; exact Finset.mem_filter.mpr ⟨hx, h2⟩
        · left; left; rw [hQ']; exact Finset.mem_filter.mpr ⟨hx, h1, h2⟩
    have e1 := Finset.card_le_card hsub
    have e2 := Finset.card_union_le (Q' ∪ Q.filter (fun x => x.2.1 = x.1.1))
      (Q.filter (fun x => x.2.2 = x.1.2))
    have e3 := Finset.card_union_le Q' (Q.filter (fun x => x.2.1 = x.1.1))
    omega
  omega

theorem erdos_70264_hyp_runs :
    ∀ A : Set ℕ, A.Finite → IsSidon A →
      runsD A ≤ 2 * isoCount A + 10 * A.ncard + 3 := by
  intro A hA hSid
  obtain ⟨F, rfl⟩ := hA.exists_finset_coe
  have hS : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F, a + c = b + d →
      (a = b ∧ c = d) ∨ (a = d ∧ c = b) := by
    intro a ha b hb c hc d hd h
    exact hSid a ha b hb c hc d hd h
  have hmem : ∀ x : ℤ, x ∈ diffSetZ (↑F : Set ℕ) ↔
      x ∈ (F ×ˢ F).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) := by
    intro x
    rw [Finset.mem_image]
    unfold diffSetZ
    rw [Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, rfl⟩
  have hR : runsD (↑F : Set ℕ) = (((F ×ˢ F).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)).filter
      (fun z => z - 1 ∉ (F ×ˢ F).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2))).card := by
    unfold runsD
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hmem]
  have hI : isoCount (↑F : Set ℕ) =
      ((F + F).filter (fun s => s - 1 ∉ F + F ∧ s + 1 ∉ F + F)).card := by
    unfold isoCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, ← Finset.coe_add]
    tauto
  have hcore := runs_core F hS _ rfl (F + F) (fun s => Finset.mem_add)
  rw [hR, hI, Set.ncard_coe_finset]
  omega
end erdos_70264_hyp_runs_ns

theorem erdos_70264_hyp_runs :
    ∀ A : Set ℕ, A.Finite → IsSidon A →
      runsD A ≤ 2 * isoCount A + 10 * A.ncard + 3 := by
  exact erdos_70264_hyp_runs_ns.erdos_70264_hyp_runs



-- Core: the difference set of a large Sidon set is not a union of O(n) intervals.
-- A counterexample to the target must violate this, by hyp_runs.
theorem erdos_70264_hyp_core :
    ∀ M : ℕ, ∃ N : ℕ, ∀ A : Set ℕ, A.Finite → IsSidon A → N ≤ A.ncard →
      2 * M + 10 * A.ncard + 3 ≤ runsD A := by
  sorry

theorem erdos_70264 :
    Tendsto f atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨N, hN⟩ := erdos_70264_hyp_core M
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨A0, hA0n, hA0S⟩ := erdos_70264_hyp_exists n
  haveI : Nonempty {A : Set ℕ | A.ncard = n ∧ IsSidon A} := ⟨⟨A0, hA0n, hA0S⟩⟩
  unfold f
  apply le_ciInf
  rintro ⟨A, hA⟩
  have hA' : A.ncard = n ∧ IsSidon A := hA
  obtain ⟨hAn, hAS⟩ := hA'
  have hne : A.ncard ≠ 0 := by omega
  have hfin : A.Finite := Set.finite_of_ncard_ne_zero hne
  have h1 := erdos_70264_hyp_runs A hfin hAS
  have h2 := hN A hfin hAS (by omega)
  show M ≤ isoCount A
  omega