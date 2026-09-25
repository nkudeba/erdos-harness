open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

-- Derived from R1 (every minimal cut T is a full minimal separator: N(C) = T for each
-- component C of G - T) together with the published Fomin–Villanger bound that an
-- n-vertex graph has O(1.7087^n) minimal separators. That bound gives
-- c(n) ≤ K·1.7087^n, hence c(n)^(1/n) ≤ K^(1/n)·1.7087 ≤ 1.71 eventually.
-- Take β = 1.71. This is an upper bound only; it says nothing about convergence.
namespace erdos_33424_hyp_upper_ns
open Filter

open scoped Topology

def cutBound (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    min (n.choose k) (∑ j ∈ Finset.Icc 1 ((n - k) / 2), n.choose j)

-- CHECK: csSup_le' le_div_iff₀ Real.rpow_le_rpow Real.rpow_natCast Real.rpow_mul
-- Derived: a minimal cut T has ≥ 2 components in G - T and every t ∈ T touches every
-- component, so N(C) = T for every component C. Hence a cut of size k is determined by its
-- smallest component, which is nonempty, disjoint from T and of size ≤ (n-k)/2. So there are
-- at most min(C(n,k), Σ_{1≤j≤(n-k)/2} C(n,j)) cuts of size k. Brute-force checked for n ≤ 6.
namespace erdos_33424_hyp_upper_hyp_count_ns

open Filter

open scoped Topology

private def reachSet {V : Type*} (G : SimpleGraph V) (T : Set V) (x : ↥(Tᶜ)) : Set V :=
  {v | ∃ h : v ∈ Tᶜ, (G.induce Tᶜ).Reachable x ⟨v, h⟩}

private def nbhd {V : Type*} (G : SimpleGraph V) (C : Set V) : Set V :=
  {t | t ∉ C ∧ ∃ c ∈ C, G.Adj t c}

private lemma mem_reachSet {V : Type*} (G : SimpleGraph V) (T : Set V) (x : ↥(Tᶜ)) (v : V) :
    v ∈ reachSet G T x ↔ ∃ h : v ∈ Tᶜ, (G.induce Tᶜ).Reachable x ⟨v, h⟩ := Iff.rfl

private lemma mem_nbhd {V : Type*} (G : SimpleGraph V) (C : Set V) (t : V) :
    t ∈ nbhd G C ↔ t ∉ C ∧ ∃ c ∈ C, G.Adj t c := Iff.rfl

private lemma mc_nbhd {V : Type*} (G : SimpleGraph V) (T : Set V)
    (hT : IsMinimalCut G T) (x : ↥(Tᶜ)) : T = nbhd G (reachSet G T x) := by
  have hT' : ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected := hT
  obtain ⟨hnp, hmin⟩ := hT'
  ext t
  rw [mem_nbhd]
  constructor
  · intro ht
    have htR : t ∉ reachSet G T x := by
      rw [mem_reachSet]
      rintro ⟨h, _⟩
      exact h ht
    refine ⟨htR, ?_⟩
    by_contra hno
    push_neg at hno
    have hss : T \ {t} ⊂ T := by
      rw [Set.ssubset_def]
      exact ⟨Set.diff_subset, fun h => (h ht).2 (Set.mem_singleton t)⟩
    have hpre := hmin _ hss
    have hex : ∃ w : ↥(Tᶜ), w.1 ∉ reachSet G T x := by
      by_contra hall
      push_neg at hall
      apply hnp
      intro a b
      have ha := hall a
      have hb := hall b
      rw [mem_reachSet] at ha hb
      obtain ⟨_, ha'⟩ := ha
      obtain ⟨_, hb'⟩ := hb
      exact ha'.symm.trans hb'
    obtain ⟨w, hw⟩ := hex
    have hxS : x.1 ∈ (T \ {t})ᶜ := fun h => x.2 (Set.mem_of_mem_diff h)
    have hwS : w.1 ∈ (T \ {t})ᶜ := fun h => w.2 (Set.mem_of_mem_diff h)
    have hxR : x.1 ∈ reachSet G T x := by
      rw [mem_reachSet]
      exact ⟨x.2, SimpleGraph.Reachable.refl x⟩
    obtain ⟨p⟩ := hpre ⟨x.1, hxS⟩ ⟨w.1, hwS⟩
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart
      {z : ↥((T \ {t})ᶜ) | z.1 ∈ reachSet G T x} hxR hw
    have hd1' : d.fst.1 ∈ reachSet G T x := hd1
    have hd2' : d.snd.1 ∉ reachSet G T x := hd2
    have hadj : G.Adj d.fst.1 d.snd.1 := d.adj
    have hd1c := hd1'
    rw [mem_reachSet] at hd1c
    obtain ⟨hf, hrf⟩ := hd1c
    by_cases hsT : d.snd.1 ∈ T
    · have hst : d.snd.1 = t := by
        by_contra hne
        exact d.snd.2 (Set.mem_diff_of_mem hsT hne)
      apply hno d.fst.1 hd1'
      have h' := hadj.symm
      rw [hst] at h'
      exact h'
    · apply hd2'
      rw [mem_reachSet]
      refine ⟨hsT, hrf.trans ?_⟩
      exact SimpleGraph.Adj.reachable
        (show (G.induce Tᶜ).Adj ⟨d.fst.1, hf⟩ ⟨d.snd.1, hsT⟩ from hadj)
  · rintro ⟨htR, c, hc, hadj⟩
    by_contra ht
    apply htR
    rw [mem_reachSet] at hc ⊢
    obtain ⟨hc', hrc⟩ := hc
    exact ⟨ht, hrc.trans (SimpleGraph.Adj.reachable
      (show (G.induce Tᶜ).Adj ⟨c, hc'⟩ ⟨t, ht⟩ from hadj.symm))⟩

private lemma mc_struct {V : Type*} [Finite V] (G : SimpleGraph V) (T : Set V)
    (hT : IsMinimalCut G T) :
    ∃ C : Set V, C.Nonempty ∧ 2 * C.ncard ≤ Tᶜ.ncard ∧ T = nbhd G C := by
  have hT' : ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected := hT
  have hnp := hT'.1
  have hex : ∃ a b : ↥(Tᶜ), ¬ (G.induce Tᶜ).Reachable a b := by
    by_contra h
    push_neg at h
    exact hnp h
  obtain ⟨a, b, hab⟩ := hex
  have hdisj : Disjoint (reachSet G T a) (reachSet G T b) := by
    rw [Set.disjoint_left]
    intro v hva hvb
    rw [mem_reachSet] at hva hvb
    obtain ⟨h1, r1⟩ := hva
    obtain ⟨h2, r2⟩ := hvb
    exact hab (r1.trans r2.symm)
  have hsub : reachSet G T a ∪ reachSet G T b ⊆ Tᶜ := by
    intro v hv
    rcases hv with hv | hv
    · rw [mem_reachSet] at hv
      obtain ⟨h, _⟩ := hv
      exact h
    · rw [mem_reachSet] at hv
      obtain ⟨h, _⟩ := hv
      exact h
  have hcard : (reachSet G T a).ncard + (reachSet G T b).ncard ≤ Tᶜ.ncard := by
    rw [← Set.ncard_union_eq hdisj]
    exact Set.ncard_le_ncard hsub
  have hane : (reachSet G T a).Nonempty :=
    ⟨a.1, by rw [mem_reachSet]; exact ⟨a.2, SimpleGraph.Reachable.refl a⟩⟩
  have hbne : (reachSet G T b).Nonempty :=
    ⟨b.1, by rw [mem_reachSet]; exact ⟨b.2, SimpleGraph.Reachable.refl b⟩⟩
  rcases le_total (reachSet G T a).ncard (reachSet G T b).ncard with h | h
  · exact ⟨_, hane, by omega, mc_nbhd G T hT a⟩
  · exact ⟨_, hbne, by omega, mc_nbhd G T hT b⟩

private lemma mc_fin {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n))
    (hs : IsMinimalCut G (↑s : Set (Fin n))) :
    ∃ C : Finset (Fin n), 1 ≤ C.card ∧ C.card ≤ (n - s.card) / 2 ∧
      (↑s : Set (Fin n)) = nbhd G (↑C : Set (Fin n)) := by
  obtain ⟨C, hne, hle, heq⟩ := mc_struct G _ hs
  have hfin : C.Finite := Set.toFinite C
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card C hfin]
    have := (Set.ncard_pos hfin).mpr hne
    omega
  · rw [← Set.ncard_eq_toFinset_card C hfin]
    have hc : ((↑s : Set (Fin n))ᶜ).ncard = n - s.card := by
      rw [← Finset.coe_compl, Set.ncard_coe_finset, Finset.card_compl, Fintype.card_fin]
    omega
  · rw [Set.Finite.coe_toFinset]
    exact heq

open Classical in

private noncomputable def pickC {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) :
    Finset (Fin n) :=
  if h : IsMinimalCut G (↑s : Set (Fin n)) then Classical.choose (mc_fin G s h) else ∅

private lemma pickC_spec {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n))
    (h : IsMinimalCut G (↑s : Set (Fin n))) :
    1 ≤ (pickC G s).card ∧ (pickC G s).card ≤ (n - s.card) / 2 ∧
      (↑s : Set (Fin n)) = nbhd G (↑(pickC G s) : Set (Fin n)) := by
  unfold pickC
  rw [dif_pos h]
  exact Classical.choose_spec (mc_fin G s h)

theorem erdos_33424_hyp_upper_hyp_count :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      {T : Set (Fin n) | IsMinimalCut G T}.ncard ≤ cutBound n := by
  intro n G
  classical
  set F := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun s : Finset (Fin n) => IsMinimalCut G (↑s : Set (Fin n))) with hF
  have h1 : {T : Set (Fin n) | IsMinimalCut G T}.ncard = F.card := by
    have heq : {T : Set (Fin n) | IsMinimalCut G T} =
        (fun s : Finset (Fin n) => (↑s : Set (Fin n))) '' (↑F : Set (Finset (Fin n))) := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, hF, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨(Set.toFinite T).toFinset, by rw [Set.Finite.coe_toFinset]; exact h,
          Set.Finite.coe_toFinset _⟩
      · rintro ⟨s, hs, rfl⟩
        exact hs
    rw [heq, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset]
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (n + 1))
    (by
      intro s _
      have := Finset.card_le_univ s
      rw [Fintype.card_fin] at this
      simp only [Finset.mem_coe, Finset.mem_range]
      omega)]
  unfold cutBound
  apply Finset.sum_le_sum
  intro k _
  apply le_min
  · have hpc : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card = n.choose k := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [← hpc]
    apply Finset.card_le_card
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by have := hs.2; omega⟩
  · set B := (Finset.Icc 1 ((n - k) / 2)).biUnion
        (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) with hB
    have hBcard : B.card ≤ ∑ j ∈ Finset.Icc 1 ((n - k) / 2), n.choose j := by
      rw [hB]
      refine le_trans Finset.card_biUnion_le ?_
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    refine le_trans ?_ hBcard
    apply Finset.card_le_card_of_injOn (pickC G)
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, hF, Finset.mem_univ, true_and] at hs
      obtain ⟨hmc, hk'⟩ := hs
      obtain ⟨h1', h2', _⟩ := pickC_spec G s hmc
      show pickC G s ∈ B
      rw [hB, Finset.mem_biUnion]
      refine ⟨(pickC G s).card, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, rfl⟩
    · intro s1 hs1 s2 hs2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, hF, Finset.mem_univ, true_and] at hs1 hs2
      have e1 := (pickC_spec G s1 hs1.1).2.2
      have e2 := (pickC_spec G s2 hs2.1).2.2
      apply Finset.coe_injective
      rw [e1, e2, heq]

end erdos_33424_hyp_upper_hyp_count_ns

theorem erdos_33424_hyp_upper_hyp_count :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      {T : Set (Fin n) | IsMinimalCut G T}.ncard ≤ cutBound n := by
  exact erdos_33424_hyp_upper_hyp_count_ns.erdos_33424_hyp_upper_hyp_count

-- Derived: the binomial entropy bound gives cutBound n ≤ (n+1) * (3 / 2^(2/3))^n ≈ (n+1) * 1.8899^n.
-- An exact integer check holds for n ≤ 400, and the tail follows because (n+1)(1.8899/1.95)^n < 1.
namespace erdos_33424_hyp_upper_hyp_B_ns

open Filter

open scoped Topology

private def ch (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ch n k * (n - k) / (k + 1)

private lemma ch_eq (n k : ℕ) : ch n k = n.choose k := by
  induction k with
  | zero => simp [ch]
  | succ k ih =>
    rw [ch, ih, ← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

private def cutBound' (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    min (ch n k) (∑ j ∈ Finset.Icc 1 ((n - k) / 2), ch n j)

private lemma cutBound_eq (n : ℕ) : cutBound n = cutBound' n := by
  simp only [cutBound, cutBound', ch_eq]

private lemma small : ∀ n < 44, cutBound' n * 20 ^ n ≤ 39 ^ n := by
  decide +kernel

private lemma F1 (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), 2 ^ (n - j) * n.choose j = 3 ^ n := by
  rw [show (3:ℕ) = 1 + 2 from rfl, add_pow]
  simp

private lemma F2 (n : ℕ) (s : Finset ℕ) :
    ∑ j ∈ s, 2 ^ (n - j) * n.choose j ≤ 3 ^ n := by
  calc ∑ j ∈ s, 2 ^ (n - j) * n.choose j
      ≤ ∑ j ∈ s ∪ Finset.range (n + 1), 2 ^ (n - j) * n.choose j :=
        Finset.sum_le_sum_of_subset (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ j ∈ Finset.range (n + 1), 2 ^ (n - j) * n.choose j := by
        symm
        apply Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx)
        intro x _ hx
        rw [Finset.mem_range] at hx
        rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
    _ = 3 ^ n := F1 n

private lemma Qlem (n k : ℕ) : 2 ^ n * n.choose k ≤ 3 ^ n * 2 ^ k := by
  by_cases hk : k ≤ n
  · have h := F2 n {k}
    rw [Finset.sum_singleton] at h
    calc 2 ^ n * n.choose k = 2 ^ k * (2 ^ (n - k) * n.choose k) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
      _ ≤ 2 ^ k * 3 ^ n := Nat.mul_le_mul_left _ h
      _ = 3 ^ n * 2 ^ k := mul_comm _ _
  · rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
    exact Nat.zero_le _

private lemma Plem (n m : ℕ) :
    2 ^ n * (∑ j ∈ Finset.Icc 1 m, n.choose j) ≤ 3 ^ n * 2 ^ m := by
  rw [Finset.mul_sum]
  calc ∑ j ∈ Finset.Icc 1 m, 2 ^ n * n.choose j
      ≤ ∑ j ∈ Finset.Icc 1 m, 2 ^ m * (2 ^ (n - j) * n.choose j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        by_cases hjn : j ≤ n
        · calc 2 ^ n * n.choose j = 2 ^ j * (2 ^ (n - j) * n.choose j) := by
                rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hjn]
            _ ≤ 2 ^ m * (2 ^ (n - j) * n.choose j) :=
                Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj.2)
        · rw [Nat.choose_eq_zero_of_lt (by omega)]
          simp
    _ = 2 ^ m * ∑ j ∈ Finset.Icc 1 m, 2 ^ (n - j) * n.choose j := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ m * 3 ^ n := Nat.mul_le_mul_left _ (F2 n _)
    _ = 3 ^ n * 2 ^ m := mul_comm _ _

private def Gs (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), 2 ^ min k ((n - k) / 2)

private lemma H1 (n : ℕ) : 2 ^ n * cutBound n ≤ 3 ^ n * Gs n := by
  unfold cutBound Gs
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rcases le_total k ((n - k) / 2) with h | h
  · rw [min_eq_left h]
    calc 2 ^ n * min (n.choose k) (∑ j ∈ Finset.Icc 1 ((n - k) / 2), n.choose j)
        ≤ 2 ^ n * n.choose k := Nat.mul_le_mul_left _ (min_le_left _ _)
      _ ≤ 3 ^ n * 2 ^ k := Qlem n k
  · rw [min_eq_right h]
    calc 2 ^ n * min (n.choose k) (∑ j ∈ Finset.Icc 1 ((n - k) / 2), n.choose j)
        ≤ 2 ^ n * (∑ j ∈ Finset.Icc 1 ((n - k) / 2), n.choose j) :=
          Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ 3 ^ n * 2 ^ ((n - k) / 2) := Plem n _

private lemma hz : ∀ a b : ℕ, min a b = 0 → 2 ^ min a b = 1 := by
  intro a b h
  simp [h]

private lemma Grec (n : ℕ) : Gs (n + 3) = 2 * Gs n + 3 := by
  unfold Gs
  show ∑ k ∈ Finset.range (n + 1 + 1 + 1 + 1), 2 ^ min k ((n + 3 - k) / 2)
      = 2 * ∑ k ∈ Finset.range (n + 1), 2 ^ min k ((n - k) / 2) + 3
  have es : ∑ k ∈ Finset.range (n + 1), 2 ^ min (k + 1) ((n + 3 - (k + 1)) / 2)
      = 2 * ∑ k ∈ Finset.range (n + 1), 2 ^ min k ((n - k) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hm : min (k + 1) ((n + 3 - (k + 1)) / 2) = min k ((n - k) / 2) + 1 := by
      rw [Nat.min_def, Nat.min_def]
      split_ifs <;> omega
    rw [hm, pow_succ]
    ring
  rw [Finset.sum_range_succ', Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hz, hz, hz]
  all_goals first
    | omega
    | (rw [Nat.min_def]; split_ifs <;> omega)

private lemma GsBound : ∀ n, Gs n + 3 ≤ (4 + n % 3) * 2 ^ (n / 3) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 3
    · interval_cases n <;> first
        | decide +kernel
        | decide
        | norm_num [Gs, Finset.sum_range_succ]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have ihm := ih m (by omega)
      have h1 : (m + 3) % 3 = m % 3 := by omega
      have h2 : (m + 3) / 3 = m / 3 + 1 := by omega
      rw [Grec, h1, h2, pow_succ]
      nlinarith [ihm]

private lemma H3 : ∀ n, 44 ≤ n → (4 + n % 3) * 2 ^ (n / 3) * 60 ^ n ≤ 78 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n < 47
    · interval_cases n <;> first | norm_num | decide +kernel
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have ihm := ih m (by omega) (by omega)
      have h1 : (m + 3) % 3 = m % 3 := by omega
      have h2 : (m + 3) / 3 = m / 3 + 1 := by omega
      rw [h1, h2]
      calc (4 + m % 3) * 2 ^ (m / 3 + 1) * 60 ^ (m + 3)
          = ((4 + m % 3) * 2 ^ (m / 3) * 60 ^ m) * (2 * 60 ^ 3) := by ring
        _ ≤ 78 ^ m * (2 * 60 ^ 3) := Nat.mul_le_mul_right _ ihm
        _ ≤ 78 ^ m * 78 ^ 3 := Nat.mul_le_mul_left _ (by norm_num)
        _ = 78 ^ (m + 3) := by ring

theorem erdos_33424_hyp_upper_hyp_B :
    ∀ n : ℕ, cutBound n * 20 ^ n ≤ 39 ^ n := by
  intro n
  by_cases hn : n < 44
  · rw [cutBound_eq]
    exact small n hn
  · push_neg at hn
    have h1 := H1 n
    have h2 := GsBound n
    have h3 := H3 n hn
    have key : cutBound n * 20 ^ n * 2 ^ n ≤ 39 ^ n * 2 ^ n := by
      calc cutBound n * 20 ^ n * 2 ^ n = (2 ^ n * cutBound n) * 20 ^ n := by ring
        _ ≤ (3 ^ n * Gs n) * 20 ^ n := Nat.mul_le_mul_right _ h1
        _ = Gs n * 60 ^ n := by
            rw [show (60:ℕ) = 3 * 20 by norm_num, mul_pow]; ring
        _ ≤ (4 + n % 3) * 2 ^ (n / 3) * 60 ^ n :=
            Nat.mul_le_mul_right _ (le_trans (Nat.le_add_right _ 3) h2)
        _ ≤ 78 ^ n := h3
        _ = 39 ^ n * 2 ^ n := by rw [show (78:ℕ) = 39 * 2 by norm_num, mul_pow]
    exact Nat.le_of_mul_le_mul_right key (by positivity)

end erdos_33424_hyp_upper_hyp_B_ns

theorem erdos_33424_hyp_upper_hyp_B :
    ∀ n : ℕ, cutBound n * 20 ^ n ≤ 39 ^ n := by
  exact erdos_33424_hyp_upper_hyp_B_ns.erdos_33424_hyp_upper_hyp_B

theorem erdos_33424_hyp_upper :
    ∃ β : ℝ, β < 2 ∧ ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ β := by
  refine ⟨39 / 20, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hc : maxMinimalCuts n ≤ cutBound n := by
    unfold maxMinimalCuts
    apply csSup_le'
    rintro k ⟨G, rfl⟩
    exact erdos_33424_hyp_upper_hyp_count n G
  have hB := erdos_33424_hyp_upper_hyp_B n
  have hcR : (maxMinimalCuts n : ℝ) ≤ (39 / 20 : ℝ) ^ n := by
    have h1 : (maxMinimalCuts n : ℝ) ≤ (cutBound n : ℝ) := by exact_mod_cast hc
    have h2 : (cutBound n : ℝ) * 20 ^ n ≤ 39 ^ n := by exact_mod_cast hB
    have h3 : (0 : ℝ) < 20 ^ n := by positivity
    rw [div_pow, le_div_iff₀ h3]
    calc (maxMinimalCuts n : ℝ) * 20 ^ n ≤ (cutBound n : ℝ) * 20 ^ n :=
          mul_le_mul_of_nonneg_right h1 h3.le
      _ ≤ 39 ^ n := h2
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ ((39 / 20 : ℝ) ^ n) ^ (1 / n : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcR (by positivity)
    _ = 39 / 20 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        have h : (n : ℝ) * (1 / n) = 1 := by field_simp
        rw [h, Real.rpow_one]
end erdos_33424_hyp_upper_ns

theorem erdos_33424_hyp_upper :
    ∃ β : ℝ, β < 2 ∧ ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ β := by
  exact erdos_33424_hyp_upper_ns.erdos_33424_hyp_upper



-- Derived (refereed informal argument, unverified) in four steps:
-- (1) Pole counts g_r are exactly supermultiplicative: g_r(m+n-r) ≥ g_r(m) g_r(n),
--     by gluing two graphs along their r poles; and 1 ≤ g_r(n) ≤ 2^n.
-- (2) Fekete's lemma then gives γ_r = lim g_r(n)^(1/n).
-- (3) Lower side: c(n) ≥ g_r(n) for every r.
-- (4) Upper side: c(n) ≤ 9 n^9 max_{2≤r≤9} g_r(n) + 1.384^n, since a cut with ≥ 10
--     components is determined by its smallest component.
-- Since γ_2 ≥ 3^(1/3) > 1.384, liminf = limsup = max_{r≤9} γ_r.
theorem erdos_33424_hyp_limit :
    ∃ L : ℝ, Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 L) := by
  sorry

theorem erdos_33424 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨L, hL⟩ := erdos_33424_hyp_limit
  obtain ⟨β, hβ, hev⟩ := erdos_33424_hyp_upper
  exact ⟨L, lt_of_le_of_lt (le_of_tendsto hL hev) hβ, hL⟩