open Filter
open scoped Topology

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

def IsTwoSidedCut {V : Type*} (G : SimpleGraph V) (s t : V) (T : Set V) : Prop :=
  ∃ hs : s ∈ Tᶜ, ∃ ht : t ∈ Tᶜ,
    ¬ (G.induce Tᶜ).Reachable ⟨s, hs⟩ ⟨t, ht⟩ ∧
    (∀ x : (Tᶜ : Set V), (G.induce Tᶜ).Reachable ⟨s, hs⟩ x ∨ (G.induce Tᶜ).Reachable ⟨t, ht⟩ x) ∧
    ∀ v ∈ T, (∃ x : (Tᶜ : Set V), (G.induce Tᶜ).Reachable ⟨s, hs⟩ x ∧ G.Adj v (x : V)) ∧
      (∃ y : (Tᶜ : Set V), (G.induce Tᶜ).Reachable ⟨t, ht⟩ y ∧ G.Adj v (y : V))

noncomputable def maxTwoSidedCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), ∃ s t : Fin n,
    {T : Set (Fin n) | IsTwoSidedCut G s t T}.ncard = k}

-- Lemma 1(b): every two-sided s|t cut is a minimal cut, so the two-sided count is at most c(n).
namespace erdos_90824_hyp_le_ns
open Filter

open scoped Topology

private lemma lift_reach {V : Type*} (G : SimpleGraph V) {A B : Set V} (h : A ⊆ B)
    {x y : A} (hr : (G.induce A).Reachable x y) :
    (G.induce B).Reachable ⟨x.1, h x.2⟩ ⟨y.1, h y.2⟩ := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj p ih =>
    have h1 : (G.induce B).Adj ⟨u.1, h u.2⟩ ⟨v.1, h v.2⟩ := hadj
    exact h1.reachable.trans ih

private lemma twoSided_minimal {V : Type*} (G : SimpleGraph V) (s t : V) (T : Set V)
    (hT : IsTwoSidedCut G s t T) : IsMinimalCut G T := by
  unfold IsTwoSidedCut at hT
  obtain ⟨hs, ht, hst, hcov, hadj⟩ := hT
  unfold IsMinimalCut
  refine ⟨fun hp => hst (hp _ _), ?_⟩
  intro S hS
  obtain ⟨v, hvT, hvS⟩ := Set.exists_of_ssubset hS
  have hTS : Tᶜ ⊆ Sᶜ := Set.compl_subset_compl.mpr hS.subset
  have hsS : s ∈ Sᶜ := hTS hs
  have htS : t ∈ Sᶜ := hTS ht
  have key : ∀ w (hw : w ∈ T) (hwS : w ∈ Sᶜ),
      (G.induce Sᶜ).Reachable ⟨w, hwS⟩ ⟨s, hsS⟩ := by
    intro w hw hwS
    obtain ⟨⟨x, hxr, hxadj⟩, -⟩ := hadj w hw
    have h1 : (G.induce Sᶜ).Adj ⟨w, hwS⟩ ⟨x.1, hTS x.2⟩ := hxadj
    have h2 := lift_reach G hTS hxr
    exact h1.reachable.trans h2.symm
  have keyt : ∀ w (hw : w ∈ T) (hwS : w ∈ Sᶜ),
      (G.induce Sᶜ).Reachable ⟨w, hwS⟩ ⟨t, htS⟩ := by
    intro w hw hwS
    obtain ⟨-, ⟨x, hxr, hxadj⟩⟩ := hadj w hw
    have h1 : (G.induce Sᶜ).Adj ⟨w, hwS⟩ ⟨x.1, hTS x.2⟩ := hxadj
    have h2 := lift_reach G hTS hxr
    exact h1.reachable.trans h2.symm
  have hts : (G.induce Sᶜ).Reachable ⟨t, htS⟩ ⟨s, hsS⟩ :=
    (keyt v hvT hvS).symm.trans (key v hvT hvS)
  have toS : ∀ a : (Sᶜ : Set V), (G.induce Sᶜ).Reachable a ⟨s, hsS⟩ := by
    intro a
    by_cases haT : a.1 ∈ T
    · exact key a.1 haT a.2
    · rcases hcov ⟨a.1, haT⟩ with h | h
      · exact (lift_reach G hTS h).symm
      · exact (lift_reach G hTS h).symm.trans hts
  intro a b
  exact (toS a).trans (toS b).symm

theorem erdos_90824_hyp_le :
    ∀ n : ℕ, maxTwoSidedCuts n ≤ maxMinimalCuts n := by
  intro n
  unfold maxTwoSidedCuts
  apply csSup_le'
  rintro k ⟨G, s, t, rfl⟩
  have hsub : {T | IsTwoSidedCut G s t T} ⊆ {T | IsMinimalCut G T} :=
    fun T hT => twoSided_minimal G s t T hT
  have hfin : {T : Set (Fin n) | IsMinimalCut G T}.Finite := Set.toFinite _
  calc {T | IsTwoSidedCut G s t T}.ncard ≤ {T | IsMinimalCut G T}.ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ maxMinimalCuts n := by
      unfold maxMinimalCuts
      apply le_csSup
      · refine ⟨(Set.univ : Set (Set (Fin n))).ncard, ?_⟩
        rintro m ⟨G', rfl⟩
        exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      · exact ⟨G, rfl⟩
end erdos_90824_hyp_le_ns

theorem erdos_90824_hyp_le :
    ∀ n : ℕ, maxTwoSidedCuts n ≤ maxMinimalCuts n := by
  exact erdos_90824_hyp_le_ns.erdos_90824_hyp_le



-- Lemma 3: parallel composition at s,t gives F(a+b-2) ≥ F(a)F(b); F(m+2) ≥ 1; F ≤ 2^n; then Fekete.
theorem erdos_90824_hyp_fekete :
    ∃ β : ℝ, Tendsto (fun n : ℕ ↦ (maxTwoSidedCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 β) := by
  sorry

-- Lemma 4: clique-merging W (|W| = k-1) turns k-component cuts into two-component cuts,
-- giving c_k ≤ C(n,k-1)·n²·F_st(n); cuts with > εn+1 components have a component of size < 1/ε.
theorem erdos_90824_hyp_merge :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ (maxTwoSidedCuts n : ℝ) ^ (1 / n : ℝ) + ε := by
  sorry

-- Lemma 2 (R2): c(n) ≤ (n+1)·Σ_{j≤n/3} C(n,j) ≤ (n+1)·1.89^n, hence the n-th root is eventually ≤ 1.9.
theorem erdos_90824_hyp_upper :
    ∀ᶠ n : ℕ in atTop, (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ) ≤ 19 / 10 := by
  sorry

theorem erdos_90824 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  obtain ⟨β, hβ⟩ := erdos_90824_hyp_fekete
  have hT : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 β) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have h1 := (tendsto_order.1 hβ).1 a ha
      filter_upwards [h1] with n hn
      have hle : (maxTwoSidedCuts n : ℝ) ≤ (maxMinimalCuts n : ℝ) := by
        exact_mod_cast erdos_90824_hyp_le n
      have hexp : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      exact lt_of_lt_of_le hn (Real.rpow_le_rpow (Nat.cast_nonneg _) hle hexp)
    · intro b hb
      have h1 := (tendsto_order.1 hβ).2 (β + (b - β) / 2) (by linarith)
      have h2 := erdos_90824_hyp_merge ((b - β) / 2) (by linarith)
      filter_upwards [h1, h2] with n hn1 hn2
      linarith
  have hα : β ≤ 19 / 10 := le_of_tendsto hT erdos_90824_hyp_upper
  exact ⟨β, by linarith, hT⟩