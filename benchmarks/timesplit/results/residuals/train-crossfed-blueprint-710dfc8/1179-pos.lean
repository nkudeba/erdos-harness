open scoped Classical
open Filter Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def repCount (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S ↦ ∑ x ∈ S, x = g).card

def IsBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(repCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

noncomputable def successProbability (G : Type*) [AddCommGroup G] [Fintype G] (ε : ℝ) (k : ℕ) :
    ℝ :=
  (((univ : Finset G).powersetCard k).filter (IsBalanced ε)).card /
    ((univ : Finset G).powersetCard k).card

def UniformGood (ε : ℝ) (N : ℕ) (k : ℕ) (η : ℝ) : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H], Fintype.card H = N →
    1 - η ≤ successProbability H ε k

-- Derived (pure real analysis, no groups): take δ_j = 1/(j+1) and strictly increasing
-- thresholds M_j ≥ N₀(δ_j); on [M_j, M_{j+1}) set k N = ⌈(1+δ_j) log₂ N⌉₊ and p N = δ_j.
-- Then j(N) → ∞, so p → 0 and k N / log₂ N ∈ [1+δ_j, 1+δ_j+1/log₂ N] → 1.
namespace erdos_99065_hyp_diag_ns
open scoped Classical

open Filter Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem erdos_99065_hyp_diag :
    ∀ P : ℕ → ℕ → ℝ → Prop,
      (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        P N ⌈(1 + δ) * Real.logb 2 N⌉₊ δ) →
      ∃ k : ℕ → ℕ, Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
        ∃ p : ℕ → ℝ, Tendsto p atTop (nhds 0) ∧ ∀ᶠ N in atTop, P N (k N) (p N) := by
  intro P h
  choose N₀ hN₀ using fun j : ℕ => h (1 / ((j : ℝ) + 1)) (by positivity)
  set J : ℕ → ℕ := fun N => Nat.findGreatest (fun j => ∀ i ≤ j, N₀ i ≤ N) N with hJdef
  have hJ : Tendsto J atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (m + (Finset.range (m+1)).sup N₀)] with N hN
    show m ≤ Nat.findGreatest (fun j => ∀ i ≤ j, N₀ i ≤ N) N
    apply Nat.le_findGreatest (by omega)
    intro i hi
    have hle : N₀ i ≤ (Finset.range (m+1)).sup N₀ :=
      Finset.le_sup (f := N₀) (Finset.mem_range.2 (by omega))
    omega
  have hδ : Tendsto (fun N => 1 / ((J N : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hJ
  have hL : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine ⟨fun N => ⌈(1 + 1 / ((J N : ℝ) + 1)) * Real.logb 2 N⌉₊, ?_,
    fun N => 1 / ((J N : ℝ) + 1), hδ, ?_⟩
  · have hlo : Tendsto (fun N => 1 + 1 / ((J N : ℝ) + 1)) atTop (nhds 1) := by
      have := hδ.const_add 1
      rwa [add_zero] at this
    have hhi : Tendsto (fun N => 1 + 1 / ((J N : ℝ) + 1) + (Real.logb 2 N)⁻¹)
        atTop (nhds 1) := by
      have := (hδ.const_add 1).add (tendsto_inv_atTop_zero.comp hL)
      rwa [add_zero, add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hL.eventually_gt_atTop 0] with N hN
      rw [le_div_iff₀ hN]
      exact Nat.le_ceil _
    · filter_upwards [hL.eventually_gt_atTop 0] with N hN
      rw [div_le_iff₀ hN, add_mul _ (Real.logb 2 N)⁻¹, inv_mul_cancel₀ hN.ne']
      have h0 : 0 ≤ (1 + 1 / ((J N : ℝ) + 1)) * Real.logb 2 N :=
        mul_nonneg (by positivity) hN.le
      exact (Nat.ceil_lt_add_one h0).le
  · filter_upwards [eventually_ge_atTop (N₀ 0)] with N hN
    have hspec : ∀ i ≤ J N, N₀ i ≤ N :=
      Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, N₀ i ≤ N) (Nat.zero_le N)
        (by intro i hi; rw [Nat.le_zero.1 hi]; exact hN)
    exact hN₀ (J N) N (hspec _ le_rfl)
end erdos_99065_hyp_diag_ns

theorem erdos_99065_hyp_diag :
    ∀ P : ℕ → ℕ → ℝ → Prop,
      (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        P N ⌈(1 + δ) * Real.logb 2 N⌉₊ δ) →
      ∃ k : ℕ → ℕ, Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
        ∃ p : ℕ → ℝ, Tendsto p atTop (nhds 0) ∧ ∀ᶠ N in atTop, P N (k N) (p N) := by
  exact erdos_99065_hyp_diag_ns.erdos_99065_hyp_diag



-- Conjecture (core): fixed-δ, uniform-in-G form of the Erdős–Rényi 1965 upper bound
-- log₂N + O_ε(log log N). Proved informally for F_2^n (spanning, failure ≤ 2^{n-k}) and
-- for Z/p (2m-th moments + Odlyzko + Littlewood–Offord). The general case needs the
-- truncated moment bound G2' (low-order kernel concentration excluded).
theorem erdos_99065_hyp_fixed_delta :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      UniformGood ε N ⌈(1 + δ) * Real.logb 2 N⌉₊ δ := by
  sorry

-- CHECK: div_le_one_of_le₀ tendsto_of_tendsto_of_tendsto_of_le_of_le' Finset.card_filter_le
theorem erdos_99065 :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ k : ℕ → ℕ,
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
      ∀ (G : ℕ → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i ↦ Fintype.card (G i)) atTop atTop →
          Tendsto (fun i ↦ successProbability (G i) ε (k (Fintype.card (G i)))) atTop
            (nhds 1) := by
  intro ε hε hε1
  obtain ⟨k, hk, p, hp, hP⟩ :=
    erdos_99065_hyp_diag (UniformGood ε) (erdos_99065_hyp_fixed_delta ε hε hε1)
  refine ⟨k, hk, ?_⟩
  intro G _ _ hG
  have h2 : Tendsto (fun i ↦ (1:ℝ) - p (Fintype.card (G i))) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (hp.comp hG)
  rw [sub_zero] at h2
  have hev := hG.eventually hP
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with i hi
    exact hi (G i) rfl
  · filter_upwards with i
    unfold successProbability
    apply div_le_one_of_le₀
    · exact_mod_cast Finset.card_filter_le _ _
    · positivity