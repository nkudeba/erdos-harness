import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Combinatorics.Hindman

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-- Every finite sum of a positive stream is positive. -/
private lemma erdos_532_pos_of_mem_FS {a : Stream' ℕ} (ha : ∀ n, 0 < a n) {m : ℕ}
    (hm : m ∈ Hindman.FS a) : 0 < m := by
  induction hm with
  | head' a => exact ha 0
  | tail' a m h ih => exact ih (fun n => ha (n + 1))
  | cons' a m h ih =>
    have h1 := ih (fun n => ha (n + 1))
    have h2 := ha 0
    show 0 < a 0 + m
    omega

/-- Block boundaries: block `k` is `[N k, N (k+1))`, of length `1 + ∑_{j < N k} a j`. -/
private def erdos_532_N (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => erdos_532_N a k + 1 + ∑ j ∈ Finset.range (erdos_532_N a k), a j

/-- Block sums. -/
private def erdos_532_B (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1)), a j

private lemma erdos_532_N_succ (a : ℕ → ℕ) (k : ℕ) :
    erdos_532_N a (k + 1) = erdos_532_N a k + 1 + ∑ j ∈ Finset.range (erdos_532_N a k), a j :=
  rfl

private lemma erdos_532_N_strictMono (a : ℕ → ℕ) : StrictMono (erdos_532_N a) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [erdos_532_N_succ]
  omega

private lemma erdos_532_B_ge (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (k : ℕ) :
    1 + ∑ j ∈ Finset.range (erdos_532_N a k), a j ≤ erdos_532_B a k := by
  unfold erdos_532_B
  calc 1 + ∑ j ∈ Finset.range (erdos_532_N a k), a j
      = (Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1))).card := by
        rw [Nat.card_Ico, erdos_532_N_succ]; omega
    _ = ∑ j ∈ Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1)), 1 :=
        Finset.card_eq_sum_ones _
    _ ≤ ∑ j ∈ Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1)), a j :=
        Finset.sum_le_sum (fun j _ => ha j)

private lemma erdos_532_B_strictMono (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) :
    StrictMono (erdos_532_B a) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 := erdos_532_B_ge a ha (k + 1)
  have h2 : erdos_532_B a k ≤ ∑ j ∈ Finset.range (erdos_532_N a (k + 1)), a j := by
    unfold erdos_532_B
    apply Finset.sum_le_sum_of_subset
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    omega
  omega

private lemma erdos_532_disjoint (a : ℕ → ℕ) (T : Finset ℕ) :
    (↑T : Set ℕ).PairwiseDisjoint
      (fun k => Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1))) := by
  intro k _ l _ hkl
  have hmono := (erdos_532_N_strictMono a).monotone
  rw [Function.onFun, Finset.disjoint_left]
  intro j hj hj'
  simp only [Finset.mem_Ico] at hj hj'
  rcases lt_or_gt_of_ne hkl with h | h
  · have : erdos_532_N a (k + 1) ≤ erdos_532_N a l := hmono h
    omega
  · have : erdos_532_N a (l + 1) ≤ erdos_532_N a k := hmono h
    omega

theorem erdos_532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∃ i : Fin 2, ∀ S : Finset ℕ, S.Nonempty → (↑S : Set ℕ) ⊆ A →
        c (∑ n ∈ S, n) = i := by
  classical
  have hcov : Hindman.FS (Stream'.const (1 : ℕ)) ⊆
      ⋃₀ Set.range (fun i : Fin 2 => {n : ℕ | c n = i ∧ 0 < n}) := by
    intro m hm
    have hpos : 0 < m := erdos_532_pos_of_mem_FS (fun n => Nat.one_pos) hm
    exact Set.mem_sUnion.mpr ⟨_, ⟨c m, rfl⟩, ⟨rfl, hpos⟩⟩
  obtain ⟨C, hC, a, ha⟩ := Hindman.FS_partition_regular (Stream'.const (1 : ℕ)) _
    (Set.finite_range _) hcov
  obtain ⟨i, rfl⟩ := hC
  have hapos : ∀ n, 0 < a n := fun n => (ha (Hindman.FS.singleton a n)).2
  have hB := erdos_532_B_strictMono a hapos
  refine ⟨Set.range (erdos_532_B a), Set.infinite_range_of_injective hB.injective, ?_, i, ?_⟩
  · rintro n ⟨k, rfl⟩
    have := erdos_532_B_ge a hapos k
    omega
  · intro S hS hSA
    have hSA' : (↑S : Set ℕ) ⊆ erdos_532_B a '' Set.univ := by rwa [Set.image_univ]
    obtain ⟨T, -, rfl⟩ := Finset.subset_set_image_iff.mp hSA'
    have hT : T.Nonempty := Finset.image_nonempty.mp hS
    rw [Finset.sum_image (fun x _ y _ h => hB.injective h)]
    have hne : (T.biUnion (fun k => Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1)))).Nonempty := by
      rw [Finset.biUnion_nonempty]
      obtain ⟨k, hk⟩ := hT
      refine ⟨k, hk, ?_⟩
      rw [Finset.nonempty_Ico]
      exact erdos_532_N_strictMono a (Nat.lt_succ_self k)
    have hmem := Hindman.FS.finsetSum a _ hne
    have key : (∑ k ∈ T, erdos_532_B a k) =
        ∑ j ∈ T.biUnion (fun k => Finset.Ico (erdos_532_N a k) (erdos_532_N a (k + 1))), a j := by
      rw [Finset.sum_biUnion (erdos_532_disjoint a T)]
      rfl
    rw [key]
    exact (ha hmem).1
