open Finset Filter
open scoped Asymptotics

def TriFree (A : Finset ℕ) : Prop :=
  ¬ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

def topMiss (N : ℕ) (A : Finset ℕ) : ℕ :=
  (((Icc 1 N).filter (fun x => N < 2 * x)) \ A).card

-- Stability conjecture: a triangle-free A ⊆ [1,N] of size ≥ 5N/8 + C must contain all but
-- at most N/100 elements of the top half (N/2, N]. Every known near-extremal example has this shape:
-- {odd x ≤ N/4} ∪ (N/2,N], and (N/8,N/4] ∪ (N/2,N].
-- Adding many evens to the odds breaks triangle-freeness: three odd numbers near N/2 have all
-- pairwise sums even and near N.
theorem erdos_29255_hyp_stability :
    ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A →
      (A.card : ℝ) ≥ (5 / 8 : ℝ) * N + C → 100 * topMiss N A ≤ N := by
  sorry

-- Exact step for the near-extremal regime: if the top half is almost full (≤ N/100 missing),
-- then the low part S = A ∩ [1,N/2] is forced to be nearly sum-free, with pairwise sums ≤ N/2.
-- Each missing top element can only unblock boundedly many low configurations.
-- This yields |A| < 5N/8 + C. It is the target restricted to the near-extremal shape.
namespace erdos_29255_hyp_exact_ns
open Finset Filter

open scoped Asymptotics

-- Derived (rigorous, refutation stage "Lemma 1"): for c in (N/2, N-b], the numbers c, c+a, c+b all lie in
-- the top half T; if all three lie in A then (a,b,c) is a triangle, because c > N/2 ≥ b > a.
-- Each missing y ∈ T \ A excludes at most 3 values of c (c = y, y-a, y-b).
namespace erdos_29255_hyp_exact_hyp_schur_ns

open Finset Filter

open scoped Asymptotics

open Finset Filter

open scoped Asymptotics

theorem erdos_29255_hyp_exact_hyp_schur :
    ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A → ∀ a ∈ A, ∀ b ∈ A, a < b → 2 * b ≤ N →
      a + b ∈ A → N - b - N / 2 ≤ 3 * topMiss N A := by
  intro N A hA hT a ha b hb hab h2b habA
  set M := ((Icc 1 N).filter (fun x => N < 2 * x)) \ A with hM
  have hmem : ∀ x, 1 ≤ x → x ≤ N → N < 2 * x → x ∉ A → x ∈ M := by
    intro x h1 h2 h3 h4
    rw [hM, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  have hsub : Icc (N/2+1) (N-b) ⊆
      M ∪ M.image (fun m => m - a) ∪ M.image (fun m => m - b) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases h1 : c ∈ A
    · by_cases h2 : c + a ∈ A
      · by_cases h3 : c + b ∈ A
        · exfalso
          apply hT
          refine ⟨a, ha, b, hb, c, h1, ?_, ?_, ?_, habA, ?_, ?_⟩
          · omega
          · omega
          · omega
          · rw [Nat.add_comm]; exact h2
          · rw [Nat.add_comm]; exact h3
        · right
          exact ⟨c + b, hmem _ (by omega) (by omega) (by omega) h3, by simp⟩
      · left; right
        exact ⟨c + a, hmem _ (by omega) (by omega) (by omega) h2, by simp⟩
    · left; left
      exact hmem c (by omega) (by omega) (by omega) h1
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have h1 := Finset.card_union_le (M ∪ M.image (fun m => m - a)) (M.image (fun m => m - b))
  have h2 := Finset.card_union_le M (M.image (fun m => m - a))
  have h3 : (M.image (fun m => m - a)).card ≤ M.card := Finset.card_image_le
  have h4 : (M.image (fun m => m - b)).card ≤ M.card := Finset.card_image_le
  have htop : topMiss N A = M.card := rfl
  rw [htop]
  omega

end erdos_29255_hyp_exact_hyp_schur_ns

theorem erdos_29255_hyp_exact_hyp_schur :
    ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A → ∀ a ∈ A, ∀ b ∈ A, a < b → 2 * b ≤ N →
      a + b ∈ A → N - b - N / 2 ≤ 3 * topMiss N A := by
  exact erdos_29255_hyp_exact_hyp_schur_ns.erdos_29255_hyp_exact_hyp_schur

-- Derived (elementary): let x = max W. The pairs {y, x-y} with y ≠ x-y each hold at most one element of W.
-- Hence |W| ≤ ⌊x/2⌋ + 1 ≤ M/2 + 1.
namespace erdos_29255_hyp_exact_hyp_sumfree_ns

open Finset Filter

open scoped Asymptotics

open Finset Filter

open scoped Asymptotics

theorem erdos_29255_hyp_exact_hyp_sumfree :
    ∀ M : ℕ, ∀ W : Finset ℕ, W ⊆ Icc 1 M →
      (∀ a ∈ W, ∀ b ∈ W, a < b → a + b ∉ W) → 2 * W.card ≤ M + 2 := by
  intro M W hW hsum
  rcases W.eq_empty_or_nonempty with h | h
  · simp [h]
  obtain ⟨m, hmW, hle⟩ : ∃ m ∈ W, ∀ x ∈ W, x ≤ m :=
    ⟨W.max' h, W.max'_mem h, fun x hx => W.le_max' x hx⟩
  have hmM : m ≤ M := (Finset.mem_Icc.mp (hW hmW)).2
  have hT : (W.erase m).card + 1 = W.card := Finset.card_erase_add_one hmW
  have hinj : Set.InjOn (fun x => m - x) (W.erase m : Set ℕ) := by
    intro x hx y hy hxy
    have hxy' : m - x = m - y := hxy
    have h1 := hle x (Finset.mem_of_mem_erase hx)
    have h2 := hle y (Finset.mem_of_mem_erase hy)
    omega
  have himg : ((W.erase m).image (fun x => m - x)).card = (W.erase m).card :=
    Finset.card_image_of_injOn hinj
  have hsub : W.erase m ∪ (W.erase m).image (fun x => m - x) ⊆ Icc 1 (m - 1) := by
    intro z hz
    rw [Finset.mem_union, Finset.mem_image] at hz
    rw [Finset.mem_Icc]
    rcases hz with hz | ⟨x, hx, hxz⟩
    · have h1 := Finset.ne_of_mem_erase hz
      have h2 := Finset.mem_of_mem_erase hz
      have h3 := hle z h2
      have h4 := (Finset.mem_Icc.mp (hW h2)).1
      omega
    · have hxz' : m - x = z := hxz
      have h1 := Finset.ne_of_mem_erase hx
      have h2 := Finset.mem_of_mem_erase hx
      have h3 := hle x h2
      have h4 := (Finset.mem_Icc.mp (hW h2)).1
      omega
  have hinter : W.erase m ∩ (W.erase m).image (fun x => m - x) ⊆ {m / 2} := by
    intro z hz
    rw [Finset.mem_inter, Finset.mem_image] at hz
    obtain ⟨hzT, x, hx, hxz⟩ := hz
    have hxz' : m - x = z := hxz
    rw [Finset.mem_singleton]
    have hz2 := Finset.mem_of_mem_erase hzT
    have hx2 := Finset.mem_of_mem_erase hx
    have h3 := hle z hz2
    have h4 := hle x hx2
    by_contra hne
    have hsumzx : z + x = m := by omega
    rcases lt_trichotomy z x with hlt | heq | hgt
    · exact hsum z hz2 x hx2 hlt (by rw [hsumzx]; exact hmW)
    · omega
    · exact hsum x hx2 z hz2 hgt (by rw [add_comm, hsumzx]; exact hmW)
  have hcard := Finset.card_union_add_card_inter (W.erase m) ((W.erase m).image (fun x => m - x))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card hinter
  rw [Nat.card_Icc] at h1
  rw [Finset.card_singleton] at h2
  omega

end erdos_29255_hyp_exact_hyp_sumfree_ns

theorem erdos_29255_hyp_exact_hyp_sumfree :
    ∀ M : ℕ, ∀ W : Finset ℕ, W ⊆ Icc 1 M →
      (∀ a ∈ W, ∀ b ∈ W, a < b → a + b ∉ W) → 2 * W.card ≤ M + 2 := by
  exact erdos_29255_hyp_exact_hyp_sumfree_ns.erdos_29255_hyp_exact_hyp_sumfree

-- Conjecture (hard core): the elements of A in (N/4, N/2] are paid for by missing top elements.
-- Mid elements (below N/2 - 3m) have all pairwise sums missing from T, giving ≤ (m+3)/2 of them.
-- Band elements need missing sums or missing c's; the parity example (N/2-k, N/2] with k evens
-- missing near N gives equality u = m.
-- When m = 0 the bound is u ≤ 2, rigorously from hyp_schur.
theorem erdos_29255_hyp_exact_hyp_mid :
    ∃ C : ℕ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A → 100 * topMiss N A ≤ N →
      (A.filter (fun x => N / 4 < x ∧ 2 * x ≤ N)).card ≤ topMiss N A + C := by
  sorry

-- CHECK: Finset.card_sdiff_add_card_inter Nat.card_Icc Finset.card_union_le Finset.card_le_card
open Finset Filter

open scoped Asymptotics

theorem erdos_29255_hyp_exact :
    ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A →
      100 * topMiss N A ≤ N → (A.card : ℝ) < (5 / 8 : ℝ) * N + C := by
  obtain ⟨C0, hC0⟩ := erdos_29255_hyp_exact_hyp_mid
  refine ⟨(C0 : ℝ) + 3, by positivity, ?_⟩
  intro N A hA hT hm
  have htop : (A.filter (fun x => N < 2 * x)).card + topMiss N A ≤ N - N / 2 := by
    have h1 : (A.filter (fun x => N < 2 * x)) ⊆
        ((Icc 1 N).filter (fun x => N < 2 * x)) ∩ A := by
      intro x hx
      rw [mem_filter] at hx
      rw [mem_inter, mem_filter]
      exact ⟨⟨hA hx.1, hx.2⟩, hx.1⟩
    have h2 := Finset.card_sdiff_add_card_inter ((Icc 1 N).filter (fun x => N < 2 * x)) A
    have h3 : ((Icc 1 N).filter (fun x => N < 2 * x)) = Icc (N / 2 + 1) N := by
      ext x
      simp only [mem_filter, mem_Icc]
      omega
    have h4 : (Icc (N / 2 + 1) N).card = N + 1 - (N / 2 + 1) := Nat.card_Icc _ _
    have h5 := Finset.card_le_card h1
    have hmeq : topMiss N A = (((Icc 1 N).filter (fun x => N < 2 * x)) \ A).card := rfl
    rw [h3] at h2 h5 hmeq
    omega
  have hW : 2 * (A.filter (fun x => x ≤ N / 4)).card ≤ N / 4 + 2 := by
    apply erdos_29255_hyp_exact_hyp_sumfree (N / 4)
    · intro x hx
      rw [mem_filter] at hx
      have hx1 := hA hx.1
      rw [mem_Icc] at hx1 ⊢
      omega
    · intro a ha b hb hab hsum
      rw [mem_filter] at ha hb hsum
      have hsch := erdos_29255_hyp_exact_hyp_schur N A hA hT a ha.1 b hb.1 hab
        (by omega) hsum.1
      have hb1 := hA hb.1
      rw [mem_Icc] at hb1
      omega
  have hU := hC0 N A hA hT hm
  have hcover : A ⊆ (A.filter (fun x => N < 2 * x)) ∪ (A.filter (fun x => x ≤ N / 4)) ∪
      (A.filter (fun x => N / 4 < x ∧ 2 * x ≤ N)) := by
    intro x hx
    simp only [mem_union, mem_filter, hx, true_and]
    omega
  have hcard : A.card ≤ (A.filter (fun x => N < 2 * x)).card +
      (A.filter (fun x => x ≤ N / 4)).card +
      (A.filter (fun x => N / 4 < x ∧ 2 * x ≤ N)).card :=
    le_trans (Finset.card_le_card hcover)
      (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnat : 8 * A.card ≤ 5 * N + 12 + 8 * C0 := by omega
  have hr : (8 * A.card : ℝ) ≤ 5 * N + 12 + 8 * C0 := by exact_mod_cast hnat
  linarith
end erdos_29255_hyp_exact_ns

theorem erdos_29255_hyp_exact :
    ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ A ⊆ Icc 1 N, TriFree A →
      100 * topMiss N A ≤ N → (A.card : ℝ) < (5 / 8 : ℝ) * N + C := by
  exact erdos_29255_hyp_exact_ns.erdos_29255_hyp_exact



open Finset Filter
open scoped Asymptotics

theorem erdos_29255 :
    ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A := by
  obtain ⟨C1, hC1pos, hC1⟩ := erdos_29255_hyp_exact
  obtain ⟨C2, hC2pos, hC2⟩ := erdos_29255_hyp_stability
  refine ⟨C1 + C2, by linarith, Filter.Eventually.of_forall ?_⟩
  intro N A hA hcard
  by_contra h
  have hT : TriFree A := h
  have hm := hC2 N A hA hT (by linarith)
  have hlt := hC1 N A hA hT hm
  linarith