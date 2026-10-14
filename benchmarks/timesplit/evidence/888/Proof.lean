import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.Bertrand

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- CHECK: Real.exp_one_lt_d9 Real.log_le_log Real.log_exp Real.log_nonneg one_div_pos
open scoped Classical

open Filter

def ErdosValid41635 (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

noncomputable def erdosSpq (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter (fun m => ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a < b ∧ m = a * b)

noncomputable def erdosOctaHom (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)) : ℕ :=
  (((X ×ˢ X) ×ˢ ((Y ×ˢ Y) ×ˢ (Z ×ˢ Z))).filter (fun t =>
    ∀ a b c : Bool, ((if a then t.1.1 else t.1.2), (if b then t.2.1.1 else t.2.1.2),
      (if c then t.2.2.1 else t.2.2.2)) ∈ T)).card

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop := ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

namespace erdos_41635_hyp_pasch_ns
-- CHECK: Asymptotics.IsBigO.antisymm Asymptotics.IsBigO.of_bound Nat.findGreatest_spec Nat.le_findGreatest Nat.card_Ioc Finset.card_le_card
open scoped Classical

open Filter

open scoped Classical

open Filter

private lemma four (A : Finset ℕ) (n : ℕ) (hA : ErdosValid41635 A n) (w x y z : ℕ)
    (hw : w ∈ A) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hsq : IsSquare (w * x * y * z)) :
    w * x = y * z ∨ w * y = x * z ∨ w * z = x * y := by
  obtain ⟨r, hr⟩ := hsq
  have H := hA.2
  rcases le_total w x with h1 | h1 <;> rcases le_total w y with h2 | h2 <;>
  rcases le_total w z with h3 | h3 <;> rcases le_total x y with h4 | h4 <;>
  rcases le_total x z with h5 | h5 <;> rcases le_total y z with h6 | h6 <;>
  first
  | (have e := H w hw x hx y hy z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H w hw x hx z hz y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H w hw y hy x hx z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H w hw y hy z hz x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H w hw z hz x hx y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H w hw z hz y hy x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx w hw y hy z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx w hw z hz y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx y hy w hw z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx y hy z hz w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx z hz w hw y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H x hx z hz y hy w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy w hw x hx z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy w hw z hz x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy x hx w hw z hz (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy x hx z hz w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy z hz w hw x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H y hy z hz x hx w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz w hw x hx y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz w hw y hy x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz x hx w hw y hy (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz x hx y hy w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz y hy w hw x hx (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))
  | (have e := H z hz y hy x hx w hw (by omega) (by omega) (by omega) ⟨r, by linarith [hr]⟩
     first | exact Or.inl (by linarith [e]) | exact Or.inr (Or.inl (by linarith [e])) | exact Or.inr (Or.inr (by linarith [e])))

private lemma sq_cancel (u v K : ℕ) (hK : 0 < K) (huv : u ≠ v) (h : u * u * K = v * v * K) : False := by
  have h' : u * u = v * v := Nat.eq_of_mul_eq_mul_right hK h
  rcases Nat.lt_or_gt_of_ne huv with hl | hl <;> nlinarith

theorem erdos_41635_hyp_pasch : ∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n →
    ∀ x1 x2 y1 y2 z1 z2 : ℕ, 0 < x1 → 0 < x2 → 0 < y1 → 0 < y2 → 0 < z1 → 0 < z2 →
    x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
    ¬ (x1 * y1 * z1 ∈ A ∧ x1 * y2 * z2 ∈ A ∧ x2 * y1 * z2 ∈ A ∧ x2 * y2 * z1 ∈ A) := by
  intro n A hA x1 x2 y1 y2 z1 z2 hx1 hx2 hy1 hy2 hz1 hz2 hx hy hz hmem
  obtain ⟨h1, h2, h3, h4⟩ := hmem
  have hsq : IsSquare (x1 * y1 * z1 * (x1 * y2 * z2) * (x2 * y1 * z2) * (x2 * y2 * z1)) :=
    ⟨x1 * x2 * y1 * y2 * z1 * z2, by ring⟩
  rcases four A n hA _ _ _ _ h1 h2 h3 h4 hsq with e | e | e
  · exact sq_cancel x1 x2 (y1 * y2 * z1 * z2) (by positivity) hx (by linarith [e])
  · exact sq_cancel y1 y2 (x1 * x2 * z1 * z2) (by positivity) hy (by linarith [e])
  · exact sq_cancel z1 z2 (x1 * x2 * y1 * y2) (by positivity) hz (by linarith [e])
end erdos_41635_hyp_pasch_ns

namespace erdos_41635_hyp_cs_pair_ns
-- CHECK: Finset.sum_mul_sq_le_sq_mul_sq Finset.sum_filter Finset.sum_product Finset.card_eq_sum_ones Finset.sum_comm mul_self_le_mul_self
open scoped Classical

open Filter

open scoped Classical

open Filter

private noncomputable def ind41635 (G : Finset (ℕ × ℕ)) (x y : ℕ) : ℝ :=
  if (x, y) ∈ G then 1 else 0

private lemma cs41635 {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
  nlinarith [h]

theorem erdos_41635_hyp_cs_pair : ∀ (X Y : Finset ℕ) (G : Finset (ℕ × ℕ)), G ⊆ X ×ˢ Y →
    X.Nonempty → Y.Nonempty →
    (G.card : ℝ) ^ 4 ≤ (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 *
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2 := by
  intro X Y G hG _ _
  have hfilt : (X ×ˢ Y).filter (fun p => p ∈ G) = G := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hG h, h⟩
  have hcard : (G.card : ℝ) = ∑ x ∈ X, ∑ y ∈ Y, ind41635 G x y := by
    calc (G.card : ℝ) = ∑ q ∈ (X ×ˢ Y).filter (fun p => p ∈ G), (1:ℝ) := by
          rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ q ∈ X ×ˢ Y, (if q ∈ G then (1:ℝ) else 0) := Finset.sum_filter _ _
      _ = ∑ x ∈ X, ∑ y ∈ Y, ind41635 G x y := by
          rw [Finset.sum_product]
          first | rfl | simp [ind41635]
  have hc : ∀ y1 y2, ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)
      = ∑ x ∈ X, ind41635 G x y1 * ind41635 G x y2 := by
    intro y1 y2
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold ind41635
    by_cases h1 : (x, y1) ∈ G <;> by_cases h2 : (x, y2) ∈ G <;> simp [h1, h2]
  have hS : ∑ y1 ∈ Y, ∑ y2 ∈ Y, ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)
      = ∑ x ∈ X, (∑ y ∈ Y, ind41635 G x y) ^ 2 := by
    calc ∑ y1 ∈ Y, ∑ y2 ∈ Y, ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)
        = ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x ∈ X, ind41635 G x y1 * ind41635 G x y2 :=
          Finset.sum_congr rfl (fun y1 _ => Finset.sum_congr rfl (fun y2 _ => hc y1 y2))
      _ = ∑ y1 ∈ Y, ∑ x ∈ X, ∑ y2 ∈ Y, ind41635 G x y1 * ind41635 G x y2 :=
          Finset.sum_congr rfl (fun y1 _ => Finset.sum_comm)
      _ = ∑ x ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ind41635 G x y1 * ind41635 G x y2 := Finset.sum_comm
      _ = ∑ x ∈ X, (∑ y ∈ Y, ind41635 G x y) ^ 2 := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [sq, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun y1 _ => by rw [Finset.mul_sum])
  have h1 : (G.card : ℝ) ^ 2 ≤ (X.card : ℝ) * ∑ x ∈ X, (∑ y ∈ Y, ind41635 G x y) ^ 2 := by
    rw [hcard]; exact cs41635 X _
  have h2 : (∑ x ∈ X, (∑ y ∈ Y, ind41635 G x y) ^ 2) ^ 2 ≤ (Y.card : ℝ) ^ 2 *
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2 := by
    rw [← hS]
    have hA := cs41635 Y (fun y1 => ∑ y2 ∈ Y,
      ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ))
    have hB : ∀ y1 ∈ Y, (∑ y2 ∈ Y, ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2
        ≤ (Y.card : ℝ) * ∑ y2 ∈ Y, (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2 :=
      fun y1 _ => cs41635 Y _
    have hC := Finset.sum_le_sum hB
    rw [← Finset.mul_sum] at hC
    calc _ ≤ (Y.card : ℝ) * ∑ y1 ∈ Y,
            (∑ y2 ∈ Y, ((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2 := hA
      _ ≤ (Y.card : ℝ) * ((Y.card : ℝ) * ∑ y1 ∈ Y, ∑ y2 ∈ Y,
            (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by ring
  have hSnn : 0 ≤ ∑ x ∈ X, (∑ y ∈ Y, ind41635 G x y) ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have h3 := mul_self_le_mul_self (sq_nonneg (G.card : ℝ)) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (X.card : ℝ))
  nlinarith [h3, h4]
end erdos_41635_hyp_cs_pair_ns

namespace erdos_41635_hyp_octahedra_ns
-- CHECK: Finset.sum_mul_sq_le_sq_mul_sq sq_sum_le_card_mul_sum_sq Finset.card_filter Finset.sum_mul_sum Finset.mul_sum Finset.sum_comm
open scoped Classical

open Filter

open scoped Classical

open Filter

private lemma cs1 {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

private lemma cs_step {ι : Type*} (s : Finset ι) (F B : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, F i ^ 2 ≤ c * B i) :
    (∑ i ∈ s, F i) ^ 2 ≤ ((s.card : ℝ) * c) * ∑ i ∈ s, B i := by
  calc (∑ i ∈ s, F i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, F i ^ 2 := cs1 s F
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, c * B i := by
        gcongr with i hi
        exact h i hi
    _ = ((s.card : ℝ) * c) * ∑ i ∈ s, B i := by rw [← Finset.mul_sum]; ring

private lemma pm4 {ι : Type*} (s : Finset ι) (S : ι → ℝ) :
    (∑ i ∈ s, S i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, S i ^ 4 := by
  have h1 : (∑ i ∈ s, S i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, S i ^ 2 := cs1 s S
  have h2 : (∑ i ∈ s, S i ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (S i ^ 2) ^ 2 :=
    cs1 s (fun i => S i ^ 2)
  have h3 : ∑ i ∈ s, (S i ^ 2) ^ 2 = ∑ i ∈ s, S i ^ 4 :=
    Finset.sum_congr rfl fun i _ => by ring
  calc (∑ i ∈ s, S i) ^ 4 = ((∑ i ∈ s, S i) ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ i ∈ s, S i ^ 2) ^ 2 := by gcongr
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, S i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (S i ^ 2) ^ 2) := by gcongr
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, S i ^ 4 := by rw [h3]; ring

private lemma slice (X Y : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 4 ≤ ((X.card : ℝ) * Y.card) ^ 2 *
      ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x1 y1 * g x1 y2 * g x2 y1 * g x2 y2 := by
  have e1 : ∑ x ∈ X, ∑ y ∈ Y, g x y = ∑ y ∈ Y, ∑ x ∈ X, g x y := Finset.sum_comm
  have e2 : ∑ y ∈ Y, (∑ x ∈ X, g x y) ^ 2 =
      ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y := by
    calc ∑ y ∈ Y, (∑ x ∈ X, g x y) ^ 2
        = ∑ y ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X, g x1 y * g x2 y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ x1 ∈ X, ∑ y ∈ Y, ∑ x2 ∈ X, g x1 y * g x2 y := Finset.sum_comm
      _ = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y := by
          refine Finset.sum_congr rfl fun x1 _ => ?_
          exact Finset.sum_comm
  have e3 : ∀ x1 x2, (∑ y ∈ Y, g x1 y * g x2 y) ^ 2 =
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x1 y1 * g x1 y2 * g x2 y1 * g x2 y2 := by
    intro x1 x2
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
    ring
  have h1 : (∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 2 ≤
      (Y.card : ℝ) * ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y := by
    rw [e1, ← e2]
    exact cs1 _ _
  have h2 : (∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y) ^ 2 ≤
      ((X.card : ℝ) * ((X.card : ℝ) * 1)) *
        ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x1 y1 * g x1 y2 * g x2 y1 * g x2 y2 := by
    refine cs_step _ _ _ _ (by positivity) fun x1 _ => ?_
    try dsimp only
    refine cs_step _ _ _ _ (by norm_num) fun x2 _ => ?_
    try dsimp only
    exact le_of_eq (by rw [e3, one_mul])
  calc (∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 4 = ((∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 2) ^ 2 := by ring
    _ ≤ ((Y.card : ℝ) * ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y) ^ 2 := by gcongr
    _ = (Y.card : ℝ) ^ 2 * (∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, g x1 y * g x2 y) ^ 2 := by ring
    _ ≤ (Y.card : ℝ) ^ 2 * (((X.card : ℝ) * ((X.card : ℝ) * 1)) *
        ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x1 y1 * g x1 y2 * g x2 y1 * g x2 y2) := by
        gcongr
    _ = ((X.card : ℝ) * Y.card) ^ 2 *
        ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x1 y1 * g x1 y2 * g x2 y1 * g x2 y2 := by
        ring

private lemma comm4 (A B C D E : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, F a b c d e =
    ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d e := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, F a b c d e
      = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ E, ∑ d ∈ D, F a b c d e := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm
    _ = ∑ a ∈ A, ∑ b ∈ B, ∑ e ∈ E, ∑ c ∈ C, ∑ d ∈ D, F a b c d e := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact Finset.sum_comm
    _ = ∑ a ∈ A, ∑ e ∈ E, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d e := Finset.sum_comm

private lemma key8 (T : Finset (ℕ × ℕ × ℕ)) (f : ℕ → ℕ → ℕ → ℝ)
    (hf' : ∀ x y z, f x y z = if (x, y, z) ∈ T then 1 else 0)
    (x1 x2 y1 y2 z1 z2 : ℕ) (P : Prop) [Decidable P]
    (hP : P ↔ ∀ a b c : Bool, ((if a then x1 else x2), (if b then y1 else y2),
      (if c then z1 else z2)) ∈ T) :
    ((if P then 1 else 0 : ℕ) : ℝ) =
      (f x1 y1 z1 * f x1 y2 z1 * f x2 y1 z1 * f x2 y2 z1) *
      (f x1 y1 z2 * f x1 y2 z2 * f x2 y1 z2 * f x2 y2 z2) := by
  by_cases h : P
  · have H := hP.mp h
    have m1 : (x1, y1, z1) ∈ T := by simpa using H true true true
    have m2 : (x1, y2, z1) ∈ T := by simpa using H true false true
    have m3 : (x2, y1, z1) ∈ T := by simpa using H false true true
    have m4 : (x2, y2, z1) ∈ T := by simpa using H false false true
    have m5 : (x1, y1, z2) ∈ T := by simpa using H true true false
    have m6 : (x1, y2, z2) ∈ T := by simpa using H true false false
    have m7 : (x2, y1, z2) ∈ T := by simpa using H false true false
    have m8 : (x2, y2, z2) ∈ T := by simpa using H false false false
    rw [if_pos h]
    simp [hf', m1, m2, m3, m4, m5, m6, m7, m8]
  · rw [if_neg h, Nat.cast_zero]
    have H : ¬ ∀ a b c : Bool, ((if a then x1 else x2), (if b then y1 else y2),
        (if c then z1 else z2)) ∈ T := fun H' => h (hP.mpr H')
    by_contra hne
    apply H
    intro a b c
    by_contra hm
    apply hne
    have hz : f (if a then x1 else x2) (if b then y1 else y2) (if c then z1 else z2) = 0 := by
      rw [hf', if_neg hm]
    cases a <;> cases b <;> cases c <;> simp at hz <;> simp [hz]

theorem erdos_41635_hyp_octahedra : ∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)),
    T ⊆ X ×ˢ (Y ×ˢ Z) → X.Nonempty → Y.Nonempty → Z.Nonempty →
    (T.card : ℝ) ^ 8 ≤ ((X.card : ℝ) * Y.card * Z.card) ^ 6 * (erdosOctaHom X Y Z T : ℝ) := by
  intro X Y Z T hT hX hY hZ
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ → ℕ → ℝ, f = fun x y z => if (x, y, z) ∈ T then 1 else 0 :=
    ⟨_, rfl⟩
  have hf' : ∀ x y z, f x y z = if (x, y, z) ∈ T then 1 else 0 := by
    intro x y z; rw [hf]
  have hTf : (X ×ˢ (Y ×ˢ Z)).filter (fun t => t ∈ T) = T := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  have hcard : (T.card : ℝ) = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z := by
    calc (T.card : ℝ) = (((X ×ˢ (Y ×ˢ Z)).filter (fun t => t ∈ T)).card : ℝ) := by rw [hTf]
      _ = ∑ t ∈ X ×ˢ (Y ×ˢ Z), (if t ∈ T then (1:ℝ) else 0) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
      _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
          rw [hf']
  have hhom : (erdosOctaHom X Y Z T : ℝ) = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y,
      (∑ z ∈ Z, f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z) ^ 2 := by
    unfold erdosOctaHom
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ =>
      Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    exact key8 T f hf' x1 x2 y1 y2 z1 z2 _ Iff.rfl
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y,
      (∑ z ∈ Z, f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z) ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y,
      ∑ z ∈ Z, f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z := ⟨_, rfl⟩
  have ha : W ^ 2 ≤ ((X.card : ℝ) * ((X.card : ℝ) * ((Y.card : ℝ) * ((Y.card : ℝ) * 1)))) * H := by
    rw [hW, hH]
    refine cs_step _ _ _ _ (by positivity) fun x1 _ => ?_
    try dsimp only
    refine cs_step _ _ _ _ (by positivity) fun x2 _ => ?_
    try dsimp only
    refine cs_step _ _ _ _ (by positivity) fun y1 _ => ?_
    try dsimp only
    refine cs_step _ _ _ _ (by norm_num) fun y2 _ => ?_
    try dsimp only
    exact le_of_eq (one_mul _).symm
  have e4 : ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ z ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z := by
    calc ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ x ∈ X, ∑ z ∈ Z, ∑ y ∈ Y, f x y z :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ z ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z := Finset.sum_comm
  have e5 : W = ∑ z ∈ Z, ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y,
      f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z := by
    rw [hW]
    exact comm4 X X Y Y Z (fun x1 x2 y1 y2 z => f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z)
  have hb : (T.card : ℝ) ^ 4 ≤ (Z.card : ℝ) ^ 3 * ((X.card : ℝ) * Y.card) ^ 2 * W := by
    calc (T.card : ℝ) ^ 4 = (∑ z ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z) ^ 4 := by rw [hcard, e4]
      _ ≤ (Z.card : ℝ) ^ 3 * ∑ z ∈ Z, (∑ x ∈ X, ∑ y ∈ Y, f x y z) ^ 4 := pm4 Z _
      _ ≤ (Z.card : ℝ) ^ 3 * ∑ z ∈ Z, ((X.card : ℝ) * Y.card) ^ 2 *
          ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y,
            f x1 y1 z * f x1 y2 z * f x2 y1 z * f x2 y2 z := by
          gcongr with z hz
          exact slice X Y (fun x y => f x y z)
      _ = (Z.card : ℝ) ^ 3 * ((X.card : ℝ) * Y.card) ^ 2 * W := by
          rw [← Finset.mul_sum, ← e5]; ring
  rw [hhom, ← hH]
  calc (T.card : ℝ) ^ 8 = ((T.card : ℝ) ^ 4) ^ 2 := by ring
    _ ≤ ((Z.card : ℝ) ^ 3 * ((X.card : ℝ) * Y.card) ^ 2 * W) ^ 2 := by gcongr
    _ = (Z.card : ℝ) ^ 6 * ((X.card : ℝ) * Y.card) ^ 4 * W ^ 2 := by ring
    _ ≤ (Z.card : ℝ) ^ 6 * ((X.card : ℝ) * Y.card) ^ 4 *
        (((X.card : ℝ) * ((X.card : ℝ) * ((Y.card : ℝ) * ((Y.card : ℝ) * 1)))) * H) := by
        gcongr
    _ = ((X.card : ℝ) * Y.card * Z.card) ^ 6 * H := by ring
end erdos_41635_hyp_octahedra_ns

namespace erdos_41635_hyp_box_ns
-- CHECK: sq_sum_le_card_mul_sum_sq Finset.sum_mul_sq_le_sq_mul_sq Finset.sum_ite_eq mul_self_le_mul_self Nat.eq_of_mul_eq_mul_right mul_lt_mul'' Finset.card_filter Finset.sum_product
open scoped Classical

open Filter

open scoped Classical

open Filter

private lemma e41_core (A : Finset ℕ) (n : ℕ) (hA : ErdosValid41635 A n) {u v w t : ℕ}
    (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A) (ht : t ∈ A)
    (hsq : IsSquare (u * v * w * t))
    (h1 : u * v ≠ w * t) (h2 : u * w ≠ v * t) (h3 : u * t ≠ v * w) : False := by
  rcases le_total u v with c1 | c1 <;> rcases le_total u w with c2 | c2 <;>
    rcases le_total u t with c3 | c3 <;> rcases le_total v w with c4 | c4 <;>
    rcases le_total v t with c5 | c5 <;> rcases le_total w t with c6 | c6 <;>
    first
    | exact absurd (hA.2 u hu v hv w hw t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 u hu v hv t ht w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 u hu w hw v hv t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 u hu w hw t ht v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 u hu t ht v hv w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 u hu t ht w hw v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv u hu w hw t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv u hu t ht w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv w hw u hu t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv w hw t ht u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv t ht u hu w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 v hv t ht w hw u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw u hu v hv t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw u hu t ht v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw v hv u hu t ht (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw v hv t ht u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw t ht u hu v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 w hw t ht v hv u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht u hu v hv w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht u hu w hw v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht v hv u hu w hw (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht v hv w hw u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht w hw u hu v hv (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))
    | exact absurd (hA.2 t ht w hw v hv u hu (by omega) (by omega) (by omega) (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hsq)) (fun e => by first | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith))

private lemma e41_sq_ne {a b c : ℕ} (hc : 0 < c) (hab : a ≠ b) : a * a * c ≠ b * b * c := by
  intro e
  have h := Nat.eq_of_mul_eq_mul_right hc e
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have h' : a * a < b * b := by
      first
      | exact mul_lt_mul'' hlt hlt (Nat.zero_le _) (Nat.zero_le _)
      | exact Nat.mul_self_lt_mul_self hlt
      | nlinarith
    rw [h] at h'
    exact lt_irrefl _ h'
  · have h' : b * b < a * a := by
      first
      | exact mul_lt_mul'' hlt hlt (Nat.zero_le _) (Nat.zero_le _)
      | exact Nat.mul_self_lt_mul_self hlt
      | nlinarith
    rw [h] at h'
    exact lt_irrefl _ h'

private lemma e41_pasch (A : Finset ℕ) (n : ℕ) (hA : ErdosValid41635 A n)
    {x1 x2 y1 y2 z1 z2 : ℕ}
    (h1 : x1 * y1 * z1 ∈ A) (h2 : x1 * y2 * z2 ∈ A) (h3 : x2 * y1 * z2 ∈ A)
    (h4 : x2 * y2 * z1 ∈ A) (hx : x1 ≠ x2) (hy : y1 ≠ y2) (hz : z1 ≠ z2) : False := by
  have pos : ∀ a ∈ A, 0 < a := fun a ha => (Finset.mem_Ioc.mp (hA.1 ha)).1
  have p1 := pos _ h1
  have p2 := pos _ h2
  have p3 := pos _ h3
  have hx1 : 0 < x1 := Nat.pos_of_ne_zero (fun h => by simp [h] at p1)
  have hx2 : 0 < x2 := Nat.pos_of_ne_zero (fun h => by simp [h] at p3)
  have hy1 : 0 < y1 := Nat.pos_of_ne_zero (fun h => by simp [h] at p1)
  have hy2 : 0 < y2 := Nat.pos_of_ne_zero (fun h => by simp [h] at p2)
  have hz1 : 0 < z1 := Nat.pos_of_ne_zero (fun h => by simp [h] at p1)
  have hz2 : 0 < z2 := Nat.pos_of_ne_zero (fun h => by simp [h] at p2)
  have c1 : 0 < y1 * y2 * z1 * z2 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hy1 hy2) hz1) hz2
  have c2 : 0 < x1 * x2 * z1 * z2 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hx1 hx2) hz1) hz2
  have c3 : 0 < x1 * x2 * y1 * y2 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hx1 hx2) hy1) hy2
  refine e41_core A n hA h1 h2 h3 h4 ⟨x1 * x2 * y1 * y2 * z1 * z2, by ring⟩ ?_ ?_ ?_
  · intro e
    apply e41_sq_ne c1 hx
    calc x1 * x1 * (y1 * y2 * z1 * z2) = x1 * y1 * z1 * (x1 * y2 * z2) := by ring
      _ = x2 * y1 * z2 * (x2 * y2 * z1) := e
      _ = x2 * x2 * (y1 * y2 * z1 * z2) := by ring
  · intro e
    apply e41_sq_ne c2 hy
    calc y1 * y1 * (x1 * x2 * z1 * z2) = x1 * y1 * z1 * (x2 * y1 * z2) := by ring
      _ = x1 * y2 * z2 * (x2 * y2 * z1) := e
      _ = y2 * y2 * (x1 * x2 * z1 * z2) := by ring
  · intro e
    apply e41_sq_ne c3 hz
    calc z1 * z1 * (x1 * x2 * y1 * y2) = x1 * y1 * z1 * (x2 * y2 * z1) := by ring
      _ = x1 * y2 * z2 * (x2 * y1 * z2) := e
      _ = z2 * z2 * (x1 * x2 * y1 * y2) := by ring

private lemma e41_cs (s : Finset ℕ) (F : ℕ → ℝ) :
    (∑ i ∈ s, F i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, F i ^ 2 := by
  first
  | exact sq_sum_le_card_mul_sum_sq
  | (have h := Finset.sum_mul_sq_le_sq_mul_sq s F (fun _ => (1 : ℝ))
     simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
     linarith)

private lemma e41_sq_sum (s : Finset ℕ) (F : ℕ → ℝ) :
    (∑ i ∈ s, F i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, F i * F j := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]

private lemma e41_cs2 (s t : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, F a b) ^ 2 ≤ (s.card : ℝ) * t.card * ∑ a ∈ s, ∑ b ∈ t, F a b ^ 2 := by
  have h1 : (∑ a ∈ s, ∑ b ∈ t, F a b) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (∑ b ∈ t, F a b) ^ 2 :=
    e41_cs s (fun a => ∑ b ∈ t, F a b)
  have h2 : ∑ a ∈ s, (∑ b ∈ t, F a b) ^ 2 ≤ ∑ a ∈ s, (t.card : ℝ) * ∑ b ∈ t, F a b ^ 2 :=
    Finset.sum_le_sum (fun a _ => e41_cs t (fun b => F a b))
  rw [← Finset.mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (s.card : ℝ))
  exact h1.trans (h3.trans (le_of_eq (by ring)))

private lemma e41_swap4 (X Y Z : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, ∑ z1 ∈ Z, ∑ z2 ∈ Z, F x y z1 z2 =
      ∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, F x y z1 z2 := by
  calc ∑ x ∈ X, ∑ y ∈ Y, ∑ z1 ∈ Z, ∑ z2 ∈ Z, F x y z1 z2
      = ∑ x ∈ X, ∑ z1 ∈ Z, ∑ y ∈ Y, ∑ z2 ∈ Z, F x y z1 z2 :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ z1 ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, ∑ z2 ∈ Z, F x y z1 z2 := Finset.sum_comm
    _ = ∑ z1 ∈ Z, ∑ x ∈ X, ∑ z2 ∈ Z, ∑ y ∈ Y, F x y z1 z2 :=
        Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))
    _ = ∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, F x y z1 z2 :=
        Finset.sum_congr rfl (fun z1 _ => Finset.sum_comm)

private lemma e41_alg1 (s Q I x y : ℝ) (hB : s ^ 2 ≤ x * Q) (hC : Q ^ 2 ≤ y * y * I)
    (hx : 0 ≤ x) : s ^ 4 ≤ x ^ 2 * y ^ 2 * I := by
  have e1 : s ^ 2 * s ^ 2 ≤ (x * Q) * (x * Q) := mul_self_le_mul_self (sq_nonneg _) hB
  have e2 : x ^ 2 * Q ^ 2 ≤ x ^ 2 * (y * y * I) := mul_le_mul_of_nonneg_left hC (by positivity)
  nlinarith [e1, e2]

private lemma e41_box (X Y : Finset ℕ) (g : ℕ → ℕ → ℝ) (hg : ∀ x y, 0 ≤ g x y) :
    (∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 4 ≤ (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 *
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X, g x1 y1 * g x1 y2 * (g x2 y1 * g x2 y2) := by
  have hB : (∑ x ∈ X, ∑ y ∈ Y, g x y) ^ 2 ≤ (X.card : ℝ) * ∑ x ∈ X, (∑ y ∈ Y, g x y) ^ 2 :=
    e41_cs X (fun x => ∑ y ∈ Y, g x y)
  have hA : ∑ x ∈ X, (∑ y ∈ Y, g x y) ^ 2 = ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x ∈ X, g x y1 * g x y2 := by
    calc ∑ x ∈ X, (∑ y ∈ Y, g x y) ^ 2 = ∑ x ∈ X, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g x y1 * g x y2 :=
          Finset.sum_congr rfl (fun x _ => e41_sq_sum Y (fun y => g x y))
      _ = ∑ y1 ∈ Y, ∑ x ∈ X, ∑ y2 ∈ Y, g x y1 * g x y2 := Finset.sum_comm
      _ = ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x ∈ X, g x y1 * g x y2 :=
          Finset.sum_congr rfl (fun y1 _ => Finset.sum_comm)
  have hC : (∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x ∈ X, g x y1 * g x y2) ^ 2 ≤
      (Y.card : ℝ) * Y.card * ∑ y1 ∈ Y, ∑ y2 ∈ Y, (∑ x ∈ X, g x y1 * g x y2) ^ 2 :=
    e41_cs2 Y Y (fun y1 y2 => ∑ x ∈ X, g x y1 * g x y2)
  have hD : ∑ y1 ∈ Y, ∑ y2 ∈ Y, (∑ x ∈ X, g x y1 * g x y2) ^ 2 =
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X, g x1 y1 * g x1 y2 * (g x2 y1 * g x2 y2) :=
    Finset.sum_congr rfl (fun y1 _ => Finset.sum_congr rfl
      (fun y2 _ => e41_sq_sum X (fun x => g x y1 * g x y2)))
  rw [hA] at hB
  rw [hD] at hC
  exact e41_alg1 _ _ _ _ _ hB hC (by positivity)

private lemma e41_pm4 (s : Finset ℕ) (G : ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, G a b) ^ 4 ≤ (s.card : ℝ) ^ 6 * ∑ a ∈ s, ∑ b ∈ s, G a b ^ 4 := by
  have h1 : (∑ a ∈ s, ∑ b ∈ s, G a b) ^ 2 ≤
      (s.card : ℝ) * s.card * ∑ a ∈ s, ∑ b ∈ s, G a b ^ 2 := e41_cs2 s s G
  have h2 : (∑ a ∈ s, ∑ b ∈ s, G a b ^ 2) ^ 2 ≤
      (s.card : ℝ) * s.card * ∑ a ∈ s, ∑ b ∈ s, G a b ^ 4 := by
    have h := e41_cs2 s s (fun a b => G a b ^ 2)
    have e : ∑ a ∈ s, ∑ b ∈ s, (G a b ^ 2) ^ 2 = ∑ a ∈ s, ∑ b ∈ s, G a b ^ 4 :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    rw [← e]
    exact h
  exact (e41_alg1 _ _ _ _ _ h1 h2 (by positivity)).trans (le_of_eq (by ring))

private lemma e41_combine (S P Q H x y z m : ℝ) (hm : 0 ≤ m)
    (hS : S ^ 2 ≤ x * y * P) (hPQ : P ^ 4 ≤ z ^ 6 * Q) (hQH : Q ≤ x ^ 2 * y ^ 2 * H)
    (hH : H * m ≤ 3 * (x * y * z) ^ 2) : S ^ 8 * m ≤ 3 * (x * y * z) ^ 8 := by
  have e1 : S ^ 2 * S ^ 2 ≤ (x * y * P) * (x * y * P) := mul_self_le_mul_self (sq_nonneg _) hS
  have e2 : (S ^ 2 * S ^ 2) * (S ^ 2 * S ^ 2) ≤
      ((x * y * P) * (x * y * P)) * ((x * y * P) * (x * y * P)) :=
    mul_self_le_mul_self (by positivity) e1
  have e4 : (x * y) ^ 4 * P ^ 4 ≤ (x * y) ^ 4 * (z ^ 6 * Q) :=
    mul_le_mul_of_nonneg_left hPQ (by positivity)
  have e5 : (x * y) ^ 4 * (z ^ 6 * Q) ≤ (x * y) ^ 4 * (z ^ 6 * (x ^ 2 * y ^ 2 * H)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQH (by positivity)) (by positivity)
  have e6 : S ^ 8 ≤ x ^ 6 * y ^ 6 * z ^ 6 * H := by nlinarith [e2, e4, e5]
  have e7 : S ^ 8 * m ≤ (x ^ 6 * y ^ 6 * z ^ 6 * H) * m := mul_le_mul_of_nonneg_right e6 hm
  have e8 : (x ^ 6 * y ^ 6 * z ^ 6) * (H * m) ≤ (x ^ 6 * y ^ 6 * z ^ 6) * (3 * (x * y * z) ^ 2) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith [e7, e8]

private lemma e41_hIsum (s : Finset ℕ) (c : ℝ) :
    ∑ a ∈ s, ∑ b ∈ s, (if a = b then c else 0) = (s.card : ℝ) * c := by
  have h : ∀ a ∈ s, ∑ b ∈ s, (if a = b then c else 0) = c := by
    intro a ha
    first
    | rw [Finset.sum_ite_eq, if_pos ha]
    | simp [ha]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

private lemma e41_hom (X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ)
    (h0 : ∀ x y z, 0 ≤ f x y z) (h1 : ∀ x y z, f x y z ≤ 1)
    (hP : ∀ x1 x2 y1 y2 z1 z2, x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
      f x1 y1 z1 * f x1 y2 z2 * f x2 y1 z2 * f x2 y2 z1 = 0)
    (m : ℝ) (hm0 : 0 ≤ m) (hmX : m ≤ X.card) (hmY : m ≤ Y.card) (hmZ : m ≤ Z.card) :
    (∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X,
      f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2))) * m ≤
      3 * ((X.card : ℝ) * Y.card * Z.card) ^ 2 := by
  have u : ∀ a b : ℝ, 0 ≤ a ∧ a ≤ 1 → 0 ≤ b ∧ b ≤ 1 → 0 ≤ a * b ∧ a * b ≤ 1 := by
    intro a b ha hb
    refine ⟨mul_nonneg ha.1 hb.1, ?_⟩
    nlinarith [ha.1, ha.2, hb.1, hb.2]
  have v : ∀ x y z, 0 ≤ f x y z ∧ f x y z ≤ 1 := fun x y z => ⟨h0 x y z, h1 x y z⟩
  have hpt : ∀ x1 x2 y1 y2 z1 z2 : ℕ,
      f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2)) ≤
      (if z1 = z2 then (1 : ℝ) else 0) + (if y1 = y2 then (1 : ℝ) else 0) +
        (if x1 = x2 then (1 : ℝ) else 0) := by
    intro x1 x2 y1 y2 z1 z2
    have ht : 0 ≤ f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2)) ∧
        f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2)) ≤ 1 :=
      u _ _ (u _ _ (u _ _ (v _ _ _) (v _ _ _)) (u _ _ (v _ _ _) (v _ _ _)))
        (u _ _ (u _ _ (v _ _ _) (v _ _ _)) (u _ _ (v _ _ _) (v _ _ _)))
    have i1 : (0 : ℝ) ≤ (if z1 = z2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have i2 : (0 : ℝ) ≤ (if y1 = y2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have i3 : (0 : ℝ) ≤ (if x1 = x2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    by_cases hz : z1 = z2
    · rw [if_pos hz]; linarith [ht.2]
    by_cases hy : y1 = y2
    · rw [if_pos hy]; linarith [ht.2]
    by_cases hx : x1 = x2
    · rw [if_pos hx]; linarith [ht.2]
    rw [if_neg hz, if_neg hy, if_neg hx]
    have hz0 := hP x1 x2 y1 y2 z1 z2 hx hy hz
    have e : f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2)) =
        (f x1 y1 z1 * f x1 y2 z2 * f x2 y1 z2 * f x2 y2 z1) *
        (f x1 y1 z2 * f x1 y2 z1 * f x2 y1 z1 * f x2 y2 z2) := by ring
    rw [e, hz0]
    norm_num
  have hsum : (∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X,
      f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
        (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2))) ≤
      ∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X,
        ((if z1 = z2 then (1 : ℝ) else 0) + (if y1 = y2 then (1 : ℝ) else 0) +
          (if x1 = x2 then (1 : ℝ) else 0)) := by
    apply Finset.sum_le_sum; intro z1 _
    apply Finset.sum_le_sum; intro z2 _
    apply Finset.sum_le_sum; intro y1 _
    apply Finset.sum_le_sum; intro y2 _
    apply Finset.sum_le_sum; intro x1 _
    apply Finset.sum_le_sum; intro x2 _
    exact hpt x1 x2 y1 y2 z1 z2
  have hval : (∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X,
        ((if z1 = z2 then (1 : ℝ) else 0) + (if y1 = y2 then (1 : ℝ) else 0) +
          (if x1 = x2 then (1 : ℝ) else 0))) =
      (Z.card : ℝ) * (Y.card : ℝ) ^ 2 * (X.card : ℝ) ^ 2 +
        (Z.card : ℝ) ^ 2 * (Y.card : ℝ) * (X.card : ℝ) ^ 2 +
        (Z.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 * (X.card : ℝ) := by
    first
    | (simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_ite, mul_one,
        mul_zero, e41_hIsum]; ring)
    | (simp [Finset.sum_add_distrib, e41_hIsum, mul_ite]; ring)
  have e0 := mul_le_mul_of_nonneg_right (hsum.trans hval.le) hm0
  have a1 : m * ((Z.card : ℝ) * (Y.card : ℝ) ^ 2 * (X.card : ℝ) ^ 2) ≤
      (Z.card : ℝ) * ((Z.card : ℝ) * (Y.card : ℝ) ^ 2 * (X.card : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hmZ (by positivity)
  have a2 : m * ((Z.card : ℝ) ^ 2 * (Y.card : ℝ) * (X.card : ℝ) ^ 2) ≤
      (Y.card : ℝ) * ((Z.card : ℝ) ^ 2 * (Y.card : ℝ) * (X.card : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hmY (by positivity)
  have a3 : m * ((Z.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 * (X.card : ℝ)) ≤
      (X.card : ℝ) * ((Z.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 * (X.card : ℝ)) :=
    mul_le_mul_of_nonneg_right hmX (by positivity)
  nlinarith [e0, a1, a2, a3]

private lemma e41_main (X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ)
    (h0 : ∀ x y z, 0 ≤ f x y z) (h1 : ∀ x y z, f x y z ≤ 1)
    (hP : ∀ x1 x2 y1 y2 z1 z2, x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
      f x1 y1 z1 * f x1 y2 z2 * f x2 y1 z2 * f x2 y2 z1 = 0)
    (m : ℝ) (hm0 : 0 ≤ m) (hmX : m ≤ X.card) (hmY : m ≤ Y.card) (hmZ : m ≤ Z.card) :
    (∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z) ^ 8 * m ≤
      3 * ((X.card : ℝ) * Y.card * Z.card) ^ 8 := by
  have hS : (∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z) ^ 2 ≤
      (X.card : ℝ) * Y.card * ∑ x ∈ X, ∑ y ∈ Y, (∑ z ∈ Z, f x y z) ^ 2 :=
    e41_cs2 X Y (fun x y => ∑ z ∈ Z, f x y z)
  have hG : ∑ x ∈ X, ∑ y ∈ Y, (∑ z ∈ Z, f x y z) ^ 2 =
      ∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z1 * f x y z2 := by
    have e1 : ∑ x ∈ X, ∑ y ∈ Y, (∑ z ∈ Z, f x y z) ^ 2 =
        ∑ x ∈ X, ∑ y ∈ Y, ∑ z1 ∈ Z, ∑ z2 ∈ Z, f x y z1 * f x y z2 :=
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
        (fun y _ => e41_sq_sum Z (fun z => f x y z)))
    rw [e1]
    exact e41_swap4 X Y Z (fun x y z1 z2 => f x y z1 * f x y z2)
  rw [hG] at hS
  have hPM : (∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z1 * f x y z2) ^ 4 ≤
      (Z.card : ℝ) ^ 6 * ∑ z1 ∈ Z, ∑ z2 ∈ Z, (∑ x ∈ X, ∑ y ∈ Y, f x y z1 * f x y z2) ^ 4 :=
    e41_pm4 Z (fun z1 z2 => ∑ x ∈ X, ∑ y ∈ Y, f x y z1 * f x y z2)
  have hbox : ∑ z1 ∈ Z, ∑ z2 ∈ Z, (∑ x ∈ X, ∑ y ∈ Y, f x y z1 * f x y z2) ^ 4 ≤
      (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 *
        ∑ z1 ∈ Z, ∑ z2 ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X,
          f x1 y1 z1 * f x1 y1 z2 * (f x1 y2 z1 * f x1 y2 z2) *
            (f x2 y1 z1 * f x2 y1 z2 * (f x2 y2 z1 * f x2 y2 z2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro z1 _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro z2 _
    exact e41_box X Y (fun x y => f x y z1 * f x y z2)
      (fun x y => mul_nonneg (h0 x y z1) (h0 x y z2))
  have hH := e41_hom X Y Z f h0 h1 hP m hm0 hmX hmY hmZ
  exact e41_combine _ _ _ _ _ _ _ _ hm0 hS hPM hbox hH

theorem erdos_41635_hyp_box : ∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n →
    ∀ (X Y Z : Finset ℕ), X.Nonempty → Y.Nonempty → Z.Nonempty →
    (∀ x ∈ X, 0 < x) → (∀ y ∈ Y, 0 < y) → (∀ z ∈ Z, 0 < z) →
    (((X ×ˢ (Y ×ˢ Z)).filter (fun t => t.1 * t.2.1 * t.2.2 ∈ A)).card : ℝ) ^ 8 *
      ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ 3 * ((X.card : ℝ) * Y.card * Z.card) ^ 8 := by
  intro n A hA X Y Z _ _ _ _ _ _
  have hcard : (((X ×ˢ (Y ×ˢ Z)).filter (fun t => t.1 * t.2.1 * t.2.2 ∈ A)).card : ℝ) =
      ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, (if x * y * z ∈ A then (1 : ℝ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : x * y * z ∈ A <;> simp [h]
  have h0 : ∀ x y z : ℕ, (0 : ℝ) ≤ (if x * y * z ∈ A then (1 : ℝ) else 0) := by
    intro x y z; split_ifs <;> norm_num
  have h1 : ∀ x y z : ℕ, (if x * y * z ∈ A then (1 : ℝ) else 0) ≤ 1 := by
    intro x y z; split_ifs <;> norm_num
  have hP : ∀ x1 x2 y1 y2 z1 z2 : ℕ, x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
      (if x1 * y1 * z1 ∈ A then (1 : ℝ) else 0) * (if x1 * y2 * z2 ∈ A then (1 : ℝ) else 0) *
        (if x2 * y1 * z2 ∈ A then (1 : ℝ) else 0) * (if x2 * y2 * z1 ∈ A then (1 : ℝ) else 0)
        = 0 := by
    intro x1 x2 y1 y2 z1 z2 hx hy hz
    by_cases a1 : x1 * y1 * z1 ∈ A
    · by_cases a2 : x1 * y2 * z2 ∈ A
      · by_cases a3 : x2 * y1 * z2 ∈ A
        · by_cases a4 : x2 * y2 * z1 ∈ A
          · exact (e41_pasch A n hA a1 a2 a3 a4 hx hy hz).elim
          · simp [a4]
        · simp [a3]
      · simp [a2]
    · simp [a1]
  have hmX : ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ X.card :=
    Nat.cast_le.mpr (min_le_left _ _)
  have hmY : ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ Y.card :=
    Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_left _ _))
  have hmZ : ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ Z.card :=
    Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_right _ _))
  rw [hcard]
  exact e41_main X Y Z (fun x y z => if x * y * z ∈ A then (1 : ℝ) else 0) h0 h1 hP _
    (Nat.cast_nonneg _) hmX hmY hmZ
end erdos_41635_hyp_box_ns

namespace erdos_41635_hyp_sq_cancel_ns
-- CHECK: Nat.pow_dvd_pow_iff Nat.eq_of_mul_eq_mul_left Nat.mul_self_dvd_mul_self_iff
open scoped Classical

open Filter

open scoped Classical

open Filter

theorem erdos_41635_hyp_sq_cancel : ∀ x y z : ℕ, 0 < x → IsSquare (x ^ 2 * (y * z)) →
    IsSquare (y * z) := by
  intro x y z hx h
  obtain ⟨r, hr⟩ := h
  have hdvd : x ^ 2 ∣ r ^ 2 := ⟨y * z, by rw [sq r, ← hr]⟩
  have hxr : x ∣ r := (Nat.pow_dvd_pow_iff two_ne_zero).mp hdvd
  obtain ⟨s, rfl⟩ := hxr
  have h2 : x ^ 2 * (y * z) = x ^ 2 * (s * s) := by rw [hr]; ring
  exact ⟨s, Nat.eq_of_mul_eq_mul_left (by positivity) h2⟩
end erdos_41635_hyp_sq_cancel_ns

namespace erdos_41635_hyp_Sn_valid_ns
open scoped Classical

open Filter

open scoped Classical

open Filter

private lemma sq_dvd {p m : ℕ} (hp : p.Prime) (h : IsSquare (p * m)) : p ∣ m := by
  obtain ⟨r, hr⟩ := h
  have h1 : p ∣ r * r := ⟨m, hr.symm⟩
  have h2 : p ∣ r := by
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h <;> exact h
  obtain ⟨t, ht⟩ := h2
  have hm : p * m = p * (p * (t * t)) := by rw [hr, ht]; ring
  exact ⟨t * t, Nat.eq_of_mul_eq_mul_left hp.pos hm⟩

private lemma sq_cancel {p m : ℕ} (hp : p.Prime) (h : IsSquare (p * p * m)) : IsSquare m := by
  obtain ⟨r, hr⟩ := h
  have h1 : p ∣ r * r := ⟨p * m, by rw [← hr]; ring⟩
  have h2 : p ∣ r := by
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h <;> exact h
  obtain ⟨t, ht⟩ := h2
  have hm : p * p * m = p * p * (t * t) := by rw [hr, ht]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hp.pos) hm⟩

private lemma sq_prime_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : IsSquare (p * q)) :
    p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp (sq_dvd hp h)

private lemma sq_dvd2 {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : IsSquare (p * (q * m))) : p ∣ m := by
  rcases (Nat.Prime.dvd_mul hp).mp (sq_dvd hp h) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h1) hpq
  · exact h1

private abbrev SP (x : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ x = p * q

private lemma sp_eq {x y : ℕ} (hx : SP x) (hy : SP y) (h : IsSquare (x * y)) : x = y := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
  have h1 : p ∣ s * t :=
    sq_dvd2 hp hq hpq (by rwa [show p * (q * (s * t)) = p * q * (s * t) by ring])
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · have e := (Nat.prime_dvd_prime_iff_eq hp hs).mp h2
    rw [← e] at h ⊢
    have h3 : IsSquare (q * t) :=
      sq_cancel hp (by rwa [show p * p * (q * t) = p * q * (p * t) by ring])
    rw [sq_prime_eq hq ht h3]
  · have e := (Nat.prime_dvd_prime_iff_eq hp ht).mp h2
    rw [← e] at h ⊢
    have h3 : IsSquare (q * s) :=
      sq_cancel hp (by rwa [show p * p * (q * s) = p * q * (s * p) by ring])
    rw [sq_prime_eq hq hs h3]; ring

private lemma sp_not_sq {x : ℕ} (hx : SP x) : ¬ IsSquare x := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
  intro h
  exact hpq (sq_prime_eq hp hq h)

private lemma key2 {s t d : ℕ} (hs : s.Prime) (ht : t.Prime) (hd : SP d)
    (h : IsSquare (s * t * d)) : d = s * t := by
  by_cases hst : s = t
  · rw [← hst] at h
    exact absurd (sq_cancel hs h) (sp_not_sq hd)
  · obtain ⟨u, v, hu, hv, huv, rfl⟩ := hd
    have h1 : s ∣ u * v :=
      sq_dvd2 hs ht hst (by rwa [show s * (t * (u * v)) = s * t * (u * v) by ring])
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · have e := (Nat.prime_dvd_prime_iff_eq hs hu).mp h2
      rw [← e] at h ⊢
      have h3 : IsSquare (t * v) :=
        sq_cancel hs (by rwa [show s * s * (t * v) = s * t * (s * v) by ring])
      rw [sq_prime_eq ht hv h3]
    · have e := (Nat.prime_dvd_prime_iff_eq hs hv).mp h2
      rw [← e] at h ⊢
      have h3 : IsSquare (t * u) :=
        sq_cancel hs (by rwa [show s * s * (t * u) = s * t * (u * s) by ring])
      rw [sq_prime_eq ht hu h3]; ring

private lemma key1 {p q s c d : ℕ} (hq : q.Prime) (hs : s.Prime)
    (hc : SP c) (hd : SP d) (h : IsSquare (q * s * c * d)) :
    p * q * (p * s) = c * d ∨ p * q * c = p * s * d ∨ p * q * d = p * s * c := by
  by_cases hqs : q = s
  · rw [← hqs] at h ⊢
    have h1 : IsSquare (c * d) :=
      sq_cancel hq (by rwa [show q * q * (c * d) = q * q * c * d by ring])
    rw [sp_eq hc hd h1]
    right; left; ring
  · have h1 : q ∣ c * d :=
      sq_dvd2 hq hs hqs (by rwa [show q * (s * (c * d)) = q * s * c * d by ring])
    rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · obtain ⟨u, v, hu, hv, huv, rfl⟩ := hc
      rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
      · have e := (Nat.prime_dvd_prime_iff_eq hq hu).mp h3
        rw [← e] at h ⊢
        have h4 : IsSquare (s * v * d) :=
          sq_cancel hq (by rwa [show q * q * (s * v * d) = q * s * (q * v) * d by ring])
        rw [key2 hs hv hd h4]
        right; right; ring
      · have e := (Nat.prime_dvd_prime_iff_eq hq hv).mp h3
        rw [← e] at h ⊢
        have h4 : IsSquare (s * u * d) :=
          sq_cancel hq (by rwa [show q * q * (s * u * d) = q * s * (u * q) * d by ring])
        rw [key2 hs hu hd h4]
        right; right; ring
    · obtain ⟨u, v, hu, hv, huv, rfl⟩ := hd
      rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
      · have e := (Nat.prime_dvd_prime_iff_eq hq hu).mp h3
        rw [← e] at h ⊢
        have h4 : IsSquare (s * v * c) :=
          sq_cancel hq (by rwa [show q * q * (s * v * c) = q * s * c * (q * v) by ring])
        rw [key2 hs hv hc h4]
        right; left; ring
      · have e := (Nat.prime_dvd_prime_iff_eq hq hv).mp h3
        rw [← e] at h ⊢
        have h4 : IsSquare (s * u * c) :=
          sq_cancel hq (by rwa [show q * q * (s * u * c) = q * s * c * (u * q) by ring])
        rw [key2 hs hu hc h4]
        right; left; ring

private lemma keyM' {p q b c d : ℕ} (hp : p.Prime) (hq : q.Prime) (hb : SP b) (hc : SP c)
    (hd : SP d) (hpb : p ∣ b) (h : IsSquare (p * q * b * c * d)) :
    p * q * b = c * d ∨ p * q * c = b * d ∨ p * q * d = b * c := by
  obtain ⟨s1, s2, hs1, hs2, hs12, rfl⟩ := hb
  rcases (Nat.Prime.dvd_mul hp).mp hpb with h1 | h1
  · have e := (Nat.prime_dvd_prime_iff_eq hp hs1).mp h1
    rw [← e] at h ⊢
    have h2 : IsSquare (q * s2 * c * d) :=
      sq_cancel hp (by rwa [show p * p * (q * s2 * c * d) = p * q * (p * s2) * c * d by ring])
    exact key1 hq hs2 hc hd h2
  · have e := (Nat.prime_dvd_prime_iff_eq hp hs2).mp h1
    rw [← e] at h ⊢
    have h2 : IsSquare (q * s1 * c * d) :=
      sq_cancel hp (by rwa [show p * p * (q * s1 * c * d) = p * q * (s1 * p) * c * d by ring])
    have := key1 (p := p) hq hs1 hc hd h2
    rw [show s1 * p = p * s1 by ring]
    exact this

private lemma keyM {a b c d : ℕ} (ha : SP a) (hb : SP b) (hc : SP c) (hd : SP d)
    (h : IsSquare (a * b * c * d)) : a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := ha
  have h1 : p ∣ b * c * d :=
    sq_dvd2 hp hq hpq (by rwa [show p * (q * (b * c * d)) = p * q * b * c * d by ring])
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact keyM' hp hq hb hc hd h3 h
    · have := keyM' hp hq hc hb hd h3
        (by rwa [show p * q * c * b * d = p * q * b * c * d by ring])
      rcases this with e | e | e
      · right; left; exact e
      · left; exact e
      · right; right; rw [e]; ring
  · have := keyM' hp hq hd hb hc h2
      (by rwa [show p * q * d * b * c = p * q * b * c * d by ring])
    rcases this with e | e | e
    · right; right; exact e
    · left; rw [e]; ring
    · right; left; rw [e]; ring

theorem erdos_41635_hyp_Sn_valid : ∀ n : ℕ, ErdosValid41635 (erdosSpq n) n := by
  intro n
  unfold ErdosValid41635
  have toSP : ∀ x ∈ erdosSpq n, SP x := by
    intro x hx
    unfold erdosSpq at hx
    rw [Finset.mem_filter] at hx
    obtain ⟨_, p, q, hp, hq, hpq, rfl⟩ := hx
    exact ⟨p, q, hp, hq, hpq.ne, rfl⟩
  have hpos : ∀ x ∈ erdosSpq n, 0 < x := by
    intro x hx
    unfold erdosSpq at hx
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx
    exact hx.1.1
  refine ⟨by unfold erdosSpq; exact Finset.filter_subset _ _, ?_⟩
  intro a ha b hb c hc d hd hab hbc hcd hsq
  have hb0 := hpos b hb
  have hc0 := hpos c hc
  have hd0 := hpos d hd
  rcases keyM (toSP a ha) (toSP b hb) (toSP c hc) (toSP d hd) hsq with h | h | h
  · have h1 : c * d ≤ c * b := by
      rw [← h]; exact Nat.mul_le_mul (by omega) (le_refl b)
    have h2 : c * b ≤ c * d := Nat.mul_le_mul (le_refl c) (by omega)
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left hc0 (le_antisymm h2 h1)
    rw [hbd] at h
    have hac : a = c := Nat.eq_of_mul_eq_mul_right hd0 h
    rw [hac, hbd]; ring
  · have h1 : b * d ≤ b * c := by
      rw [← h]; exact Nat.mul_le_mul hab (le_refl c)
    have h2 : b * c ≤ b * d := Nat.mul_le_mul (le_refl b) hcd
    have hcd' : c = d := Nat.eq_of_mul_eq_mul_left hb0 (le_antisymm h2 h1)
    rw [← hcd'] at h
    have hab' : a = b := Nat.eq_of_mul_eq_mul_right hc0 h
    rw [hab', ← hcd']
  · exact h
end erdos_41635_hyp_Sn_valid_ns

namespace erdos_41635_hyp_mertens_lower_ns
-- CHECK: Nat.ordProj_mul_ordCompl_eq_self Nat.ordCompl_pos Nat.not_dvd_ordCompl Nat.ordProj_dvd Summable.sum_le_tsum Finset.sum_image Real.exp_sum
open scoped Classical

open Filter

open scoped Classical

open Filter

private lemma geom_bound (q : ℕ) (hq : q.Prime) (E : Finset ℕ) :
    ∑ e ∈ E, (1 / (q:ℝ)) ^ e ≤ (1 - 1 / (q:ℝ))⁻¹ := by
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  have h0 : (0:ℝ) ≤ 1 / (q:ℝ) := by positivity
  have h1 : 1 / (q:ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact Summable.sum_le_tsum E (fun i _ => by positivity) (summable_geometric_of_lt_one h0 h1)

private lemma euler_ineq : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    ∀ S : Finset ℕ, (∀ m ∈ S, 0 < m ∧ ∀ p, p.Prime → p ∣ m → p ∈ P) →
      ∑ m ∈ S, (1 / (m:ℝ)) ≤ ∏ p ∈ P, (1 - 1 / (p:ℝ))⁻¹ := by
  intro P
  refine Finset.induction_on P ?_ ?_
  · intro _ S hS
    have hsub : S ⊆ {1} := by
      intro m hm
      rw [Finset.mem_singleton]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have := (hS m hm).2 p hp hpd
      simp at this
    calc ∑ m ∈ S, (1 / (m:ℝ)) ≤ ∑ m ∈ ({1} : Finset ℕ), (1 / (m:ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = ∏ p ∈ (∅ : Finset ℕ), (1 - 1 / (p:ℝ))⁻¹ := by simp
  · intro q P hqP ih hP S hS
    have hq : q.Prime := hP q (Finset.mem_insert_self q P)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hS' : ∀ m ∈ S.image (fun m : ℕ => m / q ^ m.factorization q),
        0 < m ∧ ∀ p, p.Prime → p ∣ m → p ∈ P := by
      intro m' hm'
      rw [Finset.mem_image] at hm'
      obtain ⟨m, hm, rfl⟩ := hm'
      have hm0 : m ≠ 0 := (hS m hm).1.ne'
      refine ⟨Nat.ordCompl_pos q hm0, ?_⟩
      intro p hp hpd
      have hpm : p ∣ m := hpd.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m q))
      rcases Finset.mem_insert.mp ((hS m hm).2 p hp hpm) with h | h
      · rw [h] at hpd hp
        exact absurd hpd (Nat.not_dvd_ordCompl hp hm0)
      · exact h
    have hdec : ∀ m ∈ S, (1 / (m:ℝ)) =
        (1 / (q:ℝ)) ^ (m.factorization q) * (1 / ((m / q ^ m.factorization q : ℕ) : ℝ)) := by
      intro m _
      have h := Nat.ordProj_mul_ordCompl_eq_self m q
      conv_lhs => rw [← h]
      rw [Nat.cast_mul, Nat.cast_pow, div_pow, one_pow, div_mul_div_comm, one_mul]
    have hinj : Set.InjOn (fun m : ℕ => (m.factorization q, m / q ^ m.factorization q)) ↑S := by
      intro x _ y _ hxy
      have h1 : x.factorization q = y.factorization q := congrArg Prod.fst hxy
      have h2 : x / q ^ x.factorization q = y / q ^ y.factorization q := congrArg Prod.snd hxy
      rw [← Nat.ordProj_mul_ordCompl_eq_self x q, ← Nat.ordProj_mul_ordCompl_eq_self y q, h2, h1]
    have hsub : S.image (fun m : ℕ => (m.factorization q, m / q ^ m.factorization q)) ⊆
        (S.image (fun m : ℕ => m.factorization q)) ×ˢ
          (S.image (fun m : ℕ => m / q ^ m.factorization q)) := by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨m, hm, rfl⟩ := ht
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩,
        Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    have hinv : (0:ℝ) ≤ (1 - 1 / (q:ℝ))⁻¹ := by
      have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
      have : 1 / (q:ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
      exact inv_nonneg.mpr (by linarith)
    calc ∑ m ∈ S, (1 / (m:ℝ))
        = ∑ m ∈ S, (1 / (q:ℝ)) ^ (m.factorization q) *
            (1 / ((m / q ^ m.factorization q : ℕ) : ℝ)) := Finset.sum_congr rfl hdec
      _ = ∑ t ∈ S.image (fun m : ℕ => (m.factorization q, m / q ^ m.factorization q)),
            (1 / (q:ℝ)) ^ t.1 * (1 / (t.2 : ℝ)) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ t ∈ (S.image (fun m : ℕ => m.factorization q)) ×ˢ
            (S.image (fun m : ℕ => m / q ^ m.factorization q)),
            (1 / (q:ℝ)) ^ t.1 * (1 / (t.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t _ _ => mul_nonneg (pow_nonneg (by positivity) _) (by positivity))
      _ = (∑ e ∈ S.image (fun m : ℕ => m.factorization q), (1 / (q:ℝ)) ^ e) *
            (∑ m ∈ S.image (fun m : ℕ => m / q ^ m.factorization q), (1 / (m:ℝ))) := by
          simp only [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (1 - 1 / (q:ℝ))⁻¹ * ∏ p ∈ P, (1 - 1 / (p:ℝ))⁻¹ :=
          mul_le_mul (geom_bound q hq _) (ih hP' _ hS')
            (Finset.sum_nonneg (fun i _ => by positivity)) hinv
      _ = ∏ p ∈ insert q P, (1 - 1 / (p:ℝ))⁻¹ := by rw [Finset.prod_insert hqP]

private lemma log_le_harm : ∀ n : ℕ,
    Real.log ((n:ℝ) + 1) ≤ ∑ i ∈ Finset.range n, 1 / ((i:ℝ) + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < ((n:ℝ) + 1 + 1) / ((n:ℝ) + 1) by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at h
    have hid : ((n:ℝ) + 1 + 1) / ((n:ℝ) + 1) - 1 = 1 / ((n:ℝ) + 1) := by
      rw [div_sub_one hpos.ne']
      congr 1
      ring
    push_cast
    linarith

private lemma f_nonneg (m : ℕ) : 0 ≤ 1 / ((m:ℝ) * ((m:ℝ) - 1)) := by
  apply div_nonneg zero_le_one
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have : (1:ℝ) ≤ m := by exact_mod_cast h
    nlinarith

private lemma tele (N : ℕ) :
    ∑ m ∈ Finset.range (N + 2), (1 / ((m:ℝ) * ((m:ℝ) - 1))) = 1 - 1 / ((N:ℝ) + 1) := by
  induction N with
  | zero => norm_num [Finset.sum_range_succ]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Finset.sum_range_succ, ih]
    push_cast
    have hA : (n:ℝ) + 1 ≠ 0 := by positivity
    have hB : (n:ℝ) + 2 ≠ 0 := by positivity
    have hC : (n:ℝ) + 1 + 1 ≠ 0 := by positivity
    have h3 : (n:ℝ) + 2 - 1 = (n:ℝ) + 1 := by ring
    rw [h3]
    field_simp
    ring

private lemma inv_le_exp (p : ℕ) (hp : p.Prime) :
    (1 - 1 / (p:ℝ))⁻¹ ≤ Real.exp (1 / ((p:ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p:ℝ) ≠ 0 := (by linarith : (0:ℝ) < p).ne'
  have hp1 : (p:ℝ) - 1 ≠ 0 := (by linarith : (0:ℝ) < p - 1).ne'
  have heq : (1 - 1 / (p:ℝ))⁻¹ = 1 / ((p:ℝ) - 1) + 1 := by
    rw [inv_eq_one_div, one_sub_div hp0, one_div_div, div_add_one hp1]
    congr 1
    ring
  rw [heq]
  linarith [Real.add_one_le_exp (1 / ((p:ℝ) - 1))]

private lemma split_prime (p : ℕ) (hp : p.Prime) :
    1 / ((p:ℝ) - 1) = 1 / (p:ℝ) + 1 / ((p:ℝ) * ((p:ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p:ℝ) ≠ 0 := (by linarith : (0:ℝ) < p).ne'
  have hp1 : (p:ℝ) - 1 ≠ 0 := (by linarith : (0:ℝ) < p - 1).ne'
  rw [div_add_div _ _ hp0 (mul_ne_zero hp0 hp1),
    div_eq_div_iff hp1 (mul_ne_zero hp0 (mul_ne_zero hp0 hp1))]
  ring

theorem erdos_41635_hyp_mertens_lower : ∀ x : ℝ, 1 < x →
    Real.log (Real.log x) - 1 <
      ∑ q ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 / (q : ℝ)) := by
  intro x hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⌊x⌋₊ = N := ⟨_, rfl⟩
  have hxN : x < (N:ℝ) + 1 := by rw [← hN]; exact Nat.lt_floor_add_one x
  rw [hN]
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Finset ℕ, (Finset.range (N + 1)).filter Nat.Prime = Ps := ⟨_, rfl⟩
  rw [hPs]
  have hPsP : ∀ p ∈ Ps, p.Prime := by
    intro p hp
    rw [← hPs] at hp
    exact (Finset.mem_filter.mp hp).2
  have hPsub : Ps ⊆ Finset.range (N + 1) := by
    rw [← hPs]; exact Finset.filter_subset _ _
  have hinj1 : Set.InjOn (fun i : ℕ => i + 1) ↑(Finset.range N) := by
    intro a _ b _ h
    simpa using h
  have hE := euler_ineq Ps hPsP ((Finset.range N).image (fun i : ℕ => i + 1)) (by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.mem_range] at hi
    refine ⟨Nat.succ_pos i, ?_⟩
    intro p hp hpd
    have := Nat.le_of_dvd (Nat.succ_pos i) hpd
    rw [← hPs]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  have hS : ∑ m ∈ (Finset.range N).image (fun i : ℕ => i + 1), (1 / (m:ℝ)) =
      ∑ i ∈ Finset.range N, 1 / ((i:ℝ) + 1) := by
    rw [Finset.sum_image hinj1]
    simp
  have hH := log_le_harm N
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log x < Real.log ((N:ℝ) + 1) := Real.log_lt_log hx0 hxN
  have hG : Real.log x < ∏ p ∈ Ps, (1 - 1 / (p:ℝ))⁻¹ := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hGpos : 0 < ∏ p ∈ Ps, (1 - 1 / (p:ℝ))⁻¹ := by linarith
  have h1 := Real.log_lt_log hlogpos hG
  have h2 : ∏ p ∈ Ps, (1 - 1 / (p:ℝ))⁻¹ ≤ Real.exp (∑ p ∈ Ps, 1 / ((p:ℝ) - 1)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hPsP p hp).two_le
      have : 1 / (p:ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      exact inv_le_exp p (hPsP p hp)
  have h3 : Real.log (∏ p ∈ Ps, (1 - 1 / (p:ℝ))⁻¹) ≤ ∑ p ∈ Ps, 1 / ((p:ℝ) - 1) :=
    (Real.log_le_log hGpos h2).trans (le_of_eq (Real.log_exp _))
  have h4 : ∑ p ∈ Ps, 1 / ((p:ℝ) - 1) =
      ∑ p ∈ Ps, 1 / (p:ℝ) + ∑ p ∈ Ps, 1 / ((p:ℝ) * ((p:ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p hp => split_prime p (hPsP p hp))
  have h5 : ∑ p ∈ Ps, 1 / ((p:ℝ) * ((p:ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ Ps, 1 / ((p:ℝ) * ((p:ℝ) - 1))
        ≤ ∑ m ∈ Finset.range (N + 1), 1 / ((m:ℝ) * ((m:ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun i _ _ => f_nonneg i)
      _ ≤ ∑ m ∈ Finset.range (N + 1 + 2), 1 / ((m:ℝ) * ((m:ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro i hi; rw [Finset.mem_range] at hi ⊢; omega) (fun i _ _ => f_nonneg i)
      _ = 1 - 1 / (((N + 1 : ℕ) : ℝ) + 1) := tele (N + 1)
      _ ≤ 1 := by
          have : (0:ℝ) ≤ 1 / (((N + 1 : ℕ) : ℝ) + 1) := by positivity
          linarith
  linarith
end erdos_41635_hyp_mertens_lower_ns

theorem erdos_41635_hyp_pasch : ∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n →
    ∀ x1 x2 y1 y2 z1 z2 : ℕ, 0 < x1 → 0 < x2 → 0 < y1 → 0 < y2 → 0 < z1 → 0 < z2 →
    x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
    ¬ (x1 * y1 * z1 ∈ A ∧ x1 * y2 * z2 ∈ A ∧ x2 * y1 * z2 ∈ A ∧ x2 * y2 * z1 ∈ A) := by
  exact erdos_41635_hyp_pasch_ns.erdos_41635_hyp_pasch

theorem erdos_41635_hyp_cs_pair : ∀ (X Y : Finset ℕ) (G : Finset (ℕ × ℕ)), G ⊆ X ×ˢ Y →
    X.Nonempty → Y.Nonempty →
    (G.card : ℝ) ^ 4 ≤ (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 *
      ∑ y1 ∈ Y, ∑ y2 ∈ Y, (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2 := by
  exact erdos_41635_hyp_cs_pair_ns.erdos_41635_hyp_cs_pair

theorem erdos_41635_hyp_octahedra : ∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)),
    T ⊆ X ×ˢ (Y ×ˢ Z) → X.Nonempty → Y.Nonempty → Z.Nonempty →
    (T.card : ℝ) ^ 8 ≤ ((X.card : ℝ) * Y.card * Z.card) ^ 6 * (erdosOctaHom X Y Z T : ℝ) := by
  exact erdos_41635_hyp_octahedra_ns.erdos_41635_hyp_octahedra

theorem erdos_41635_hyp_box : ∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n →
    ∀ (X Y Z : Finset ℕ), X.Nonempty → Y.Nonempty → Z.Nonempty →
    (∀ x ∈ X, 0 < x) → (∀ y ∈ Y, 0 < y) → (∀ z ∈ Z, 0 < z) →
    (((X ×ˢ (Y ×ˢ Z)).filter (fun t => t.1 * t.2.1 * t.2.2 ∈ A)).card : ℝ) ^ 8 *
      ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ 3 * ((X.card : ℝ) * Y.card * Z.card) ^ 8 := by
  exact erdos_41635_hyp_box_ns.erdos_41635_hyp_box

namespace erdos_41635_hyp_upper_ns
open scoped Classical

def erdosPaschFree (A : Finset ℕ) : Prop :=
  ∀ x1 x2 y1 y2 z1 z2 : ℕ, x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 →
    x1 * y1 * z1 ∈ A → x1 * y2 * z2 ∈ A → x2 * y1 * z2 ∈ A → x2 * y2 * z1 ∈ A → False

def erdosBoxTriples (A X Y Z : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (X ×ˢ (Y ×ˢ Z)).filter (fun t => t.1 * t.2.1 * t.2.2 ∈ A)

def erdosBoxSparse (A : Finset ℕ) : Prop :=
  ∀ X Y Z : Finset ℕ, (erdosBoxTriples A X Y Z).card ^ 8 ≤
    (X.card * Y.card ^ 2 * Z.card ^ 2 + X.card ^ 2 * Y.card * Z.card ^ 2
      + X.card ^ 2 * Y.card ^ 2 * Z.card) * (X.card * Y.card * Z.card) ^ 6

-- S1a: the four Pasch products multiply to a square; the three pairings are
-- W*z1^2 vs W*z2^2, x1^2 vs x2^2 (times y1y2z1z2) and y1^2 vs y2^2 (times x1x2z1z2),
-- all unequal because elements of A are positive. The sorted ad = bc is one of
-- these pairings, so A is invalid.
namespace erdos_41635_hyp_upper_hyp_pasch_ns

open scoped Classical

open scoped Classical

open Filter

private lemma s3 (A : Finset ℕ)
    (H : ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsq : IsSquare (a * b * c * d)) (h1 : a * b ≠ c * d) (h2 : a * c ≠ b * d)
    (h3 : a * d ≠ b * c) (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) : False := by
  rcases le_total b c with hbc | hcb
  · exact h3 (H a ha b hb c hc d hd hab hbc hcd hsq)
  · rcases le_total b d with hbd | hdb
    · have hsq' : IsSquare (a * c * b * d) := by
        rw [show a * c * b * d = a * b * c * d by ring]; exact hsq
      have := H a ha c hc b hb d hd hac hcb hbd hsq'
      exact h3 (by linarith [mul_comm c b])
    · have hsq' : IsSquare (a * c * d * b) := by
        rw [show a * c * d * b = a * b * c * d by ring]; exact hsq
      have := H a ha c hc d hd b hb hac hcd hdb hsq'
      exact h1 this

private lemma s2 (A : Finset ℕ)
    (H : ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsq : IsSquare (a * b * c * d)) (h1 : a * b ≠ c * d) (h2 : a * c ≠ b * d)
    (h3 : a * d ≠ b * c) (hab : a ≤ b) (hcd : c ≤ d) : False := by
  rcases le_total a c with hac | hca
  · exact s3 A H a b c d ha hb hc hd hsq h1 h2 h3 hab hcd hac
  · have hsq' : IsSquare (c * d * a * b) := by
      rw [show c * d * a * b = a * b * c * d by ring]; exact hsq
    exact s3 A H c d a b hc hd ha hb hsq' (fun h => h1 h.symm)
      (fun h => h2 (by linarith [mul_comm a c, mul_comm b d]))
      (fun h => h3 (by linarith [mul_comm a d, mul_comm b c, mul_comm c b, mul_comm d a]))
      hcd hab hca

private lemma s1 (A : Finset ℕ)
    (H : ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsq : IsSquare (a * b * c * d)) (h1 : a * b ≠ c * d) (h2 : a * c ≠ b * d)
    (h3 : a * d ≠ b * c) (hab : a ≤ b) : False := by
  rcases le_total c d with hcd | hdc
  · exact s2 A H a b c d ha hb hc hd hsq h1 h2 h3 hab hcd
  · have hsq' : IsSquare (a * b * d * c) := by
      rw [show a * b * d * c = a * b * c * d by ring]; exact hsq
    exact s2 A H a b d c ha hb hd hc hsq'
      (fun h => h1 (by linarith [mul_comm d c]))
      (fun h => h3 h) (fun h => h2 h) hab hdc

private lemma four (A : Finset ℕ)
    (H : ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsq : IsSquare (a * b * c * d)) (h1 : a * b ≠ c * d) (h2 : a * c ≠ b * d)
    (h3 : a * d ≠ b * c) : False := by
  rcases le_total a b with hab | hba
  · exact s1 A H a b c d ha hb hc hd hsq h1 h2 h3 hab
  · have hsq' : IsSquare (b * a * c * d) := by
      rw [show b * a * c * d = a * b * c * d by ring]; exact hsq
    exact s1 A H b a c d hb ha hc hd hsq'
      (fun h => h1 (by linarith [mul_comm a b]))
      (fun h => h3 h.symm) (fun h => h2 h.symm) hba

theorem erdos_41635_hyp_upper_hyp_pasch : ∀ (A : Finset ℕ) (n : ℕ),
    A ⊆ Finset.Ioc 0 n →
    (∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c) →
    erdosPaschFree A := by
  intro A n hA H x1 x2 y1 y2 z1 z2 hx hy hz h1 h2 h3 h4
  have p1 := (Finset.mem_Ioc.mp (hA h1)).1
  have p2 := (Finset.mem_Ioc.mp (hA h2)).1
  have p3 := (Finset.mem_Ioc.mp (hA h3)).1
  have hx1 : 0 < x1 := Nat.pos_of_ne_zero (by rintro rfl; simp at p1)
  have hy1 : 0 < y1 := Nat.pos_of_ne_zero (by rintro rfl; simp at p1)
  have hz1 : 0 < z1 := Nat.pos_of_ne_zero (by rintro rfl; simp at p1)
  have hx2 : 0 < x2 := Nat.pos_of_ne_zero (by rintro rfl; simp at p3)
  have hy2 : 0 < y2 := Nat.pos_of_ne_zero (by rintro rfl; simp at p2)
  have hz2 : 0 < z2 := Nat.pos_of_ne_zero (by rintro rfl; simp at p2)
  apply four A H _ _ _ _ h1 h2 h3 h4
  · exact ⟨x1 * x2 * y1 * y2 * z1 * z2, by ring⟩
  · intro h
    apply hx
    have w : 0 < y1 * y2 * z1 * z2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hy1 hy2) hz1) hz2
    have e : x1 * x1 * (y1 * y2 * z1 * z2) = x2 * x2 * (y1 * y2 * z1 * z2) := by
      calc x1 * x1 * (y1 * y2 * z1 * z2) = (x1 * y1 * z1) * (x1 * y2 * z2) := by ring
        _ = (x2 * y1 * z2) * (x2 * y2 * z1) := h
        _ = x2 * x2 * (y1 * y2 * z1 * z2) := by ring
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right w e)
  · intro h
    apply hy
    have w : 0 < x1 * x2 * z1 * z2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hx1 hx2) hz1) hz2
    have e : y1 * y1 * (x1 * x2 * z1 * z2) = y2 * y2 * (x1 * x2 * z1 * z2) := by
      calc y1 * y1 * (x1 * x2 * z1 * z2) = (x1 * y1 * z1) * (x2 * y1 * z2) := by ring
        _ = (x1 * y2 * z2) * (x2 * y2 * z1) := h
        _ = y2 * y2 * (x1 * x2 * z1 * z2) := by ring
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right w e)
  · intro h
    apply hz
    have w : 0 < x1 * x2 * y1 * y2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hx1 hx2) hy1) hy2
    have e : z1 * z1 * (x1 * x2 * y1 * y2) = z2 * z2 * (x1 * x2 * y1 * y2) := by
      calc z1 * z1 * (x1 * x2 * y1 * y2) = (x1 * y1 * z1) * (x2 * y2 * z1) := by ring
        _ = (x1 * y2 * z2) * (x2 * y1 * z2) := h
        _ = z2 * z2 * (x1 * x2 * y1 * y2) := by ring
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_right w e)

end erdos_41635_hyp_upper_hyp_pasch_ns

theorem erdos_41635_hyp_upper_hyp_pasch : ∀ (A : Finset ℕ) (n : ℕ),
    A ⊆ Finset.Ioc 0 n →
    (∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
      a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c) →
    erdosPaschFree A := by
  exact erdos_41635_hyp_upper_hyp_pasch_ns.erdos_41635_hyp_upper_hyp_pasch

-- S1c: every 6-tuple counted by erdosOctaHom contains the four Pasch triples, so by
-- Pasch-freeness it has x1 = x2, y1 = y2 or z1 = z2. Count each of the three cases.
namespace erdos_41635_hyp_upper_hyp_hom_upper_ns

open scoped Classical

open scoped Classical

open Filter

theorem erdos_41635_hyp_upper_hyp_hom_upper : ∀ (A : Finset ℕ), erdosPaschFree A →
    ∀ X Y Z : Finset ℕ, erdosOctaHom X Y Z (erdosBoxTriples A X Y Z) ≤
      X.card * Y.card ^ 2 * Z.card ^ 2 + X.card ^ 2 * Y.card * Z.card ^ 2
        + X.card ^ 2 * Y.card ^ 2 * Z.card := by
  intro A hA X Y Z
  unfold erdosOctaHom
  have hsub : (((X ×ˢ X) ×ˢ ((Y ×ˢ Y) ×ˢ (Z ×ˢ Z))).filter (fun t =>
      ∀ a b c : Bool, ((if a then t.1.1 else t.1.2), (if b then t.2.1.1 else t.2.1.2),
        (if c then t.2.2.1 else t.2.2.2)) ∈ erdosBoxTriples A X Y Z)) ⊆
      (X.diag ×ˢ ((Y ×ˢ Y) ×ˢ (Z ×ˢ Z)) ∪ (X ×ˢ X) ×ˢ (Y.diag ×ˢ (Z ×ˢ Z)))
        ∪ (X ×ˢ X) ×ˢ ((Y ×ˢ Y) ×ˢ Z.diag) := by
    intro t ht
    rcases t with ⟨⟨x1, x2⟩, ⟨y1, y2⟩, ⟨z1, z2⟩⟩
    rw [Finset.mem_filter] at ht
    obtain ⟨hmem, hall⟩ := ht
    simp only [Finset.mem_product] at hmem
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hz1, hz2⟩ := hmem
    by_cases hx : x1 = x2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨Finset.mem_diag.mpr ⟨hx1, hx⟩,
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hy1, hy2⟩,
            Finset.mem_product.mpr ⟨hz1, hz2⟩⟩⟩))
    by_cases hy : y1 = y2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx1, hx2⟩,
          Finset.mem_product.mpr ⟨Finset.mem_diag.mpr ⟨hy1, hy⟩,
            Finset.mem_product.mpr ⟨hz1, hz2⟩⟩⟩))
    by_cases hz : z1 = z2
    · exact Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx1, hx2⟩,
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hy1, hy2⟩,
            Finset.mem_diag.mpr ⟨hz1, hz⟩⟩⟩)
    exfalso
    have h1 := hall true true true
    have h2 := hall true false false
    have h3 := hall false true false
    have h4 := hall false false true
    simp [erdosBoxTriples] at h1 h2 h3 h4
    exact hA x1 x2 y1 y2 z1 z2 hx hy hz h1.2 h2.2 h3.2 h4.2
  have h := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  refine h.trans (le_of_eq ?_)
  simp only [Finset.card_product, Finset.diag_card]
  ring

end erdos_41635_hyp_upper_hyp_hom_upper_ns

theorem erdos_41635_hyp_upper_hyp_hom_upper : ∀ (A : Finset ℕ), erdosPaschFree A →
    ∀ X Y Z : Finset ℕ, erdosOctaHom X Y Z (erdosBoxTriples A X Y Z) ≤
      X.card * Y.card ^ 2 * Z.card ^ 2 + X.card ^ 2 * Y.card * Z.card ^ 2
        + X.card ^ 2 * Y.card ^ 2 * Z.card := by
  exact erdos_41635_hyp_upper_hyp_hom_upper_ns.erdos_41635_hyp_upper_hyp_hom_upper

-- S1b: Cauchy-Schwarz over y-pairs, then over x, then the power mean over the
-- |Z|^2 pairs (z1, z2), then Cauchy-Schwarz over (x, y).
namespace erdos_41635_hyp_upper_hyp_octa_cs_ns

-- IMPORTS: Mathlib.Algebra.Order.Chebyshev
open scoped Classical

-- CHECK: Real.exp_one_lt_d9 Real.log_le_log Real.log_exp Real.log_nonneg one_div_pos
open scoped Classical

open Filter

private def ind (T : Finset (ℕ × ℕ × ℕ)) (x y z : ℕ) : ℕ := if (x, y, z) ∈ T then 1 else 0

private lemma cs1 (s : Finset ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  first
  | exact sq_sum_le_card_mul_sum_sq
  | (have h : (∑ i ∈ s, (f i : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
     exact_mod_cast h)
  | (have hz : (∑ i ∈ s, (f i : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 := by
        have hnn : (0:ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, ((f i:ℤ) - f j) ^ 2 :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
        have hexp : ∑ i ∈ s, ∑ j ∈ s, ((f i:ℤ) - f j) ^ 2
            = 2 * ((s.card:ℤ) * ∑ i ∈ s, (f i:ℤ) ^ 2) - 2 * (∑ i ∈ s, (f i:ℤ)) ^ 2 := by
          simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
        linarith
     exact_mod_cast hz)

private lemma sq_sum_eq (s : Finset ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i * f j := by
  rw [sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

private lemma cs2 (A B : Finset ℕ) (F : ℕ → ℕ → ℕ) :
    (∑ a ∈ A, ∑ b ∈ B, F a b) ^ 2 ≤ (A.card * B.card) * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 2 := by
  calc (∑ a ∈ A, ∑ b ∈ B, F a b) ^ 2 ≤ A.card * ∑ a ∈ A, (∑ b ∈ B, F a b) ^ 2 := cs1 _ _
    _ ≤ A.card * ∑ a ∈ A, (B.card * ∑ b ∈ B, F a b ^ 2) :=
        Nat.mul_le_mul le_rfl (Finset.sum_le_sum fun a _ => cs1 _ _)
    _ = (A.card * B.card) * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 2 := by
        rw [← Finset.mul_sum]; ring

private lemma cs4 (A B : Finset ℕ) (F : ℕ → ℕ → ℕ) :
    (∑ a ∈ A, ∑ b ∈ B, F a b) ^ 4 ≤ (A.card * B.card) ^ 3 * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 4 := by
  have h1 := cs2 A B F
  have h2 := cs2 A B (fun a b => F a b ^ 2)
  have e : ∀ a b, (F a b ^ 2) ^ 2 = F a b ^ 4 := fun a b => by ring
  simp only [e] at h2
  calc (∑ a ∈ A, ∑ b ∈ B, F a b) ^ 4 = ((∑ a ∈ A, ∑ b ∈ B, F a b) ^ 2) ^ 2 := by ring
    _ ≤ ((A.card * B.card) * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = (A.card * B.card) ^ 2 * (∑ a ∈ A, ∑ b ∈ B, F a b ^ 2) ^ 2 := by ring
    _ ≤ (A.card * B.card) ^ 2 * ((A.card * B.card) * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 4) :=
        Nat.mul_le_mul le_rfl h2
    _ = (A.card * B.card) ^ 3 * ∑ a ∈ A, ∑ b ∈ B, F a b ^ 4 := by ring

private lemma swap3 (Z Y : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ) :
    ∑ z ∈ Z, ∑ a ∈ Y, ∑ b ∈ Y, F z a b = ∑ a ∈ Y, ∑ b ∈ Y, ∑ z ∈ Z, F z a b := by
  calc ∑ z ∈ Z, ∑ a ∈ Y, ∑ b ∈ Y, F z a b = ∑ a ∈ Y, ∑ z ∈ Z, ∑ b ∈ Y, F z a b :=
        Finset.sum_comm
    _ = ∑ a ∈ Y, ∑ b ∈ Y, ∑ z ∈ Z, F z a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm

private lemma swapA (X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ y ∈ Y, ∑ z ∈ Z, ∑ x ∈ X, f x y z := by
  calc ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ y ∈ Y, ∑ x ∈ X, ∑ z ∈ Z, f x y z :=
        Finset.sum_comm
    _ = ∑ y ∈ Y, ∑ z ∈ Z, ∑ x ∈ X, f x y z := Finset.sum_congr rfl fun y _ => Finset.sum_comm

private lemma sum4_comm (X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) :
    ∑ y ∈ Y, ∑ z ∈ Z, ∑ x1 ∈ X, ∑ x2 ∈ X, f y z x1 x2
      = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f y z x1 x2 := by
  calc ∑ y ∈ Y, ∑ z ∈ Z, ∑ x1 ∈ X, ∑ x2 ∈ X, f y z x1 x2
      = ∑ y ∈ Y, ∑ x1 ∈ X, ∑ z ∈ Z, ∑ x2 ∈ X, f y z x1 x2 :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y ∈ Y, ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ z ∈ Z, f y z x1 x2 :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
    _ = ∑ x1 ∈ X, ∑ y ∈ Y, ∑ x2 ∈ X, ∑ z ∈ Z, f y z x1 x2 := Finset.sum_comm
    _ = ∑ x1 ∈ X, ∑ x2 ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f y z x1 x2 :=
        Finset.sum_congr rfl fun x1 _ => Finset.sum_comm

private lemma L2 (Y Z : Finset ℕ) (g : ℕ → ℕ → ℕ) :
    (∑ y ∈ Y, ∑ z ∈ Z, g y z) ^ 4 ≤
      (Y.card * Z.card) ^ 2 * ∑ y1 ∈ Y, ∑ y2 ∈ Y, (∑ z ∈ Z, g y1 z * g y2 z) ^ 2 := by
  have h1 : (∑ y ∈ Y, ∑ z ∈ Z, g y z) ^ 2 ≤
      Z.card * ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ z ∈ Z, g y1 z * g y2 z := by
    calc (∑ y ∈ Y, ∑ z ∈ Z, g y z) ^ 2 = (∑ z ∈ Z, ∑ y ∈ Y, g y z) ^ 2 := by
          rw [Finset.sum_comm]
      _ ≤ Z.card * ∑ z ∈ Z, (∑ y ∈ Y, g y z) ^ 2 := cs1 _ _
      _ = Z.card * ∑ z ∈ Z, ∑ y1 ∈ Y, ∑ y2 ∈ Y, g y1 z * g y2 z := by
          congr 1; exact Finset.sum_congr rfl fun z _ => sq_sum_eq _ _
      _ = Z.card * ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ z ∈ Z, g y1 z * g y2 z := by
          congr 1; exact swap3 _ _ _
  have h2 := cs2 Y Y (fun y1 y2 => ∑ z ∈ Z, g y1 z * g y2 z)
  calc (∑ y ∈ Y, ∑ z ∈ Z, g y z) ^ 4 = ((∑ y ∈ Y, ∑ z ∈ Z, g y z) ^ 2) ^ 2 := by ring
    _ ≤ (Z.card * ∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ z ∈ Z, g y1 z * g y2 z) ^ 2 :=
        Nat.pow_le_pow_left h1 2
    _ = Z.card ^ 2 * (∑ y1 ∈ Y, ∑ y2 ∈ Y, ∑ z ∈ Z, g y1 z * g y2 z) ^ 2 := by ring
    _ ≤ Z.card ^ 2 * ((Y.card * Y.card) *
          ∑ y1 ∈ Y, ∑ y2 ∈ Y, (∑ z ∈ Z, g y1 z * g y2 z) ^ 2) :=
        Nat.mul_le_mul le_rfl h2
    _ = (Y.card * Z.card) ^ 2 * ∑ y1 ∈ Y, ∑ y2 ∈ Y, (∑ z ∈ Z, g y1 z * g y2 z) ^ 2 := by ring

private def sPair (T : Finset (ℕ × ℕ × ℕ)) (Y Z : Finset ℕ) (x1 x2 : ℕ) : ℕ :=
  ∑ y ∈ Y, ∑ z ∈ Z, ind T x1 y z * ind T x2 y z

private def hPair (T : Finset (ℕ × ℕ × ℕ)) (Y Z : Finset ℕ) (x1 x2 : ℕ) : ℕ :=
  ∑ y1 ∈ Y, ∑ y2 ∈ Y,
    (∑ z ∈ Z, ind T x1 y1 z * ind T x2 y1 z * (ind T x1 y2 z * ind T x2 y2 z)) ^ 2

theorem erdos_41635_hyp_upper_hyp_octa_cs : ∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)),
    T ⊆ X ×ˢ (Y ×ˢ Z) →
    T.card ^ 8 ≤ erdosOctaHom X Y Z T * (X.card * Y.card * Z.card) ^ 6 := by
  intro X Y Z T hT
  have hA : T.card = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, ind T x y z := by
    have hf : (X ×ˢ (Y ×ˢ Z)).filter (fun t => t ∈ T) = T := by
      ext t; constructor
      · intro h; exact (Finset.mem_filter.mp h).2
      · intro h; exact Finset.mem_filter.mpr ⟨hT h, h⟩
    calc T.card = ((X ×ˢ (Y ×ˢ Z)).filter (fun t => t ∈ T)).card := by rw [hf]
      _ = ∑ t ∈ X ×ˢ (Y ×ˢ Z), if t ∈ T then 1 else 0 := by rw [Finset.card_filter]
      _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, ind T x y z := by
          simp only [Finset.sum_product, ind]
  have h1 : T.card ^ 2 ≤ (Y.card * Z.card) * ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 := by
    calc T.card ^ 2 = (∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, ind T x y z) ^ 2 := by rw [hA]
      _ = (∑ y ∈ Y, ∑ z ∈ Z, ∑ x ∈ X, ind T x y z) ^ 2 := by
          congr 1; exact swapA _ _ _ _
      _ ≤ (Y.card * Z.card) * ∑ y ∈ Y, ∑ z ∈ Z, (∑ x ∈ X, ind T x y z) ^ 2 :=
          cs2 Y Z (fun y z => ∑ x ∈ X, ind T x y z)
      _ = (Y.card * Z.card) * ∑ y ∈ Y, ∑ z ∈ Z, ∑ x1 ∈ X, ∑ x2 ∈ X,
            ind T x1 y z * ind T x2 y z := by
          congr 1
          exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => sq_sum_eq _ _
      _ = (Y.card * Z.card) * ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 := by
          congr 1; exact sum4_comm _ _ _ _
  have h3 : (∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2) ^ 4 ≤
      (X.card * X.card) ^ 3 * ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 ^ 4 :=
    cs4 X X (fun x1 x2 => sPair T Y Z x1 x2)
  have h4 : ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 ^ 4 ≤
      (Y.card * Z.card) ^ 2 * ∑ x1 ∈ X, ∑ x2 ∈ X, hPair T Y Z x1 x2 := by
    calc ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 ^ 4
        ≤ ∑ x1 ∈ X, ∑ x2 ∈ X, (Y.card * Z.card) ^ 2 * hPair T Y Z x1 x2 :=
          Finset.sum_le_sum fun x1 _ => Finset.sum_le_sum fun x2 _ =>
            L2 Y Z (fun y z => ind T x1 y z * ind T x2 y z)
      _ = (Y.card * Z.card) ^ 2 * ∑ x1 ∈ X, ∑ x2 ∈ X, hPair T Y Z x1 x2 := by
          simp only [← Finset.mul_sum]
  have h5 : erdosOctaHom X Y Z T = ∑ x1 ∈ X, ∑ x2 ∈ X, hPair T Y Z x1 x2 := by
    unfold erdosOctaHom hPair
    rw [Finset.card_filter]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ =>
      Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
    rw [sq_sum_eq]
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    split_ifs with h
    · have m1 : (x1, y1, z1) ∈ T := h true true true
      have m2 : (x1, y1, z2) ∈ T := h true true false
      have m3 : (x1, y2, z1) ∈ T := h true false true
      have m4 : (x1, y2, z2) ∈ T := h true false false
      have m5 : (x2, y1, z1) ∈ T := h false true true
      have m6 : (x2, y1, z2) ∈ T := h false true false
      have m7 : (x2, y2, z1) ∈ T := h false false true
      have m8 : (x2, y2, z2) ∈ T := h false false false
      simp [ind, m1, m2, m3, m4, m5, m6, m7, m8]
    · push_neg at h
      obtain ⟨a, b, c, hm⟩ := h
      cases a <;> cases b <;> cases c <;> simp_all [ind]
  calc T.card ^ 8 = (T.card ^ 2) ^ 4 := by ring
    _ ≤ ((Y.card * Z.card) * ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2) ^ 4 :=
        Nat.pow_le_pow_left h1 4
    _ = (Y.card * Z.card) ^ 4 * (∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2) ^ 4 := by ring
    _ ≤ (Y.card * Z.card) ^ 4 * ((X.card * X.card) ^ 3 *
          ∑ x1 ∈ X, ∑ x2 ∈ X, sPair T Y Z x1 x2 ^ 4) := Nat.mul_le_mul le_rfl h3
    _ ≤ (Y.card * Z.card) ^ 4 * ((X.card * X.card) ^ 3 *
          ((Y.card * Z.card) ^ 2 * ∑ x1 ∈ X, ∑ x2 ∈ X, hPair T Y Z x1 x2)) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl h4)
    _ = (∑ x1 ∈ X, ∑ x2 ∈ X, hPair T Y Z x1 x2) * (X.card * Y.card * Z.card) ^ 6 := by ring
    _ = erdosOctaHom X Y Z T * (X.card * Y.card * Z.card) ^ 6 := by rw [h5]

end erdos_41635_hyp_upper_hyp_octa_cs_ns

theorem erdos_41635_hyp_upper_hyp_octa_cs : ∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)),
    T ⊆ X ×ˢ (Y ×ˢ Z) →
    T.card ^ 8 ≤ erdosOctaHom X Y Z T * (X.card * Y.card * Z.card) ^ 6 := by
  exact erdos_41635_hyp_upper_hyp_octa_cs_ns.erdos_41635_hyp_upper_hyp_octa_cs

-- S2: dyadic box decomposition a = s*q*P(a); generic boxes are handled by
-- box-sparsity, the remaining a have a/P(a) y0-smooth (Mertens + Rankin).
-- Uses only the box-sparse property of A.
namespace erdos_41635_hyp_upper_hyp_box_to_bound_ns

open scoped Classical

open scoped Classical

open Filter

noncomputable def erdosPiReal (x : ℝ) : ℕ :=
  Nat.card {q : ℕ // q.Prime ∧ (q : ℝ) ≤ x}

def erdosLpf (a : ℕ) : ℕ := a.primeFactors.sup id

noncomputable def erdosRough (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter (fun m => m = 1 ∨ m.Prime)

noncomputable def erdosSmoothTail (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter (fun a => ¬ (a = 1 ∨ a.Prime) ∧
    ∀ q ∈ (a / erdosLpf a).primeFactors, (q : ℝ) ≤ Real.log n ^ 20)

-- S1.1.1: p ≤ x ↔ p ≤ ⌊x⌋₊ for x ≥ 0 (Nat.le_floor_iff), so the two prime sets coincide.
namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor_ns

open scoped Classical

open scoped Classical

open Filter

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor :
    ∀ x : ℝ, 0 ≤ x → erdosPiReal x = Nat.primeCounting ⌊x⌋₊ := by
  intro x hx
  have h : ∀ q : ℕ, (q.Prime ∧ (q : ℝ) ≤ x) ↔
      q ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    intro q
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff, Nat.le_floor_iff hx]
    tauto
  have e : erdosPiReal x = ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card := by
    unfold erdosPiReal
    rw [Nat.card_congr (Equiv.subtypeEquivRight h)]
    exact Nat.card_eq_finsetCard _
  rw [e]
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

end erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor_ns

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor :
    ∀ x : ℝ, 0 ≤ x → erdosPiReal x = Nat.primeCounting ⌊x⌋₊ := by
  exact erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor_ns.erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor

-- OPERATOR-ASSISTED (2026-10-14): in place of the two Rosser–Schoenfeld premises. The pieces need SOME constant
-- in Chebyshev's upper bound, not theirs; 5 follows from Mathlib's `Chebyshev.pi_le_log4_mul_div`. The dyadic
-- bounds box_part needs are proved inside its namespace from the central binomial coefficient (Erdős's proof of
-- Bertrand's postulate, kept quantitative).
theorem erdos_41635_cheb_upper5 :
    ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x := by
  intro x hx
  have h := Chebyshev.pi_le_log4_mul_div hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL' : Real.log x ≠ 0 := hL.ne'
  have hs : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  rw [hs] at h
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlogs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
  rw [hs] at hlogs
  have hlx : Real.log x < 2 * Real.sqrt x := by linarith
  have h1 : Real.sqrt x < 2 * (x / Real.log x) := by
    rw [mul_div_assoc', lt_div_iff₀ hL]
    nlinarith
  have h4 : Real.log 4 < 1.3863 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [e]; have := Real.log_two_lt_d9; linarith
  have h2 : Real.log 4 * x / (Real.log x / 2) = 2 * Real.log 4 * (x / Real.log x) := by
    field_simp
  have h3 : 5 * x / Real.log x = 5 * (x / Real.log x) := by ring
  have hq : 0 < x / Real.log x := div_pos hx0 hL
  rw [h2] at h
  rw [h3]
  have := mul_lt_mul_of_pos_right h4 hq
  linarith

-- S2 bullet 1: |{1} ∪ primes ≤ n| ≤ π(n)+1 < 5 n/log n + 1 ≤ C n loglog n / log n once loglog n ≥ 1.
namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough_ns

open scoped Classical

open scoped Classical

open Filter

private lemma rough_card_le (n : ℕ) : (erdosRough n).card ≤ Nat.primeCounting n + 1 := by
  have hsub : erdosRough n ⊆ insert 1 ((Finset.range (n+1)).filter Nat.Prime) := by
    intro m hm
    simp only [erdosRough, Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    rcases hm with ⟨⟨_, h2⟩, h3 | h3⟩
    · left; exact h3
    · right; exact ⟨by omega, h3⟩
  have hpc : Nat.primeCounting n = ((Finset.range (n+1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  calc (erdosRough n).card ≤ (insert 1 ((Finset.range (n+1)).filter Nat.Prime)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range (n+1)).filter Nat.Prime).card + 1 := Finset.card_insert_le _ _
    _ = Nat.primeCounting n + 1 := by rw [hpc]

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough :
    (∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x) →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((erdosRough n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  intro hcheb
  refine ⟨6, ⌈Real.exp (Real.exp 1)⌉₊, fun n hn => ?_⟩
  have hn' : Real.exp (Real.exp 1) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have he1 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have hee : Real.exp 1 + 1 ≤ Real.exp (Real.exp 1) := Real.add_one_le_exp _
  have h1 : (1:ℝ) < n := by linarith
  have hpi := hcheb n h1
  rw [Nat.floor_natCast] at hpi
  have hcard : ((erdosRough n).card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 1 := by
    exact_mod_cast rough_card_le n
  have hexp : Real.exp 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hn'
    rwa [Real.log_exp] at this
  have hLle : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos (by linarith)
  set L := Real.log (n:ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hLL : 1 ≤ Real.log L := by
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) hexp
  have hu : 1 ≤ (n:ℝ) / L := by
    rw [le_div_iff₀ hLpos]; linarith
  have hgoal : 6 * ((n:ℝ) * Real.log L / L) = 6 * ((n:ℝ) / L) * Real.log L := by ring
  have h126 : 5 * (n:ℝ) / L = 5 * ((n:ℝ) / L) := by ring
  rw [hgoal]
  rw [h126] at hpi
  have hm := mul_le_mul_of_nonneg_left hLL (by linarith : (0:ℝ) ≤ 6 * ((n:ℝ) / L))
  linarith

end erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough_ns

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough :
    (∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x) →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((erdosRough n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  exact erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough_ns.erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough

-- S2 Case E: a/P(a) is y0-smooth with y0 = (log n)^20, ln y0 = O(loglog n); Mertens + Chebyshev for
-- m ≤ √n, Rankin for m > √n.
namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail_ns

open scoped Classical

open scoped Classical

open Filter

def sm41635 (y : ℝ) (m : ℕ) : Prop := ∀ q : ℕ, q ∈ m.primeFactors → (q : ℝ) ≤ y

noncomputable def pr41635 (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

private lemma lpf_spec41635 {a : ℕ} (h1 : 1 < a) : (erdosLpf a).Prime ∧ erdosLpf a ∣ a := by
  have hne : a.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h1
  obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_sup a.primeFactors hne id
  have hq' : erdosLpf a = q := hqe
  rw [hq']
  exact ⟨Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq⟩

private lemma card_primes41635 (k : ℕ) :
    ((Finset.range (k + 1)).filter Nat.Prime).card = Nat.primeCounting k := by
  show _ = Nat.primeCounting' (k + 1)
  rw [← Nat.primesBelow_card_eq_primeCounting']
  rfl

private lemma tail_le_sum41635 (n : ℕ) :
    (erdosSmoothTail n).card ≤
      ∑ m ∈ (Finset.Icc 2 n).filter (sm41635 (Real.log n ^ 20)), Nat.primeCounting (n / m) := by
  set S := (Finset.Icc 2 n).filter (sm41635 (Real.log n ^ 20)) with hS
  have hsub : erdosSmoothTail n ⊆ S.biUnion
      (fun m => ((Finset.range (n / m + 1)).filter Nat.Prime).image (fun P => P * m)) := by
    intro a ha
    unfold erdosSmoothTail at ha
    rw [Finset.mem_filter, Finset.mem_Ioc] at ha
    obtain ⟨⟨ha0, han⟩, hnot, hsm⟩ := ha
    have ha1 : 1 < a := by
      rcases Nat.lt_or_ge 1 a with h | h
      · exact h
      · exfalso; exact hnot (Or.inl (by omega))
    obtain ⟨hP, m, hm⟩ := lpf_spec41635 ha1
    generalize hPdef : erdosLpf a = P at hP hm hsm
    subst hm
    have hP0 : 0 < P := hP.pos
    rw [Nat.mul_div_cancel_left m hP0] at hsm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at ha0
      · exact h
    have hm2 : 2 ≤ m := by
      by_contra h
      have h1' : m = 1 := by omega
      subst h1'
      exact hnot (Or.inr (by simpa using hP))
    have hmn : m ≤ n := by
      have : m ≤ P * m := Nat.le_mul_of_pos_left m hP0
      omega
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [hS, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm2, hmn⟩, fun q hq => hsm q hq⟩
    · rw [Finset.mem_image]
      refine ⟨P, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hP⟩
      have : P ≤ n / m := (Nat.le_div_iff_mul_le hm0).mpr han
      omega
  calc (erdosSmoothTail n).card
      ≤ (S.biUnion (fun m => ((Finset.range (n / m + 1)).filter Nat.Prime).image
          (fun P => P * m))).card := Finset.card_le_card hsub
    _ ≤ ∑ m ∈ S, (((Finset.range (n / m + 1)).filter Nat.Prime).image (fun P => P * m)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ m ∈ S, ((Finset.range (n / m + 1)).filter Nat.Prime).card :=
          Finset.sum_le_sum (fun m _ => Finset.card_image_le)
    _ = ∑ m ∈ S, Nat.primeCounting (n / m) :=
          Finset.sum_congr rfl (fun m _ => card_primes41635 (n / m))

private lemma term41635
    (hπ : ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Nat.primeCounting (n / m) : ℝ) ≤ 10 * n / Real.log n * ((m : ℝ) ^ (1 : ℝ))⁻¹
      + n * ((n : ℝ) ^ (δ / 2))⁻¹ * ((m : ℝ) ^ (1 - δ))⁻¹ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hfl : ⌊(n : ℝ) / m⌋₊ = n / m := Nat.floor_div_eq_div n m
  rcases le_or_gt (m * m) n with hmm | hmm
  · -- small m: use the Chebyshev hypothesis
    have hk : m ≤ n / m := (Nat.le_div_iff_mul_le (by omega)).mpr hmm
    have hx2 : (2 : ℝ) ≤ (n : ℝ) / m := by
      have : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
      have : (2 : ℝ) ≤ ((n / m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n / m by omega)
      linarith
    have h := hπ ((n : ℝ) / m) (by linarith)
    rw [hfl] at h
    have hsq : (n : ℝ) ≤ ((n : ℝ) / m) ^ 2 := by
      have hmm' : (m : ℝ) * m ≤ n := by exact_mod_cast hmm
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith
    have hlogx : Real.log n / 2 ≤ Real.log ((n : ℝ) / m) := by
      have := Real.log_le_log hn0 hsq
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hlogx0 : 0 < Real.log ((n : ℝ) / m) := by linarith
    have h1 : 5 * ((n : ℝ) / m) / Real.log ((n : ℝ) / m) ≤
        10 * n / Real.log n * ((m : ℝ) ^ (1 : ℝ))⁻¹ := by
      rw [Real.rpow_one, div_le_iff₀ hlogx0]
      have : 10 * (n : ℝ) / Real.log n * (m : ℝ)⁻¹ * Real.log ((n : ℝ) / m)
          = 5 * ((n : ℝ) / m) * (2 * Real.log ((n : ℝ) / m) / Real.log n) := by
        field_simp
        ring
      rw [this]
      have h2 : 1 ≤ 2 * Real.log ((n : ℝ) / m) / Real.log n := by
        rw [le_div_iff₀ hlogn]; linarith
      have : 0 ≤ 5 * ((n : ℝ) / m) := by positivity
      nlinarith
    have h2 : 0 ≤ (n : ℝ) * ((n : ℝ) ^ (δ / 2))⁻¹ * ((m : ℝ) ^ (1 - δ))⁻¹ := by positivity
    linarith
  · -- large m: trivial bound and Rankin's trick
    have hle : Nat.primeCounting (n / m) ≤ n / m := by
      rw [← card_primes41635]
      calc ((Finset.range (n / m + 1)).filter Nat.Prime).card ≤ (Finset.Icc 1 (n / m)).card := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter, Finset.mem_range] at hp
            rw [Finset.mem_Icc]
            have := hp.2.two_le
            omega
        _ = n / m := by rw [Nat.card_Icc]; omega
    have h1 : (Nat.primeCounting (n / m) : ℝ) ≤ (n : ℝ) / m :=
      le_trans (by exact_mod_cast hle) Nat.cast_div_le
    have hmm' : (n : ℝ) < (m : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; exact_mod_cast (show n < m ^ 2 by rw [sq]; exact hmm)
    have hrk : (n : ℝ) ^ (δ / 2) ≤ (m : ℝ) ^ δ := by
      calc (n : ℝ) ^ (δ / 2) ≤ ((m : ℝ) ^ (2 : ℝ)) ^ (δ / 2) :=
            Real.rpow_le_rpow hn0.le hmm'.le (by linarith)
        _ = (m : ℝ) ^ δ := by rw [← Real.rpow_mul hm0.le]; ring_nf
    have hsplit : (m : ℝ) = (m : ℝ) ^ δ * (m : ℝ) ^ (1 - δ) := by
      rw [← Real.rpow_add hm0]; simp
    have hpos1 : 0 < (n : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos hn0 _
    have hpos2 : 0 < (m : ℝ) ^ (1 - δ) := Real.rpow_pos_of_pos hm0 _
    have h2 : (n : ℝ) / m ≤ n * ((n : ℝ) ^ (δ / 2))⁻¹ * ((m : ℝ) ^ (1 - δ))⁻¹ := by
      rw [mul_assoc, ← mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hn0.le
      apply inv_anti₀ (by positivity)
      calc (n : ℝ) ^ (δ / 2) * (m : ℝ) ^ (1 - δ) ≤ (m : ℝ) ^ δ * (m : ℝ) ^ (1 - δ) :=
            mul_le_mul_of_nonneg_right hrk hpos2.le
        _ = m := hsplit.symm
    have h3 : 0 ≤ 10 * n / Real.log n * ((m : ℝ) ^ (1 : ℝ))⁻¹ := by positivity
    linarith

private lemma eulerK41635 (s : ℝ) (hs : 0 < s) (K : ℕ) : ∀ T : Finset ℕ,
    (∀ m ∈ T, 0 < m ∧ ∀ q ∈ m.primeFactors, q < K) →
    ∑ m ∈ T, ((m : ℝ) ^ s)⁻¹ ≤ ∏ p ∈ (Finset.range K).filter Nat.Prime, (1 - ((p : ℝ) ^ s)⁻¹)⁻¹ := by
  induction K with
  | zero =>
    intro T hT
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    have hsub : T ⊆ {1} := by
      intro m hm
      obtain ⟨hm0, hq⟩ := hT m hm
      rw [Finset.mem_singleton]
      by_contra h1
      obtain ⟨q, hq'⟩ := Nat.nonempty_primeFactors.mpr (show 1 < m by omega)
      have := hq q hq'
      omega
    calc ∑ m ∈ T, ((m : ℝ) ^ s)⁻¹ ≤ ∑ m ∈ ({1} : Finset ℕ), ((m : ℝ) ^ s)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | succ K ih =>
    intro T hT
    by_cases hK : K.Prime
    · set p := K with hpK
      have hp1 : (1 : ℝ) < (p : ℝ) ^ s :=
        Real.one_lt_rpow (by exact_mod_cast hK.one_lt) hs
      set r := ((p : ℝ) ^ s)⁻¹ with hr
      have hr0 : 0 < r := by positivity
      have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hp1
      rw [Finset.range_add_one, Finset.filter_insert, if_pos hK,
        Finset.prod_insert (by simp)]
      set T' := T.image (fun m => m / p ^ m.factorization p) with hT'
      set V := T.sup (fun m => m.factorization p) with hV
      have hT'K : ∀ m ∈ T', 0 < m ∧ ∀ q ∈ m.primeFactors, q < K := by
        intro m' hm'
        rw [hT', Finset.mem_image] at hm'
        obtain ⟨m, hm, rfl⟩ := hm'
        obtain ⟨hm0, hq⟩ := hT m hm
        refine ⟨Nat.ordCompl_pos p (by omega), fun q hq' => ?_⟩
        have hqd : q ∣ m / p ^ m.factorization p := Nat.dvd_of_mem_primeFactors hq'
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq'
        have hqm : q ∣ m := hqd.trans (Nat.ordCompl_dvd m p)
        have := hq q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, by omega⟩)
        rcases Nat.lt_or_ge q K with h | h
        · exact h
        · exfalso
          have hqK : q = K := by omega
          rw [hqK] at hqd
          exact Nat.not_dvd_ordCompl hK (by omega) hqd
      have ih' := ih T' hT'K
      have hinj : Set.InjOn (fun m => (m.factorization p, m / p ^ m.factorization p)) T := by
        intro a _ b _ hab
        simp only [Prod.mk.injEq] at hab
        obtain ⟨h1, h2⟩ := hab
        calc a = p ^ a.factorization p * (a / p ^ a.factorization p) :=
              (Nat.ordProj_mul_ordCompl_eq_self a p).symm
          _ = p ^ b.factorization p * (b / p ^ b.factorization p) := by rw [h2, h1]
          _ = b := Nat.ordProj_mul_ordCompl_eq_self b p
      have hmul : ∀ m ∈ T, ((m : ℝ) ^ s)⁻¹ =
          r ^ (m.factorization p) * (((m / p ^ m.factorization p : ℕ) : ℝ) ^ s)⁻¹ := by
        intro m _
        conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), mul_inv, Nat.cast_pow,
          hr, inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_mul (by positivity), mul_comm s]
      calc ∑ m ∈ T, ((m : ℝ) ^ s)⁻¹
          = ∑ m ∈ T, r ^ (m.factorization p) * (((m / p ^ m.factorization p : ℕ) : ℝ) ^ s)⁻¹ :=
            Finset.sum_congr rfl hmul
        _ = ∑ x ∈ T.image (fun m => (m.factorization p, m / p ^ m.factorization p)),
              r ^ (x : ℕ × ℕ).1 * (((x.2 : ℕ) : ℝ) ^ s)⁻¹ :=
            (Finset.sum_image (f := fun x : ℕ × ℕ => r ^ x.1 * (((x.2 : ℕ) : ℝ) ^ s)⁻¹) hinj).symm
        _ ≤ ∑ x ∈ Finset.range (V + 1) ×ˢ T',
              r ^ (x : ℕ × ℕ).1 * (((x.2 : ℕ) : ℝ) ^ s)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_image] at hx
              obtain ⟨m, hm, rfl⟩ := hx
              rw [Finset.mem_product, Finset.mem_range, hT']
              refine ⟨Nat.lt_succ_of_le (Finset.le_sup (f := fun m => m.factorization p) hm),
                Finset.mem_image_of_mem _ hm⟩
            · intro _ _ _; positivity
        _ = (∑ e ∈ Finset.range (V + 1), r ^ e) * ∑ m ∈ T', ((m : ℝ) ^ s)⁻¹ := by
            rw [Finset.sum_product, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun e _ => ?_)
            rw [Finset.mul_sum]
        _ ≤ (1 - r)⁻¹ * ∏ p ∈ (Finset.range K).filter Nat.Prime, (1 - ((p : ℝ) ^ s)⁻¹)⁻¹ := by
            apply mul_le_mul _ ih' (Finset.sum_nonneg (fun _ _ => by positivity))
              (by have : 0 < 1 - r := by linarith
                  positivity)
            rw [geom_sum_eq hr1.ne, div_le_iff_of_neg (by linarith)]
            have h0 : (1 - r) ≠ 0 := by linarith
            have : (1 - r)⁻¹ * (r - 1) = -1 := by field_simp; ring
            have : 0 ≤ r ^ (V + 1) := by positivity
            linarith
    · rw [Finset.range_add_one, Finset.filter_insert, if_neg hK]
      apply ih T
      intro m hm
      obtain ⟨hm0, hq⟩ := hT m hm
      refine ⟨hm0, fun q hq' => ?_⟩
      have := hq q hq'
      rcases Nat.lt_or_ge q K with h | h
      · exact h
      · exfalso
        have hqK : q = K := by omega
        exact hK (hqK ▸ Nat.prime_of_mem_primeFactors hq')

private lemma euler41635 (y s : ℝ) (hs : 0 < s) (T : Finset ℕ)
    (hT : ∀ m ∈ T, 0 < m ∧ sm41635 y m) :
    ∑ m ∈ T, ((m : ℝ) ^ s)⁻¹ ≤ ∏ p ∈ pr41635 y, (1 - ((p : ℝ) ^ s)⁻¹)⁻¹ := by
  apply eulerK41635 s hs (⌊y⌋₊ + 1) T
  intro m hm
  obtain ⟨hm0, hq⟩ := hT m hm
  exact ⟨hm0, fun q hq' => Nat.lt_succ_of_le (Nat.le_floor (hq q hq'))⟩

private lemma theta41635 (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ≤ N * Real.log 4 := by
  rw [← Real.log_prod (fun p hp => by
    have := (Finset.mem_filter.mp hp).2.pos
    positivity)]
  have h := primorial_le_four_pow N
  unfold primorial at h
  rw [← Real.log_pow]
  apply Real.log_le_log (Finset.prod_pos (fun p hp => by
    have := (Finset.mem_filter.mp hp).2.pos
    positivity))
  rw [← Nat.cast_prod]
  exact_mod_cast h

private lemma mertens1_41635 (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.range_one, Finset.filter_singleton, if_neg Nat.not_prime_zero]
    simp only [Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p
      = ∑ k ∈ Finset.Ioc 0 N, ∑ p ∈ k.primeFactors, Real.log p := by
    rw [Finset.sum_comm' (t' := P) (s' := fun p => (Finset.Ioc 0 N).filter (p ∣ ·))]
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    · intro k p
      rw [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primeFactors, hP, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨⟨hk0, hkN⟩, hp, hpk, _⟩
        have := Nat.le_of_dvd hk0 hpk
        exact ⟨⟨⟨hk0, hkN⟩, hpk⟩, by omega, hp⟩
      · rintro ⟨⟨⟨hk0, hkN⟩, hpk⟩, _, hp⟩
        exact ⟨⟨hk0, hkN⟩, hp, hpk, by omega⟩
  have h2 : ∑ k ∈ Finset.Ioc 0 N, ∑ p ∈ k.primeFactors, Real.log p ≤ N * Real.log N := by
    calc ∑ k ∈ Finset.Ioc 0 N, ∑ p ∈ k.primeFactors, Real.log p
        ≤ ∑ k ∈ Finset.Ioc 0 N, Real.log N := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Ioc] at hk
          rw [← Real.log_prod (fun p hp => by
            have := (Nat.prime_of_mem_primeFactors hp).pos
            positivity)]
          have hpos : 0 < ∏ p ∈ k.primeFactors, (p : ℝ) := Finset.prod_pos (fun p hp => by
            have := (Nat.prime_of_mem_primeFactors hp).pos
            positivity)
          apply Real.log_le_log hpos
          have := Nat.le_of_dvd hk.1 (Nat.prod_primeFactors_dvd k)
          have : ∏ p ∈ k.primeFactors, p ≤ N := le_trans this hk.2
          rw [← Nat.cast_prod]
          exact_mod_cast this
      _ = N * Real.log N := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp
  have h3 : ∀ p ∈ P, (N : ℝ) * (Real.log p / p) ≤ ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlt : N < p * (N / p + 1) := by
      have := Nat.div_add_mod N p
      have := Nat.mod_lt N hpp.pos
      nlinarith
    have hlt' : (N : ℝ) ≤ p * ((N / p : ℕ) + 1) := by exact_mod_cast hlt.le
    have : (N : ℝ) * (Real.log p / p) = (N / p) * Real.log p := by ring
    rw [this]
    have : (N : ℝ) / p ≤ (N / p : ℕ) + 1 := by rw [div_le_iff₀ hp0]; linarith
    nlinarith
  have h4 := theta41635 N
  have h5 : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * Real.log N + N * Real.log 4 := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ P, (((N / p : ℕ) : ℝ) * Real.log p + Real.log p) := Finset.sum_le_sum h3
      _ = ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ N * Real.log N + N * Real.log 4 := by rw [h1]; linarith
  have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left this hNr

private lemma one_sub_le_log41635 {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at this
  linarith

private lemma mertens2_41635 : ∀ K : ℕ, 2 ≤ K →
    ∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, 1 / (p : ℝ)
      - (∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, Real.log p / p) / Real.log K
      - Real.log (Real.log K) + Real.log 4 / Real.log K
    ≤ ∑ p ∈ (Finset.range (2 + 1)).filter Nat.Prime, 1 / (p : ℝ)
      - (∑ p ∈ (Finset.range (2 + 1)).filter Nat.Prime, Real.log p / p) / Real.log 2
      - Real.log (Real.log 2) + Real.log 4 / Real.log 2 := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => exact le_refl _
  | succ K hK ih =>
    refine le_trans ?_ ih
    set S := ∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, 1 / (p : ℝ) with hS
    set A := ∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, Real.log p / p with hA
    have hA' := mertens1_41635 K
    rw [← hA] at hA'
    have hK0 : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hlK : 0 < Real.log K := Real.log_pos (by linarith)
    have hlt : Real.log K < Real.log ((K + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by linarith) (by push_cast; linarith)
    set l1 := Real.log ((K + 1 : ℕ) : ℝ) with hl1
    set l0 := Real.log (K : ℝ) with hl0
    have hl1p : 0 < l1 := by linarith
    -- the new sums
    have hnew : ∑ p ∈ (Finset.range (K + 1 + 1)).filter Nat.Prime, 1 / (p : ℝ)
        - (∑ p ∈ (Finset.range (K + 1 + 1)).filter Nat.Prime, Real.log p / p) / l1
        = S - A / l1 := by
      rw [Finset.range_add_one (n := K + 1), Finset.filter_insert]
      split_ifs with hp
      · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), ← hS, ← hA]
        have : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
        field_simp
        ring
      · rw [← hS, ← hA]
    rw [hnew]
    -- key inequality
    have hlog : 1 - l0 / l1 ≤ Real.log l1 - Real.log l0 := by
      rw [← Real.log_div hl1p.ne' hlK.ne']
      have := one_sub_le_log41635 (show 0 < l1 / l0 by positivity)
      rw [inv_div] at this
      exact this
    have hd : 0 ≤ 1 / l0 - 1 / l1 := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hlK hlt.le
    have hAb : A * (1 / l0 - 1 / l1) ≤ (l0 + Real.log 4) * (1 / l0 - 1 / l1) :=
      mul_le_mul_of_nonneg_right hA' hd
    have e1 : (l0 + Real.log 4) * (1 / l0 - 1 / l1)
        = (1 - l0 / l1) + Real.log 4 * (1 / l0 - 1 / l1) := by
      field_simp
    have e2 : A * (1 / l0 - 1 / l1) = A / l0 - A / l1 := by ring
    have e3 : Real.log 4 * (1 / l0 - 1 / l1) = Real.log 4 / l0 - Real.log 4 / l1 := by ring
    linarith

private lemma mertens41635 : ∃ C : ℝ, ∀ y : ℝ, 3 ≤ y →
    ∑ p ∈ pr41635 y, (1 / (p : ℝ)) ≤ Real.log (Real.log y) + C := by
  set G := ∑ p ∈ (Finset.range (2 + 1)).filter Nat.Prime, 1 / (p : ℝ)
      - (∑ p ∈ (Finset.range (2 + 1)).filter Nat.Prime, Real.log p / p) / Real.log 2
      - Real.log (Real.log 2) + Real.log 4 / Real.log 2 with hG
  refine ⟨1 + G, fun y hy => ?_⟩
  set K := ⌊y⌋₊ with hKdef
  have hK3 : 3 ≤ K := Nat.le_floor (by exact_mod_cast hy)
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hK0 : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hlK : 0 < Real.log K := Real.log_pos (by linarith)
  have h := mertens2_41635 K (by omega)
  rw [← hG] at h
  have hA := mertens1_41635 K
  have hll : Real.log (Real.log K) ≤ Real.log (Real.log y) :=
    Real.log_le_log hlK (Real.log_le_log (by linarith) hKy)
  have hdiv : (∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, Real.log p / p) / Real.log K
      ≤ 1 + Real.log 4 / Real.log K := by
    rw [div_le_iff₀ hlK, add_mul, div_mul_cancel₀ _ hlK.ne']
    linarith
  unfold pr41635
  rw [← hKdef]
  linarith

private lemma sq_sum41635 (K : ℕ) :
    ∑ p ∈ (Finset.range (K + 1)).filter Nat.Prime, (1 / (p : ℝ)) ^ 2 ≤ 2 - 2 / ((K : ℝ) + 1) := by
  induction K with
  | zero =>
    rw [Finset.range_one, Finset.filter_singleton, if_neg Nat.not_prime_zero]
    simp
  | succ K ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hK
    · rw [Finset.sum_insert (by simp)]
      have hK1 : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast (show 1 ≤ K + 1 by omega)
      have : (1 / ((K + 1 : ℕ) : ℝ)) ^ 2 ≤ 2 / (K + 1) - 2 / ((K + 1 : ℕ) + 1) := by
        push_cast at hK1 ⊢
        rw [div_pow, div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at this ⊢
      linarith
    · push_cast
      have : (2 : ℝ) / (K + 1 + 1) ≤ 2 / (K + 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      linarith

private lemma mem_pr41635 {y : ℝ} {p : ℕ} (hp : p ∈ pr41635 y) : p.Prime ∧ (p : ℝ) ≤ y := by
  rw [pr41635, Finset.mem_filter, Finset.mem_range] at hp
  refine ⟨hp.2, ?_⟩
  have h0 : 0 ≤ y := by
    by_contra h
    rw [Nat.floor_of_nonpos (by linarith)] at hp
    have := hp.2.two_le
    omega
  exact (Nat.le_floor_iff h0).mp (by omega)

private lemma prod_one41635 : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 8 ≤ y →
    ∏ p ∈ pr41635 y, (1 - ((p : ℝ) ^ (1 : ℝ))⁻¹)⁻¹ ≤ C * Real.log y := by
  obtain ⟨C, hC⟩ := mertens41635
  refine ⟨Real.exp (C + 4), Real.exp_pos _, fun y hy => ?_⟩
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have h1 : ∀ p ∈ pr41635 y, (1 - ((p : ℝ) ^ (1 : ℝ))⁻¹)⁻¹ ≤
      Real.exp (1 / (p : ℝ) + 2 * (1 / (p : ℝ)) ^ 2) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_pr41635 hp).1.two_le
    rw [Real.rpow_one]
    set t := 1 / (p : ℝ) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 2 := by rw [ht]; exact one_div_le_one_div_of_le (by norm_num) h2
    have hinv : (p : ℝ)⁻¹ = t := by rw [ht, one_div]
    rw [hinv]
    refine le_trans ?_ (Real.add_one_le_exp _)
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith [mul_pos ht0 ht0]
  have h2 := Finset.prod_le_prod (fun p _ => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_pr41635 ‹_›).1.two_le
      have : ((p : ℝ) ^ (1 : ℝ))⁻¹ < 1 := by
        rw [Real.rpow_one]; exact inv_lt_one_of_one_lt₀ (by linarith)
      exact (inv_pos.mpr (by linarith)).le) h1
  refine h2.trans ?_
  rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h3 := hC y (by linarith)
  have h4 := sq_sum41635 ⌊y⌋₊
  have h5 : (0 : ℝ) ≤ 2 / (⌊y⌋₊ + 1) := by positivity
  unfold pr41635 at h3 ⊢
  calc Real.exp (∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, 1 / (p : ℝ) +
        2 * ∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 / (p : ℝ)) ^ 2)
      ≤ Real.exp (Real.log (Real.log y) + (C + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (C + 4) * Real.log y := by
      rw [Real.exp_add, Real.exp_log hlog, mul_comm]

private lemma prod_delta41635 : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 8 ≤ y →
    ∏ p ∈ pr41635 y, (1 - ((p : ℝ) ^ (1 - 1 / Real.log y))⁻¹)⁻¹ ≤ C * Real.log y ^ 11 := by
  obtain ⟨C, hC⟩ := mertens41635
  refine ⟨Real.exp (11 * C), Real.exp_pos _, fun y hy => ?_⟩
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have he1 := Real.exp_one_lt_d9
  have hlog2 : 2 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  set δ := 1 / Real.log y with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by rw [hδ]; exact one_div_le_one_div_of_le (by norm_num) hlog2
  have hsqrt2 : (4 / 3 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h1 : ∀ p ∈ pr41635 y, (1 - ((p : ℝ) ^ (1 - δ))⁻¹)⁻¹ ≤ Real.exp (11 * (1 / (p : ℝ))) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_pr41635 hp).1.two_le
    have hpy : (p : ℝ) ≤ y := (mem_pr41635 hp).2
    have hp0 : (0 : ℝ) < p := by linarith
    set t := ((p : ℝ) ^ (1 - δ))⁻¹ with ht
    have ht0 : 0 < t := by positivity
    -- t ≤ 3/4
    have hge : Real.sqrt 2 ≤ (p : ℝ) ^ (1 - δ) := by
      rw [Real.sqrt_eq_rpow]
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
        _ ≤ (p : ℝ) ^ (1 - δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have ht34 : t ≤ 3 / 4 := by
      rw [ht]
      calc ((p : ℝ) ^ (1 - δ))⁻¹ ≤ (4 / 3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
        _ = 3 / 4 := by norm_num
    -- t ≤ e / p
    have hpd : (p : ℝ) ^ δ ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp0]
      apply Real.exp_le_exp.mpr
      rw [hδ, mul_one_div, div_le_one hlog]
      exact Real.log_le_log hp0 hpy
    have hte : t ≤ Real.exp 1 / p := by
      rw [ht, Real.rpow_sub hp0, Real.rpow_one, inv_div]
      exact div_le_div_of_nonneg_right hpd hp0.le
    have h11 : 4 * t ≤ 11 * (1 / (p : ℝ)) := by
      have : 4 * (Real.exp 1 / p) ≤ 11 * (1 / (p : ℝ)) := by
        rw [mul_one_div, mul_div_assoc']
        exact div_le_div_of_nonneg_right (by linarith) hp0.le
      linarith
    refine le_trans ?_ (Real.exp_le_exp.mpr h11)
    refine le_trans ?_ (Real.add_one_le_exp _)
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  have h2 := Finset.prod_le_prod (fun p hp => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_pr41635 hp).1.two_le
      have : (1 : ℝ) < (p : ℝ) ^ (1 - δ) := Real.one_lt_rpow (by linarith) (by linarith)
      have : ((p : ℝ) ^ (1 - δ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
      exact (inv_pos.mpr (by linarith)).le) h1
  refine h2.trans ?_
  rw [← Real.exp_sum, ← Finset.mul_sum]
  have h3 := hC y (by linarith)
  calc Real.exp (11 * ∑ p ∈ pr41635 y, 1 / (p : ℝ))
      ≤ Real.exp (11 * Real.log (Real.log y) + 11 * C) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (11 * C) * Real.log y ^ 11 := by
      rw [Real.exp_add, show 11 * Real.log (Real.log y) = Real.log (Real.log y ^ 11) by
        rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
      ring

private lemma asymp41635 (K : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (n : ℝ) * ((n : ℝ) ^ ((1 / Real.log (Real.log n ^ 20)) / 2))⁻¹
      * (K * Real.log (Real.log n ^ 20) ^ 11) ≤ (n : ℝ) * Real.log (Real.log n) / Real.log n := by
  set K' := max K 1 with hK'
  have hK1 : 1 ≤ K' := le_max_right _ _
  have hKK : K ≤ K' := le_max_left _ _
  set A : ℝ := 3200 * K' * 20 ^ 11 with hA
  have hA0 : 0 < A := by positivity
  have hf0 : (0 : ℝ) < (Nat.factorial 13 : ℝ) := by exact_mod_cast Nat.factorial_pos 13
  set T0 : ℝ := A * (Nat.factorial 13 : ℝ) + 1 with hT0
  refine ⟨⌈Real.exp (Real.exp T0)⌉₊, fun n hn => ?_⟩
  have hnr : Real.exp (Real.exp T0) ≤ n := (Nat.ceil_le).mp hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hnr
  set L := Real.log n with hLdef
  have hL : Real.exp T0 ≤ L := by rw [hLdef, Real.le_log_iff_exp_le hn0]; exact hnr
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  set t := Real.log L with htdef
  have ht : T0 ≤ t := by rw [htdef, Real.le_log_iff_exp_le hL0]; exact hL
  have hT0pos : 1 ≤ T0 := by rw [hT0]; have := mul_pos hA0 hf0; linarith
  have ht0 : 0 < t := by linarith
  have hLt : Real.exp t = L := Real.exp_log hL0
  have hlog20 : Real.log (L ^ 20) = 20 * t := by rw [Real.log_pow, htdef]; norm_num
  rw [hlog20]
  set u := L / (40 * t) with hu
  have hpow : (n : ℝ) ^ (1 / (20 * t) / 2) = Real.exp u := by
    rw [Real.rpow_def_of_pos hn0, hu, ← hLdef]; congr 1; field_simp; ring
  rw [hpow]
  have hu0 : 0 ≤ u := by positivity
  have hexpu : u ^ 2 / 2 ≤ Real.exp u := by
    have := Real.pow_div_factorial_le_exp u hu0 2
    simpa [Nat.factorial] using this
  have hexpt : t ^ 13 / (Nat.factorial 13 : ℝ) ≤ L :=
    hLt ▸ Real.pow_div_factorial_le_exp t ht0.le 13
  have htA : A ≤ t / (Nat.factorial 13 : ℝ) := by
    rw [le_div_iff₀ hf0]; linarith
  have hLA : t ^ 12 * A ≤ L := by
    have : t ^ 13 / (Nat.factorial 13 : ℝ) = t ^ 12 * (t / (Nat.factorial 13 : ℝ)) := by ring
    have h12 : 0 ≤ t ^ 12 := by positivity
    nlinarith
  -- key inequality
  have hkey : K' * (20 * t) ^ 11 * L ≤ t * Real.exp u := by
    have h1 : t * (u ^ 2 / 2) = L * L / (3200 * t) := by rw [hu]; field_simp; try ring
    have h2 : K' * (20 * t) ^ 11 * L = L * (t ^ 12 * A) / (3200 * t) := by
      rw [hA]; field_simp; try ring
    have h3 : L * (t ^ 12 * A) / (3200 * t) ≤ L * L / (3200 * t) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hLA hL0.le
    have h4 : t * (u ^ 2 / 2) ≤ t * Real.exp u := mul_le_mul_of_nonneg_left hexpu ht0.le
    linarith
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hP : 0 ≤ (20 * t) ^ 11 := by positivity
  calc (n : ℝ) * (Real.exp u)⁻¹ * (K * (20 * t) ^ 11)
      ≤ (n : ℝ) * (Real.exp u)⁻¹ * (K' * (20 * t) ^ 11) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hKK hP
    _ ≤ (n : ℝ) * t / L := by
        rw [div_eq_mul_inv, mul_assoc, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hn0.le
        rw [inv_mul_le_iff₀ hE, ← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hL0]
        linarith

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail :
    (∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x) →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((erdosSmoothTail n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  intro hπ
  obtain ⟨C1, hC1, hP1⟩ := prod_one41635
  obtain ⟨C2, hC2, hP2⟩ := prod_delta41635
  obtain ⟨N0, hN0⟩ := asymp41635 C2
  refine ⟨200 * C1 + 1, max N0 16, fun n hn => ?_⟩
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  set L := Real.log n with hL
  set y := L ^ 20 with hy
  have he1 := Real.exp_one_lt_d9
  have hL2 : 2 < L := by
    rw [hL]
    have : Real.exp 2 < 16 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hy8 : 8 ≤ y := by
    rw [hy]
    have : (2:ℝ) ^ 20 ≤ L ^ 20 := pow_le_pow_left₀ (by norm_num) hL2.le 20
    linarith
  have hlogy : Real.log y = 20 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set δ := 1 / Real.log y with hδ
  have hδ0 : 0 < δ := by rw [hδ, hlogy]; positivity
  have hδ1 : δ < 1 := by
    rw [hδ, hlogy, div_lt_one (by positivity)]
    have : (1 / 2 : ℝ) < Real.log L := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    linarith
  set S := (Finset.Icc 2 n).filter (sm41635 y) with hS
  have hSm : ∀ m ∈ S, 2 ≤ m ∧ sm41635 y m := by
    intro m hm
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨hm.1.1, hm.2⟩
  have hT : ∀ m ∈ S, 0 < m ∧ sm41635 y m := fun m hm =>
    ⟨by have := (hSm m hm).1; omega, (hSm m hm).2⟩
  have h1 : ((erdosSmoothTail n).card : ℝ) ≤ ∑ m ∈ S, (Nat.primeCounting (n / m) : ℝ) := by
    have := tail_le_sum41635 n
    exact_mod_cast this
  have hn4 : 4 ≤ n := by have := le_of_max_le_right hn; omega
  have h2 : ∑ m ∈ S, (Nat.primeCounting (n / m) : ℝ) ≤
      10 * n / L * ∑ m ∈ S, ((m : ℝ) ^ (1 : ℝ))⁻¹
        + n * ((n : ℝ) ^ (δ / 2))⁻¹ * ∑ m ∈ S, ((m : ℝ) ^ (1 - δ))⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun m hm => term41635 hπ n m hn4 (hSm m hm).1 δ hδ0 hδ1)
  have h3 := euler41635 y 1 one_pos S hT
  have h4 := euler41635 y (1 - δ) (by linarith) S hT
  have h3' := hP1 y hy8
  have h4' := hP2 y hy8
  have h5 := hN0 n (le_of_max_le_left hn)
  have hA : 0 ≤ 10 * (n : ℝ) / L := by positivity
  have hB : 0 ≤ (n : ℝ) * ((n : ℝ) ^ (δ / 2))⁻¹ := by positivity
  have hfin : ((erdosSmoothTail n).card : ℝ) ≤
      10 * n / L * (C1 * Real.log y) + n * ((n : ℝ) ^ (δ / 2))⁻¹ * (C2 * Real.log y ^ 11) := by
    refine h1.trans (h2.trans (add_le_add ?_ ?_))
    · exact mul_le_mul_of_nonneg_left (h3.trans h3') hA
    · exact mul_le_mul_of_nonneg_left (h4.trans h4') hB
  have h5' : (n : ℝ) * ((n : ℝ) ^ (δ / 2))⁻¹ * (C2 * Real.log y ^ 11) ≤
      n * Real.log L / L := h5
  refine hfin.trans ?_
  rw [hlogy]
  have hL0 : 0 < L := by linarith
  have : 10 * (n : ℝ) / L * (C1 * (20 * Real.log L)) = 200 * C1 * (n * Real.log L / L) := by
    field_simp; ring
  rw [this]
  rw [hlogy] at h5'
  nlinarith [h5']

end erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail_ns

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail :
    (∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x) →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((erdosSmoothTail n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  exact erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail_ns.erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail

-- S2 Cases G and S: a outside rough ∪ smooth tail has q = P(a/P(a)) > (log n)^20 ≥ y0, so the box
-- Z_{l,j}×Q_j×P_k has |Q_j|,|P_k| ≥ T and (j<l → |Z| ≥ T); box sparsity gives |T_B| ≤ (3/m_B)^{1/8}|B|,
-- and the mass sums give O(n loglog n/log n). Uses Chebyshev upper/lower bounds (F3).
namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part_ns

open scoped Classical

open scoped Classical

open Filter

private def dyX (l : ℕ) : Finset ℕ := Finset.Ico (2 ^ l) (2 ^ (l + 1))

/-- Primes in the dyadic block `[2^j, 2^(j+1))`. -/

private def dyQ (j : ℕ) : Finset ℕ := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime

/-- Box indices `(l, j, k)` with `l + j + k ≤ log₂ n`, `j ≤ k`, `2^(j+1) > (log n)^20`. -/

private noncomputable def boxIdx (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (Nat.log 2 n + 1) ×ˢ (Finset.range (Nat.log 2 n + 1) ×ˢ
    Finset.range (Nat.log 2 n + 1))).filter
    (fun t => t.1 + t.2.1 + t.2.2 ≤ Nat.log 2 n ∧ t.2.1 ≤ t.2.2 ∧
      Real.log n ^ 20 < (2 : ℝ) ^ (t.2.1 + 1))

/-- The box-sparse bound on the number of triples in a box with side sizes `x, y, z`. -/

private noncomputable def boxW (x y z : ℕ) : ℝ :=
  (((x * y ^ 2 * z ^ 2 + x ^ 2 * y * z ^ 2 + x ^ 2 * y ^ 2 * z) * (x * y * z) ^ 6 : ℕ) : ℝ)
    ^ ((8 : ℝ)⁻¹)

/-- `rr = 2^(-1/8)`. -/

private noncomputable def rr : ℝ := ((1 : ℝ) / 2) ^ ((8 : ℝ)⁻¹)

private lemma rr_pos : 0 < rr := by unfold rr; positivity

private lemma rr_pow8 : rr ^ 8 = 1 / 2 := by
  unfold rr
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma rr_lt_one : rr < 1 := by
  unfold rr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

private lemma boxW_split (l y z : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hy : 0 < y) (hz : 0 < z)
    (hyz : (1 : ℝ) / y + 1 / z ≤ δ ^ 8) :
    boxW (2 ^ l) y z ≤ (rr ^ l + δ) * ((2 : ℝ) ^ l * y * z) := by
  unfold boxW
  have hx : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  have hr0 := rr_pos
  have hB0 : 0 ≤ (rr ^ l + δ) * ((2 : ℝ) ^ l * y * z) := by positivity
  have hS : ((((2 ^ l) * y ^ 2 * z ^ 2 + (2 ^ l) ^ 2 * y * z ^ 2 + (2 ^ l) ^ 2 * y ^ 2 * z) *
      ((2 ^ l) * y * z) ^ 6 : ℕ) : ℝ) ≤ ((rr ^ l + δ) * ((2 : ℝ) ^ l * y * z)) ^ 8 := by
    have h8 : (rr ^ l) ^ 8 + δ ^ 8 ≤ (rr ^ l + δ) ^ 8 :=
      pow_add_pow_le (by positivity) hδ (by norm_num)
    have hr : (rr ^ l) ^ 8 = 1 / (2 : ℝ) ^ l := by
      rw [← pow_mul, mul_comm, pow_mul, rr_pow8, one_div_pow]
    have heq : ((((2 ^ l) * y ^ 2 * z ^ 2 + (2 ^ l) ^ 2 * y * z ^ 2 + (2 ^ l) ^ 2 * y ^ 2 * z) *
        ((2 ^ l) * y * z) ^ 6 : ℕ) : ℝ)
        = (1 / (2 : ℝ) ^ l + (1 / y + 1 / z)) * ((2 : ℝ) ^ l * y * z) ^ 8 := by
      push_cast
      field_simp
      ring
    rw [heq, mul_pow (rr ^ l + δ)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← hr]
    linarith
  calc _ ≤ (((rr ^ l + δ) * ((2 : ℝ) ^ l * y * z)) ^ 8) ^ ((8 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hS (by norm_num)
    _ = (rr ^ l + δ) * ((2 : ℝ) ^ l * y * z) := by
        rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num]
        exact Real.pow_rpow_inv_natCast hB0 (by norm_num)

private lemma card_dyQ_le_primeCounting (j : ℕ) :
    (dyQ j).card ≤ Nat.primeCounting (2 ^ (j + 1)) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro p hp
  unfold dyQ at hp
  rw [Finset.mem_filter, Finset.mem_Ico] at hp
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp.2⟩

private lemma floor_two_pow (m : ℕ) : ⌊(2 : ℝ) ^ m⌋₊ = 2 ^ m := by
  have := Nat.floor_natCast (R := ℝ) (2 ^ m)
  push_cast at this
  exact this

/-- OPERATOR-ASSISTED (2026-10-14): every prime in `(n, 2n]` divides the central binomial coefficient. -/
private lemma pow_card_primes_le41635 (n : ℕ) :
    n ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card ≤ 4 ^ n := by
  set T := (Finset.Ioc n (2 * n)).filter Nat.Prime with hT
  calc n ^ T.card = ∏ _p ∈ T, n := (Finset.prod_const n).symm
    _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' (fun p hp => by
        rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp; omega)
    _ ≤ Nat.centralBinom n := Nat.le_of_dvd (Nat.centralBinom_pos n)
        (Finset.prod_primes_dvd _ (fun p hp => (Finset.mem_filter.1 hp).2.prime)
          (fun p hp => by
            rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
            rw [Nat.centralBinom_eq_two_mul_choose]
            exact hp.2.dvd_choose hp.1.1 (by omega) hp.1.2))
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

/-- OPERATOR-ASSISTED (2026-10-14): Erdős's proof of Bertrand's postulate, kept quantitative. The central binomial
coefficient is at most what the primes up to `2n/3` contribute, times `2n` for each prime in `(n, 2n]`. -/
private lemma centralBinom_le_with_primes41635 (n : ℕ) (hn : 2 < n) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  set T := (Finset.Ioc n (2 * n)).filter Nat.Prime with hT
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hsplit : Nat.centralBinom n = (∏ x ∈ Finset.range (2 * n / 3 + 1), f x) * ∏ x ∈ T, f x := by
    have hsub : Finset.range (2 * n / 3 + 1) ⊆ Finset.range (2 * n + 1) :=
      Finset.range_subset_range.2 (by omega)
    conv_lhs => rw [← Nat.prod_pow_factorization_centralBinom n]
    rw [← Finset.prod_sdiff hsub, mul_comm]
    congr 1
    symm
    apply Finset.prod_subset
    · intro p hp
      rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range]
      omega
    · intro p hp hpT
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hp
      by_cases hpr : p.Prime
      · have hpn : p ≤ n := by
          by_contra hcon
          exact hpT (by rw [hT, Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, by omega⟩, hpr⟩)
        show p ^ n.centralBinom.factorization p = 1
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega), pow_zero]
      · show p ^ n.centralBinom.factorization p = 1
        rw [Nat.factorization_eq_zero_of_not_prime _ hpr, pow_zero]
  have hsmall : ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h; dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  have hT' : ∏ x ∈ T, f x ≤ (2 * n) ^ T.card := by
    calc ∏ x ∈ T, f x ≤ ∏ _x ∈ T, (2 * n) :=
          Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      _ = (2 * n) ^ T.card := Finset.prod_const _
  rw [hsplit]
  exact Nat.mul_le_mul hsmall hT'

private lemma not_prime_two_pow41635 (j : ℕ) (hj : 2 ≤ j) : ¬ (2 ^ j).Prime := by
  intro hp
  have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

/-- For `j ≥ 2` the dyadic block's primes are the primes in `(2^j, 2·2^j]`. -/
private lemma dyQ_eq41635 (j : ℕ) (hj : 2 ≤ j) :
    dyQ j = (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter Nat.Prime := by
  unfold dyQ
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hA := not_prime_two_pow41635 j hj
  have hB := not_prime_two_pow41635 (j + 1) (by omega)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    refine ⟨⟨?_, by omega⟩, hp⟩
    rcases Nat.lt_or_ge (2 ^ j) p with h | h
    · exact h
    · exact absurd (show p = 2 ^ j by omega ▸ hp) (by
        intro hq; exact hA (by rw [show 2 ^ j = p by omega]; exact hp))
  · rintro ⟨⟨h1, h2⟩, hp⟩
    refine ⟨⟨by omega, ?_⟩, hp⟩
    rcases Nat.lt_or_ge p (2 ^ (j + 1)) with h | h
    · exact h
    · exfalso; exact hB (by rw [show 2 ^ (j + 1) = p by omega]; exact hp)

private lemma big_pow41635 (j : ℕ) (hj : 20 ≤ j) : 288 * (j + 1) ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 2) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    calc 288 * (k + 1 + 1) ^ 2 = 288 * (k + 2) ^ 2 := by ring
      _ ≤ 288 * (2 * (k + 1) ^ 2) := by omega
      _ = 2 * (288 * (k + 1) ^ 2) := by ring
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

/-- OPERATOR-ASSISTED (2026-10-14): the dyadic upper bound, from `n ^ #primes ≤ 4 ^ n`, with no hypothesis. -/
private lemma cheb_up (j : ℕ) :
    ((dyQ j).card : ℝ) ≤ 4 * 2 ^ j / (j + 1) := by
  set c := (dyQ j).card with hc
  suffices h : (j + 1) * c ≤ 4 * 2 ^ j by
    rw [le_div_iff₀ (by positivity)]
    have : (((j + 1) * c : ℕ) : ℝ) ≤ ((4 * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rcases Nat.lt_or_ge j 2 with hj | hj
  · have hc' : c ≤ 2 ^ j := by
      calc c ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := by rw [hc]; unfold dyQ; exact Finset.card_filter_le _ _
        _ = 2 ^ j := by rw [Nat.card_Ico]; omega
    have h0 : 0 < 2 ^ j := by positivity
    interval_cases j <;> omega
  · rw [hc, dyQ_eq41635 j hj]
    set c' := ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter Nat.Prime).card with hc'
    have h := pow_card_primes_le41635 (2 ^ j)
    rw [← hc', ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h
    have h' : j * c' ≤ 2 * 2 ^ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp h
    have : c' ≤ j * c' := Nat.le_mul_of_pos_left c' (by omega)
    nlinarith

private lemma primeCounting_le_add (j : ℕ) (hj : 1 ≤ j) :
    Nat.primeCounting (2 ^ (j + 1)) ≤ Nat.primeCounting (2 ^ j) + (dyQ j).card := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  unfold dyQ
  rw [Finset.mem_filter, Finset.mem_Ico]
  have h4 : 4 ≤ 2 ^ (j + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  by_cases hle : p < 2 ^ j + 1
  · left; exact ⟨hle, hp.2⟩
  · right
    refine ⟨⟨by omega, ?_⟩, hp.2⟩
    rcases Nat.lt_or_ge p (2 ^ (j + 1)) with h | h
    · exact h
    · exfalso
      have hpe : p = 2 ^ (j + 1) := by omega
      have h2 : 2 ∣ p := by rw [hpe]; exact dvd_pow_self 2 (by omega)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.2).mp h2
      omega

/-- OPERATOR-ASSISTED (2026-10-14): the dyadic lower bound for `j ≥ 80`, from the quantitative Bertrand bound
above, with no hypothesis. Its only use is at `j ≥ 80`. -/
private lemma cheb_low (j : ℕ) (hj : 80 ≤ j) :
    (2 : ℝ) ^ j / (2 * (j + 1)) ≤ (dyQ j).card := by
  rw [dyQ_eq41635 j (by omega)]
  set n := 2 ^ j with hn
  set c := ((Finset.Ioc n (2 * n)).filter Nat.Prime).card with hc
  set s := Nat.sqrt (2 * n) with hs
  have hn4 : 4 ≤ n := by
    rw [hn]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2n : 2 * n = 2 ^ (j + 1) := by rw [hn, pow_succ]; ring
  have hA := Nat.four_pow_lt_mul_centralBinom n hn4
  have hB := centralBinom_le_with_primes41635 n (by omega)
  rw [← hc, ← hs] at hB
  have hC : 4 ^ n < (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) := by
    calc 4 ^ n < n * Nat.centralBinom n := hA
      _ ≤ (2 * n) * Nat.centralBinom n := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) := Nat.mul_le_mul_left _ hB
  have hD : 2 ^ (2 * n) < 2 ^ ((j + 1) * (1 + s + c) + 2 * (2 * n / 3)) := by
    have e1 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have e2 : (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) =
        2 ^ ((j + 1) * (1 + s + c) + 2 * (2 * n / 3)) := by
      rw [h2n, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul]
      ring
    rw [e1, e2] at hC
    exact hC
  have hE : 2 * n < (j + 1) * (1 + s + c) + 2 * (2 * n / 3) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hD
  have hs2 : s * s ≤ 2 * n := Nat.sqrt_le (2 * n)
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hbig := big_pow41635 j (by omega)
  have hF : (6 * (j + 1) * (1 + s)) * (6 * (j + 1) * (1 + s)) ≤ n * n := by
    have h1 : (1 + s) * (1 + s) ≤ 4 * (s * s) := by nlinarith
    have h3 : 288 * (j + 1) ^ 2 * n ≤ n * n := by
      rw [hn]; exact Nat.mul_le_mul_right _ hbig
    calc (6 * (j + 1) * (1 + s)) * (6 * (j + 1) * (1 + s))
        = 36 * (j + 1) ^ 2 * ((1 + s) * (1 + s)) := by ring
      _ ≤ 36 * (j + 1) ^ 2 * (4 * (s * s)) := Nat.mul_le_mul_left _ h1
      _ ≤ 36 * (j + 1) ^ 2 * (4 * (2 * n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs2)
      _ = 288 * (j + 1) ^ 2 * n := by ring
      _ ≤ n * n := h3
  have hG : 6 * (j + 1) * (1 + s) ≤ n := Nat.mul_self_le_mul_self_iff.mp hF
  have hH : n ≤ 2 * ((j + 1) * c) := by
    have e : (j + 1) * (1 + s + c) = (j + 1) * (1 + s) + (j + 1) * c := by ring
    rw [e] at hE
    have e2 : 6 * (j + 1) * (1 + s) = 6 * ((j + 1) * (1 + s)) := by ring
    rw [e2] at hG
    omega
  rw [div_le_iff₀ (by positivity)]
  have : ((n : ℕ) : ℝ) ≤ ((2 * ((j + 1) * c) : ℕ) : ℝ) := by exact_mod_cast hH
  push_cast at this
  rw [hn] at this
  push_cast at this
  linarith

private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (S : Finset ℕ) (c M : ℕ) :
    ∑ k ∈ S, (if c + k ≤ M then g (c + k) else 0) ≤ ∑ m ∈ Finset.range (M + 1), g m := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (f := g) (g := fun k => c + k)
    (by intro a _ b _ h; simp only at h; omega)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range]
    omega
  · intro m _ _
    exact hg m

private lemma sum_pow_two_le (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), (2 : ℝ) ^ m ≤ 2 ^ (M + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, pow_succ (2 : ℝ) (M + 1)]
    linarith

private lemma sum_pow_div_le (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), (2 : ℝ) ^ m / ((m : ℝ) + 2) ≤ 4 * 2 ^ M / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have ha : (0 : ℝ) < 2 ^ M := by positivity
    have hM : (0 : ℝ) ≤ M := by positivity
    have h1 : 4 * (2 : ℝ) ^ M / ((M : ℝ) + 2) ≤ 6 * 2 ^ M / ((M : ℝ) + 1 + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg ha.le hM]
    have h2 : 6 * (2 : ℝ) ^ M / ((M : ℝ) + 1 + 2) + 2 ^ (M + 1) / ((M : ℝ) + 1 + 2) =
        4 * 2 ^ (M + 1) / ((M : ℝ) + 1 + 2) := by
      rw [pow_succ]; field_simp; ring
    linarith

private lemma sum_boxIdx_le (n : ℕ) (f : ℕ × ℕ × ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ t ∈ boxIdx n, f t ≤ ∑ l ∈ Finset.range (Nat.log 2 n + 1),
      ∑ j ∈ Finset.range (Nat.log 2 n + 1), ∑ k ∈ Finset.range (Nat.log 2 n + 1),
        (if l + j + k ≤ Nat.log 2 n ∧ j ≤ k then f (l, j, k) else 0) := by
  unfold boxIdx
  rw [Finset.sum_filter]
  calc _ ≤ ∑ t ∈ Finset.range (Nat.log 2 n + 1) ×ˢ (Finset.range (Nat.log 2 n + 1) ×ˢ
        Finset.range (Nat.log 2 n + 1)),
        (if t.1 + t.2.1 + t.2.2 ≤ Nat.log 2 n ∧ t.2.1 ≤ t.2.2 then f t else 0) := by
        apply Finset.sum_le_sum
        intro t _
        by_cases ha : t.1 + t.2.1 + t.2.2 ≤ Nat.log 2 n ∧ t.2.1 ≤ t.2.2 ∧
            Real.log n ^ 20 < (2 : ℝ) ^ (t.2.1 + 1)
        · rw [if_pos ha, if_pos ⟨ha.1, ha.2.1⟩]
        · rw [if_neg ha]
          split_ifs
          · exact hf _
          · exact le_rfl
    _ = _ := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.sum_product]

private lemma inner_l (K j k : ℕ) :
    ∑ l ∈ Finset.range (K + 1), (if l + j + k ≤ K ∧ j ≤ k then
      (2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) else 0) ≤
      2 ^ (K + 1) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) := by
  have hD : (0 : ℝ) < ((j : ℝ) + 1) * ((k : ℝ) + 1) := by positivity
  calc _ ≤ ∑ l ∈ Finset.range (K + 1), (if (j + k) + l ≤ K then (2 : ℝ) ^ ((j + k) + l) else 0) /
        (((j : ℝ) + 1) * ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases h : l + j + k ≤ K ∧ j ≤ k
        · rw [if_pos h, if_pos (by omega), show j + k + l = l + j + k by ring]
        · rw [if_neg h]
          apply div_nonneg _ hD.le
          split_ifs <;> positivity
    _ = (∑ l ∈ Finset.range (K + 1), (if (j + k) + l ≤ K then (2 : ℝ) ^ ((j + k) + l) else 0)) /
        (((j : ℝ) + 1) * ((k : ℝ) + 1)) := by rw [Finset.sum_div]
    _ ≤ (∑ m ∈ Finset.range (K + 1), (2 : ℝ) ^ m) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) :=
        div_le_div_of_nonneg_right
          (sum_shift_le (fun m => (2 : ℝ) ^ m) (fun m => by positivity) _ _ _) hD.le
    _ ≤ _ := div_le_div_of_nonneg_right (sum_pow_two_le K) hD.le

private lemma sumF_le (K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
      (if l + j + k ≤ K ∧ j ≤ k then
        (2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) else 0)
      ≤ 2 ^ (K + 1) * (∑ j ∈ Finset.range (K + 1), 1 / ((j : ℝ) + 1)) ^ 2 := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
        (2 : ℝ) ^ (K + 1) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro k _
        exact inner_l K j k
    _ = _ := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        field_simp

private lemma inner_k (K l j : ℕ) (hl : l ≤ K) :
    ∑ k ∈ Finset.range (K + 1), (if l + j + k ≤ K ∧ j ≤ k then
      rr ^ l * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1))) else 0) ≤
      8 * rr ^ l * 2 ^ K / (((j : ℝ) + 1) * (((K - l : ℕ) : ℝ) + 2)) := by
  have hr := rr_pos
  set c : ℝ := 2 * rr ^ l * 2 ^ l / ((j : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  calc _ ≤ ∑ k ∈ Finset.range (K + 1), c * (if j + k ≤ K - l then
        (2 : ℝ) ^ (j + k) / (((j + k : ℕ) : ℝ) + 2) else 0) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases h : l + j + k ≤ K ∧ j ≤ k
        · rw [if_pos h, if_pos (by omega), hc]
          have hjk : (j : ℝ) ≤ k := by exact_mod_cast h.2
          have hP : 0 ≤ rr ^ l * 2 ^ l * 2 ^ (j + k) / ((j : ℝ) + 1) := by positivity
          have hk : 1 / ((k : ℝ) + 1) ≤ 2 / ((j : ℝ) + k + 2) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          calc rr ^ l * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)))
              = (rr ^ l * 2 ^ l * 2 ^ (j + k) / ((j : ℝ) + 1)) * (1 / ((k : ℝ) + 1)) := by
                rw [show l + j + k = l + (j + k) by ring, pow_add]
                field_simp
            _ ≤ (rr ^ l * 2 ^ l * 2 ^ (j + k) / ((j : ℝ) + 1)) * (2 / ((j : ℝ) + k + 2)) :=
                mul_le_mul_of_nonneg_left hk hP
            _ = 2 * rr ^ l * 2 ^ l / ((j : ℝ) + 1) *
                ((2 : ℝ) ^ (j + k) / (((j + k : ℕ) : ℝ) + 2)) := by
                push_cast
                field_simp
        · rw [if_neg h]
          apply mul_nonneg hc0
          split_ifs <;> positivity
    _ = c * ∑ k ∈ Finset.range (K + 1), (if j + k ≤ K - l then
        (2 : ℝ) ^ (j + k) / (((j + k : ℕ) : ℝ) + 2) else 0) := by rw [Finset.mul_sum]
    _ ≤ c * ∑ m ∈ Finset.range (K - l + 1), (2 : ℝ) ^ m / ((m : ℝ) + 2) := by
        gcongr
        exact sum_shift_le (fun m => (2 : ℝ) ^ m / ((m : ℝ) + 2)) (fun m => by positivity) _ _ _
    _ ≤ c * (4 * 2 ^ (K - l) / (((K - l : ℕ) : ℝ) + 2)) := by
        gcongr
        exact sum_pow_div_le (K - l)
    _ = _ := by
        have hp : (2 : ℝ) ^ l * 2 ^ (K - l) = 2 ^ K := by
          rw [← pow_add, Nat.add_sub_cancel' hl]
        rw [hc, ← hp]
        field_simp
        ring

private lemma summable_rr : Summable (fun l : ℕ => ((l : ℝ) + 1) * rr ^ l) := by
  have hn : ‖rr‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos rr_pos]
    exact rr_lt_one
  have ha := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hb := summable_geometric_of_lt_one rr_pos.le rr_lt_one
  have e : (fun l : ℕ => ((l : ℝ) + 1) * rr ^ l) = fun l : ℕ => (l : ℝ) ^ 1 * rr ^ l + rr ^ l := by
    funext l
    ring
  rw [e]
  exact ha.add hb

private lemma sumG_le (K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
      (if l + j + k ≤ K ∧ j ≤ k then
        rr ^ l * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1))) else 0)
      ≤ 8 * (∑' l : ℕ, ((l : ℝ) + 1) * rr ^ l) *
        (∑ j ∈ Finset.range (K + 1), 1 / ((j : ℝ) + 1)) * 2 ^ K / ((K : ℝ) + 2) := by
  set H := ∑ j ∈ Finset.range (K + 1), 1 / ((j : ℝ) + 1) with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun j _ => by positivity)
  have hr := rr_pos
  calc _ ≤ ∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1),
        8 * rr ^ l * 2 ^ K / (((j : ℝ) + 1) * (((K - l : ℕ) : ℝ) + 2)) := by
        apply Finset.sum_le_sum
        intro l hl
        apply Finset.sum_le_sum
        intro j _
        exact inner_k K l j (by rw [Finset.mem_range] at hl; omega)
    _ = ∑ l ∈ Finset.range (K + 1), 8 * rr ^ l * 2 ^ K * H / (((K - l : ℕ) : ℝ) + 2) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [hH, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
    _ ≤ ∑ l ∈ Finset.range (K + 1), 8 * 2 ^ K * H / ((K : ℝ) + 2) * (((l : ℝ) + 1) * rr ^ l) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [Finset.mem_range] at hl
        have hlK : l ≤ K := by omega
        have hlKr : (l : ℝ) ≤ K := by exact_mod_cast hlK
        have hl0 : (0 : ℝ) ≤ l := by positivity
        have hKl : ((K - l : ℕ) : ℝ) = (K : ℝ) - l := by rw [Nat.cast_sub hlK]
        have hfrac : 1 / (((K - l : ℕ) : ℝ) + 2) ≤ ((l : ℝ) + 1) / ((K : ℝ) + 2) := by
          rw [hKl, div_le_div_iff₀ (by linarith) (by positivity)]
          nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ K - l + 1)]
        have hA : 0 ≤ 8 * rr ^ l * 2 ^ K * H := by positivity
        calc 8 * rr ^ l * 2 ^ K * H / (((K - l : ℕ) : ℝ) + 2)
            = (8 * rr ^ l * 2 ^ K * H) * (1 / (((K - l : ℕ) : ℝ) + 2)) := by ring
          _ ≤ (8 * rr ^ l * 2 ^ K * H) * (((l : ℝ) + 1) / ((K : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hfrac hA
          _ = _ := by ring
    _ = 8 * 2 ^ K * H / ((K : ℝ) + 2) *
        ∑ l ∈ Finset.range (K + 1), ((l : ℝ) + 1) * rr ^ l := (Finset.mul_sum _ _ _).symm
    _ ≤ 8 * 2 ^ K * H / ((K : ℝ) + 2) * (∑' l : ℕ, ((l : ℝ) + 1) * rr ^ l) := by
        gcongr
        exact summable_rr.sum_le_tsum _ (fun l _ => by positivity)
    _ = _ := by ring

private lemma pow_big (J : ℕ) (hJ : 80 ≤ J) : 2 ^ 14 * (J + 1) ^ 5 ≤ 2 ^ J := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ J hJ ih =>
    have key : (J + 2) ^ 5 ≤ 2 * (J + 1) ^ 5 := by
      obtain ⟨u, hu⟩ : ∃ u, u = J + 1 := ⟨_, rfl⟩
      have hu81 : 81 ≤ u := by omega
      have e : J + 2 = u + 1 := by omega
      rw [e, ← hu]
      have a5 : 81 * u ^ 4 ≤ u ^ 5 := by
        rw [pow_succ u 4, mul_comm 81]; exact Nat.mul_le_mul_left _ hu81
      have a4 : 81 * u ^ 3 ≤ u ^ 4 := by
        rw [pow_succ u 3, mul_comm 81]; exact Nat.mul_le_mul_left _ hu81
      have a3 : 81 * u ^ 2 ≤ u ^ 3 := by
        rw [pow_succ u 2, mul_comm 81]; exact Nat.mul_le_mul_left _ hu81
      have a2 : 81 * u ≤ u ^ 2 := by
        rw [sq, mul_comm 81]; exact Nat.mul_le_mul_left _ hu81
      nlinarith
    calc 2 ^ 14 * (J + 1 + 1) ^ 5 = 2 ^ 14 * (J + 2) ^ 5 := by ring
      _ ≤ 2 ^ 14 * (2 * (J + 1) ^ 5) := Nat.mul_le_mul_left _ key
      _ = 2 * (2 ^ 14 * (J + 1) ^ 5) := by ring
      _ ≤ 2 * 2 ^ J := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (J + 1) := by ring

private lemma y_big
    (X : ℝ) (hX : 16 ≤ X) (j : ℕ) (hj : X ^ 20 < (2 : ℝ) ^ (j + 1)) :
    2 * X ^ 16 ≤ ((dyQ j).card : ℝ) := by
  have hX0 : 0 ≤ X := by linarith
  have hj80 : 80 ≤ j := by
    have h80 : (2 : ℝ) ^ 80 < 2 ^ (j + 1) := by
      calc (2 : ℝ) ^ 80 = 16 ^ 20 := by norm_num
        _ ≤ X ^ 20 := pow_le_pow_left₀ (by norm_num) hX 20
        _ < _ := hj
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h80
    omega
  have hlow := cheb_low j hj80
  have hpb : (2 : ℝ) ^ 14 * ((j : ℝ) + 1) ^ 5 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast pow_big j hj80
  have h5 : (4 * ((j : ℝ) + 1) * X ^ 16) ^ 5 < ((2 : ℝ) ^ j) ^ 5 := by
    have hA : (X ^ 20) ^ 4 < ((2 : ℝ) ^ (j + 1)) ^ 4 :=
      pow_lt_pow_left₀ hj (by positivity) (by norm_num)
    have hB : ((2 : ℝ) ^ (j + 1)) ^ 4 = 16 * ((2 : ℝ) ^ j) ^ 4 := by ring
    have hC : (0 : ℝ) < 2 ^ 10 * ((j : ℝ) + 1) ^ 5 := by positivity
    calc (4 * ((j : ℝ) + 1) * X ^ 16) ^ 5 = 2 ^ 10 * ((j : ℝ) + 1) ^ 5 * (X ^ 20) ^ 4 := by ring
      _ < 2 ^ 10 * ((j : ℝ) + 1) ^ 5 * (16 * ((2 : ℝ) ^ j) ^ 4) := by
          rw [← hB]; exact mul_lt_mul_of_pos_left hA hC
      _ = (2 ^ 14 * ((j : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ j) ^ 4 := by ring
      _ ≤ 2 ^ j * ((2 : ℝ) ^ j) ^ 4 := mul_le_mul_of_nonneg_right hpb (by positivity)
      _ = ((2 : ℝ) ^ j) ^ 5 := by ring
  have h4 : 4 * ((j : ℝ) + 1) * X ^ 16 < (2 : ℝ) ^ j :=
    lt_of_pow_lt_pow_left₀ 5 (by positivity) h5
  have : 2 * X ^ 16 ≤ (2 : ℝ) ^ j / (2 * (j + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Remaining analytic input (A-free): the box bounds summed over all dyadic boxes. -/

private lemma analytic_box_sum :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ t ∈ boxIdx n, boxW (dyX t.1).card (dyQ t.2.1).card (dyQ t.2.2).card ≤
        C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  set D := ∑' l : ℕ, ((l : ℝ) + 1) * rr ^ l with hD
  have hD0 : 0 ≤ D := tsum_nonneg (fun l => by have := rr_pos; positivity)
  refine ⟨16 * (24 * D + 18), 2 ^ 24, fun n hn => ?_⟩
  set K := Nat.log 2 n with hK
  set X := Real.log n with hX
  set L := Real.log X with hL
  set H := ∑ j ∈ Finset.range (K + 1), 1 / ((j : ℝ) + 1) with hH
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hnR : (2 : ℝ) ^ 24 ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hX16 : 16 ≤ X := by
    have h := Real.log_le_log (by positivity) hnR
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hXpos]
    have := Real.exp_one_lt_d9
    linarith
  have hLX : L ≤ X := by
    have := Real.log_le_sub_one_of_pos hXpos
    linarith
  have h2K : (2 : ℝ) ^ K ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn0.ne'
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hKX : (K : ℝ) * Real.log 2 ≤ X := by
    have h := Real.log_le_log (by positivity) h2K
    rwa [Real.log_pow] at h
  have hXK : X ≤ (K : ℝ) + 2 := by
    have hlt : (n : ℝ) < 2 ^ (K + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
    have h := Real.log_lt_log (by positivity) hlt
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun j _ => by positivity)
  have hH3 : H ≤ 3 * L := by
    have hharm : H = (harmonic (K + 1) : ℝ) := by
      simp only [hH, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
        Nat.cast_one, one_div, Rat.cast_add, Rat.cast_one]
    have hh := harmonic_le_one_add_log (K + 1)
    have hK15 : (K : ℝ) ≤ 1.5 * X := by nlinarith
    have hK1 : ((K + 1 : ℕ) : ℝ) ≤ X ^ 2 := by
      push_cast
      nlinarith
    have hlog : Real.log ((K + 1 : ℕ) : ℝ) ≤ 2 * L := by
      calc _ ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) hK1
        _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
    rw [hharm]
    linarith
  have hbox : ∀ t ∈ boxIdx n, boxW (dyX t.1).card (dyQ t.2.1).card (dyQ t.2.2).card ≤
      16 * ((rr ^ t.1 + 1 / X ^ 2) *
        ((2 : ℝ) ^ (t.1 + t.2.1 + t.2.2) / (((t.2.1 : ℝ) + 1) * ((t.2.2 : ℝ) + 1)))) := by
    intro t ht
    obtain ⟨l, j, k⟩ := t
    unfold boxIdx at ht
    rw [Finset.mem_filter] at ht
    obtain ⟨-, -, hjk, hY⟩ := ht
    simp only at hjk hY ⊢
    have hYk : X ^ 20 < (2 : ℝ) ^ (k + 1) :=
      lt_of_lt_of_le hY (pow_le_pow_right₀ (by norm_num) (by omega))
    have hyj := y_big X hX16 j hY
    have hyk := y_big X hX16 k hYk
    have hcardX : (dyX l).card = 2 ^ l := by
      unfold dyX
      rw [Nat.card_Ico, pow_succ]
      omega
    rw [hcardX]
    have hX16p : (0 : ℝ) < X ^ 16 := by positivity
    have hy0 : 0 < (dyQ j).card := by
      have : (0 : ℝ) < (dyQ j).card := by linarith
      exact_mod_cast this
    have hz0 : 0 < (dyQ k).card := by
      have : (0 : ℝ) < (dyQ k).card := by linarith
      exact_mod_cast this
    have hyz : (1 : ℝ) / (dyQ j).card + 1 / (dyQ k).card ≤ (1 / X ^ 2) ^ 8 := by
      have a1 : (1 : ℝ) / (dyQ j).card ≤ 1 / (2 * X ^ 16) :=
        one_div_le_one_div_of_le (by positivity) hyj
      have a2 : (1 : ℝ) / (dyQ k).card ≤ 1 / (2 * X ^ 16) :=
        one_div_le_one_div_of_le (by positivity) hyk
      have e : (1 / X ^ 2) ^ 8 = 1 / (2 * X ^ 16) + 1 / (2 * X ^ 16) := by
        field_simp
        ring
      linarith
    refine (boxW_split l _ _ (1 / X ^ 2) (by positivity) hy0 hz0 hyz).trans ?_
    have hupj := cheb_up j
    have hupk := cheb_up k
    have hw : 0 ≤ rr ^ l + 1 / X ^ 2 := by have := rr_pos; positivity
    have hyz' : (2 : ℝ) ^ l * (dyQ j).card * (dyQ k).card ≤
        16 * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1))) := by
      calc (2 : ℝ) ^ l * (dyQ j).card * (dyQ k).card ≤
          2 ^ l * (4 * 2 ^ j / (j + 1)) * (4 * 2 ^ k / (k + 1)) := by gcongr
        _ = _ := by rw [pow_add, pow_add]; field_simp; ring
    calc _ ≤ (rr ^ l + 1 / X ^ 2) *
          (16 * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left hyz' hw
      _ = _ := by ring
  have hr := rr_pos
  calc _ ≤ ∑ t ∈ boxIdx n, 16 * ((rr ^ t.1 + 1 / X ^ 2) *
        ((2 : ℝ) ^ (t.1 + t.2.1 + t.2.2) / (((t.2.1 : ℝ) + 1) * ((t.2.2 : ℝ) + 1)))) :=
        Finset.sum_le_sum hbox
    _ ≤ ∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
        (if l + j + k ≤ K ∧ j ≤ k then 16 * ((rr ^ l + 1 / X ^ 2) *
          ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)))) else 0) :=
        sum_boxIdx_le n _ (fun t => by positivity)
    _ = 16 * (∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1),
          ∑ k ∈ Finset.range (K + 1), (if l + j + k ≤ K ∧ j ≤ k then
            rr ^ l * ((2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1))) else 0)) +
        16 / X ^ 2 * (∑ l ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1),
          ∑ k ∈ Finset.range (K + 1), (if l + j + k ≤ K ∧ j ≤ k then
            (2 : ℝ) ^ (l + j + k) / (((j : ℝ) + 1) * ((k : ℝ) + 1)) else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
    _ ≤ 16 * (8 * D * H * 2 ^ K / ((K : ℝ) + 2)) + 16 / X ^ 2 * (2 ^ (K + 1) * H ^ 2) := by
        gcongr
        · exact sumG_le K
        · exact sumF_le K
    _ ≤ 16 * (24 * D * (n * L / X)) + 288 * (n * L / X) := by
        have hL0 : 0 ≤ L := by linarith
        have hnpos : (0 : ℝ) ≤ n := by positivity
        have h8D : 0 ≤ 8 * D := by linarith
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) ?_
        · have e1 : 8 * D * H * 2 ^ K ≤ 8 * D * (3 * L) * n :=
            mul_le_mul (mul_le_mul_of_nonneg_left hH3 h8D) h2K (by positivity)
              (mul_nonneg h8D (by linarith))
          calc 8 * D * H * 2 ^ K / ((K : ℝ) + 2) ≤ 8 * D * (3 * L) * n / ((K : ℝ) + 2) :=
                div_le_div_of_nonneg_right e1 (by positivity)
            _ ≤ 8 * D * (3 * L) * n / X :=
                div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg h8D (by linarith)) hnpos)
                  hXpos hXK
            _ = 24 * D * (n * L / X) := by ring
        · have hLX1 : L / X ≤ 1 := div_le_one_of_le₀ hLX hXpos.le
          have h2K1 : (2 : ℝ) ^ (K + 1) ≤ 2 * n := by rw [pow_succ]; linarith
          have hHsq : H ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hH0 hH3 2
          calc 16 / X ^ 2 * (2 ^ (K + 1) * H ^ 2) ≤ 16 / X ^ 2 * (2 * n * (3 * L) ^ 2) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h2K1 hHsq (by positivity) (by positivity))
                  (by positivity)
            _ = 288 * (n * L / X) * (L / X) := by field_simp; ring
            _ ≤ 288 * (n * L / X) :=
                mul_le_of_le_one_right
                  (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hnpos hL0) hXpos.le)) hLX1
    _ = _ := by ring

private lemma triples_le_boxW (A X Y Z : Finset ℕ) (hB : erdosBoxSparse A) :
    ((erdosBoxTriples A X Y Z).card : ℝ) ≤ boxW X.card Y.card Z.card := by
  have h := hB X Y Z
  unfold boxW
  calc ((erdosBoxTriples A X Y Z).card : ℝ)
      = (((erdosBoxTriples A X Y Z).card : ℝ) ^ 8) ^ (((8 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by positivity) (by norm_num)).symm
    _ ≤ _ := by
        rw [show (((8 : ℕ) : ℝ)) = (8 : ℝ) by norm_num]
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by norm_num)

private lemma mem_cover (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 n) (a : ℕ)
    (ha : a ∈ A \ (erdosRough n ∪ erdosSmoothTail n)) :
    ∃ t ∈ boxIdx n, a ∈ (erdosBoxTriples A (dyX t.1) (dyQ t.2.1) (dyQ t.2.2)).image
      (fun u => u.1 * u.2.1 * u.2.2) := by
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at ha
  obtain ⟨haA, hr, hs⟩ := ha
  have hIoc : a ∈ Finset.Ioc 0 n := hA haA
  have hnr : ¬ (a = 1 ∨ a.Prime) := by
    intro h
    apply hr
    unfold erdosRough
    exact Finset.mem_filter.mpr ⟨hIoc, h⟩
  have hq : ∃ q ∈ (a / erdosLpf a).primeFactors, Real.log n ^ 20 < (q : ℝ) := by
    by_contra hcon
    push Not at hcon
    apply hs
    unfold erdosSmoothTail
    exact Finset.mem_filter.mpr ⟨hIoc, hnr, hcon⟩
  rw [Finset.mem_Ioc] at hIoc
  have ha1 : 1 < a := by
    rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · exfalso; apply hnr; left; omega
  have hne : a.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr ha1
  obtain ⟨P, hPmem, hPeq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hLpf : erdosLpf a = P := hPeq
  rw [hLpf] at hq
  obtain ⟨q, hqmem, hqY⟩ := hq
  obtain ⟨hPp, hPdvd, -⟩ := Nat.mem_primeFactors.mp hPmem
  obtain ⟨hqp, hqdvd, hb0⟩ := Nat.mem_primeFactors.mp hqmem
  have hqa : q ∣ a := hqdvd.trans (Nat.div_dvd_of_dvd hPdvd)
  have hqP : q ≤ P := by
    have := Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hqp, hqa, by omega⟩)
    rw [hPeq] at this
    exact this
  set s := a / P / q with hsdef
  have hbq : a / P = q * s := (Nat.mul_div_cancel' hqdvd).symm
  have haP : a = P * (a / P) := (Nat.mul_div_cancel' hPdvd).symm
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hbq; exact hb0 hbq
  have hprod : s * q * P = a := by rw [haP, hbq]; ring
  have hq0 : q ≠ 0 := hqp.ne_zero
  have hP0 : P ≠ 0 := hPp.ne_zero
  have hlog : Nat.log 2 s + Nat.log 2 q + Nat.log 2 P ≤ Nat.log 2 n := by
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [pow_add, pow_add]
    calc 2 ^ Nat.log 2 s * 2 ^ Nat.log 2 q * 2 ^ Nat.log 2 P ≤ s * q * P := by
          gcongr
          · exact Nat.pow_log_le_self 2 hs0
          · exact Nat.pow_log_le_self 2 hq0
          · exact Nat.pow_log_le_self 2 hP0
      _ ≤ n := by omega
  have hqlt : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  refine ⟨(Nat.log 2 s, Nat.log 2 q, Nat.log 2 P), ?_, ?_⟩
  · unfold boxIdx
    rw [Finset.mem_filter]
    refine ⟨?_, hlog, Nat.log_mono_right (b := 2) hqP, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · calc Real.log n ^ 20 < (q : ℝ) := hqY
        _ < (2 : ℝ) ^ (Nat.log 2 q + 1) := by exact_mod_cast hqlt
  · rw [Finset.mem_image]
    refine ⟨(s, q, P), ?_, hprod⟩
    unfold erdosBoxTriples dyX dyQ
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
    refine ⟨⟨⟨Nat.pow_log_le_self 2 hs0, Nat.lt_pow_succ_log_self (by norm_num) s⟩,
      ⟨⟨Nat.pow_log_le_self 2 hq0, hqlt⟩, hqp⟩,
      ⟨⟨Nat.pow_log_le_self 2 hP0, Nat.lt_pow_succ_log_self (by norm_num) P⟩, hPp⟩⟩, ?_⟩
    rw [hprod]; exact haA

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A →
      ((A \ (erdosRough n ∪ erdosSmoothTail n)).card : ℝ) ≤
        C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  obtain ⟨C, N, hC⟩ := analytic_box_sum
  refine ⟨C, N, fun n hn A hA hB => ?_⟩
  refine le_trans ?_ (hC n hn)
  have hsub : A \ (erdosRough n ∪ erdosSmoothTail n) ⊆ (boxIdx n).biUnion (fun t =>
      (erdosBoxTriples A (dyX t.1) (dyQ t.2.1) (dyQ t.2.2)).image
        (fun u => u.1 * u.2.1 * u.2.2)) := by
    intro a ha
    rw [Finset.mem_biUnion]
    exact mem_cover n A hA a ha
  have hcard : (A \ (erdosRough n ∪ erdosSmoothTail n)).card ≤
      ∑ t ∈ boxIdx n, (erdosBoxTriples A (dyX t.1) (dyQ t.2.1) (dyQ t.2.2)).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun t _ => Finset.card_image_le))
  calc ((A \ (erdosRough n ∪ erdosSmoothTail n)).card : ℝ)
      ≤ ((∑ t ∈ boxIdx n, (erdosBoxTriples A (dyX t.1) (dyQ t.2.1) (dyQ t.2.2)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∑ t ∈ boxIdx n, ((erdosBoxTriples A (dyX t.1) (dyQ t.2.1) (dyQ t.2.2)).card : ℝ) := by
        push_cast; rfl
    _ ≤ _ := Finset.sum_le_sum fun t _ => triples_le_boxW A _ _ _ hB

end erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part_ns

theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A →
      ((A \ (erdosRough n ∪ erdosSmoothTail n)).card : ℝ) ≤
        C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  exact erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part_ns.erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part

theorem erdos_41635_hyp_upper_hyp_box_to_bound : ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A →
    (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  have hup : ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x :=
    erdos_41635_cheb_upper5
  obtain ⟨C1, N1, h1⟩ := erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough hup
  obtain ⟨C2, N2, h2⟩ := erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail hup
  obtain ⟨C3, N3, h3⟩ := erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part
  refine ⟨C1 + C2 + C3, max N1 (max N2 N3), ?_⟩
  intro n hn A hA hbox
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have b1 := h1 n hn1
  have b2 := h2 n hn2
  have b3 := h3 n hn3 A hA hbox
  have hsub : A ⊆ erdosRough n ∪ erdosSmoothTail n ∪
      (A \ (erdosRough n ∪ erdosSmoothTail n)) := by
    intro a ha
    by_cases h : a ∈ erdosRough n ∪ erdosSmoothTail n
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
  have hc : A.card ≤ (erdosRough n).card + (erdosSmoothTail n).card +
      (A \ (erdosRough n ∪ erdosSmoothTail n)).card := by
    have k1 := Finset.card_le_card hsub
    have k2 := Finset.card_union_le (erdosRough n ∪ erdosSmoothTail n)
      (A \ (erdosRough n ∪ erdosSmoothTail n))
    have k3 := Finset.card_union_le (erdosRough n) (erdosSmoothTail n)
    omega
  have hcR : (A.card : ℝ) ≤ ((erdosRough n).card : ℝ) + ((erdosSmoothTail n).card : ℝ) +
      ((A \ (erdosRough n ∪ erdosSmoothTail n)).card : ℝ) := by
    exact_mod_cast hc
  have e : (C1 + C2 + C3) * ((n : ℝ) * Real.log (Real.log n) / Real.log n) =
      C1 * ((n : ℝ) * Real.log (Real.log n) / Real.log n)
      + C2 * ((n : ℝ) * Real.log (Real.log n) / Real.log n)
      + C3 * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by ring
  rw [e]
  linarith

end erdos_41635_hyp_upper_hyp_box_to_bound_ns

theorem erdos_41635_hyp_upper_hyp_box_to_bound : ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A →
    (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  exact erdos_41635_hyp_upper_hyp_box_to_bound_ns.erdos_41635_hyp_upper_hyp_box_to_bound

-- CHECK: Real.exp_one_lt_d9 Real.log_le_log Real.log_exp Real.log_nonneg one_div_pos
open scoped Classical

open Filter

theorem erdos_41635_hyp_upper : ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ,
    ErdosValid41635 A n →
    (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  obtain ⟨C, N, hCN⟩ := erdos_41635_hyp_upper_hyp_box_to_bound
  refine ⟨C, N, fun n hn A hA => ?_⟩
  have hpf : erdosPaschFree A := erdos_41635_hyp_upper_hyp_pasch A n hA.1 hA.2
  have hbox : erdosBoxSparse A := by
    unfold erdosBoxSparse
    intro X Y Z
    have h1 := erdos_41635_hyp_upper_hyp_octa_cs X Y Z (erdosBoxTriples A X Y Z)
      (Finset.filter_subset _ _)
    have h2 := erdos_41635_hyp_upper_hyp_hom_upper A hpf X Y Z
    exact le_trans h1 (Nat.mul_le_mul h2 le_rfl)
  exact hCN n hn A hA.1 hbox
end erdos_41635_hyp_upper_ns

theorem erdos_41635_hyp_upper : ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ,
    ErdosValid41635 A n →
    (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  exact erdos_41635_hyp_upper_ns.erdos_41635_hyp_upper



theorem erdos_41635_hyp_sq_cancel : ∀ x y z : ℕ, 0 < x → IsSquare (x ^ 2 * (y * z)) →
    IsSquare (y * z) := by
  exact erdos_41635_hyp_sq_cancel_ns.erdos_41635_hyp_sq_cancel

theorem erdos_41635_hyp_Sn_valid : ∀ n : ℕ, ErdosValid41635 (erdosSpq n) n := by
  exact erdos_41635_hyp_Sn_valid_ns.erdos_41635_hyp_Sn_valid

theorem erdos_41635_hyp_mertens_lower : ∀ x : ℝ, 1 < x →
    Real.log (Real.log x) - 1 <
      ∑ q ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 / (q : ℝ)) := by
  exact erdos_41635_hyp_mertens_lower_ns.erdos_41635_hyp_mertens_lower

namespace erdos_41635_hyp_Sn_card_lower_ns
-- CHECK: Finset.card_le_card_of_injOn Nat.Prime.dvd_mul Nat.prime_dvd_prime_iff_eq Nat.eq_of_mul_eq_mul_left
-- LOOGLE: Nat.primeCounting, Real.log
-- GREP: theorem .*primeCounting.*log
open scoped Classical

open Filter

private noncomputable def pairSet (n y : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (y+1)).filter Nat.Prime) ×ˢ ((Finset.range (n+1)).filter Nat.Prime)).filter
    (fun pq => y < pq.2 ∧ pq.1 * pq.2 ≤ n)

private lemma card_pairSet_le (n y : ℕ) : (pairSet n y).card ≤ (erdosSpq n).card := by
  apply Finset.card_le_card_of_injOn (fun pq : ℕ × ℕ => pq.1 * pq.2)
  · intro x hx
    simp only [Finset.mem_coe, pairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hx
    obtain ⟨⟨⟨hp1, hp⟩, ⟨hq1, hq⟩⟩, hyq, hle⟩ := hx
    simp only [Finset.mem_coe, erdosSpq, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨Nat.mul_pos hp.pos hq.pos, hle⟩, x.1, x.2, hp, hq, by omega, rfl⟩
  · intro x hx x' hx' hxx
    simp only [Finset.mem_coe, pairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hx hx'
    obtain ⟨⟨⟨hp1, hp⟩, ⟨hq1, hq⟩⟩, hyq, hle⟩ := hx
    obtain ⟨⟨⟨hp1', hp'⟩, ⟨hq1', hq'⟩⟩, hyq', hle'⟩ := hx'
    have hxx' : x.1 * x.2 = x'.1 * x'.2 := hxx
    have hdvd : x.1 ∣ x'.1 * x'.2 := by
      rw [← hxx']
      exact dvd_mul_right _ _
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have e1 : x.1 = x'.1 := (Nat.prime_dvd_prime_iff_eq hp hp').mp h
      have e2 : x.2 = x'.2 := by
        rw [e1] at hxx'
        exact Nat.eq_of_mul_eq_mul_left hp'.pos hxx'
      exact Prod.ext e1 e2
    · have e1 : x.1 = x'.2 := (Nat.prime_dvd_prime_iff_eq hp hq').mp h
      exfalso
      omega

private lemma card_pairSet_eq_sum (n y : ℕ) :
    (pairSet n y).card = ∑ q ∈ (Finset.range (y+1)).filter Nat.Prime,
      ((Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ q * r ≤ n)).card := by
  unfold pairSet
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h1 : r.Prime <;> by_cases h2 : (y < r ∧ q * r ≤ n) <;> simp [h1, h2]

private lemma log_le_harm (M : ℕ) (hM : 1 ≤ M) :
    Real.log M ≤ ∑ i ∈ Finset.Ico 1 M, (i:ℝ)⁻¹ := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk]
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have : Real.log ((k+1:ℕ):ℝ) ≤ Real.log k + (k:ℝ)⁻¹ := by
      have h1 : ((k+1:ℕ):ℝ) = k * (1 + (k:ℝ)⁻¹) := by push_cast; field_simp
      rw [h1, Real.log_mul hk0.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + (k:ℝ)⁻¹ by positivity)
      linarith
    linarith

private noncomputable def invHom : ℕ →* ℝ where
  toFun m := (m:ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv]

private lemma mertens_weak (M : ℕ) (hM : 2 ≤ M) :
    Real.log (Real.log M) ≤ 2 * ∑ p ∈ M.primesBelow, (1 / (p:ℝ)) := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
    rw [inv_lt_one₀ (by linarith)]; linarith
  obtain ⟨-, hS⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hnorm M
  have hS' := (hasSum_subtype_iff_indicator).mp hS
  have h1 : ∑ i ∈ Finset.Ico 1 M, (i:ℝ)⁻¹ ≤ ∏ p ∈ M.primesBelow, (1 - invHom p)⁻¹ := by
    have := sum_le_hasSum (Finset.Ico 1 M) (fun i _ => ?_) hS'
    · refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_Ico] at hi
      rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (by omega) hi.2)]
      rfl
    · by_cases h : i ∈ M.smoothNumbers
      · rw [Set.indicator_of_mem h]
        simp [invHom]
      · rw [Set.indicator_of_notMem h]
  have h2 : ∏ p ∈ M.primesBelow, (1 - invHom p)⁻¹ ≤
      Real.exp (∑ p ∈ M.primesBelow, 2 * (1 / (p:ℝ))) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
      have ht : (p:ℝ)⁻¹ ≤ 1/2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by linarith
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]
      positivity
    · intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
      have ht : (p:ℝ)⁻¹ ≤ 1/2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have ht0 : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
      have hpos : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by linarith
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]
      have h3 : (1 - (p:ℝ)⁻¹)⁻¹ ≤ 1 + 2 * (p:ℝ)⁻¹ := by
        rw [← one_div, div_le_iff₀ hpos]; nlinarith
      have h4 := Real.add_one_le_exp (2 * (1 / (p:ℝ)))
      rw [one_div] at h4 ⊢
      linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have h3 := (log_le_harm M (by omega)).trans (h1.trans h2)
  have h4 := Real.log_le_log hlogM h3
  rw [Real.log_exp, ← Finset.mul_sum] at h4
  exact h4

private lemma cheb (m : ℕ) :
    (m:ℝ) * Real.log 2 - Real.log (m + 1) ≤ (Nat.primeCounting m : ℝ) * Real.log m :=
  (Chebyshev.psi_ge m).trans (Chebyshev.psi_le_primeCounting_mul_log m)

private lemma fiber_card (n y p : ℕ) :
    Nat.primeCounting (n / p) ≤
      (y + 1) + ((Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc (Nat.primesLE (n/p)).card ≤ (Finset.range (y+1) ∪
        (Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Nat.mem_primesLE] at hr
        rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
        by_cases hry : r ≤ y
        · left; omega
        · right
          have h1 : p * r ≤ p * (n / p) := Nat.mul_le_mul_left p hr.1
          have h2 : p * (n / p) ≤ n := Nat.mul_div_le n p
          have h3 : r ≤ n := hr.1.trans (Nat.div_le_self n p)
          exact ⟨by omega, hr.2, by omega, by omega⟩
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans ?_
        rw [Finset.card_range]

private lemma fiber_real (n y p : ℕ) (hp : 0 < p) (hn : 1 ≤ n) :
    (n:ℝ) / p * Real.log 2 - Real.log 2 - Real.log (n + 1) ≤
      ((((Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card : ℝ)
        + (y + 1 : ℝ)) * Real.log n := by
  have hc := cheb (n / p)
  have hf : ((Nat.primeCounting (n / p) : ℕ) : ℝ) ≤ (y+1 : ℝ) +
      (((Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card : ℝ) := by
    exact_mod_cast fiber_card n y p
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogm : Real.log ((n / p : ℕ) : ℝ) ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos (n / p) with h0 | h0
    · rw [h0]; simpa using hL
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.div_le_self n p)
  have hnat : n ≤ (n / p + 1) * p := by
    have := Nat.div_add_mod n p
    have := Nat.mod_lt n hp
    nlinarith
  have hmp : (n:ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hp)]
    exact_mod_cast hnat
  have hlog1 : Real.log (((n / p : ℕ) : ℝ) + 1) ≤ Real.log ((n:ℝ) + 1) :=
    Real.log_le_log (by positivity) (by
      have : ((n / p : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n p
      linarith)
  have hpc : (0:ℝ) ≤ (Nat.primeCounting (n / p) : ℝ) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 := mul_le_mul_of_nonneg_left hlogm hpc
  have e2 := mul_le_mul_of_nonneg_right hf hL
  have e3 := mul_le_mul_of_nonneg_right hmp hl2.le
  nlinarith

private lemma analytic_pairs : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * ((n : ℝ) * Real.log (Real.log n) / Real.log n) ≤
      ((pairSet n (Nat.sqrt (Nat.sqrt n))).card : ℝ) := by
  refine ⟨1/8, by norm_num, max ⌈Real.exp (Real.exp 6)⌉₊ (601^4), fun n hn => ?_⟩
  set y := Nat.sqrt (Nat.sqrt n) with hy
  have hn1 : 601^4 ≤ n := le_of_max_le_right hn
  have hn2 : Real.exp (Real.exp 6) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left hn)
  have hs1 := Nat.sqrt_le' n
  have hs2 := Nat.lt_succ_sqrt' n
  have hy1 := Nat.sqrt_le' (Nat.sqrt n)
  have hy2 := Nat.lt_succ_sqrt' (Nat.sqrt n)
  have hyn : y^4 ≤ n := by
    have : (y^2)^2 ≤ (Nat.sqrt n)^2 := Nat.pow_le_pow_left hy1 2
    calc y^4 = (y^2)^2 := by ring
      _ ≤ _ := this
      _ ≤ n := hs1
  have hny : n < (y+1)^4 := by
    have h1 : Nat.sqrt n + 1 ≤ (y+1)^2 := hy2
    have : (Nat.sqrt n + 1)^2 ≤ ((y+1)^2)^2 := Nat.pow_le_pow_left h1 2
    calc n < (Nat.sqrt n + 1)^2 := hs2
      _ ≤ ((y+1)^2)^2 := this
      _ = (y+1)^4 := by ring
  have hy600 : 600 ≤ y := by
    by_contra h
    push_neg at h
    have : (y+1)^4 ≤ 601^4 := Nat.pow_le_pow_left (by omega) 4
    omega
  -- real quantities
  set P := (Finset.range (y+1)).filter Nat.Prime with hP
  set S := ∑ p ∈ P, (1 / (p:ℝ)) with hSdef
  set L := Real.log n with hLdef
  set Y : ℝ := (y:ℝ) + 1 with hYdef
  have hyR : (600:ℝ) ≤ y := by exact_mod_cast hy600
  have hnpos : (0:ℝ) < n := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hynR : (y:ℝ)^4 ≤ n := by exact_mod_cast hyn
  have hnyR : (n:ℝ) < Y^4 := by rw [hYdef]; exact_mod_cast hny
  have hL6 : Real.exp 6 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hn2
    rwa [Real.log_exp] at this
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 6) hL6
  have hLL : 6 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hL6
    rwa [Real.log_exp] at this
  have hLY : L ≤ 4 * Real.log Y := by
    have := Real.log_le_log hnpos hnyR.le
    rwa [Real.log_pow] at this
  have hlogY : Real.log Y ≤ Y := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < Y by positivity)
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hmert : Real.log (Real.log Y) ≤ 2 * S := by
    have := mertens_weak (y+1) (by omega)
    push_cast at this
    exact this
  have hLLY : Real.log L - Real.log 4 ≤ Real.log (Real.log Y) := by
    rw [← Real.log_div hLpos.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hS : (Real.log L - 1.4) / 2 ≤ S := by linarith
  -- the summed fiber bound
  have hk : (P.card : ℝ) ≤ Y := by
    have : P.card ≤ y + 1 := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    rw [hYdef]; exact_mod_cast this
  have hsum := Finset.sum_le_sum (fun p (hp : p ∈ P) =>
    fiber_real n y p (Nat.prime_of_mem_primesBelow hp).pos (by omega))
  have hcard : ((pairSet n y).card : ℝ) = ∑ p ∈ P,
      (((Finset.range (n+1)).filter (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card : ℝ) := by
    rw [card_pairSet_eq_sum]; push_cast; rfl
  have hLHS : ∑ p ∈ P, ((n:ℝ) / p * Real.log 2 - Real.log 2 - Real.log (n + 1)) =
      n * Real.log 2 * S - P.card * (Real.log 2 + Real.log (n + 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hSdef, Finset.mul_sum]
    have : ∀ p ∈ P, (n:ℝ) / p * Real.log 2 = n * Real.log 2 * (1 / p) := fun p _ => by ring
    rw [Finset.sum_congr rfl this]; ring
  have hRHS : ∑ p ∈ P, ((((Finset.range (n+1)).filter
      (fun r => r.Prime ∧ y < r ∧ p * r ≤ n)).card : ℝ) + ((y:ℝ) + 1)) * L =
      ((pairSet n y).card : ℝ) * L + P.card * Y * L := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  rw [hLHS, hRHS] at hsum
  -- auxiliary estimates
  have hn2R : (2:ℝ) ≤ n := by linarith [show (600:ℝ)^4 ≤ (y:ℝ)^4 by gcongr]
  have hlogn1 : Real.log ((n:ℝ) + 1) ≤ 2 * L := by
    have h2 : (n:ℝ) + 1 ≤ (n:ℝ)^2 := by nlinarith
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hl2L : Real.log 2 ≤ L := by
    have : (2:ℝ) ≤ n := by linarith [show (600:ℝ)^4 ≤ (y:ℝ)^4 by gcongr]
    exact Real.log_le_log (by norm_num) this
  have hY1 : 1 ≤ Y := by linarith
  have hE : P.card * (Real.log 2 + Real.log (n + 1)) + P.card * Y * L ≤ 4 * Y^2 * L := by
    have hk0 : (0:ℝ) ≤ P.card := by positivity
    have e1 : P.card * (Real.log 2 + Real.log (n + 1)) ≤ Y * (3 * L) := by
      have : Real.log 2 + Real.log (n + 1) ≤ 3 * L := by linarith
      have hpos : 0 ≤ Real.log 2 + Real.log (n + 1) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ n + 1 by linarith); linarith
      calc _ ≤ Y * (Real.log 2 + Real.log (n + 1)) := mul_le_mul_of_nonneg_right hk hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by linarith)
    have e2 : P.card * Y * L ≤ Y * Y * L := by
      have := mul_le_mul_of_nonneg_right hk (show 0 ≤ Y * L by positivity)
      nlinarith
    nlinarith
  have hYL : 4 * Y^2 * L ≤ 16 * Y^3 := by
    have : L ≤ 4 * Y := by linarith
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 4 * Y^2 by positivity)
    nlinarith
  have hY3 : 16 * Y^3 ≤ (4/5) * n := by
    have h2y : Y ≤ 2 * y := by linarith
    have : Y^3 ≤ (2 * (y:ℝ))^3 := by gcongr
    have : 600 * (y:ℝ)^3 ≤ (y:ℝ)^4 := by
      have := mul_le_mul_of_nonneg_right hyR (show (0:ℝ) ≤ (y:ℝ)^3 by positivity)
      nlinarith
    nlinarith
  have hnLL : 6 * (n:ℝ) ≤ n * Real.log L := by nlinarith
  have hA : n * Real.log 2 * ((Real.log L - 1.4) / 2) ≤ n * Real.log 2 * S :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have hA2 : 0 ≤ (Real.log 2 - 0.69) * (n * (Real.log L - 1.4)) := by
    apply mul_nonneg
    · linarith
    · apply mul_nonneg hnpos.le; linarith
  rw [show (1:ℝ)/8 * ((n:ℝ) * Real.log L / L) = ((n:ℝ) * Real.log L / 8) / L by ring,
    div_le_iff₀ hLpos]
  nlinarith

theorem erdos_41635_hyp_Sn_card_lower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * ((n : ℝ) * Real.log (Real.log n) / Real.log n) ≤ ((erdosSpq n).card : ℝ) := by
  obtain ⟨c, hc, N, hN⟩ := analytic_pairs
  refine ⟨c, hc, N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : ((pairSet n (Nat.sqrt (Nat.sqrt n))).card : ℝ) ≤ ((erdosSpq n).card : ℝ) := by
    exact_mod_cast card_pairSet_le n _
  linarith
end erdos_41635_hyp_Sn_card_lower_ns

theorem erdos_41635_hyp_Sn_card_lower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * ((n : ℝ) * Real.log (Real.log n) / Real.log n) ≤ ((erdosSpq n).card : ℝ) := by
  exact erdos_41635_hyp_Sn_card_lower_ns.erdos_41635_hyp_Sn_card_lower



theorem erdos_41635 :
    (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  have h0 : ∀ n : ℕ, p n 0 := fun n =>
    ⟨∅, ⟨Finset.empty_subset _, fun a ha => by simp at ha⟩, Finset.card_empty⟩
  apply Asymptotics.IsBigO.antisymm
  · obtain ⟨C, N, hC⟩ := erdos_41635_hyp_upper
    apply Asymptotics.IsBigO.of_bound |C|
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    obtain ⟨A, hA, hcard⟩ := Nat.findGreatest_spec (P := p n) (Nat.zero_le n) (h0 n)
    have hAv : ErdosValid41635 A n := hA
    have hb := hC n hn A hAv
    have hc' : (A.card : ℝ) = (Nat.findGreatest (p n) n : ℝ) := by exact_mod_cast hcard
    have hf : (0:ℝ) ≤ (Nat.findGreatest (p n) n : ℝ) := Nat.cast_nonneg _
    have e1 := abs_of_nonneg hf
    have e2 := le_abs_self (C * ((n : ℝ) * Real.log (Real.log n) / Real.log n))
    have e3 : |C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)|
        = |C| * |(n : ℝ) * Real.log (Real.log n) / Real.log n| := abs_mul _ _
    simp only [Real.norm_eq_abs]
    linarith
  · obtain ⟨c, hc, N, hN⟩ := erdos_41635_hyp_Sn_card_lower
    apply Asymptotics.IsBigO.of_bound (1 / c)
    filter_upwards [Filter.eventually_ge_atTop (max N 16)] with n hn
    have hnN : N ≤ n := le_of_max_le_left hn
    have hn16 : 16 ≤ n := le_of_max_le_right hn
    have hlow := hN n hnN
    have hnR : (16:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn16
    have he : Real.exp 1 ≤ (n:ℝ) := by
      first
      | linarith [Real.exp_one_lt_d9]
      | (have h := Real.exp_one_lt_d9
         norm_num at h
         linarith)
    have hlog1 : 1 ≤ Real.log (n:ℝ) := by
      have h := Real.log_le_log (Real.exp_pos 1) he
      rwa [Real.log_exp] at h
    have hpos : 0 ≤ (n : ℝ) * Real.log (Real.log n) / Real.log n :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hlog1)) (by linarith)
    have hval : RequiredCondition (erdosSpq n) n := erdos_41635_hyp_Sn_valid n
    have hle : (erdosSpq n).card ≤ n := by
      have := Finset.card_le_card hval.1
      simpa using this
    have hfg : (erdosSpq n).card ≤ Nat.findGreatest (p n) n :=
      Nat.le_findGreatest hle ⟨erdosSpq n, hval, rfl⟩
    have hfg' : ((erdosSpq n).card : ℝ) ≤ (Nat.findGreatest (p n) n : ℝ) := by
      exact_mod_cast hfg
    have hci : (0:ℝ) ≤ 1 / c := le_of_lt (one_div_pos.mpr hc)
    have h1 := mul_le_mul_of_nonneg_left hlow hci
    have h3 := mul_le_mul_of_nonneg_left hfg' hci
    have h2 : 1 / c * (c * ((n : ℝ) * Real.log (Real.log n) / Real.log n)) =
        (n : ℝ) * Real.log (Real.log n) / Real.log n := by
      first
      | (rw [← mul_assoc, one_div_mul_cancel hc.ne', one_mul])
      | (field_simp)
    have hf : (0:ℝ) ≤ (Nat.findGreatest (p n) n : ℝ) := Nat.cast_nonneg _
    have e1 := abs_of_nonneg hf
    have e2 := abs_of_nonneg hpos
    have e3 : 1 / c * |(Nat.findGreatest (p n) n : ℝ)| =
        1 / c * (Nat.findGreatest (p n) n : ℝ) := by rw [e1]
    simp only [Real.norm_eq_abs]
    linarith
