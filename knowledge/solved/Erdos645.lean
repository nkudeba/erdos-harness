import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic

set_option maxHeartbeats 1000000

private lemma no_mono {c : ℕ → Bool}
    (H : ∀ x d, 0 < x → x < d → c x = c (x + d) → c (x + d) ≠ c (x + 2 * d))
    (x d a b : ℕ) (hx : 0 < x) (hd : x < d) (ha : a = x + d) (hb : b = x + 2 * d) :
    ¬ (c x = c a ∧ c a = c b) := by
  subst ha hb
  intro h
  exact H x d hx hd h.1 h.2

private lemma key (c : ℕ → Bool)
    (H : ∀ x d, 0 < x → x < d → c x = c (x + d) → c (x + d) ≠ c (x + 2 * d))
    (hc1 : c 1 = true) : False := by
  have blue_odd : ∀ n, 3 ≤ n → c n = true → c (2 * n - 1) = false := by
    intro n hn hcn
    have h := no_mono H 1 (n - 1) n (2 * n - 1) (by omega) (by omega) (by omega) (by omega)
    cases h' : c (2 * n - 1) with
    | false => rfl
    | true => exact (h ⟨hc1.trans hcn.symm, hcn.trans h'.symm⟩).elim
  have h0 := no_mono H 1 2 3 5 (by omega) (by omega) (by omega) (by omega)
  cases h3 : c 3 with
  | false =>
    have stepA : ∀ n, 6 ≤ n → c n = true → c (n + 1) = true := by
      intro n hn hcn
      have hb := blue_odd n (by omega) hcn
      have h := no_mono H 3 (n - 2) (n + 1) (2 * n - 1) (by omega) (by omega) (by omega) (by omega)
      cases h' : c (n + 1) with
      | true => rfl
      | false => exact (h ⟨h3.trans h'.symm, h'.trans hb.symm⟩).elim
    by_cases hex : ∃ n₀, 6 ≤ n₀ ∧ c n₀ = true
    · obtain ⟨n₀, hn₀, hcn₀⟩ := hex
      have hall : ∀ j, c (n₀ + j) = true := by
        intro j
        induction j with
        | zero => exact hcn₀
        | succ j ih =>
          rw [← Nat.add_assoc]
          exact stepA (n₀ + j) (by omega) ih
      exact H n₀ (n₀ + 1) (by omega) (by omega) (hcn₀.trans (hall (n₀ + 1)).symm)
        ((hall (n₀ + 1)).trans (hall (2 * (n₀ + 1))).symm)
    · have hf : ∀ n, 6 ≤ n → c n = false := by
        intro n hn
        cases h : c n with
        | false => rfl
        | true => exact (hex ⟨n, hn, h⟩).elim
      have h := no_mono H 6 7 13 20 (by omega) (by omega) (by omega) (by omega)
      exact h ⟨(hf 6 (by omega)).trans (hf 13 (by omega)).symm,
        (hf 13 (by omega)).trans (hf 20 (by omega)).symm⟩
  | true =>
    cases h5 : c 5 with
    | true => exact (h0 ⟨hc1.trans h3.symm, h3.trans h5.symm⟩).elim
    | false =>
      have stepB : ∀ n, 9 ≤ n → c n = true → c (n + 2) = true := by
        intro n hn hcn
        have hb := blue_odd n (by omega) hcn
        have h := no_mono H 5 (n - 3) (n + 2) (2 * n - 1) (by omega) (by omega) (by omega) (by omega)
        cases h' : c (n + 2) with
        | true => rfl
        | false => exact (h ⟨h5.trans h'.symm, h'.trans hb.symm⟩).elim
      by_cases hex : ∃ n₀, 9 ≤ n₀ ∧ c n₀ = true
      · obtain ⟨n₀, hn₀, hcn₀⟩ := hex
        have hall : ∀ j, c (n₀ + 2 * j) = true := by
          intro j
          induction j with
          | zero => simpa using hcn₀
          | succ j ih =>
            rw [show n₀ + 2 * (j + 1) = n₀ + 2 * j + 2 by omega]
            exact stepB (n₀ + 2 * j) (by omega) ih
        exact H n₀ (2 * n₀) (by omega) (by omega) (hcn₀.trans (hall n₀).symm)
          ((hall n₀).trans (hall (2 * n₀)).symm)
      · have hf : ∀ n, 9 ≤ n → c n = false := by
          intro n hn
          cases h : c n with
          | false => rfl
          | true => exact (hex ⟨n, hn, h⟩).elim
        have h := no_mono H 9 10 19 29 (by omega) (by omega) (by omega) (by omega)
        exact h ⟨(hf 9 (by omega)).trans (hf 19 (by omega)).symm,
          (hf 19 (by omega)).trans (hf 29 (by omega)).symm⟩

theorem erdos_645 (c : ℕ → Bool) :
    ∃ x d : ℕ, 0 < x ∧ x < d ∧ c x = c (x + d) ∧ c (x + d) = c (x + 2 * d) := by
  by_contra hcon
  have H : ∀ x d, 0 < x → x < d → c x = c (x + d) → c (x + d) ≠ c (x + 2 * d) := by
    intro x d hx hd h1 h2
    exact hcon ⟨x, d, hx, hd, h1, h2⟩
  cases hc1 : c 1 with
  | true => exact key c H hc1
  | false =>
    have H' : ∀ x d, 0 < x → x < d → (!c x) = (!c (x + d)) →
        (!c (x + d)) ≠ (!c (x + 2 * d)) := by
      intro x d hx hd h1 h2
      exact H x d hx hd (Bool.not_inj h1) (Bool.not_inj h2)
    exact key (fun n => !c n) H' (by simp [hc1])
