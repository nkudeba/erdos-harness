import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

private def erdos_198_f (n : ℕ) : ℕ := Nat.factorial (n + 1) + n

private lemma erdos_198_step (n : ℕ) :
    2 * erdos_198_f n < erdos_198_f (n + 1) := by
  unfold erdos_198_f
  rw [Nat.factorial_succ (n + 1)]
  have h1 : 0 < Nat.factorial (n + 1) := Nat.factorial_pos (n + 1)
  have h2 : n * 1 ≤ n * Nat.factorial (n + 1) := Nat.mul_le_mul (le_refl n) h1
  nlinarith [h1, h2]

private lemma erdos_198_mono : StrictMono erdos_198_f := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := erdos_198_step n
  omega

private lemma erdos_198_double {i j : ℕ} (h : i < j) :
    2 * erdos_198_f i < erdos_198_f j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h1 : erdos_198_f i ≤ erdos_198_f k := erdos_198_mono.monotone (by omega)
  have h2 := erdos_198_step k
  omega

private lemma erdos_198_sidon_aux (i j k l : ℕ) (hij : i ≤ j) (hkl : k ≤ l)
    (h : erdos_198_f i + erdos_198_f j = erdos_198_f k + erdos_198_f l) :
    i = k ∧ j = l := by
  have hmono := erdos_198_mono
  have hjl : j = l := by
    rcases lt_trichotomy j l with hlt | heq | hgt
    · exfalso
      have h1 := erdos_198_double hlt
      have h2 : erdos_198_f i ≤ erdos_198_f j := hmono.monotone hij
      omega
    · exact heq
    · exfalso
      have h1 := erdos_198_double hgt
      have h2 : erdos_198_f k ≤ erdos_198_f l := hmono.monotone hkl
      omega
  subst hjl
  have hik : erdos_198_f i = erdos_198_f k := by omega
  exact ⟨hmono.injective hik, rfl⟩

private lemma erdos_198_sidon (i j k l : ℕ)
    (h : erdos_198_f i + erdos_198_f j = erdos_198_f k + erdos_198_f l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  rcases le_total i j with hij | hij <;> rcases le_total k l with hkl | hkl
  · exact Or.inl (erdos_198_sidon_aux i j k l hij hkl h)
  · have := erdos_198_sidon_aux i j l k hij hkl (by omega)
    exact Or.inr ⟨this.1, this.2⟩
  · have := erdos_198_sidon_aux j i k l hij hkl (by omega)
    exact Or.inr ⟨this.2, this.1⟩
  · have := erdos_198_sidon_aux j i l k hij hkl (by omega)
    exact Or.inl ⟨this.2, this.1⟩

private lemma erdos_198_ap (a d : ℕ) (hd : 0 < d) :
    ∃ t, a + t * d = erdos_198_f (a + d) := by
  have hdvd : d ∣ Nat.factorial (a + d + 1) := Nat.dvd_factorial hd (by omega)
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q + 1, ?_⟩
  unfold erdos_198_f
  rw [hq]
  ring

theorem erdos_198 :
    ∃ A : Set ℕ,
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      (∀ a d : ℕ, 0 < d → ∃ t : ℕ, a + t * d ∈ A) := by
  refine ⟨Set.range erdos_198_f, ?_, ?_⟩
  · intro a ha b hb c hc d hd h
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hb
    obtain ⟨k, rfl⟩ := Set.mem_range.mp hc
    obtain ⟨l, rfl⟩ := Set.mem_range.mp hd
    rcases erdos_198_sidon i j k l h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  · intro a d hd
    obtain ⟨t, ht⟩ := erdos_198_ap a d hd
    refine ⟨t, ?_⟩
    rw [ht]
    exact Set.mem_range_self _
