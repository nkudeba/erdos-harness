-- CHECK: Set.finite_of_ncard_ne_zero le_ciInf Filter.tendsto_atTop_atTop Set.ncard_insert_of_notMem Set.Finite.insert Set.mem_insert_iff
open scoped Pointwise

def erdos_54847_SidonNat (A : Set ℕ) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

noncomputable def erdos_54847_isoCount (A : Set ℕ) : ℕ :=
  {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard

def erdos_54847_posDiff (A : Set ℕ) : Set ℕ :=
  {t : ℕ | ∃ a ∈ A, ∃ b ∈ A, b < a ∧ t = a - b}

noncomputable def erdos_54847_diffRunStarts (A : Set ℕ) : ℕ :=
  {t : ℕ | t ∈ erdos_54847_posDiff A ∧ t - 1 ∉ erdos_54847_posDiff A}.ncard

-- DERIVED (sum-difference duality): Σ_s r(s)r(s+1) = Σ_t δ(t)δ(t+1) (both count a+b+1=c+d).
-- For Sidon A: iso_Z = n + R₊ − Q − n[1∈A−A] + X with Q ≤ 2n, X ≥ 0, and the ℕ-truncation
-- at s = 0 costs at most 1 (R1). Exhaustively checked for diameter ≤ 51 plus ET, Bose, Ruzsa, random sets.
theorem erdos_54847_hyp_duality :
    ∀ A : Set ℕ, A.Finite → erdos_54847_SidonNat A →
      erdos_54847_diffRunStarts A ≤ erdos_54847_isoCount A + 2 * A.ncard + 1 := by
  sorry

-- CORE (empirical, Π₁ form with explicit constants): the positive difference set of an n-element
-- Sidon set has at least 3n − 64 maximal runs. Vacuous for n ≤ 21. Evidence: over families
-- (ET p<80, Bose q ≤ 23, Ruzsa p ≤ 47) and local search, min (R₊ − 3n) over n ≥ 22 is −11 (Bose q=23),
-- slack 53; Ruzsa families give R₊ ≈ 0.13 n².
theorem erdos_54847_hyp_gap_linear :
    ∀ A : Set ℕ, A.Finite → erdos_54847_SidonNat A →
      3 * A.ncard ≤ erdos_54847_diffRunStarts A + 64 := by
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

theorem erdos_54847 :
    Tendsto f atTop atTop := by
  have key : ∀ n : ℕ, ∃ A : Set ℕ, ∃ m : ℕ, A.Finite ∧ A.ncard = n ∧
      (∀ a ∈ A, a ≤ m) ∧ erdos_54847_SidonNat A := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, 0, Set.finite_empty, by simp, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro i₁ hi₁
        simp at hi₁
    | succ k ih =>
      obtain ⟨A, m, hfin, hcard, hbd, hS⟩ := ih
      have hx : (2 * m + 1) ∉ A := fun h => by
        have := hbd _ h
        omega
      refine ⟨insert (2 * m + 1) A, 2 * m + 1, hfin.insert _, ?_, ?_, ?_⟩
      · rw [Set.ncard_insert_of_notMem hx hfin, hcard]
      · intro a ha
        rw [Set.mem_insert_iff] at ha
        rcases ha with h | h
        · omega
        · have := hbd a h
          omega
      · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
        rw [Set.mem_insert_iff] at hi₁ hj₁ hi₂ hj₂
        rcases hi₁ with h1 | h1 <;> rcases hj₁ with h2 | h2 <;>
          rcases hi₂ with h3 | h3 <;> rcases hj₂ with h4 | h4
        all_goals first
          | exact hS _ h1 _ h2 _ h3 _ h4 h
          | ((try have b1 := hbd _ h1); (try have b2 := hbd _ h2);
             (try have b3 := hbd _ h3); (try have b4 := hbd _ h4); omega)
  rw [Filter.tendsto_atTop_atTop]
  intro M
  refine ⟨M + 65, fun n hn => ?_⟩
  obtain ⟨A₀, m₀, _, hA₀, _, hS₀⟩ := key n
  haveI : Nonempty {A : Set ℕ | A.ncard = n ∧ IsSidon A} :=
    ⟨⟨A₀, show A₀.ncard = n ∧ IsSidon A₀ from ⟨hA₀, hS₀⟩⟩⟩
  unfold f
  apply le_ciInf
  intro A
  have hmem : A.1.ncard = n ∧ IsSidon A.1 := A.2
  have hcard : A.1.ncard = n := hmem.1
  have hne : A.1.ncard ≠ 0 := by omega
  have hfin : A.1.Finite := Set.finite_of_ncard_ne_zero hne
  have hS : erdos_54847_SidonNat A.1 := hmem.2
  have h1 := erdos_54847_hyp_gap_linear A.1 hfin hS
  have h2 := erdos_54847_hyp_duality A.1 hfin hS
  have h3 : M ≤ erdos_54847_isoCount A.1 := by omega
  exact h3