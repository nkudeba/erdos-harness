def IsAdmissibleSet (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ c : ℕ, ∀ h ∈ H, h % p ≠ c % p

def ConsecutivePrimesInTuples : Prop :=
  ∀ m : ℕ, ∃ K : ℕ, ∀ H : Finset ℕ, K ≤ H.card → IsAdmissibleSet H →
    ∀ N : ℕ, ∃ n ≥ N, ∃ r : ℕ, ∀ j ∈ Finset.Ioc r (r + m),
      n ≤ Nat.nth Nat.Prime j ∧ Nat.nth Nat.Prime j - n ∈ H

def HasQuarterClusters (x : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ r : ℕ, ∃ a : ℝ, 0 ≤ a ∧ a + 1/4 ≤ 1 ∧
    letI I := Set.Ico a (a + 1/4)
    let count := (Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ I)
    (m : ℝ) ≤ 2 * (count.card : ℝ)

def PrimeFractClusters : Prop :=
  ∀ α : ℝ, HasQuarterClusters (fun n ↦ Int.fract (α * (n.nth Nat.Prime)))

-- PUBLISHED: W. D. Banks, T. Freiberg, C. L. Turnage-Butterbaugh, "Consecutive primes in tuples",
-- Acta Arith. 167 (2015), Theorem 1 (via Maynard's sieve): for every m, if K is large in terms of m,
-- every admissible K-tuple has infinitely many translates containing m consecutive primes.
theorem erdos_96567_hyp_bftb : ConsecutivePrimesInTuples := by
  sorry

-- Derived: given m, take K from BFTB, N := K!, and by Dirichlet q ≥ 1 with ‖q N α‖ < 1/(8K).
-- H = {i q N : 1 ≤ i ≤ K} is admissible: primes p ≤ K divide every element, so class 1 is missed;
-- primes p > K see at most K < p classes. The m consecutive primes then differ pairwise by t q N
-- with |t| < K. So their fractional parts lie in a circular arc of length ≤ 1/4. Such an arc meets
-- at most two of the intervals [l/4, (l+1)/4), so one of them holds ≥ m/2 of the values.
namespace erdos_96567_hyp_reduction_ns
open Set

private lemma fract_arc (c : ℝ) : ∃ a1 a2 : ℝ, 0 ≤ a1 ∧ a1 + 1/4 ≤ 1 ∧ 0 ≤ a2 ∧ a2 + 1/4 ≤ 1 ∧
    ∀ t : ℝ, |t| < 1/8 → Int.fract (c + t) ∈ Set.Ico a1 (a1 + 1/4) ∨
      Int.fract (c + t) ∈ Set.Ico a2 (a2 + 1/4) := by
  have hf0 : 0 ≤ Int.fract c := Int.fract_nonneg c
  have hf1 : Int.fract c < 1 := Int.fract_lt_one c
  have hcf : (⌊c⌋ : ℝ) + Int.fract c = c := Int.floor_add_fract c
  by_cases h1 : 1/8 ≤ Int.fract c ∧ Int.fract c ≤ 7/8
  · obtain ⟨h1a, h1b⟩ := h1
    refine ⟨Int.fract c - 1/8, Int.fract c - 1/8, by linarith, by linarith, by linarith,
      by linarith, fun t ht => Or.inl ?_⟩
    obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
    have hfr : Int.fract (c + t) = Int.fract c + t := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, ⌊c⌋, by linarith⟩
    rw [hfr, Set.mem_Ico]
    constructor <;> linarith
  · refine ⟨0, 3/4, by norm_num, by norm_num, by norm_num, by norm_num, fun t ht => ?_⟩
    obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
    rcases not_and_or.mp h1 with h | h
    · push_neg at h
      by_cases hs : 0 ≤ Int.fract c + t
      · left
        have hfr : Int.fract (c + t) = Int.fract c + t := by
          rw [Int.fract_eq_iff]
          exact ⟨hs, by linarith, ⌊c⌋, by linarith⟩
        rw [hfr, Set.mem_Ico]
        constructor <;> linarith
      · push_neg at hs
        right
        have hfr : Int.fract (c + t) = Int.fract c + t + 1 := by
          rw [Int.fract_eq_iff]
          refine ⟨by linarith, by linarith, ⌊c⌋ - 1, ?_⟩
          push_cast
          linarith
        rw [hfr, Set.mem_Ico]
        constructor <;> linarith
    · push_neg at h
      by_cases hs : Int.fract c + t < 1
      · right
        have hfr : Int.fract (c + t) = Int.fract c + t := by
          rw [Int.fract_eq_iff]
          exact ⟨by linarith, hs, ⌊c⌋, by linarith⟩
        rw [hfr, Set.mem_Ico]
        constructor <;> linarith
      · push_neg at hs
        left
        have hfr : Int.fract (c + t) = Int.fract c + t - 1 := by
          rw [Int.fract_eq_iff]
          refine ⟨by linarith, by linarith, ⌊c⌋ + 1, ?_⟩
          push_cast
          linarith
        rw [hfr, Set.mem_Ico]
        constructor <;> linarith

private lemma half_count (x : ℕ → ℝ) (r m : ℕ) (a1 a2 : ℝ) (h1 : 0 ≤ a1) (h1' : a1 + 1/4 ≤ 1)
    (h2 : 0 ≤ a2) (h2' : a2 + 1/4 ≤ 1)
    (h : ∀ j ∈ Finset.Ioc r (r + m), x j ∈ Set.Ico a1 (a1 + 1/4) ∨ x j ∈ Set.Ico a2 (a2 + 1/4)) :
    ∃ a : ℝ, 0 ≤ a ∧ a + 1/4 ≤ 1 ∧
      (m : ℝ) ≤ 2 * ((((Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ Set.Ico a (a + 1/4))).card : ℕ) : ℝ) := by
  have hS : (Finset.Ioc r (r + m)).card = m := by
    rw [Nat.card_Ioc]; omega
  have hsub : Finset.Ioc r (r + m) ⊆
      (Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ Set.Ico a1 (a1 + 1/4)) ∪
      (Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ Set.Ico a2 (a2 + 1/4)) := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h j hj with h' | h'
    · exact Or.inl ⟨hj, h'⟩
    · exact Or.inr ⟨hj, h'⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hS] at hc
  by_cases hab : m ≤ 2 * ((Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ Set.Ico a1 (a1 + 1/4))).card
  · exact ⟨a1, h1, h1', by exact_mod_cast hab⟩
  · refine ⟨a2, h2, h2', ?_⟩
    have hm : m ≤ 2 * ((Finset.Ioc r (r + m)).filter (fun j ↦ x j ∈ Set.Ico a2 (a2 + 1/4))).card := by
      omega
    exact_mod_cast hm

theorem erdos_96567_hyp_reduction : ConsecutivePrimesInTuples → PrimeFractClusters := by
  intro hyp
  unfold ConsecutivePrimesInTuples at hyp
  unfold PrimeFractClusters HasQuarterClusters
  intro α m
  obtain ⟨K, hK⟩ := hyp m
  obtain ⟨F, hF⟩ : ∃ F : ℕ, F = (K + 1).factorial := ⟨_, rfl⟩
  have hFpos : 0 < F := by rw [hF]; exact Nat.factorial_pos _
  obtain ⟨j0, k, hk, -, hjk⟩ :=
    Real.exists_int_int_abs_mul_sub_le ((F : ℝ) * α) (show 0 < 8 * (K + 1) by omega)
  lift k to ℕ using hk.le
  have hkpos : 0 < k := by exact_mod_cast hk
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = k * F := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hD]; exact Nat.mul_pos hkpos hFpos
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (D : ℝ) * α - j0 := ⟨_, rfl⟩
  have heq : ((k : ℤ) : ℝ) * ((F : ℝ) * α) - (j0 : ℝ) = e := by
    rw [he, hD, Nat.cast_mul, Int.cast_natCast]; ring
  rw [heq] at hjk
  have hE : |e| * (8 * ((K : ℝ) + 1) + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hjk
    push_cast at hjk
    linarith
  obtain ⟨H, hH⟩ : ∃ H : Finset ℕ, H = (Finset.range (K + 1)).image (fun i => i * D) := ⟨_, rfl⟩
  have hinj : Function.Injective (fun i : ℕ => i * D) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_right hDpos hab
  have hcard : H.card = K + 1 := by
    rw [hH, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hadm : IsAdmissibleSet H := by
    intro p hp
    by_cases hpL : p ≤ K + 1
    · refine ⟨1, fun h hh => ?_⟩
      simp only [hH, Finset.mem_image] at hh
      obtain ⟨i, -, rfl⟩ := hh
      have hdvd : p ∣ i * D := by
        have h1 : p ∣ F := by rw [hF]; exact Nat.dvd_factorial hp.pos hpL
        rw [hD]
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h1 k) i
      rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.mod_eq_of_lt hp.one_lt]
      omega
    · push_neg at hpL
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range p ⊆ H.image (fun h => h % p) := by
        intro c hc
        rw [Finset.mem_range] at hc
        obtain ⟨h, hh, hhc⟩ := hcon c
        rw [Finset.mem_image]
        exact ⟨h, hh, by rw [hhc, Nat.mod_eq_of_lt hc]⟩
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_range] at h3
      have h4 := Finset.card_image_le (s := H) (f := fun h => h % p)
      omega
  obtain ⟨n, -, r, hr⟩ := hK H (by rw [hcard]; omega) hadm 0
  obtain ⟨a1, a2, h1, h1', h2, h2', harc⟩ := fract_arc (α * n)
  refine ⟨r, half_count (fun n => Int.fract (α * (Nat.nth Nat.Prime n : ℝ))) r m a1 a2
    h1 h1' h2 h2' ?_⟩
  intro j hj
  obtain ⟨hnj, hmem⟩ := hr j hj
  simp only [hH, Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, hiD⟩ := hmem
  have hpj : ((Nat.nth Nat.Prime j : ℕ) : ℝ) = n + i * D := by
    have h5 : Nat.nth Nat.Prime j = n + i * D := by
      rw [hiD]; exact (Nat.add_sub_of_le hnj).symm
    rw [h5]; push_cast; ring
  have hx : α * (Nat.nth Nat.Prime j : ℝ) = (α * n + i * e) + ((i * j0 : ℤ) : ℝ) := by
    rw [hpj, he]; push_cast; ring
  show Int.fract (α * (Nat.nth Nat.Prime j : ℝ)) ∈ Set.Ico a1 (a1 + 1/4) ∨
    Int.fract (α * (Nat.nth Nat.Prime j : ℝ)) ∈ Set.Ico a2 (a2 + 1/4)
  rw [hx, Int.fract_add_intCast]
  apply harc
  rw [abs_mul, Nat.abs_cast]
  have hiK' : i ≤ K := by omega
  have hiK : (i : ℝ) ≤ K := by exact_mod_cast hiK'
  rcases (abs_nonneg e).eq_or_lt with h0 | h0
  · rw [← h0]; norm_num
  · nlinarith [mul_le_mul_of_nonneg_right hiK (abs_nonneg e), hE, h0]
end erdos_96567_hyp_reduction_ns

theorem erdos_96567_hyp_reduction : ConsecutivePrimesInTuples → PrimeFractClusters := by
  exact erdos_96567_hyp_reduction_ns.erdos_96567_hyp_reduction



open Set

def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

theorem erdos_96567 :
    ∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  intro α hwd
  have hall := erdos_96567_hyp_reduction erdos_96567_hyp_bftb
  unfold PrimeFractClusters at hall
  have hc := hall α
  unfold HasQuarterClusters at hc
  unfold IsWellDistributed at hwd
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hwd (1/4) (by norm_num))
  obtain ⟨r, a, ha0, ha1, hm⟩ := hc (K + 1)
  have hK' := hK (K + 1) (by omega) r a (a + 1/4) ha0 (by linarith) ha1
  try dsimp only at hK'
  try dsimp only at hm
  rw [abs_lt] at hK'
  linarith [hK'.2, hm]