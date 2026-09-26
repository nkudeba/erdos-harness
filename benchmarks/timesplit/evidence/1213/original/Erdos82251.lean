import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

def erdos82251PairSet (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 ≤ X)

-- DERIVED (R1 + R3): strict monotonicity makes each gap an honest difference in [1,K], so
-- A (s-1) ≤ a + K*(s-1). Then a + K*X < A (s-1) gives K*X < K*(s-1), hence X < s - 1.
namespace erdos_82251_hyp_long_ns
private lemma erdos82251_bound (a K s : ℕ) (A : ℕ → ℕ) (h0 : A 0 = a)
    (hgap : ∀ i, i + 1 < s → A (i + 1) - A i ≤ K) :
    ∀ j, j < s → A j ≤ a + K * j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [h0]
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hgap n hn
    rw [Nat.mul_succ]
    omega

theorem erdos_82251_hyp_long :
    ∀ (a K X s : ℕ) (A : ℕ → ℕ), 1 ≤ a → 1 ≤ K → 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) → (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      a + K * X < A (s - 1) → X + 1 < s := by
  intro a K X s A _ _ hs h0 _ hgap hlt
  have hle := erdos82251_bound a K s A h0 hgap (s - 1) (by omega)
  by_contra hc
  have h3 : s - 1 ≤ X := by omega
  have h4 : K * (s - 1) ≤ K * X := Nat.mul_le_mul le_rfl h3
  omega
end erdos_82251_hyp_long_ns

theorem erdos_82251_hyp_long :
    ∀ (a K X s : ℕ) (A : ℕ → ℕ), 1 ≤ a → 1 ≤ K → 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) → (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      a + K * X < A (s - 1) → X + 1 < s := by
  exact erdos_82251_hyp_long_ns.erdos_82251_hyp_long



-- DERIVED (R1): for j < s we have a ≤ A j ≤ a + K*j. For p = (l,u) in the pair set with u ≤ X < s,
-- the interval Ico (u-l) u has l terms, each at least a ≥ 1 and at most
-- A (u-1) ≤ a + K*(u-1) ≤ (a+K)*u. So the sum lies in [1, (a+K)*l*u] ⊆ [1, (a+K)*X].
namespace erdos_82251_hyp_sumbound_ns
theorem erdos_82251_hyp_sumbound :
    ∀ (a K X s : ℕ) (A : ℕ → ℕ), 1 ≤ a → 1 ≤ K → 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) → (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      X < s → ∀ p ∈ erdos82251PairSet X,
        1 ≤ ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ∧
        ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ≤ (a + K) * X := by
  intro a K X s A ha hK hs h0 hmono hgap hXs p hp
  obtain ⟨l, u⟩ := p
  simp only [erdos82251PairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨hl1, hlX⟩, ⟨hu1, huX⟩⟩, hlu, hprod⟩ := hp
  dsimp only
  have hlow : ∀ j, j < s → a ≤ A j := by
    intro j hj
    have := hmono.monotoneOn (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr hj) (Nat.zero_le j)
    rw [h0] at this
    exact this
  have hup : ∀ j, j < s → A j ≤ a + K * j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hgap n hn
      rw [mul_add, mul_one]
      omega
  constructor
  · have hmem : u - 1 ∈ Finset.Ico (u - l) u := by
      rw [Finset.mem_Ico]; omega
    have h1 := Finset.single_le_sum (f := A) (fun i _ => Nat.zero_le (A i)) hmem
    have h2 := hlow (u - 1) (by omega)
    omega
  · have hb : ∀ i ∈ Finset.Ico (u - l) u, A i ≤ (a + K) * u := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h1 := hup i (by omega)
      have h2 : K * i ≤ K * u := Nat.mul_le_mul_left K (by omega)
      have h3 : a ≤ a * u := by nlinarith
      rw [add_mul]
      omega
    have hs' := Finset.sum_le_card_nsmul (Finset.Ico (u - l) u) A ((a + K) * u) hb
    rw [Nat.card_Ico, smul_eq_mul] at hs'
    have hc : u - (u - l) = l := by omega
    rw [hc] at hs'
    calc _ ≤ l * ((a + K) * u) := hs'
      _ = (a + K) * (l * u) := by ring
      _ ≤ (a + K) * X := Nat.mul_le_mul_left _ hprod
end erdos_82251_hyp_sumbound_ns

theorem erdos_82251_hyp_sumbound :
    ∀ (a K X s : ℕ) (A : ℕ → ℕ), 1 ≤ a → 1 ≤ K → 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) → (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      X < s → ∀ p ∈ erdos82251PairSet X,
        1 ≤ ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ∧
        ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ≤ (a + K) * X := by
  exact erdos_82251_hyp_sumbound_ns.erdos_82251_hyp_sumbound



-- DERIVED (counting lemma): with X = 2^(4B+2), the swap symmetry gives
-- 2*#P(X) ≥ Σ_{l ≤ X} ⌊X/l⌋ ≥ X*(H_X - 1), and the dyadic bound gives H_{2^m} ≥ 1 + m/2.
-- This was verified exactly for B in [2,9].
namespace erdos_82251_hyp_count_ns
private def erdosD82251 (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p => p.1 * p.2 ≤ X)

private lemma erdosD82251_card (X : ℕ) :
    (erdosD82251 X).card = ∑ l ∈ Finset.Icc 1 X, X / l := by
  unfold erdosD82251
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [Finset.mem_Icc] at hl
  have hset : (Finset.Icc 1 X).filter (fun u => l * u ≤ X) = Finset.Icc 1 (X / l) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega)]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, by rw [mul_comm]; exact h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by nlinarith⟩, by rw [mul_comm]; exact h3⟩
  have key : ((Finset.Icc 1 X).filter (fun u => l * u ≤ X)).card = X / l := by
    rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  rw [← key, Finset.card_filter]

private lemma erdosD82251_le (X : ℕ) :
    (erdosD82251 X).card ≤ 2 * (erdos82251PairSet X).card := by
  have hsub : erdosD82251 X ⊆
      erdos82251PairSet X ∪ (erdos82251PairSet X).image Prod.swap := by
    intro p hp
    unfold erdosD82251 at hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    rw [Finset.mem_union]
    by_cases h : p.1 ≤ p.2
    · left
      unfold erdos82251PairSet
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨h1, h2⟩, h, h3⟩
    · right
      rw [Finset.mem_image]
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      unfold erdos82251PairSet
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨h2, h1⟩, ?_, ?_⟩
      · simp only [Prod.fst_swap, Prod.snd_swap]; omega
      · simp only [Prod.fst_swap, Prod.snd_swap]; rw [mul_comm]; exact h3
  calc (erdosD82251 X).card
      ≤ (erdos82251PairSet X ∪ (erdos82251PairSet X).image Prod.swap).card :=
        Finset.card_le_card hsub
    _ ≤ (erdos82251PairSet X).card + ((erdos82251PairSet X).image Prod.swap).card :=
        Finset.card_union_le _ _
    _ ≤ (erdos82251PairSet X).card + (erdos82251PairSet X).card := by
        have := Finset.card_image_le (s := erdos82251PairSet X) (f := Prod.swap)
        omega
    _ = 2 * (erdos82251PairSet X).card := by ring

private lemma erdos82251_harm (m : ℕ) :
    (m + 2) * 2 ^ m ≤ 2 * ∑ l ∈ Finset.Icc 1 (2 ^ m), 2 ^ m / l := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hpow]
    have hnpos : 0 < 2 ^ m := by positivity
    generalize 2 ^ m = n at ih hnpos ⊢
    have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Icc] at hx hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have h1 : ∑ l ∈ Finset.Icc 1 n, 2 * (n / l) ≤ ∑ l ∈ Finset.Icc 1 n, 2 * n / l := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_Icc] at hl
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := Nat.div_mul_le_self n l
      calc 2 * (n / l) * l = 2 * (n / l * l) := by ring
        _ ≤ 2 * n := by omega
    have h2 : ∑ l ∈ Finset.Icc (n + 1) (2 * n), (1 : ℕ)
        ≤ ∑ l ∈ Finset.Icc (n + 1) (2 * n), 2 * n / l := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_Icc] at hl
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have h3 : ∑ l ∈ Finset.Icc (n + 1) (2 * n), (1 : ℕ) = n := by
      rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
      omega
    rw [← Finset.mul_sum] at h1
    nlinarith [ih, h1, h2, h3]

theorem erdos_82251_hyp_count :
    ∀ B : ℕ, 1 ≤ B → ∃ X : ℕ, B * X < (erdos82251PairSet X).card := by
  intro B hB
  refine ⟨2 ^ (4 * B), ?_⟩
  have h1 := erdos82251_harm (4 * B)
  have h2 := erdosD82251_card (2 ^ (4 * B))
  have h3 := erdosD82251_le (2 ^ (4 * B))
  have hpos : 0 < 2 ^ (4 * B) := by positivity
  rw [← h2] at h1
  nlinarith
end erdos_82251_hyp_count_ns

theorem erdos_82251_hyp_count :
    ∀ B : ℕ, 1 ≤ B → ∃ X : ℕ, B * X < (erdos82251PairSet X).card := by
  exact erdos_82251_hyp_count_ns.erdos_82251_hyp_count



-- DERIVED (pigeonhole): p ↦ (p.2 - p.1, p.2) is injective on the pair set.
-- Each interval is nonempty and lies inside [0,s), since p.2 ≤ X < s.
-- More than M pairs have sums in the M-element set [1,M], so two distinct intervals collide.
namespace erdos_82251_hyp_pigeon_ns
theorem erdos_82251_hyp_pigeon :
    ∀ (A : ℕ → ℕ) (s X M : ℕ), X < s → M < (erdos82251PairSet X).card →
      (∀ p ∈ erdos82251PairSet X,
        1 ≤ ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ∧
        ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ≤ M) →
      HasEqualIntervalSums A s := by
  intro A s X M hXs hM hsum
  have hmaps : ∀ p ∈ erdos82251PairSet X,
      (fun p : ℕ × ℕ => ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i) p ∈ Finset.Icc 1 M := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsum p hp
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hc : (Finset.Icc 1 M).card < (erdos82251PairSet X).card := by
    rw [Nat.card_Icc]; omega
  obtain ⟨p, hp, q, hq, hpq, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun p : ℕ × ℕ => ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i) hc hmaps
  have hp' := hp
  have hq' := hq
  simp only [erdos82251PairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp' hq'
  obtain ⟨⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩, hp5, _⟩ := hp'
  obtain ⟨⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩, hq5, _⟩ := hq'
  refine ⟨p.2 - p.1, p.2, q.2 - q.1, q.2, by omega, by omega, by omega, by omega, ?_, heq⟩
  intro h
  apply hpq
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  exact Prod.ext (by omega) h2
end erdos_82251_hyp_pigeon_ns

theorem erdos_82251_hyp_pigeon :
    ∀ (A : ℕ → ℕ) (s X M : ℕ), X < s → M < (erdos82251PairSet X).card →
      (∀ p ∈ erdos82251PairSet X,
        1 ≤ ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ∧
        ∑ i ∈ Finset.Ico (p.2 - p.1) p.2, A i ≤ M) →
      HasEqualIntervalSums A s := by
  exact erdos_82251_hyp_pigeon_ns.erdos_82251_hyp_pigeon



theorem erdos_82251 :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s := by
  intro a K ha hK
  obtain ⟨X, hX⟩ := erdos_82251_hyp_count (a + K) (by omega)
  refine ⟨a + K * X, ?_⟩
  intro s A hs h0 hmono hgap hf
  have hlong := erdos_82251_hyp_long a K X s A ha hK hs h0 hmono hgap hf
  exact erdos_82251_hyp_pigeon A s X ((a + K) * X) (by omega) hX
    (erdos_82251_hyp_sumbound a K X s A ha hK hs h0 hmono hgap (by omega))
