open scoped ArithmeticFunction.sigma

def erdos_81796_IsDistinctSum (n : ℕ) : Prop :=
  ∃ s ⊆ n.properDivisors, n = s.sum id

-- Derived (R2): if d = Σ_{e∈S} e with S ⊆ properDivisors d, then d*k = Σ_{e∈S} e*k,
-- and the e*k are distinct proper divisors of d*k (k ≥ 1). Elementary.
namespace erdos_81796_hyp_mul_ns
open scoped ArithmeticFunction.sigma

theorem erdos_81796_hyp_mul :
    ∀ d k : ℕ, 0 < k → erdos_81796_IsDistinctSum d → erdos_81796_IsDistinctSum (d * k) := by
  intro d k hk hd
  obtain ⟨s, hs, hsum⟩ := hd
  have hinj : Function.Injective (fun x : ℕ => x * k) :=
    fun a b h => Nat.eq_of_mul_eq_mul_right hk h
  refine ⟨s.image (fun x => x * k), ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := hs hx
    rw [Nat.mem_properDivisors] at hx' ⊢
    refine ⟨Nat.mul_dvd_mul_right hx'.1 k, ?_⟩
    have h2 := hx'.2
    nlinarith
  · rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    rw [hsum, Finset.sum_mul]
    rfl
end erdos_81796_hyp_mul_ns

theorem erdos_81796_hyp_mul :
    ∀ d k : ℕ, 0 < k → erdos_81796_IsDistinctSum d → erdos_81796_IsDistinctSum (d * k) := by
  exact erdos_81796_hyp_mul_ns.erdos_81796_hyp_mul



-- Derived reduction to the primitive case: a counterexample must have no divisor that is a
-- distinct sum of its proper divisors (R2), so the target follows from: large abundancy forces
-- some divisor that is a distinct sum (e.g. an abundant practical divisor). This is the open core.
namespace erdos_81796_hyp_core_ns
open scoped ArithmeticFunction.sigma

def erdos_81796_HasSmallPair (n : ℕ) : Prop :=
  ∃ a p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < 2 ^ (a + 1) ∧ 2 ^ a * p ∣ n

-- Derived: 2^a*p = (sum_{j<a} p*2^j) + p, and p < 2^(a+1) is a sum of distinct powers 2^j with j ≤ a
-- (binary expansion). All these divisors are proper and pairwise distinct because p is odd and > 1.
namespace erdos_81796_hyp_core_hyp_pair_ns

open scoped ArithmeticFunction.sigma

private lemma erdos_81796_pow_lt {i k : ℕ} (h : i < k) : 2 ^ i < 2 ^ k :=
  Nat.pow_lt_pow_right (by norm_num) h

private lemma erdos_81796_bin_rep : ∀ k m : ℕ, m < 2 ^ k →
    ∃ T : Finset ℕ, (∀ x ∈ T, ∃ i < k, x = 2 ^ i) ∧ T.sum id = m := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have : m = 0 := by simpa using hm
    subst this
    exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    intro m hm
    by_cases h : m < 2 ^ k
    · obtain ⟨T, hT, hs⟩ := ih m h
      refine ⟨T, ?_, hs⟩
      intro x hx
      obtain ⟨i, hi, hx'⟩ := hT x hx
      exact ⟨i, Nat.lt_succ_of_lt hi, hx'⟩
    · have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rw [h2] at hm
      obtain ⟨T, hT, hs⟩ := ih (m - 2 ^ k) (by generalize 2 ^ k = t at *; omega)
      have hnot : 2 ^ k ∉ T := by
        intro hk
        obtain ⟨i, hi, he⟩ := hT _ hk
        have := erdos_81796_pow_lt hi
        rw [he] at this
        exact lt_irrefl _ this
      refine ⟨insert (2 ^ k) T, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact ⟨k, Nat.lt_succ_self k, hx⟩
        · obtain ⟨i, hi, hx'⟩ := hT x hx
          exact ⟨i, Nat.lt_succ_of_lt hi, hx'⟩
      · rw [Finset.sum_insert hnot, hs]
        simp only [id_eq]
        generalize 2 ^ k = t at *
        omega

private lemma erdos_81796_mult_rep (p : ℕ) (hp : 0 < p) : ∀ k : ℕ,
    ∃ U : Finset ℕ, (∀ x ∈ U, ∃ i < k, x = 2 ^ i * p) ∧ U.sum id + p = 2 ^ k * p := by
  intro k
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨U, hU, hs⟩ := ih
    have hnot : 2 ^ k * p ∉ U := by
      intro hk
      obtain ⟨i, hi, he⟩ := hU _ hk
      have h1 := erdos_81796_pow_lt hi
      have : 2 ^ i * p < 2 ^ k * p := Nat.mul_lt_mul_of_pos_right h1 hp
      rw [he] at this
      exact lt_irrefl _ this
    refine ⟨insert (2 ^ k * p) U, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact ⟨k, Nat.lt_succ_self k, hx⟩
      · obtain ⟨i, hi, hx'⟩ := hU x hx
        exact ⟨i, Nat.lt_succ_of_lt hi, hx'⟩
    · rw [Finset.sum_insert hnot]
      simp only [id_eq]
      rw [pow_succ]
      calc 2 ^ k * p + U.sum id + p = 2 ^ k * p + (U.sum id + p) := by ring
        _ = 2 ^ k * p + 2 ^ k * p := by rw [hs]
        _ = 2 ^ k * 2 * p := by ring

theorem erdos_81796_hyp_core_hyp_pair :
    ∀ a p : ℕ, p.Prime → p ≠ 2 → p < 2 ^ (a + 1) →
      erdos_81796_IsDistinctSum (2 ^ a * p) := by
  intro a p hp hp2 hpa
  obtain ⟨T, hT, hTs⟩ := erdos_81796_bin_rep (a + 1) p hpa
  obtain ⟨U, hU, hUs⟩ := erdos_81796_mult_rep p hp.pos a
  have hp3 : 2 ≤ p := hp.two_le
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro x hxT hxU
    obtain ⟨i, hi, hxi⟩ := hT x hxT
    obtain ⟨j, hj, hje⟩ := hU _ hxU
    have hdvd : p ∣ 2 ^ i := by
      rw [← hxi, hje]
      exact Dvd.intro_left _ rfl
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  refine ⟨T ∪ U, ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_properDivisors]
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := hT x hx
      refine ⟨Dvd.dvd.mul_right (pow_dvd_pow 2 (Nat.le_of_lt_succ hi)) p, ?_⟩
      have h1 : 2 ^ i ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt_succ hi)
      have h2 : 0 < 2 ^ a := by positivity
      calc 2 ^ i ≤ 2 ^ a := h1
        _ < 2 ^ a * 2 := by omega
        _ ≤ 2 ^ a * p := Nat.mul_le_mul_left _ hp3
    · obtain ⟨j, hj, rfl⟩ := hU x hx
      refine ⟨mul_dvd_mul_right (pow_dvd_pow 2 hj.le) p, ?_⟩
      exact Nat.mul_lt_mul_of_pos_right (erdos_81796_pow_lt hj) hp.pos
  · rw [Finset.sum_union hdisj, hTs, add_comm]
    exact hUs.symm

end erdos_81796_hyp_core_hyp_pair_ns

theorem erdos_81796_hyp_core_hyp_pair :
    ∀ a p : ℕ, p.Prime → p ≠ 2 → p < 2 ^ (a + 1) →
      erdos_81796_IsDistinctSum (2 ^ a * p) := by
  exact erdos_81796_hyp_core_hyp_pair_ns.erdos_81796_hyp_core_hyp_pair

-- Hard core, even case. A counterexample at a valid C is weird (C > 72/35 > 2). If it is even with
-- 2^k ∥ n, it has no odd prime factor below 2^(k+1) (by the pair lemma). This hypothesis asserts that
-- large abundancy is impossible under that restriction without some pseudoperfect divisor.
theorem erdos_81796_hyp_core_hyp_even :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, σ 1 n > C * n → Even n → ¬ erdos_81796_HasSmallPair n →
      ∃ d ∈ n.divisors, erdos_81796_IsDistinctSum d := by
  sorry

-- Hard core, odd case. A counterexample would be an odd weird number of large abundancy.
-- No odd weird number is known.
theorem erdos_81796_hyp_core_hyp_odd :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, σ 1 n > C * n → Odd n →
      ∃ d ∈ n.divisors, erdos_81796_IsDistinctSum d := by
  sorry

theorem erdos_81796_hyp_core :
    ∃ (C : ℝ) (_ : C > 0), ∀ (n : ℕ) (_ : σ 1 n > C * n),
      ∃ d ∈ n.divisors, erdos_81796_IsDistinctSum d := by
  obtain ⟨C1, hC1, h1⟩ := erdos_81796_hyp_core_hyp_even
  obtain ⟨C2, hC2, h2⟩ := erdos_81796_hyp_core_hyp_odd
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have e1 : σ 1 n > C1 * n :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hn0) hn
  have e2 : σ 1 n > C2 * n :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hn0) hn
  have hne : n ≠ 0 := by
    rintro rfl
    simp at hn
  by_cases hp : erdos_81796_HasSmallPair n
  · obtain ⟨a, p, hpr, hp2, hlt, hdvd⟩ := hp
    exact ⟨2 ^ a * p, Nat.mem_divisors.2 ⟨hdvd, hne⟩,
      erdos_81796_hyp_core_hyp_pair a p hpr hp2 hlt⟩
  · rcases Nat.even_or_odd n with he | ho
    · exact h1 n e1 he hp
    · exact h2 n e2 ho
end erdos_81796_hyp_core_ns

theorem erdos_81796_hyp_core :
    ∃ (C : ℝ) (_ : C > 0), ∀ (n : ℕ) (_ : σ 1 n > C * n),
      ∃ d ∈ n.divisors, erdos_81796_IsDistinctSum d := by
  exact erdos_81796_hyp_core_ns.erdos_81796_hyp_core



theorem erdos_81796 :
    ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id := by
  obtain ⟨C, hC, h⟩ := erdos_81796_hyp_core
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨d, hd, hds⟩ := h n hn
  rw [Nat.mem_divisors] at hd
  obtain ⟨⟨k, rfl⟩, hne⟩ := hd
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at hne
    · exact h0
  exact erdos_81796_hyp_mul d k hk hds