def erdos_57606_Feasible (n t : ℕ) : Prop :=
  ∃ a : Fin (t + 1) → ℕ, Nat.factorial n = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2

-- Derived (R1, volume bound): if n! = ∏ a_i with all a_i ≤ n^2 then n! ≤ (n^2)^(t+1), so
-- t+1 ≥ log n!/(2 log n) ≥ (n log n - n + 1)/(2 log n) > n/2 - n/(2 log n), using log n! ≥ n log n - n + 1.
namespace erdos_57606_hyp_lower_ns
open Filter

open scoped Nat

theorem erdos_57606_hyp_lower : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, erdos_57606_Feasible n t →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ (t : ℝ) + 1 := by
  intro n hn t ⟨a, hprod, hmono, hlast⟩
  have hle : ∀ i, a i ≤ n ^ 2 := fun i => (hmono (Fin.le_last i)).trans hlast
  have hfac : n ! ≤ (n ^ 2) ^ (t + 1) := by
    rw [hprod]
    calc ∏ i, a i ≤ (n ^ 2) ^ (Finset.univ : Finset (Fin (t + 1))).card :=
          Finset.prod_le_pow_card _ _ _ (fun i _ => hle i)
      _ = (n ^ 2) ^ (t + 1) := by rw [Finset.card_univ, Fintype.card_fin]
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hfpos : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfacR : (n ! : ℝ) ≤ (n : ℝ) ^ (2 * (t + 1)) := by
    rw [pow_mul]; exact_mod_cast hfac
  have h1 : Real.log (n ! : ℝ) ≤ Real.log ((n : ℝ) ^ (2 * (t + 1))) :=
    Real.log_le_log hfpos hfacR
  rw [Real.log_pow] at h1
  push_cast at h1
  have hexp := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
  have h2 : (n : ℝ) ^ n ≤ Real.exp n * n ! := by
    rw [div_le_iff₀ hfpos] at hexp; linarith
  have h3 : (n : ℝ) * Real.log n ≤ n + Real.log (n ! : ℝ) := by
    have := Real.log_le_log (pow_pos hnpos n) h2
    rw [Real.log_mul (Real.exp_pos _).ne' hfpos.ne', Real.log_exp, Real.log_pow] at this
    exact this
  have key : (n : ℝ) * Real.log n - n ≤ 2 * ((t : ℝ) + 1) * Real.log n := by
    linarith [h1, h3]
  have h2L : (0:ℝ) < 2 * Real.log n := mul_pos two_pos hL
  have heq : (n : ℝ) / 2 - n / (2 * Real.log n) = (n * Real.log n - n) / (2 * Real.log n) := by
    field_simp
  rw [heq, div_le_iff₀ h2L]
  linarith [key]
end erdos_57606_hyp_lower_ns

theorem erdos_57606_hyp_lower : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, erdos_57606_Feasible n t →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ (t : ℝ) + 1 := by
  exact erdos_57606_hyp_lower_ns.erdos_57606_hyp_lower



-- Derived (bookkeeping): sorting a nonempty multiset of factors gives a monotone Fin-indexed
-- family with the same product; its largest entry is ≤ n^2.
namespace erdos_57606_hyp_sort_ns
open Filter

open scoped Nat

private lemma list_feasible (l : List ℕ) (t : ℕ) (ht : l.length = t + 1)
    (hp : l.Pairwise (· ≤ ·)) :
    ∃ a : Fin (t + 1) → ℕ, l.prod = ∏ i, a i ∧ Monotone a ∧ ∀ i, a i ∈ l := by
  refine ⟨fun i => l[i.val]'(by omega), ?_, ?_, ?_⟩
  · rw [← List.prod_ofFn]
    congr 1
    apply List.ext_getElem
    · simp [ht]
    · intro i h1 h2
      rw [List.getElem_ofFn]
  · intro i j hij
    rcases (Fin.le_iff_val_le_val.1 hij).lt_or_eq with h | h
    · exact List.pairwise_iff_getElem.1 hp _ _ _ _ h
    · simp only [h, le_refl]
  · intro i
    exact List.getElem_mem _

theorem erdos_57606_hyp_sort : ∀ (n : ℕ) (s : Multiset ℕ), 0 < Multiset.card s →
    s.prod = Nat.factorial n → (∀ x ∈ s, x ≤ n ^ 2) →
    erdos_57606_Feasible n (Multiset.card s - 1) := by
  intro n s hs hprod hle
  have hcoe : ((s.sort (· ≤ ·) : List ℕ) : Multiset ℕ) = s := Multiset.sort_eq _ _
  have hpw : (s.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hlen : (s.sort (· ≤ ·)).length = Multiset.card s - 1 + 1 := by
    rw [← Multiset.coe_card, hcoe]; omega
  obtain ⟨a, ha1, ha2, ha3⟩ := list_feasible _ _ hlen hpw
  refine ⟨a, ?_, ha2, ?_⟩
  · rw [← hprod, ← ha1, ← Multiset.prod_coe, hcoe]
  · apply hle
    have h := Multiset.mem_coe.2 (ha3 (Fin.last _))
    rwa [hcoe] at h
end erdos_57606_hyp_sort_ns

theorem erdos_57606_hyp_sort : ∀ (n : ℕ) (s : Multiset ℕ), 0 < Multiset.card s →
    s.prod = Nat.factorial n → (∀ x ∈ s, x ≤ n ^ 2) →
    erdos_57606_Feasible n (Multiset.card s - 1) := by
  exact erdos_57606_hyp_sort_ns.erdos_57606_hyp_sort



-- Derived (R1 consequence): the target's upper half, i.e. factorizations of n! into parts ≤ n^2
-- with total waste ∑ log(n^2/a_i) = o(n). This is the hard core (believed proved in the literature).
theorem erdos_57606_hyp_upper : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Multiset ℕ, 0 < Multiset.card s ∧ s.prod = Nat.factorial n ∧ (∀ x ∈ s, x ≤ n ^ 2) ∧
      (Multiset.card s : ℝ) ≤ (n : ℝ) / 2 - n / (2 * Real.log n) + ε * ((n : ℝ) / Real.log n) := by
  sorry

open Filter
open scoped Nat

theorem erdos_57606 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := erdos_57606_hyp_upper c hc
  rw [Filter.eventually_atTop]
  refine ⟨max N 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := by omega
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos h1
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨t, ht, hAt⟩ := (h n hnpos).1
  have hlow := erdos_57606_hyp_lower n (by omega) t ht
  obtain ⟨s, hcard, hprod, hle, hsize⟩ := hN n hnN
  have hfeas := erdos_57606_hyp_sort n s hcard hprod hle
  have hlb := (h n hnpos).2
  rw [mem_lowerBounds] at hlb
  have hAle : A n ≤ Multiset.card s - 1 + 1 := by
    refine hlb _ ?_
    simp only [Set.mem_setOf_eq]
    exact ⟨Multiset.card s - 1, hfeas, rfl⟩
  have hsub : Multiset.card s - 1 + 1 = Multiset.card s := Nat.sub_add_cancel hcard
  rw [hsub] at hAle
  have hAleR : (A n : ℝ) ≤ (Multiset.card s : ℝ) := by exact_mod_cast hAle
  have hAeq : (A n : ℝ) = (t : ℝ) + 1 := by exact_mod_cast hAt.symm
  have hpos : 0 ≤ c * ((n : ℝ) / Real.log n) := mul_nonneg hc.le (div_nonneg hnR hlog.le)
  show ‖((A n : ℝ) - (n : ℝ) / 2 + (n : ℝ) / (2 * Real.log n))‖ ≤ c * ‖(n : ℝ) / Real.log n‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnR hlog.le), abs_le]
  constructor <;> linarith