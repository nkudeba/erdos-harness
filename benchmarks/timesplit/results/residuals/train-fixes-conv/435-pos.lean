def erdos_44628_Rep (n : ℕ) (m : ℤ) : Prop :=
  ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)

def erdos_44628_F (n : ℕ) : ℤ :=
  (∑ p ∈ n.primeFactors,
    (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n

-- Elementary: add 1 to the coefficient of index 1, since C(n,1) = n and 1 ∈ [1, n) when n ≥ 2.
namespace erdos_44628_hyp_shift_ns
theorem erdos_44628_hyp_shift :
    ∀ n : ℕ, 2 ≤ n → ∀ m : ℤ, erdos_44628_Rep n m → erdos_44628_Rep n (m + n) := by
  intro n hn m hrep
  obtain ⟨c, hm⟩ := hrep
  refine ⟨fun i => if i = 1 then c i + 1 else c i, ?_⟩
  have h1 : (1:ℕ) ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have key : ∀ i ∈ Finset.Ico 1 n,
      (((if i = 1 then c i + 1 else c i : ℕ) : ℤ) * (n.choose i : ℤ)) =
      (c i : ℤ) * (n.choose i : ℤ) + (if i = 1 then (n.choose i : ℤ) else 0) := by
    intro i _
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos h1,
    Nat.choose_one_right, hm]
end erdos_44628_hyp_shift_ns

theorem erdos_44628_hyp_shift :
    ∀ n : ℕ, 2 ≤ n → ∀ m : ℤ, erdos_44628_Rep n m → erdos_44628_Rep n (m + n) := by
  exact erdos_44628_hyp_shift_ns.erdos_44628_hyp_shift



-- Upper half, reduced to one window of n consecutive integers (the Apéry-set bound of R2).
-- It uses only R1-admissible coefficients: c_i = 0 when (i ≠ 1 and gcd(i,n) = 1) or when i > n/2.
-- Verified exactly for all non-prime-power n ≤ 200.
theorem erdos_44628_hyp_window :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∀ m : ℤ, erdos_44628_F n < m → m ≤ erdos_44628_F n + n →
        ∃ c : ℕ → ℕ, (∀ i : ℕ, ((i ≠ 1 ∧ Nat.Coprime i n) ∨ n < 2 * i) → c i = 0) ∧
          m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ) := by
  sorry

-- Lower half (R2 lower bound): the residue class of F mod n has Apéry element F + n.
-- Hard core; verified exactly for all non-prime-power n ≤ 200.
theorem erdos_44628_hyp_lower :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ¬ erdos_44628_Rep n (erdos_44628_F n) := by
  sorry

theorem erdos_44628 (n : ℕ) (hn : n ≠ 0)
    (hpk : ∀ p k : ℕ, p.Prime → n ≠ p ^ k) :
    IsGreatest
      {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
      ((∑ p ∈ n.primeFactors,
        (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n) := by
  have h1 : n ≠ 1 := by
    intro h
    exact hpk 2 0 Nat.prime_two (by simp [h])
  have h2 : 2 ≤ n := by omega
  have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : 1 ≤ n)
  have key : ∀ k : ℕ, ∀ m : ℤ, erdos_44628_F n < m →
      m ≤ erdos_44628_F n + (n : ℤ) + (n : ℤ) * (k : ℤ) → erdos_44628_Rep n m := by
    intro k
    induction k with
    | zero =>
      intro m hm1 hm2
      have hm2' : m ≤ erdos_44628_F n + (n : ℤ) := by simpa using hm2
      obtain ⟨c, _, hc⟩ := erdos_44628_hyp_window n hn hpk m hm1 hm2'
      exact ⟨c, hc⟩
    | succ k ih =>
      intro m hm1 hm2
      by_cases hc : m ≤ erdos_44628_F n + (n : ℤ) + (n : ℤ) * (k : ℤ)
      · exact ih m hm1 hc
      · push_neg at hc
        have hnk : (0 : ℤ) ≤ (n : ℤ) * (k : ℤ) := by positivity
        have hexp : (n : ℤ) * (((k + 1 : ℕ) : ℤ)) = (n : ℤ) * (k : ℤ) + n := by
          push_cast; ring
        rw [hexp] at hm2
        have hr := ih (m - n) (by linarith) (by linarith)
        have hs := erdos_44628_hyp_shift n h2 (m - n) hr
        rwa [sub_add_cancel] at hs
  refine ⟨?_, ?_⟩
  · exact erdos_44628_hyp_lower n hn hpk
  · intro m hm
    have hm' : ¬ erdos_44628_Rep n m := hm
    by_contra hlt
    push_neg at hlt
    have hlt' : erdos_44628_F n < m := hlt
    have ht : (((m - erdos_44628_F n).toNat : ℕ) : ℤ) = m - erdos_44628_F n :=
      Int.toNat_of_nonneg (by linarith)
    apply hm'
    apply key (m - erdos_44628_F n).toNat m hlt'
    rw [ht]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (le_of_lt (sub_pos.mpr hlt'))]