def frobN (n : ℕ) : ℤ :=
  (∑ p ∈ n.primeFactors,
    (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n

-- CONJECTURE (derived; upper-bound half, "Apery-set" form). From R1/R2/R3: for each residue class
-- mod n, the per-prime digit construction with generators C(n,p^d) (digits in [0,p-1], glued by CRT)
-- gives a representable r in that class with r ≤ Σ_p (p-1)Σ_d C(n,p^d) = frobN n + n.
theorem erdos_21718_hyp_apery :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∀ m : ℤ, ∃ r : ℤ,
        (∃ c : ℕ → ℕ, r = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)) ∧
        r ≤ frobN n + n ∧ (n : ℤ) ∣ m - r := by
  sorry

-- CONJECTURE (derived; lower-bound half, as a subadditive certificate). Take W = D, the least
-- element of the restricted semigroup (generators n and C(n,p^d)) in the residue class mod n.
-- Then D(0)=0. D is subadditive by Lemma L (carry reduction, using the growth bound
-- C(n,p^(e+1)) ≥ p·C(n,p^e)). D(C(n,i)) ≤ C(n,i) is the key claim (R4). Finally
-- D(frobN n) = frobN n + n, the all-(p-1)-digits value.
theorem erdos_21718_hyp_cert :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∃ W : ℤ → ℤ, W 0 ≤ 0 ∧ (∀ x y : ℤ, W (x + y) ≤ W x + W y) ∧
        (∀ i ∈ Finset.Ico 1 n, W (n.choose i : ℤ) ≤ (n.choose i : ℤ)) ∧
        frobN n < W (frobN n) := by
  sorry

theorem erdos_21718 (n : ℕ) (hn : n ≠ 0)
    (hpk : ∀ p k : ℕ, p.Prime → n ≠ p ^ k) :
    IsGreatest
      {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
      ((∑ p ∈ n.primeFactors,
        (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n) := by
  have hn' : (0:ℤ) < (n:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : n ≠ 1 := by
    have h := hpk 2 0 Nat.prime_two
    simpa using h
  have h1 : (1:ℕ) ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [Set.mem_setOf_eq]
    rintro ⟨c, hc⟩
    have hc' : frobN n = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ) := hc
    obtain ⟨W, hW0, hWadd, hWgen, hWN⟩ := erdos_21718_hyp_cert n hn hpk
    have hmul : ∀ i ∈ Finset.Ico 1 n, ∀ k : ℕ,
        W ((k:ℤ) * (n.choose i : ℤ)) ≤ (k:ℤ) * (n.choose i : ℤ) := by
      intro i hi k
      induction k with
      | zero => simpa using hW0
      | succ j ih =>
        have hadd := hWadd ((j:ℤ) * (n.choose i : ℤ)) (n.choose i : ℤ)
        have h2 := hWgen i hi
        push_cast
        rw [add_mul, one_mul]
        linarith
    have hsum : W (∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)) ≤
        ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ) := by
      refine Finset.sum_induction (fun i => (c i : ℤ) * (n.choose i : ℤ)) (fun x => W x ≤ x)
        ?_ ?_ ?_
      · intro a b ha hb
        have ha' : W a ≤ a := ha
        have hb' : W b ≤ b := hb
        have hab := hWadd a b
        show W (a + b) ≤ a + b
        linarith
      · show W 0 ≤ 0
        exact hW0
      · intro i hi
        exact hmul i hi (c i)
    rw [← hc'] at hsum
    linarith
  · intro m hm
    rw [Set.mem_setOf_eq] at hm
    by_contra hlt
    push_neg at hlt
    have hlt' : frobN n < m := hlt
    apply hm
    obtain ⟨r, ⟨c, hc⟩, hr, hdiv⟩ := erdos_21718_hyp_apery n hn hpk m
    obtain ⟨k, hk⟩ := hdiv
    have hk0 : 0 ≤ k := by
      by_contra hneg
      push_neg at hneg
      have hk1 : k ≤ -1 := by omega
      have hmk := mul_le_mul_of_nonneg_left hk1 hn'.le
      linarith
    lift k to ℕ using hk0
    refine ⟨fun i => c i + if i = 1 then k else 0, ?_⟩
    show m = ∑ i ∈ Finset.Ico 1 n, ((c i + if i = 1 then k else 0 : ℕ) : ℤ) * (n.choose i : ℤ)
    have hsplit : ∑ i ∈ Finset.Ico 1 n, ((c i + if i = 1 then k else 0 : ℕ) : ℤ) * (n.choose i : ℤ)
        = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ) +
          ∑ i ∈ Finset.Ico 1 n, (if i = 1 then (k : ℤ) * (n.choose i : ℤ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> push_cast <;> ring
    rw [hsplit]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, h1, if_true, ↓reduceIte,
      Nat.choose_one_right]
    linear_combination hk + hc