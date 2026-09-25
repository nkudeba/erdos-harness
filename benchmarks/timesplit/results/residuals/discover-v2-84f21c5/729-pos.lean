-- Follows from R1: v_p(den(x/y)) = max(0, v_p(y) - v_p(x)) for x = n!, y = a!b!, using additivity of v_p.
namespace erdos_47489_hyp_den_of_val_ns
theorem erdos_47489_hyp_den_of_val :
    ∀ (n a b p : ℕ), p.Prime →
      padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial →
      padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 := by
  intro n a b p hp h
  haveI := Fact.mk hp
  have hn : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ha : ((a.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : ((b.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have hval : padicValRat p ((n.factorial / (a.factorial * b.factorial) : ℚ))
      = (padicValNat p n.factorial : ℤ)
        - ((padicValNat p a.factorial : ℤ) + (padicValNat p b.factorial : ℤ)) := by
    rw [padicValRat.div hn (mul_ne_zero ha hb), padicValRat.mul ha hb,
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
  set q : ℚ := (n.factorial / (a.factorial * b.factorial) : ℚ) with hq
  by_contra hne
  have hpd : p ∣ q.den := by
    by_contra hnd
    exact hne (padicValNat.eq_zero_of_not_dvd hnd)
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hd
    have h1 : p ∣ q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hd
      simpa using this
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hpd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hv : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
  rw [padicValInt.eq_zero_of_not_dvd hnum] at hv
  have hpos : 0 < padicValNat p q.den := Nat.pos_of_ne_zero hne
  omega
end erdos_47489_hyp_den_of_val_ns

theorem erdos_47489_hyp_den_of_val :
    ∀ (n a b p : ℕ), p.Prime →
      padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial →
      padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 := by
  exact erdos_47489_hyp_den_of_val_ns.erdos_47489_hyp_den_of_val



-- Kummer: v_p C(2m,m) = #{j : 2(m mod p^j) ≥ p^j}.
-- If p > 2k and p^j | m+i with 1 ≤ i ≤ k, then i is unique and m mod p^j = p^j - i > p^j/2,
-- so level j carries. Hence v_p((m+1)...(m+k)) ≤ v_p C(2m,m).
namespace erdos_47489_hyp_large_primes_ns
private lemma floor_key (m k q : ℕ) (hq : 2 * k < q) :
    m / q + (m + k) / q ≤ (2 * m) / q := by
  have hq0 : 0 < q := by omega
  have hm := Nat.div_add_mod m q
  have hr := Nat.mod_lt m hq0
  generalize m / q = a at hm ⊢
  generalize m % q = r at hm hr ⊢
  subst hm
  have h1 : (q * a + r + k) / q = (r + k) / q + a := by
    have : q * a + r + k = (r + k) + q * a := by ring
    rw [this, Nat.add_mul_div_left _ _ hq0]
  have h2 : (2 * (q * a + r)) / q = (2 * r) / q + 2 * a := by
    have : 2 * (q * a + r) = 2 * r + q * (2 * a) := by ring
    rw [this, Nat.add_mul_div_left _ _ hq0]
  rw [h1, h2]
  have h4 : (r + k) / q ≤ (2 * r) / q := by
    rcases Nat.lt_or_ge (r + k) q with h | h
    · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
    · have e1 : (r + k) / q < 2 := by
        rw [Nat.div_lt_iff_lt_mul hq0]; omega
      have e2 : 1 ≤ (2 * r) / q := by
        rw [Nat.le_div_iff_mul_le hq0]; omega
      omega
  omega

theorem erdos_47489_hyp_large_primes :
    ∀ (m k p : ℕ), p.Prime → 2 * k < p →
      padicValNat p m.factorial + padicValNat p (m + k).factorial ≤ padicValNat p (2 * m).factorial := by
  intro m k p hp hk
  haveI := Fact.mk hp
  have hb : ∀ x, x ≤ 2 * m + k → Nat.log p x < Nat.log p (2 * m + k) + 1 :=
    fun x hx => Nat.lt_succ_of_le (Nat.log_mono_right hx)
  rw [padicValNat_factorial (hb m (by omega)), padicValNat_factorial (hb (m + k) (by omega)),
    padicValNat_factorial (hb (2 * m) (by omega)), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  apply floor_key
  have : p ≤ p ^ i := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
  omega
end erdos_47489_hyp_large_primes_ns

theorem erdos_47489_hyp_large_primes :
    ∀ (m k p : ℕ), p.Prime → 2 * k < p →
      padicValNat p m.factorial + padicValNat p (m + k).factorial ≤ padicValNat p (2 * m).factorial := by
  exact erdos_47489_hyp_large_primes_ns.erdos_47489_hyp_large_primes



-- Hard core (medium primes K < p ≤ 2k). Route: choose base-p digits in [(p+1)/2, p-2] at positions t with p^t > k,
-- then a Chernoff bound and a union bound over m < e^{k/(2C)}.
theorem erdos_47489_hyp_medium :
    ∀ C : ℝ, C > 0 → ∃ K : ℕ, K ≥ 3 ∧ ∀ N : ℕ, ∃ m k : ℕ, N < m ∧
      (k : ℝ) > C * Real.log ((2 * m : ℕ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → K < p → p ≤ 2 * k →
        padicValNat p m.factorial + padicValNat p (m + k).factorial
          ≤ padicValNat p (2 * m).factorial := by
  sorry

theorem erdos_47489 :
    ∀ (C : ℝ) (hC : C > 0),
      ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
  intro C hC
  obtain ⟨K, hK3, H⟩ := erdos_47489_hyp_medium C hC
  refine ⟨K, hK3, ?_⟩
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image (fun T : ℕ × ℕ × ℕ => T.2.2)).bddAbove
  obtain ⟨m, k, hmN, hk, hval⟩ := H B
  have hmem : ((m, m + k, 2 * m) : ℕ × ℕ × ℕ) ∈ { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 } := by
    show m > 0 ∧ m + k > 0 ∧ 2 * m > 0 ∧
      ((m : ℕ) : ℝ) + ((m + k : ℕ) : ℝ) > ((2 * m : ℕ) : ℝ) + C * Real.log ((2 * m : ℕ) : ℝ) ∧
      ∀ p, p.Prime → p > K →
        padicValNat p (((2 * m).factorial / (m.factorial * (m + k).factorial) : ℚ).den) = 0
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · have hk' := hk
      push_cast at hk' ⊢
      linarith
    · intro p hp hpK
      apply erdos_47489_hyp_den_of_val (2 * m) m (m + k) p hp
      by_cases h : p ≤ 2 * k
      · exact hval p hp hpK h
      · exact erdos_47489_hyp_large_primes m k p hp (by omega)
  have h2 := hB (Set.mem_image_of_mem (fun T : ℕ × ℕ × ℕ => T.2.2) hmem)
  have h3 : 2 * m ≤ B := h2
  omega