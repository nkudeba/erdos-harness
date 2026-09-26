# Partial result — Erdős #699 (run pos)

**Status: PARTIAL — the main theorem was NOT proved.** These sorry-free auxiliary lemmas compiled against the frozen setting and are kept for reuse. They are NOT a resolution of the problem and require human review before any external claim.

## Frozen target (unproved)
```lean
theorem erdos_699 :
    ∀ n i j : ℕ, 1 ≤ i → i < j → 2 * j ≤ n →
      ∃ p : ℕ, Nat.Prime p ∧ i ≤ p ∧
        p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry
```

## Compiled lemmas
- `quot_gcd_dvd_choose'`
- `dvd_descFactorial'`

```lean
private lemma quot_gcd_dvd_choose' (n j : ℕ) (hj : 1 ≤ j) :
    n / Nat.gcd n j ∣ Nat.choose n j := by
  obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd0 : 0 < Nat.gcd (m + 1) (l + 1) := by
    rcases Nat.eq_zero_or_pos (Nat.gcd (m + 1) (l + 1)) with h | h
    · exact absurd (Nat.eq_zero_of_gcd_eq_zero_right h) (by omega)
    · exact h
  have ha : Nat.gcd (m + 1) (l + 1) * ((m + 1) / Nat.gcd (m + 1) (l + 1)) = m + 1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hb : Nat.gcd (m + 1) (l + 1) * ((l + 1) / Nat.gcd (m + 1) (l + 1)) = l + 1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime ((m + 1) / Nat.gcd (m + 1) (l + 1))
      ((l + 1) / Nat.gcd (m + 1) (l + 1)) := Nat.coprime_div_gcd_div_gcd hd0
  have hid : (m + 1) * Nat.choose m l = Nat.choose (m + 1) (l + 1) * (l + 1) := by
    simpa using Nat.succ_mul_choose_eq m l
  have key : ((m + 1) / Nat.gcd (m + 1) (l + 1)) * Nat.choose m l
      = Nat.choose (m + 1) (l + 1) * ((l + 1) / Nat.gcd (m + 1) (l + 1)) := by
    refine Nat.eq_of_mul_eq_mul_left hd0 ?_
    calc Nat.gcd (m + 1) (l + 1) * (((m + 1) / Nat.gcd (m + 1) (l + 1)) * Nat.choose m l)
        = (Nat.gcd (m + 1) (l + 1) * ((m + 1) / Nat.gcd (m + 1) (l + 1))) * Nat.choose m l := by
          ring
      _ = (m + 1) * Nat.choose m l := by rw [ha]
      _ = Nat.choose (m + 1) (l + 1) * (l + 1) := hid
      _ = Nat.choose (m + 1) (l + 1) *
            (Nat.gcd (m + 1) (l + 1) * ((l + 1) / Nat.gcd (m + 1) (l + 1))) := by rw [hb]
      _ = Nat.gcd (m + 1) (l + 1) *
            (Nat.choose (m + 1) (l + 1) * ((l + 1) / Nat.gcd (m + 1) (l + 1))) := by ring
  exact hcop.dvd_of_dvd_mul_right ⟨Nat.choose m l, key.symm⟩


private lemma dvd_descFactorial' (p n t : ℕ) (h : p ∣ n - t) :
    ∀ i, t < i → p ∣ Nat.descFactorial n i := by
  intro i
  induction i with
  | zero => intro hti; omega
  | succ k ih =>
    intro hti
    rw [Nat.descFactorial_succ]
    rcases Nat.lt_or_ge t k with hk | hk
    · exact dvd_mul_of_dvd_right (ih hk) _
    · have htk : t = k := by omega
      rw [htk] at h
      exact dvd_mul_of_dvd_left h _

```
