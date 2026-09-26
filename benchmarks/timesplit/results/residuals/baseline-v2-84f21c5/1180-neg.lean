open Filter

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

-- Failure at a single ε = 1/k (reduction R4), with the coprimality side condition dropped
-- (reduction R3), so this is a stronger failure statement than the target needs.
-- A counterexample to the ∀ε statement must satisfy this (by R1, R3, R4).
-- Believed FALSE: the affirmative answer is recalled in the literature, and the data
-- for ε = 1/2 and ε = 1/3 show no growth in the worst-case count.
theorem erdos_85699_neg_hyp_fail_at_inv_k :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ C : ℕ, ∃ p : ℕ, p.Prime ∧ ∃ a : ZMod p,
      ∀ s : Multiset ℕ, s.card ≤ C →
        (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / (k : ℝ))) →
        (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum ≠ a := by
  sorry

theorem erdos_85699_neg :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s) := by
  intro h
  obtain ⟨k, hk, hfail⟩ := erdos_85699_neg_hyp_fail_at_inv_k
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkpos : (0 : ℝ) < (1 : ℝ) / (k : ℝ) := div_pos one_pos hk0
  obtain ⟨C, hC⟩ := h _ hkpos
  obtain ⟨p, hp, a, ha⟩ := hfail C
  obtain ⟨s, hs, hrep⟩ := hC p hp a
  exact ha s hs (fun n hn => ⟨(hrep.1 n hn).1, (hrep.1 n hn).2.1⟩) hrep.2