open scoped Classical
open Filter

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop := ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

-- Upper-bound core (open): every admissible set in [1,n] has size O(n loglog n / log n).
-- A counterexample would need admissible sets of size ≫ n loglog n / log n. Such sets are
-- still bounded by the squarefree count (R1).
theorem erdos_87680_hyp_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, RequiredCondition A n →
      (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  sorry

-- Lower-bound core (open): a construction of admissible sets of size ≫ n loglog n / log n.
-- The absolute value is harmless, since the quantity is positive for n ≥ 3.
-- The primes ∪ {1} construction gives only π(n)+1, which is too small.
namespace erdos_87680_hyp_lower_ns
open scoped Classical

noncomputable def semiprimeSet (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter (fun m => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ m = p * q)

-- Derived (conjecture, elementary): every element of semiprimeSet n is squarefree, so it is an edge
-- {p,q} of a simple graph on the primes. Suppose abcd is a square. Then every prime has even total
-- multiplicity in abcd.
-- Degenerate multisets: two distinct squarefree numbers never have square product. So a=b forces
-- c=d, and b=c forces a=d.
-- Four distinct edges with all degrees even form a 4-cycle. Sort its vertices w<x<y<z.
-- In every configuration the minimal edge and the maximal edge are opposite edges of the cycle,
-- so ad = product of all four vertices = bc.
namespace erdos_87680_hyp_lower_hyp_admissible_ns

private lemma e87680_sq_cancel {k X : ℕ} (hk : 0 < k) (h : IsSquare (k * k * X)) : IsSquare X := by
  obtain ⟨m, hm⟩ := h
  have h2 : k * k ∣ m * m := ⟨X, hm.symm⟩
  have hdvd : k ∣ m := by
    first
    | exact Nat.mul_self_dvd_mul_self_iff.mp h2
    | exact (Nat.pow_dvd_pow_iff two_ne_zero).mp (by rw [sq, sq]; exact h2)
  obtain ⟨t, rfl⟩ := hdvd
  refine ⟨t, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hk hk)
  rw [hm]; ring

private lemma e87680_dvd_of_sq {v X : ℕ} (hv : v.Prime) (h : IsSquare (v * X)) : v ∣ X := by
  obtain ⟨m, hm⟩ := h
  have h1 : v ∣ m * m := ⟨X, hm.symm⟩
  have h2 : v ∣ m := by
    rcases (Nat.Prime.dvd_mul hv).mp h1 with h | h <;> exact h
  obtain ⟨t, rfl⟩ := h2
  refine ⟨t * t, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hv.pos
  rw [hm]; ring

private lemma e87680_eq_of_dvd_mul {v r s : ℕ} (hv : v.Prime) (hr : r.Prime) (hs : s.Prime)
    (h : v ∣ r * s) : v = r ∨ v = s := by
  rcases (Nat.Prime.dvd_mul hv).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hv hr).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hv hs).mp h)

private lemma e87680_not_sq {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    ¬ IsSquare (r * s) := by
  intro h
  exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp (e87680_dvd_of_sq hr h))

private lemma e87680_pair {a1 a2 b1 b2 : ℕ} (ha1 : a1.Prime) (ha2 : a2.Prime)
    (hb1 : b1.Prime) (hb2 : b2.Prime) (ha : a1 ≠ a2) (hb : b1 ≠ b2)
    (h : IsSquare (a1 * a2 * (b1 * b2))) : a1 * a2 = b1 * b2 := by
  have h1 : a1 ∣ a2 * (b1 * b2) := by
    apply e87680_dvd_of_sq ha1
    have e : a1 * (a2 * (b1 * b2)) = a1 * a2 * (b1 * b2) := by ring
    rw [e]; exact h
  have h2 : a2 ∣ a1 * (b1 * b2) := by
    apply e87680_dvd_of_sq ha2
    have e : a2 * (a1 * (b1 * b2)) = a1 * a2 * (b1 * b2) := by ring
    rw [e]; exact h
  have h1' : a1 ∣ b1 * b2 := by
    rcases (Nat.Prime.dvd_mul ha1).mp h1 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq ha1 ha2).mp h) ha
    · exact h
  have h2' : a2 ∣ b1 * b2 := by
    rcases (Nat.Prime.dvd_mul ha2).mp h2 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq ha2 ha1).mp h) (Ne.symm ha)
    · exact h
  rcases e87680_eq_of_dvd_mul ha1 hb1 hb2 h1' with h3 | h3 <;>
    rcases e87680_eq_of_dvd_mul ha2 hb1 hb2 h2' with h4 | h4
  · exact absurd (h3.trans h4.symm) ha
  · rw [h3, h4]
  · rw [h3, h4]; ring
  · exact absurd (h3.trans h4.symm) ha

private lemma e87680_T1 {u v w x y : ℕ} (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hx : x.Prime) (hy : y.Prime) (hxy : x ≠ y)
    (h : IsSquare (u * v * (u * w) * (x * y))) : u * (x * y) = v * (u * w) := by
  have h' : IsSquare (v * w * (x * y)) := by
    apply e87680_sq_cancel hu.pos
    have e : u * u * (v * w * (x * y)) = u * v * (u * w) * (x * y) := by ring
    rw [e]; exact h
  by_cases hvw : v = w
  · rw [← hvw] at h'
    exact absurd (e87680_sq_cancel hv.pos h') (e87680_not_sq hx hy hxy)
  · have := e87680_pair hv hw hx hy hvw hxy h'
    rw [← this]; ring

private lemma e87680_T {u v x3 y3 x4 y4 : ℕ} (hu : u.Prime) (hv : v.Prime)
    (hx3 : x3.Prime) (hy3 : y3.Prime) (hx4 : x4.Prime) (hy4 : y4.Prime)
    (huv : u ≠ v) (h3 : x3 ≠ y3) (h4 : x4 ≠ y4)
    (h : IsSquare (u * v * (x3 * y3) * (x4 * y4))) :
    u * (x4 * y4) = v * (x3 * y3) ∨ u * (x3 * y3) = v * (x4 * y4) := by
  have hd : u ∣ v * (x3 * y3 * (x4 * y4)) := by
    apply e87680_dvd_of_sq hu
    have e : u * (v * (x3 * y3 * (x4 * y4))) = u * v * (x3 * y3) * (x4 * y4) := by ring
    rw [e]; exact h
  rcases (Nat.Prime.dvd_mul hu).mp hd with hd | hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hu hv).mp hd) huv
  rcases (Nat.Prime.dvd_mul hu).mp hd with hd | hd
  · rcases e87680_eq_of_dvd_mul hu hx3 hy3 hd with e | e
    · rw [← e] at h ⊢
      left; exact e87680_T1 hu hv hy3 hx4 hy4 h4 h
    · rw [← e] at h ⊢
      left
      have hs : IsSquare (u * v * (u * x3) * (x4 * y4)) := by
        have e' : u * v * (u * x3) * (x4 * y4) = u * v * (x3 * u) * (x4 * y4) := by ring
        rw [e']; exact h
      have := e87680_T1 hu hv hx3 hx4 hy4 h4 hs
      rw [this]; ring
  · rcases e87680_eq_of_dvd_mul hu hx4 hy4 hd with e | e
    · rw [← e] at h ⊢
      right
      have hs : IsSquare (u * v * (u * y4) * (x3 * y3)) := by
        have e' : u * v * (u * y4) * (x3 * y3) = u * v * (x3 * y3) * (u * y4) := by ring
        rw [e']; exact h
      exact e87680_T1 hu hv hy4 hx3 hy3 h3 hs
    · rw [← e] at h ⊢
      right
      have hs : IsSquare (u * v * (u * x4) * (x3 * y3)) := by
        have e' : u * v * (u * x4) * (x3 * y3) = u * v * (x3 * y3) * (x4 * u) := by ring
        rw [e']; exact h
      have := e87680_T1 hu hv hx4 hx3 hy3 h3 hs
      rw [this]; ring

private lemma e87680_G1 {x y1 y2 x3 y3 x4 y4 : ℕ}
    (hx : x.Prime) (hy1 : y1.Prime) (hy2 : y2.Prime)
    (hx3 : x3.Prime) (hy3 : y3.Prime) (hx4 : x4.Prime) (hy4 : y4.Prime)
    (h3 : x3 ≠ y3) (h4 : x4 ≠ y4)
    (h : IsSquare (x * y1 * (x * y2) * (x3 * y3) * (x4 * y4))) :
    x * y1 * (x * y2) = x3 * y3 * (x4 * y4) ∨
    x * y1 * (x3 * y3) = x * y2 * (x4 * y4) ∨
    x * y1 * (x4 * y4) = x * y2 * (x3 * y3) := by
  have h' : IsSquare (y1 * y2 * (x3 * y3) * (x4 * y4)) := by
    apply e87680_sq_cancel hx.pos
    have e : x * x * (y1 * y2 * (x3 * y3) * (x4 * y4)) =
        x * y1 * (x * y2) * (x3 * y3) * (x4 * y4) := by ring
    rw [e]; exact h
  by_cases hyy : y1 = y2
  · rw [← hyy] at h' ⊢
    have hcd : IsSquare (x3 * y3 * (x4 * y4)) := by
      apply e87680_sq_cancel hy1.pos
      have e : y1 * y1 * (x3 * y3 * (x4 * y4)) = y1 * y1 * (x3 * y3) * (x4 * y4) := by ring
      rw [e]; exact h'
    have := e87680_pair hx3 hy3 hx4 hy4 h3 h4 hcd
    right; left; rw [this]
  · rcases e87680_T hy1 hy2 hx3 hy3 hx4 hy4 hyy h3 h4 h' with r | r
    · right; right
      calc x * y1 * (x4 * y4) = x * (y1 * (x4 * y4)) := by ring
        _ = x * (y2 * (x3 * y3)) := by rw [r]
        _ = x * y2 * (x3 * y3) := by ring
    · right; left
      calc x * y1 * (x3 * y3) = x * (y1 * (x3 * y3)) := by ring
        _ = x * (y2 * (x4 * y4)) := by rw [r]
        _ = x * y2 * (x4 * y4) := by ring

private lemma e87680_G {x1 y1 x2 y2 x3 y3 x4 y4 : ℕ}
    (hx1 : x1.Prime) (hy1 : y1.Prime) (hx2 : x2.Prime) (hy2 : y2.Prime)
    (hx3 : x3.Prime) (hy3 : y3.Prime) (hx4 : x4.Prime) (hy4 : y4.Prime)
    (h1 : x1 ≠ y1) (h2 : x2 ≠ y2) (h3 : x3 ≠ y3) (h4 : x4 ≠ y4)
    (h : IsSquare (x1 * y1 * (x2 * y2) * (x3 * y3) * (x4 * y4))) :
    x1 * y1 * (x2 * y2) = x3 * y3 * (x4 * y4) ∨
    x1 * y1 * (x3 * y3) = x2 * y2 * (x4 * y4) ∨
    x1 * y1 * (x4 * y4) = x2 * y2 * (x3 * y3) := by
  have hd : x1 ∣ y1 * (x2 * y2 * (x3 * y3 * (x4 * y4))) := by
    apply e87680_dvd_of_sq hx1
    have e : x1 * (y1 * (x2 * y2 * (x3 * y3 * (x4 * y4)))) =
        x1 * y1 * (x2 * y2) * (x3 * y3) * (x4 * y4) := by ring
    rw [e]; exact h
  rcases (Nat.Prime.dvd_mul hx1).mp hd with hd | hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hx1 hy1).mp hd) h1
  rcases (Nat.Prime.dvd_mul hx1).mp hd with hd | hd
  · rcases e87680_eq_of_dvd_mul hx1 hx2 hy2 hd with e | e
    · rw [← e] at h ⊢
      exact e87680_G1 hx1 hy1 hy2 hx3 hy3 hx4 hy4 h3 h4 h
    · rw [← e] at h ⊢
      have hs : IsSquare (x1 * y1 * (x1 * x2) * (x3 * y3) * (x4 * y4)) := by
        have e' : x1 * y1 * (x1 * x2) * (x3 * y3) * (x4 * y4) =
            x1 * y1 * (x2 * x1) * (x3 * y3) * (x4 * y4) := by ring
        rw [e']; exact h
      rcases e87680_G1 hx1 hy1 hx2 hx3 hy3 hx4 hy4 h3 h4 hs with r | r | r <;>
      first
      | (left; linarith)
      | (right; left; linarith)
      | (right; right; linarith)
  rcases (Nat.Prime.dvd_mul hx1).mp hd with hd | hd
  · rcases e87680_eq_of_dvd_mul hx1 hx3 hy3 hd with e | e
    · rw [← e] at h ⊢
      have hs : IsSquare (x1 * y1 * (x1 * y3) * (x2 * y2) * (x4 * y4)) := by
        have e' : x1 * y1 * (x1 * y3) * (x2 * y2) * (x4 * y4) =
            x1 * y1 * (x2 * y2) * (x1 * y3) * (x4 * y4) := by ring
        rw [e']; exact h
      rcases e87680_G1 hx1 hy1 hy3 hx2 hy2 hx4 hy4 h2 h4 hs with r | r | r <;>
      first
      | (left; linarith)
      | (right; left; linarith)
      | (right; right; linarith)
    · rw [← e] at h ⊢
      have hs : IsSquare (x1 * y1 * (x1 * x3) * (x2 * y2) * (x4 * y4)) := by
        have e' : x1 * y1 * (x1 * x3) * (x2 * y2) * (x4 * y4) =
            x1 * y1 * (x2 * y2) * (x3 * x1) * (x4 * y4) := by ring
        rw [e']; exact h
      rcases e87680_G1 hx1 hy1 hx3 hx2 hy2 hx4 hy4 h2 h4 hs with r | r | r <;>
      first
      | (left; linarith)
      | (right; left; linarith)
      | (right; right; linarith)
  · rcases e87680_eq_of_dvd_mul hx1 hx4 hy4 hd with e | e
    · rw [← e] at h ⊢
      have hs : IsSquare (x1 * y1 * (x1 * y4) * (x2 * y2) * (x3 * y3)) := by
        have e' : x1 * y1 * (x1 * y4) * (x2 * y2) * (x3 * y3) =
            x1 * y1 * (x2 * y2) * (x3 * y3) * (x1 * y4) := by ring
        rw [e']; exact h
      rcases e87680_G1 hx1 hy1 hy4 hx2 hy2 hx3 hy3 h2 h3 hs with r | r | r <;>
      first
      | (left; linarith)
      | (right; left; linarith)
      | (right; right; linarith)
    · rw [← e] at h ⊢
      have hs : IsSquare (x1 * y1 * (x1 * x4) * (x2 * y2) * (x3 * y3)) := by
        have e' : x1 * y1 * (x1 * x4) * (x2 * y2) * (x3 * y3) =
            x1 * y1 * (x2 * y2) * (x3 * y3) * (x4 * x1) := by ring
        rw [e']; exact h
      rcases e87680_G1 hx1 hy1 hx4 hx2 hy2 hx3 hy3 h2 h3 hs with r | r | r <;>
      first
      | (left; linarith)
      | (right; left; linarith)
      | (right; right; linarith)

private lemma e87680_F {A B C D : ℕ} (hB : 0 < B) (hC : 0 < C)
    (hab : A ≤ B) (hbc : B ≤ C) (hcd : C ≤ D)
    (h : A * B = C * D ∨ A * C = B * D ∨ A * D = B * C) : A * D = B * C := by
  rcases h with h | h | h
  · have h1 : A * B ≤ C * B := Nat.mul_le_mul (le_trans hab hbc) le_rfl
    have h2 : C * B ≤ C * D := Nat.mul_le_mul le_rfl (le_trans hbc hcd)
    have h3 : C * B = C * D := by linarith
    have h4 : A * B = C * B := by linarith
    have hBD : B = D := Nat.eq_of_mul_eq_mul_left hC h3
    have hAC : A = C := Nat.eq_of_mul_eq_mul_right hB h4
    rw [hAC, ← hBD]; ring
  · have h1 : A * C ≤ B * C := Nat.mul_le_mul hab le_rfl
    have h2 : B * C ≤ B * D := Nat.mul_le_mul le_rfl hcd
    have h3 : B * C = B * D := by linarith
    have h4 : A * C = B * C := by linarith
    have hCD : C = D := Nat.eq_of_mul_eq_mul_left hB h3
    have hAB : A = B := Nat.eq_of_mul_eq_mul_right hC h4
    rw [hAB, hCD]
  · exact h

open scoped Classical

open scoped Classical

open Filter

theorem erdos_87680_hyp_lower_hyp_admissible :
    ∀ n : ℕ, semiprimeSet n ⊆ Finset.Ioc 0 n ∧
      ∀ᵉ (a ∈ semiprimeSet n) (b ∈ semiprimeSet n) (c ∈ semiprimeSet n) (d ∈ semiprimeSet n),
        a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c := by
  intro n
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [semiprimeSet, Finset.mem_filter] at hx
    exact hx.1
  · intro a ha b hb c hc d hd hab hbc hcd hsq
    simp only [semiprimeSet, Finset.mem_filter] at ha hb hc hd
    obtain ⟨_, x1, y1, hx1, hy1, hl1, rfl⟩ := ha
    obtain ⟨_, x2, y2, hx2, hy2, hl2, rfl⟩ := hb
    obtain ⟨_, x3, y3, hx3, hy3, hl3, rfl⟩ := hc
    obtain ⟨_, x4, y4, hx4, hy4, hl4, rfl⟩ := hd
    exact e87680_F (Nat.mul_pos hx2.pos hy2.pos) (Nat.mul_pos hx3.pos hy3.pos) hab hbc hcd
      (e87680_G hx1 hy1 hx2 hy2 hx3 hy3 hx4 hy4 hl1.ne hl2.ne hl3.ne hl4.ne hsq)

end erdos_87680_hyp_lower_hyp_admissible_ns

theorem erdos_87680_hyp_lower_hyp_admissible :
    ∀ n : ℕ, semiprimeSet n ⊆ Finset.Ioc 0 n ∧
      ∀ᵉ (a ∈ semiprimeSet n) (b ∈ semiprimeSet n) (c ∈ semiprimeSet n) (d ∈ semiprimeSet n),
        a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c := by
  exact erdos_87680_hyp_lower_hyp_admissible_ns.erdos_87680_hyp_lower_hyp_admissible

-- PUBLISHED: E. Landau, Handbuch der Lehre von der Verteilung der Primzahlen (1909), §56;
-- also Hardy–Wright, An Introduction to the Theory of Numbers, Theorem 437.
-- The theorem says pi_2(x) ~ x loglog x / log x, where pi_2(x) counts products of two distinct
-- primes up to x. Below is the lower-bound consequence of that asymptotic.
theorem erdos_87680_hyp_lower_hyp_semiprime_count :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(n : ℝ) * Real.log (Real.log n) / Real.log n| ≤ c * ((semiprimeSet n).card : ℝ) := by
  sorry

open scoped Classical

open Filter

theorem erdos_87680_hyp_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ A : Finset ℕ, RequiredCondition A n ∧
      |(n : ℝ) * Real.log (Real.log n) / Real.log n| ≤ c * (A.card : ℝ) := by
  obtain ⟨c, hc, N, hN⟩ := erdos_87680_hyp_lower_hyp_semiprime_count
  refine ⟨c, hc, N, fun n hn => ⟨semiprimeSet n, ?_, hN n hn⟩⟩
  exact erdos_87680_hyp_lower_hyp_admissible n
end erdos_87680_hyp_lower_ns

theorem erdos_87680_hyp_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ A : Finset ℕ, RequiredCondition A n ∧
      |(n : ℝ) * Real.log (Real.log n) / Real.log n| ≤ c * (A.card : ℝ) := by
  exact erdos_87680_hyp_lower_ns.erdos_87680_hyp_lower



theorem erdos_87680 :
    (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  obtain ⟨C, hC, N, hN⟩ := erdos_87680_hyp_upper
  obtain ⟨c, hc, M, hM⟩ := erdos_87680_hyp_lower
  have hempty : ∀ n : ℕ, p n 0 := by
    intro n
    refine ⟨∅, ⟨Finset.empty_subset _, ?_⟩, rfl⟩
    intro a ha
    simp at ha
  unfold Asymptotics.IsTheta
  refine ⟨?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound C ?_
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    show ‖((Nat.findGreatest (p n) n : ℕ) : ℝ)‖
        ≤ C * ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖
    have hs : p n (Nat.findGreatest (p n) n) :=
      Nat.findGreatest_spec (Nat.zero_le n) (hempty n)
    obtain ⟨A, hA, hcard⟩ := hs
    rw [Real.norm_natCast, ← hcard]
    calc (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := hN n hn A hA
      _ ≤ C * ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖ :=
          mul_le_mul_of_nonneg_left (Real.le_norm_self _) hC.le
  · refine Asymptotics.IsBigO.of_bound c ?_
    refine Filter.eventually_atTop.2 ⟨M, fun n hn => ?_⟩
    show ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖
        ≤ c * ‖((Nat.findGreatest (p n) n : ℕ) : ℝ)‖
    obtain ⟨A, hA, hg⟩ := hM n hn
    have hk : A.card ≤ n := by
      obtain ⟨hsub, -⟩ := hA
      have h1 := Finset.card_le_card hsub
      simpa using h1
    have hpA : p n A.card := ⟨A, hA, rfl⟩
    have hle : A.card ≤ Nat.findGreatest (p n) n := Nat.le_findGreatest hk hpA
    rw [Real.norm_natCast, Real.norm_eq_abs]
    calc |(n : ℝ) * Real.log (Real.log n) / Real.log n| ≤ c * (A.card : ℝ) := hg
      _ ≤ c * ((Nat.findGreatest (p n) n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hc.le