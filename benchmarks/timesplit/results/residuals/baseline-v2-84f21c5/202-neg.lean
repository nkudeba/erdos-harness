open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- Derived: for N ≥ 3, log N > 1 because exp 1 < 3, so log (log N) > 0.
-- Hence log N * log (log N) > 0, its square root is positive, and exp of a positive number exceeds 1.
namespace erdos_30426_neg_hyp_scaleL_gt_one_ns
open Real

open Filter Real

theorem erdos_30426_neg_hyp_scaleL_gt_one :
    ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  intro N hN
  unfold scaleL
  have hN3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have h1 : 1 < Real.log N := by
    by_contra hc
    push_neg at hc
    have h := Real.exp_le_exp.mpr hc
    rw [Real.exp_log hNpos] at h
    have := Real.exp_one_lt_d9
    linarith
  have h2 : 0 < Real.log (Real.log N) := Real.log_pos h1
  have h3 : 0 < Real.log N * Real.log (Real.log N) := mul_pos (by linarith) h2
  have h4 : 0 < Real.sqrt (Real.log N * Real.log (Real.log N)) := Real.sqrt_pos.mpr h3
  have h5 := Real.add_one_le_exp (Real.sqrt (Real.log N * Real.log (Real.log N)))
  linarith
end erdos_30426_neg_hyp_scaleL_gt_one_ns

theorem erdos_30426_neg_hyp_scaleL_gt_one :
    ∀ N : ℕ, 3 ≤ N → 1 < scaleL N := by
  exact erdos_30426_neg_hyp_scaleL_gt_one_ns.erdos_30426_neg_hyp_scaleL_gt_one



-- Conjecture (the open core): the de la Bretèche–Ford–Vandehey exponent c satisfies liminf e(N) < 1,
-- where e(N) = log(N / f N) / sqrt(log N * log log N).
-- The target is equivalent to e(N) not tending to 1.
-- Given the (recalled) lower bound f N ≥ N / L^(1+o(1)), the only way the target can hold is that f is frequently large, as stated here.
theorem erdos_30426_neg_hyp_freq_large :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (N : ℝ) * scaleL N ^ (-1 + δ) ≤ (f N : ℝ) := by
  sorry

theorem erdos_30426_neg :
    ¬ (∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N)) := by
  rintro ⟨o, ho, hev⟩
  obtain ⟨δ, hδ, hfreq⟩ := erdos_30426_neg_hyp_freq_large
  have ht : Tendsto o atTop (nhds 0) := by
    simpa using ho.tendsto_div_nhds_zero
  have h1 : ∀ᶠ N : ℕ in atTop, o N < δ := ht (Iio_mem_nhds hδ)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 ((hev.and h1).and (eventually_ge_atTop 3))
  obtain ⟨N, hMN, hN⟩ := hfreq M
  obtain ⟨⟨hfN, hoN⟩, h3⟩ := hM N hMN
  have hL : 1 < scaleL N := erdos_30426_neg_hyp_scaleL_gt_one N h3
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast h3
    linarith
  have hlt : scaleL N ^ (-1 + o N) < scaleL N ^ (-1 + δ) :=
    Real.rpow_lt_rpow_of_exponent_lt hL (by linarith)
  have hmul := mul_lt_mul_of_pos_left hlt hNpos
  rw [hfN] at hN
  linarith