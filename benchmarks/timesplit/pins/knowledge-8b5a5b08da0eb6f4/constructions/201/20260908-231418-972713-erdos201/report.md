# Construction — Erdős #201 (run 20260908-231418-972713-erdos201)

**CERTIFIED BOUND, NOT A RESOLUTION.** Lean certificate did NOT compile for the finite property of the best object found. Requires human review before any external claim.

- known bound (literature/triage): G_k(N) ≤ R_k(N) trivially, with strict inequality possible (G_3(5)=3<4=R_3(5)); Komlós–Sulyok–Szemerédi: R_k(N) ≤ C_k·G_k(N); limit R_3/G_3 → 1 unknown in both directions; achieved score: 1.014
- object: `{"N": 14, "A": [0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26]}`
- description: N=14, A=[0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26]: roth(A)=7, R_3(N)=8, gap=1 (score unit: R_3(N)-roth(A); known best gap 1). Certifies G_3(14) <= 7 and R_3(14) >= 8.
- iterations: 2; archive top scores: [1.014, 1.014, 1.014, 1.014, 1.014]

## Frozen target (unproved)
```lean
-- IMPORTS: Mathlib.Combinatorics.Additive.AP.Three.Defs
-- IMPORTS: Mathlib.Analysis.SpecificLimits.Basic
-- CHECK: addRothNumber rothNumberNat
/-- `G_3(N)` as the minimum, over all `N`-element sets `A ⊆ ℤ`, of the Roth number of `A`
(the largest 3-AP-free subset of `A`). -/
noncomputable def erdos201_G (N : ℕ) : ℕ :=
  ⨅ A : {A : Finset ℤ // A.card = N}, addRothNumber A.1

theorem erdos_201 :
    Filter.Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (erdos201_G N : ℝ))
      Filter.atTop (nhds 1) := by
  sorry
```
