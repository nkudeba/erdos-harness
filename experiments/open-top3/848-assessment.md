# Erdős #848 — feasibility assessment (open problem, site class "decidable")

**Verdict: 2/10. The mathematics is done; only an unreachable finite check remains.**

Statement: is the maximum size of A ⊆ {1..N} with ab+1 never squarefree achieved by taking n ≡ 7 (mod 25)?

## Exact computation (independent, this session)

Reduced to maximum clique: vertices are the ~0.105N candidates (a with a²+1 non-squarefree), edges are pairs
with ab+1 non-squarefree. Exact branch-and-bound, graph cross-validated against brute-force squarefree
testing at N = 300 with zero mismatches.

| N | candidates | conjectured optimum | true optimum | agree | best set containing an outsider |
|---|---|---|---|---|---|
| 1 006 | 105 | 40 | 40 | yes | 18 |
| 10 006 | 1 048 | 400 | 400 | yes | 153 |
| 20 006 | 2 100 | 800 | 800 | yes | 301 |
| 60 006 | 6 303 | 2 400 | 2 400 | yes | — |

The conjecture is exactly tight at every N tested, extending the "few hundred" range reported on the forum.
**The margin grows linearly**: any valid set containing even one element outside ±7 mod 25 tops out near
0.376 of the optimum at N = 20006, and that ratio is still falling. There is no near-miss structure to chase.

## Why it is out of reach

Sawhney proved the conjecture for all sufficiently large N. Four months of collaborative work ground the
explicit threshold from exp(682276) down to **2.64×10^17**, reported as the wall of the current proof
structure. The residual open region is every N below that. The largest feasible exact check is around
N ≈ 10^6 (dense adjacency is 1.4 GB at 10^6, 137 GB at 10^7), leaving a gap of roughly eleven orders of
magnitude. Closing it needs analytic improvement to Sawhney's constants, specifically a large sieve for
square moduli that several people and frontier models have failed to make applicable. That is not
computation, and not something this harness does.

Note the forum's one proof claim, a C++ verification to N = 10^7, was rebutted as likely incorrect. Any
computational range we report must be stated as "verified, no counterexample, N ≤ X", never as progress.

## The one genuinely useful find

Greedy colouring meets the clique number exactly at every N tested (40/40, 200/200, 400/400, 1000/1000).
A proper colouring is a small kernel-checkable certificate for the upper bound, and a plain degree-ordered
greedy already achieves it. That is a real certificate route nobody in the thread has remarked on.

## Lean cost, measured

Certifying non-squarefreeness from an explicit witness is free. Certifying squarefreeness needs a
factorization certificate per number: `decide` via `Nat.minSqFac` was killed after seven minutes on a single
seven-digit number, while `rw [Nat.squarefree_iff_nodup_primeFactorsList]; simp` with the Factors simproc
takes 0.1–0.3 s. A single N needs about 1.07N such facts, so N = 60006 is roughly 3.6 hours of Lean and
N = 10^6 about 2.5 days, for one value of N. An existing 3,900-line Lean formalization of Sawhney's
asymptotic theorem already exists with no sorries and no `native_decide`.
