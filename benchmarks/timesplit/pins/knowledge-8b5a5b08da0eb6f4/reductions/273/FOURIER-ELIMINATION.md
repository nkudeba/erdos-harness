# Erdős #273 — the fibre/Fourier test eliminates 20 of the 29 candidate lcm values

**Date:** 2026-09-11.  **Cost:** $0, no model calls, milliseconds of compute.
**Supersedes** the divisibility-maximal condition in `STRUCTURE.md`, which is the `|W| = 1` special case.

## Result

Of the 29 values of `L ≤ 400,000` whose admissible divisors have reciprocal sum `≥ 1`,
**20 are eliminated outright** — no covering system with distinct moduli of the form `p−1`
(`p ≥ 5` prime) has any of those lcm values, whatever the residues.

Eliminated: 55440, 65520, 100800, 131040, 151200, 181440, 196560, 201600, 205920, 226800,
231840, 241920, 257040, 308880, 327600, 342720, 347760, 360360, 362880, 378000.

Surviving: 110880, 166320, 221760, 262080, 277200, 302400, 332640, 388080, 393120.

**The search floor advances from a `screen` at 55,440 to `exhaustive` at 110,880.**
Every candidate below 110,880 is now excluded by proof, not by a filter.

This settles by algebra the two candidates that consumed every previous attempt:
`L = 55,440` (three attempts, two hand encodings and one harness escalation) and
`L = 100,800` (two encodings). Four solver runs timed out on them; the test decides
both in under a millisecond.

## The condition

Let `U` be the modulus set (all `m | L`), `a_m` the residues, and let the classes cover ℤ
with excess count `k = Σ_{m∈U} L/m − L`. Then for every `d | L`, `d > 1`, and every
primitive `d`-th root of unity `ζ`:

        Σ_{m ∈ U, d | m} (L/m) · ζ^{a_m}  =  Σ_{j mod d} e(j) · ζ^j,       so  |LHS| ≤ k

where `e(j) ≥ 0` is the excess on the fibre `j mod d` and `Σ_j e(j) = k`.

### Elementary proof (no generating functions)

Split ℤ/L into the `d` fibres `j mod d`, each holding `L/d` points.
- A modulus `m` with `d | m` lies inside a single fibre and contributes `L/m` to it.
- A modulus with `d ∤ m` has `g = gcd(m,d) < d` and spreads evenly over the `d/g` fibres
  `j ≡ a_m (mod g)`; its ζ-transform is `ζ^{a_m} · Σ_t ζ^{gt} = 0` because `ζ^g ≠ 1`.
- The total multiplicity on fibre `j` is `L/d + e(j)`; the constant part has zero transform.

Hence the transform of the whole configuration reduces to the `d | m` terms on the left and
the excess on the right. Only the excess can survive, and it has only `k` units of mass. ∎

This is the standard argument behind Mirsky–Newman, applied at every `d` rather than only at
the largest modulus. **No novelty of technique is claimed.**

### The residue-free screen

By the reverse triangle inequality, with `W = {L/m : m ∈ U, d | m}`,

        2·max(W) − Σ(W)  >  k      ⟹  no such covering system.

Universal form (independent of which `U ⊆ A` is chosen), using `A` = all admissible divisors
of `L`, `slack = Σ_{m∈A} 1/m − 1`, and `forced = {m ∈ A : 1/m > slack}` (in every valid `U`):

        2·max{L/m : m forced, d|m}  −  Σ{L/m : m ∈ A, d|m}   >   ⌊slack·L⌋

## Why it bites hardest exactly where the candidate looked best

`k ≤ slack·L`. The candidates with tiny slack — the ones chosen for being "nearly determined"
— are precisely the ones with almost no excess budget, so the inequality is brutal there.
`L = 100,800` has `slack = 1/11200`, so `k ≤ 9`, against a forced Fourier mass of 1903 at `d = 16`.

| L | d | forced weight `L/m` | Σ weights | `\|P(ζ)\| ≥` | `k ≤` | margin |
|---|---|---|---|---|---|---|
| 55,440 | 16 | 3465 (`m=16`) | 4493 | 2437 | 2421 | **16** |
| 100,800 | 16 | 6300 (`m=16`) | 10697 | 1903 | 9 | 1894 |
| 327,600 | 16 | 20475 (`m=16`) | 27598 | 13352 | 12436 | 916 |
| 360,360 | 28 | 12870 (`m=28`) | 16350 | 9390 | 8535 | 855 |

`m = 16` does most of the work: `17` is prime, so `16` is admissible, and it is forced in every
one of these candidates while the other admissible multiples of 16 are too sparse to cancel it.
The 55,440 margin is only 16 units wide and was re-verified in exact rational arithmetic.

## Validation performed before use

- The identity was checked numerically at **every divisor `d`** of `L` on five genuine covering
  systems (`L` = 12, 24, 36, 48), residues found by exhaustive search rather than guessed.
  Worst residual `9.7e−15`.
- Regression: 18 genuine covering systems with distinct moduli and `lcm = L` exactly,
  enumerated over `L ∈ {12,16,24,30,36,48,60}` — **zero false kills** (`fourier_regression.py`).
- The two tightest eliminations re-derived in exact `Fraction` arithmetic.

## What this does NOT do

It does not resolve #273. Nine candidates below 400,000 survive, all of them loose
(slack 0.02–0.08, so `k` in the thousands, where the inequality has no bite), and the candidate
list itself is capped at 400,000 by compute, not by any theorem — a witness may have a much
larger lcm. A covering system still has to be exhibited, or an infinite argument found.

Reproduce: `python3 knowledge/reductions/273/fourier_sweep.py`

---

# Follow-up (same day): the test family is now provably exhausted

The question asked was whether a branch-and-bound over modulus subsets could kill the nine
survivors, since the universal test above deliberately used the weakest case (all admissible
moduli in the sum, maximal `k`). The answer is **no, and it is not a search failure** — the
question is decidable in polynomial time and the answer comes out negative.

## 1. The tightest form ranges over `μ ∈ U`, not over `d | L`

For a divisor `d`, let `μ_d = min{m ∈ U : d | m}`, so `max(W) = L/μ_d`. Because `d | μ_d`, the
set `{m ∈ U : μ_d | m}` is a *subset* of `{m ∈ U : d | m}`, so its weight sum is smaller and the
constraint taken at `d = μ_d` is **strictly tighter**. Every `d`-constraint is therefore implied
by a `μ`-constraint, and the whole family collapses to:

        U is alive  ⟺  for every μ ∈ U:   L/μ  −  Σ_{m ∈ U, μ|m, m≠μ} L/m   ≤   k_U

*Reading:* each modulus's own mass `L/μ` must be balanced by the proper multiples of `μ` present
in `U`, to within the total excess budget.

## 2. Deciding it is propagation, not search

Write `w_m = L/m`, `T = Σ_U w_m`, `k_U = T − L`. The constraint at `μ` rearranges to

        Σ_{m ∈ U} c_m^μ  ≥  w_μ + L,     c_m^μ = w_m · (2 if μ|m and m≠μ else 1)

The left side is **monotone increasing in `U`** and every `c > 0`. So if `μ` violates its
constraint under the maximal set `A`, it violates under *every* `U ⊆ A` containing it: `μ` can
belong to no valid modulus set at all and may be deleted outright. Iterating to a fixed point is
complete — the final set is a superset of every valid `U`. If its reciprocal sum drops below 1,
`L` is eliminated; otherwise no subset whatsoever is killed by this family.

`2^47`-style enumeration is unnecessary and was never the obstacle.

## 3. Result

Propagation eliminates **exactly the same 20** candidates — and at all nine survivors it deletes
**zero** moduli: the full admissible set already satisfies every constraint. No subset search can
improve on that, so this test family is finished on those nine.

How far short it falls (best `d` over all divisors, using the full admissible set):

| L | dominant weight | other weights | \|P(ζ)\| ≥ | k may reach | short by |
|---|---|---|---|---|---|
| 302,400 | 18,900 | 14,144 | 4,756 | 6,700 | **1,944** |
| 262,080 | 16,380 | 10,896 | 5,484 | 9,036 | 3,552 |
| 110,880 | 6,930 | 3,851 | 3,079 | 6,637 | 3,558 |
| 388,080 | 24,255 | 7,286 | 16,969 | 20,845 | 3,876 |
| 166,320 | 10,395 | 3,564 | 6,831 | 11,085 | 4,254 |
| 393,120 | 24,570 | 13,812 | 10,758 | 18,626 | 7,868 |
| 277,200 | 17,325 | 6,166 | 11,159 | 19,463 | 8,304 |
| 221,760 | 13,860 | 9,888 | 3,972 | 15,460 | 11,488 |
| 332,640 | 20,790 | 12,537 | 8,253 | 27,579 | 19,326 |

Compare the eliminations: 55,440 is over by 16 and 100,800 by 1,894. The closest survivor misses
by 1,944 out of a 6,700 budget — a 29% gap, not a near miss.

**The structural reason is intrinsic, not incidental.** `k ≤ slack·L`, so the inequality has bite
exactly when slack is tiny. The 20 eliminated candidates are the tight ones; the nine survivors
all have slack 0.02–0.08, leaving thousands of units of excess to absorb any imbalance. Tightness
was what made a candidate look attackable, and it is the same property this test needs — so the
algebra consumed precisely the candidates that a search would also have preferred, and left behind
the ones that are loose for both.

## 4. Regression for the tighter form

3,130 genuine covering systems built by randomized greedy construction across
`L ∈ {12,…,720}`, distinct moduli, `lcm = L` exactly, overlaps `k` from 4 upward —
**zero false kills** (`fourier_propagate.py`, `mu_kill`).

## 5. Consequence for the attack plan

The nine survivors need SAT or new mathematics, and they are *worse* SAT targets than the ones
already tried: larger (`L` = 110k–393k, `|A|` = 52–72) and looser (more residue freedom). The two
collapsible candidates are gone. **#273 is now a less attractive resolution target than before
this work, not a more attractive one** — the banked value is the floor, not a route to a witness.
