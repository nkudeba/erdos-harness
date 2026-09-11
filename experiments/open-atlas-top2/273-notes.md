# Erdős #273 — analysis produced in this session (operator-supplied to the run)

Statement: *Is there a covering system all of whose moduli are of the form `p−1` for some prime `p ≥ 5`?*

## 0. The statement needs "distinct"

The site's wording omits it, but [ErGr80] — the source — and google-deepmind/formal-conjectures both mean
**distinct** moduli: the formal statement is `∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ p, p.Prime ∧ 5 ≤ p ∧
c.moduli i = Ideal.span {↑(p−1)}`, and `StrictCoveringSystem` is `CoveringSystem` plus
`injective_moduli`, with a docstring saying this is "the notion of a covering system that Erdős was
using in [ErGr80]". **Without distinctness the problem is trivially YES**: `0,1,2,3 (mod 4)` covers ℤ and
`4 = 5−1`. Any formalisation that drops injectivity is unfaithful and vacuously solvable.

## 1. Parity reduction

Every allowed modulus `p−1` (`p ≥ 5`) is **even**. A class `a mod 2m'` consists entirely of even numbers
when `a` is even and entirely of odd numbers when `a` is odd. Halving (`n = 2t` resp. `n = 2t+1`) turns
such a class into `t ≡ b (mod m')`. So a covering system with distinct moduli from `P = {p−1 : p ≥ 5}`
is **exactly** a pair of **disjoint** distinct-modulus covering systems with moduli drawn from

    H = { m ≥ 2 : 2m+1 is prime } = {2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,33,35,36,39,41,44,…}

(disjoint because the original moduli must be distinct and halving is injective).

## 2. A self-verified floor on the lcm

Each of the two families needs reciprocal sum `≥ 1`, and both draw from the divisors of `L'` = lcm of the
halved moduli. So a **necessary** condition is

    f(L') := Σ_{d | L', 2d+1 prime} 1/d  ≥  2.

A divisor sieve to `3·10^6` gives `min{ L' : f(L') ≥ 2 } = 27720`, so the lcm of the original moduli is
**at least 55440**, and only **29** values of `L'` are `≤ 200000`:

    27720, 32760, 50400, 55440, 65520, 75600, 83160, 90720, 98280, 100800, 102960, 110880, 113400,
    115920, 120960, 128520, 131040, 138600, 151200, 154440, 163800, 166320, 171360, 173880, 180180,
    181440, 189000, 194040, 196560

Cross-check: 28 of these are `< 196560`, matching the "28 candidates with L < 393120" in the (unverified)
third-party proof claim on the site, whose bound `393120 = 2 · 196560` is exactly `2 ×` the largest entry
of this list. The screen here is independent and reproduces their candidate set.

## 3. The budget is the obstruction, and it is severe

`f(L')` never gets far above 2: the richest smooth `L' ≤ 4·10^6` is `3603600` with `f = 2.3038`. So across
**both** families the total slack is at most ≈ 0.30, and every modulus with `1/m >` slack must be used.

## 4. Search results (this session)

- **Exhaustive elimination** of the 29 candidates by DFS (residues forced by "cover the least uncovered
  point"): **inconclusive**. Two prunes were tried. (a) combined remaining density vs. unused reciprocal
  budget — tree exceeds 3·10^6 nodes on the very first candidate. (b) additionally a per-prime-power
  *capacity* prune: for `q = p^a || L'` every fibre `y ∈ ℤ/q` needs capacity `≥ 1`, where a class of
  modulus `m` contributes `p^{v_p(m)}/m` to the `q/p^{v_p(m)}` fibres it meets, and an unused `m` can
  supply at most `q/m` in total, giving
  `Σ_y max(0,1−capA[y]) + Σ_y max(0,1−capB[y]) ≤ q · Σ_{unused} 1/m` (the plain density bound is the
  `q = 1` case). Still inconclusive: `L' = 27720` alone exceeds 2·10^7 nodes. So this session did **not**
  independently confirm the third-party `lcm ≥ 393120` claim; the candidate *list* was reproduced, the
  elimination of it was not.
- **Constructive search** (randomized, reciprocal-balanced split of the divisor pool, then a greedy
  ascending build per family), on the richest candidates:

  | L' | budget | pool | balanced restarts | best combined residual |
  |---|---|---|---|---|
  | 3603600 | 2.3038 | 141 | 230 | 852514 / 7207200 = **11.83 %** |
  | 2162160 | 2.2945 | 132 | 343 | 507090 / 4324320 = **11.73 %** |
  | 3243240 | 2.2794 | 129 | 250 | 786474 / 6486480 = **12.12 %** |

  Not a near miss: the best attempt still leaves ~12 % of both cyclic groups uncovered. The density in
  this pool is concentrated in a handful of small moduli (2, 3, 5, 6, 8, 9, 11) that only **one** of the
  two families can hold, and the other family's tail cannot make it up.

Conclusion for the Atlas: the affirmative direction is a finite certificate in principle, but the search
is not close, and the reciprocal budget makes it structurally tight rather than merely large.
