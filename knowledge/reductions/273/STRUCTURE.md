# Erdős #273 — the candidate structure, and where the search actually stands

## The candidate list

A covering system's moduli have some lcm `L`, and every modulus divides `L`, so a solution with
`lcm = L` exists only if the admissible divisors of `L` have reciprocal sum `≥ 1`. Exactly **29**
values of `L ≤ 400000` pass that screen; the smallest is 55,440 and the largest 393,120.

## Order candidates by SLACK, not by size

`slack(L) = Σ_{m | L, m admissible} 1/m − 1` is the total reciprocal weight that may go unused, so
**every modulus with `1/m > slack` is forced into any solution**. Small slack ⇒ almost everything
forced ⇒ a nearly determined instance.

| slack | L | moduli | forced | free |
|---|---|---|---|---|
| 0.000089 | **100,800** | 50 | **45** | **5** |
| 0.0031 | 205,920 | 48 | 23 | 25 |
| 0.0033 | 201,600 | 56 | 24 | 32 |
| 0.0437 | **55,440** | 43 | **7** | **36** |
| 0.0829 | 332,640 | 71 | 4 | 67 |

**55,440 is the smallest candidate and among the loosest.** Three separate attempts were spent on it
(two hand encodings, one harness escalation) purely because it is first numerically. That was the wrong
entry point, and the timeouts were saying so.

## L = 100,800 is the uniquely collapsible candidate

- 45 of 50 moduli forced; free = `[12600, 14400, 20160, 33600, 100800]`.
- The forced moduli alone cover **100,785 of 100,800** points with multiplicity — deficit 15.
- Total overlap is exactly `Σ_{used} L/m − L`, bounded by `slack·L` = **9 points**, so the classes must
  almost exactly TILE ℤ/L.
- Only **12 of 32** free subsets reach full coverage, and the subset choice leaves the SAT entirely.
- **2 of those 12 have overlap exactly 0** and are excluded by a theorem, not a search:
  Mirsky–Newman / Davenport–Rado — a disjoint covering system of ℤ by ≥ 2 congruences must repeat its
  largest modulus, so distinct moduli admit no exact cover.

## What is still out of reach

The 10 surviving subsets fix the modulus set, so each modulus takes **exactly one** residue (stronger
propagation than at-most-one). Each instance is still ≈440k variables / 740k clauses, and CaDiCaL did
not decide even the first one in 37 minutes. Four solver attempts on this problem have now timed out:
55,440 twice by hand, 55,440 once via the harness escalation, and 100,800 twice (monolithic, then
decomposed).

Deciding all 29 candidates would **not** resolve the problem. It would raise the verified floor from a
screen at 55,440 to an exhaustive 393,120 and independently confirm a third-party claim we could not
check. Resolution needs a witness, or an infinite argument.

## The next lever, untried and unverified

For a fixed modulus set with overlap `k ≤ 9`, the Mirsky–Newman generating-function argument does not
die — it becomes a *condition*. Writing the cover as `Σ_m z^{a_m}/(1−z^m) = 1/(1−z) + P(z)/(1−z^L)`
with `P` carrying at most `k` terms, and evaluating near a primitive `M`-th root of unity for
`M = max modulus`, the pole from the `M` term must be cancelled by the pole of `P/(1−z^L)`. That
matching is a strong necessary condition on WHICH residues the overlap points occupy, and with only 9
of them `P` is heavily constrained. It may kill the surviving subsets algebraically and cheaply.

**This is a suggestion, not a result.** It has not been derived carefully, checked numerically, or
verified by anyone. Do not treat it as established.

---

# The root-of-unity condition — derived, validated, applied (2026-09-11)

The lever flagged as "untried and unverified" above has now been derived and **checked numerically
before use**. It is a standard generating-function argument, not a new idea; no novelty is claimed.

## The identity

For classes `(aᵢ mod mᵢ)` covering ℤ with excess multiset `E` (residues mod `L = lcm`, counted with
their extra multiplicity):

    Σᵢ z^{aᵢ}/(1 − z^{mᵢ})  =  1/(1−z)  +  Σ_{r∈E} z^r/(1 − z^L)

Validated to ~1e-16 on four known systems, including the classic `{2,3,4,6,12}` cover and an exact
cover with a repeated modulus (`rootofunity_validation.py`).

## The condition

Let `m ∈ U` be **divisibility-maximal** (no other modulus in `U` is a multiple of it). Then no other
term has a pole at a primitive `m`-th root of unity `ζ`, so multiplying by `(1 − z^m)` and letting
`z → ζ` gives `ζ^{a_m} = (Σ_{r∈E} ζ^r)/s` with `s = L/m`. Hence `|Σ_{r∈E} ζ^r| = s`, and since `E` has
`k = |E|` terms of modulus 1:

    **L/m ≤ k  for every divisibility-maximal m ∈ U.**

Validated exactly on a cover with *two* maximal moduli (`{2,3,4,8,6,12}`, L=24, k=11): the predicted
equality held at both `m = 8` (|Σ| = 3 = L/8) and `m = 12` (|Σ| = 2 = L/12), to 1e-15.

It **subsumes Mirsky–Newman** for distinct moduli: `k = 0` demands `L/m ≤ 0`, impossible.

## Applied to L = 100,800

Cuts the 12 coverage-reaching subsets to **7**, in milliseconds — where the SAT encoding of a single
subset did not decide in 37 minutes:

| excluded | overlap k | binding L/m |
|---|---|---|
| `[14400, 20160, 33600]` | 0 | 16 |
| `[12600, 14400]` | 0 | 225 |
| `[12600, 20160, 33600]` | 1 | 8 |
| `[12600, 14400, 33600]` | 3 | 50 |
| `[12600, 14400, 20160]` | 5 | 36 |

The 7 survivors are the 6 subsets containing the modulus 100,800 — for which `L/m = 1` and the
condition is vacuous — plus `[12600, 14400, 20160, 33600]` at `k = 8`, `L/m = 8`, surviving exactly.

For the vacuous cases the *equality* `|Σ_{r∈E} ζ^r| = 1` at every primitive 100,800-th root of unity is
still severe, and is the obvious place to push next. Not attempted here.
