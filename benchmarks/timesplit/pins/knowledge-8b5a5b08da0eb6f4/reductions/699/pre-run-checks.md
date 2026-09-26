# Checked reductions — Erdős #699 (pre-run, operator-executed)

**Provenance.** These are *public* claims from the #699 forum thread, re-verified here in exact integer
arithmetic on 2026-09-11 **before** the first harness run, so the paid run does not spend budget
rediscovering or mis-stating them. They were checked by the operator's own scripts, **not** produced by
`stage_reduce`, and they have not been through `REDUCTION-OK` sandbox validation. A numerical check is
evidence, not a proof. None of this is a new search floor.

Sources: Bloom's proof exposition on the thread; comments by Marco Del Pin (24 Jul 2026), MaxDKaos
(25 Jul 2026), Thomas Bloom (19 Jul 2026) and Cong (06 Jan 2026).

## identity (checked)

**`C(n,i)·C(n-i,j-i) = C(n,j)·C(j,i)`** — verified for every `1 ≤ i < j ≤ n/2` with `n ≤ 160`. No failures.

This is the identity behind the whole problem: if `d | C(n,i)` is coprime to `C(n,j)` then `d | C(j,i)`.
Applied to `V = V_i(n)` (the part of `C(n,i)` supported on primes `≥ i`), a counterexample forces `V | C(j,i)`.

**Three-factor form** `C(n,j)·C(j,i-h)·C(n-j,h) = C(n,i)·C(i,h)·C(n-i,j-i+h)` — verified for every
`1 ≤ i < j ≤ n/2`, every `0 ≤ h ≤ i`, `n ≤ 90`. No failures. This is the form the Van Doorn/Rocca
determinant argument uses (see `experiments/699-first-attack/CONTEXT.md`).

## forced (checked)

**Kummer bound `U_i(n) ≤ n^π(i-1)`**, where `U_i(n)` is the part of `C(n,i)` on primes `< i` — verified for
every `2 ≤ i ≤ n/2`, `n ≤ 900`. No failures; tightest observed ratio 1.

By Kummer, `v_q(C(n,i))` counts carries adding `i` and `n-i` in base `q`, so `q^{v_q} ≤ n` for each of the
`π(i-1)` primes below `i`. Equivalently `V_i(n) ≥ C(n,i)/n^{π(i-1)}`, an exponent `1 - π(i-1)/i → 1` against
the constant `1/2` of the [EEES78] bound; they cross at `i = 9`.

## decomposition — the prime-window obstruction (checked)

**For `p > n/2`: `p | C(n,k) ⟺ (n mod p) < k`** — verified for every prime `p ∈ (n/2, n]` and every
`1 ≤ k ≤ n/2`, `n ≤ 1200`. No failures.

**Hence a prime `p ∈ (n-i, n]` forces `n mod p < i`, so `p | C(n,i)` and `p | C(n,j)` for every `j > i`** —
verified over 10,786,824 `(n,i,p)` combinations, `n ≤ 1200`. No failures.

*Consequence:* **any counterexample triple `(n,i,j)` must have `(n-i, n]` containing no prime at all.**
This is the binding structural constraint, and it is arithmetic rather than size-based — the axis
Marco Del Pin's comment identifies as necessary to get past the `j ≤ 3i/2` ceiling of size arguments.

### the known extremal triples sit exactly on this obstruction

All nine known failures of the **strict** `p > i` variant were recomputed exactly. Every one has a
prime-free window `(n-i, n]`, and for `i = 3` and `i = 5` the known `n` is the **smallest** `n` at which the
window argument fails at all:

| `(n,i,j)` | window `(n-i,n]` | primes | smallest prime-free `n` at this `i` |
|---|---|---|---|
| `(10,3,5)` | `(7,10]` | none | **10 — this n** |
| `(16,2,6)` | `(14,16]` | none | 9 |
| `(28,3,14)` | `(25,28]` | none | 10 |
| `(28,5,14)` | `(23,28]` | none | **28 — this n** |
| `(244,3,122)` | `(241,244]` | none | 10 |
| `(512,2,147)` | `(510,512]` | none | 9 |
| `(2048,2,713)` | `(2046,2048]` | none | 9 |
| `(2188,3,1094)` | `(2185,2188]` | none | 10 |
| `(1594324,3,797162)` | `(1594321,1594324]` | none | 10 |

This is a consistency check of the reduction, not evidence that a counterexample exists: in all nine the
largest shared prime is exactly `i`, so each **satisfies** the `p ≥ i` target and refutes only the strict
variant. See the CRITICAL READING block in `problems/erdos_699.json` — these nine are the trap that would
let a run "refute" the wrong statement.

---

# Addendum — the sharp obstruction and the remaining region (2026-09-11, second attempt)

## (F5) smoothness reduction — derived, then checked

**If a prime `p > j` divides any one of `n, n-1, …, n-i+1`, then `p` divides *both* `C(n,i)` and
`C(n,j)`, and `p > j > i`. Hence in any counterexample the descending product `n(n-1)⋯(n-i+1)` is
`j`-smooth.**

*Proof.* Say `p | n-t` with `0 ≤ t < i`. Since `p > j > i > t`, we get `n mod p = t`. Then `n mod p = t
< i < j`, so the single-digit Kummer lemma (F4) applies with both `i` and `j`. ∎

Checked over **2,559,266** `(n,i,j,p)` witnesses for `n < 400`; no failures.

This is strictly stronger than the better-known "a counterexample needs no prime in `(n-i, n]`", which
is only the special case where `n-t` is *itself* prime. It is the sharp arithmetic form of the
obstruction, and the axis past the `j ≤ 3i/2` ceiling that size arguments cannot cross.

## i = 2 is settled outright, by size alone

`π(1) = 0`, so (F3) gives `U_2(n) ≤ n^0 = 1` and `V_2(n) = C(n,2)`. A counterexample would force
`C(n,2) | C(j,2)` by (F1), hence `n ≤ j` — contradicting `2j ≤ n`. So **no counterexample has `i = 2`**,
unconditionally and by an elementary argument. (The three known `i = 2` entries in the table above are
failures of the *strict* `p > i` variant only; for the target, `p = 2 ≥ i` always serves.)

## The remaining region, per i

A counterexample `(n,i,j)` must satisfy `2j ≤ n ≤ j^e` with `e = i/(i − π(i−1))`, **and** have
`n(n-1)⋯(n-i+1)` `j`-smooth. Since `n ≤ j^e` gives `j ≥ n^{1/e}`, the smoothness demand is that a
product of `i` consecutive integers near `n` be `n^{1/e}`-smooth:

| i | π(i−1) | e | region nonempty from | smoothness demand |
|---|---|---|---|---|
| 2 | 0 | 1.000 | **never** (`n ≤ j` vs `n ≥ 2j`) | — settled |
| 3 | 1 | 1.500 | j ≥ 4 | `n^{2/3}`-smooth |
| 4 | 2 | 2.000 | j ≥ 2 | `n^{1/2}`-smooth |
| 5 | 2 | 1.667 | j ≥ 3 | `n^{3/5}`-smooth |
| 7 | 3 | 1.750 | j ≥ 3 | `n^{4/7}`-smooth |
| 11 | 4 | 1.571 | j ≥ 4 | `n^{7/11}`-smooth |

Note (a) alone closes for **no** `i ≥ 3`: the region is an infinite family. What must become effective
is the smoothness condition. That is exactly the Bugeaud–Evertse–Győry territory the Van Doorn/Rocca
manuscript invokes **ineffectively**, and `i = 3` with the gcd a power of two is the case it explicitly
cannot rule out. So the honest statement of where #699 stands: it reduces to an *effective* statement
about smooth values of products of consecutive integers, and that reduction is the thing worth
certifying.
