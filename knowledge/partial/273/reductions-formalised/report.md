# Partial result — Erdős #273: the checked reductions, formalised

**Status: PARTIAL. #273 is OPEN and nothing here resolves it.** These are the elementary structural
facts the reduction stage proposed and checked empirically, now proved in Lean. All five are sorry-free
on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the two that need no choice
depend on only `propext` and `Quot.sound`.

| lemma | content |
|---|---|
| `erdos_273_sieve` | For every prime `q`, an admissible modulus `m` with `q < m+1` has `q ∤ m+1`. Taking `q = 3` with evenness gives "no admissible modulus is `2 mod 6`" (deleting 8, 14, 20, 26, …); every prime contributes its own exclusion. |
| `erdos_273_even` | Every admissible modulus is even. |
| `erdos_273_parity` | A congruence class with an even modulus lies entirely inside one parity class — the engine of the decomposition into two disjoint covering systems. |
| `erdos_273_seventeen_insufficient` | The 17 smallest halved admissible moduli have reciprocal sum `< 2`, so with the density bound any solution needs **at least 18** congruences. |
| `erdos_273_halved_admissible` | …and those 17 really are halved admissible moduli (`2h+1` prime, `≥ 5`), by `decide`. |

Moduli are written `m` with `m + 1 = p`, avoiding truncated natural subtraction — a reading the
formalisation stage flagged explicitly.

## Deliberately NOT formalised

**Mirsky–Newman / Davenport–Rado** (a disjoint covering system of `ℤ` by ≥ 2 congruences must repeat its
largest modulus, so distinct moduli admit no exact cover). This is used to exclude the overlap-0 cases at
`L = 100800`, but it is a published theorem proved by a generating-function argument, not an elementary
fact. Reconstructing it was out of scope and would not be new mathematics. The exclusion it licenses is
recorded as resting on that theorem, not on anything proved here.
