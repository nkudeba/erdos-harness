# Erdős #287 — feasibility assessment (open problem, site class "falsifiable")

**Verdict: 2/10. Do not run as a search target.**

**Statement correction.** The Atlas snippet truncates this one and it is easy to misread. The conjecture is
NOT a bound on the largest denominator. It is: for k ≥ 2 and distinct 1 < n_1 < … < n_k with
1 = 1/n_1 + … + 1/n_k, must max(n_{i+1} − n_i) ≥ 3? Equivalently, no representation of 1 by distinct
reciprocals has every consecutive gap equal to 1 or 2. The constant 3 is tight, via 1 = 1/2 + 1/3 + 1/6.

## Enumeration (exact arithmetic, independent)

| k | representations | max denominator | smallest max-gap | conjecture |
|---|---|---|---|---|
| 3 | 1 | 6 | 3 | tight |
| 4 | 6 | 42 | 6 | holds |
| 5 | 72 | 1 806 | 6 | holds |
| 6 | 2 320 | 3 263 442 | 4 | holds |
| 7 | 245 765 | 1.07×10^13 | 5 | holds |

Counts match OEIS A006585; maxima are the Sylvester numbers minus one. All 248,164 representations with
k ≤ 7 satisfy the conjecture. The direct gap-restricted search reaches n_1 = 12 in 117 seconds, reproducing
a published forum search to the digit, with node count growing ×5.52 per unit of n_1.

## Why no search can ever work

Forum contributors have established, and this assessment independently re-verified the prime chains, that a
counterexample must have **n_1 > 3.9×10^19** and **k ≥ 6.9×10^19 terms**. The obstruction is a chain of
"good primes" p with (p±1)/2 prime, which forces a p-adic valuation contradiction. A counterexample could
therefore never be written down, let alone certified in Lean. Reaching even n_1 = 100 by search needs ~10^65
nodes. The "falsifiable" label promises a finite counterexample that no finite search can exhibit.

The proof direction is blocked on a Sophie-Germain-type statement (for all large N, a prime p in [N, 2N] with
(p+1)/2 prime), which is twin-prime-class difficulty. There is no tractable middle.

## State of the art already published

A Lean project covering max denominator up to 4×10^9 with no `sorry` and no `native_decide` already exists,
as does a k ≤ 18 verification that *depends* on `native_decide` — which this harness bans. Under
`decide +kernel` the harness would stall around k ≈ 10–12, strictly weaker than what is public.

## Two harness defects this surfaced

1. **Routing trap.** `decide_mode` sends any unresolved problem whose site class is falsifiable/verifiable/
   decidable straight to `search-first`. For #287 that spends the whole search budget hunting a
   counterexample certified not to exist below 4×10^19. The class needs an escape hatch for problems whose
   counterexample is known to be astronomically large.
2. **Construct-stage scoring trap.** The only maximizable object here is a good-prime chain, and extending it
   is pure CPU: 1.2 seconds of Python pushed the published bound from 4×10^19 to ~10^31. A score that grows
   linearly with CPU seconds looks like progress and is not.

## If pursued anyway

The one genuine gap is a Lean proof of the good-prime chain obstruction (harmonic window bound, the p-adic
valuation lemma, the q-adic case, and Pocklington-certified primality of 66 numbers up to 1.5×10^20),
estimated at 1,500–3,000 lines. That is a research/campaign target, not a search target.
