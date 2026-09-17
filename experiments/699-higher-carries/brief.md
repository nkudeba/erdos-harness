---
problem: 699
updated: 2026-09-12
run: 20260911-195529-727426-erdos699
outcome: partial
solved: false
certified: 10
search_floor: 4.17e+19
cost_usd: 30.54
---

## What the problem asks

For any n and positions 1 ≤ i < j ≤ n/2, must the two binomial coefficients C(n,i) and C(n,j) share a prime factor at least i? A binomial coefficient counts choices of a given size. The prime is allowed to equal i. The full statement remains unproved here.

## What we tried

The inherited research run ended with a session-limit failure in the positive direction and partial results in the negative direction. Its aggregate records contain 10 certified declaration names, 54 model calls, 83 Lean checks, and $30.54 spend. Those counts describe the harness run, not the later operator-assisted continuation. No additional paid harness calls were launched by Codex; Codex session cost is unavailable. The existing published search floor of roughly 4.17 × 10^19 candidate triples was preserved; it was not rerun.

Codex continued directly in Lean using Mathlib's Lucas theorem. Claude repaired one failed proof tactic and moved the results into a shared binomial-coefficient library. This was assisted work, not an autonomous resolution.

## What we found

The carry lemma and the stronger reduction are mechanically verified: if any number among n,n−1,…,n−i+1 has a prime factor greater than j, that prime divides both binomial coefficients. Therefore a counterexample would force every prime factor of every number in that block to be at most j. This property is called j-smoothness. It is a necessary condition for a counterexample, not a proof that counterexamples are impossible.

The proposed next route, Conjecture D, is false at (10,3,5). These binomial coefficients are 120 and 252; the shared prime 3 satisfies #699 but is missed by the proposed units-digit test. The test remains useful as a sufficient condition. It can also find primes between i and j, as p=5 at (16,3,7) demonstrates; only the narrower block-prime argument requires p>j.

A later direct argument for i=3 rules out odd n and gives n ≤ (9/4)·4^r+1 for even n, where r counts factors of two in n. Its intermediate numerical checks passed, but it is a written argument for review, not a new Lean-certified result: the separate formal check timed out. It leaves r unbounded and does not address i≥4. Details are in experiments/699-higher-carries/REPORT.md.

## What would move it

Reuse the certified carry and smoothness lemmas in Formal.Library.BinomialCoefficients. A full proof must handle the remaining shared primes in [i,j], including equality p=i and divisibility caused by higher base-p digits. Do not treat the false units-digit conjecture as a replacement for #699. A generic search would repeat published ground, and no effective bound on the remaining cases has been established here.

The continuation's proof checks and assistance history are saved in experiments/699-continuation/. Mechanically verified consequences of published mathematics do not constitute a resolution of the open problem.
