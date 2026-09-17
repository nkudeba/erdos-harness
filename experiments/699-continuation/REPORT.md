# #699 continuation — Codex, 2026-09-12

This continues Claude's saved research program after its session-limit failure. It does not resolve #699. Assistance: Codex inspected the saved plans, supplied proofs directly, and used Mathlib's published Lucas theorem. No additional paid harness calls were launched; Codex session cost is unavailable.

## Inherited run

`runs/20260911-195529-727426-erdos699` reports exit 3, positive direction infrastructure_error, negative direction partial, $30.539896 recorded spend, 54 model calls, 83 Lean checks, and 10 certified declaration names. These are aggregate facts from `collect_run_facts`, not inferred from the parent checkpoint. The old brief still described the earlier fast run and needs replacement. The original $35 cap was not increased. No active harness run was found at takeover.

## Correction to the next research plan

The positive plan's Conjecture D requires a prime p >= i with both n mod p < i mod p and n mod p < j mod p for every admissible triple with i >= 2. It is false at (10,3,5): C(10,3)=120, C(10,5)=252, gcd=12. The only common prime at least 3 is 3; but i mod 3=0, so the proposed strict residue inequality cannot hold. The triple satisfies the actual target using p=3. Thus the proposed criterion remains sufficient but cannot be a universal replacement for #699. Do not spend another research cycle trying to prove D. This correction does not disprove #699 and does not establish any new search floor.

## Formal continuation

`Continuation.lean` gives the general units-digit divisibility implication from Lucas, its small-index specialization, the block-prime implication, and the contrapositive: a counterexample forces every prime factor of every n-t (t<i) to be <=j. It also states the explicit failure of Conjecture D and the fact that the same example satisfies #699. Consult `verification.log` for kernel-check status and axiom output.

The smoothness implication is one-way. Proving it does not establish that smooth blocks are impossible, nor provide a finite cutoff. A full proof must still handle primes in [i,j], including p=i and carries at higher base-p digits. The next mathematical work should retain those cases instead of strengthening the target to a units-digit witness claim.

## Verification correction and handoff

The first Codex check failed: `residue_route_fails` used a tactic sequence that produced nine errors and a `sorryAx` dependency. The other five declarations had only standard axioms. The initial report referenced a verification log before it existed. Claude subsequently repaired the failing tactic to `interval_cases p <;> revert hp hi hj <;> decide` and migrated the results into `Formal.Library.BinomialCoefficients`; this assistance is part of the provenance. Fresh checks of the repaired source and the public library theorems are saved in `verification.log` and `library-axioms.log` respectively.

A further precision correction: the general units-digit criterion does NOT require p>j. At (n,i,j,p)=(16,3,7,5), both residue inequalities hold with i<p<j. `LibraryAxioms.lean` checks this example. Only the narrower block-prime sufficient condition imposes p>j. The units-digit criterion cannot use p=i, which is enough to explain its failure at (10,3,5).

The public library audit completed with exit 0: all 11 public theorem dependencies are subsets of propext, Classical.choice, and Quot.sound; no sorryAx occurs. The middle-prime example also passed. The corrected Atlas brief and persistent positive research plan are saved.

The repaired standalone continuation also completed with exit 0 after replacing the broad Mathlib import with Mathlib.Tactic. All six declarations have only standard axioms, with no sorryAx. The earlier broad-import verification was stopped before this successful check. One harmless unused-tactic warning remains.
