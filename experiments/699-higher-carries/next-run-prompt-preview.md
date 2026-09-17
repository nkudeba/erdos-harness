CURRENT PLAN: old checkpoint

CURRENT OPERATOR RESEARCH GUIDANCE (not a verified proof):
Use this to prioritize work over older plans. Audit unverified claims; do not alter the frozen target or assume a proposed reduction.
# Erdős #699 — current next steps (2026-09-13)

Objective: a full proof or counterexample to the frozen p >= i statement. The immediate research priority is the i=3 obstruction; completing this slice would still leave i>=4. This guidance supersedes the old Conjecture-D plan and requests to reprove the already certified carry lemmas.

## Work in this order

1. Audit the written i=3 localization argument in experiments/699-higher-carries/REPORT.md. Check parity, removal of factors 2 and 3, and every coprime cancellation. The argument claims odd n is excluded and, for even n with r=v_2(n), n <= (9/4)*4^r+1. Numerical implication checks passed, but the 180-second Lean attempt timed out. Bound.lean is an unverified draft of only the final algebraic inequality, NOT an end-to-end certificate. Complete the formalization or record the precise failed step; do not assume this reduction in downstream proofs before auditing it.
2. Attack the remaining gap by bringing the factor n-2 into the simultaneous constraints already obtained from n and n-1. Keep prime-power valuations and higher-digit carries, especially p=i=3. Derive and empirically check a concrete additional necessary condition; then try to prove it. The existing even-n derivation uses n=c*m, j=k*m, e=gcd(n-1,3), b=(n-1)/e and b | k(c-k). Do not just repeat those two-factor inequalities.
3. Seek a contradiction uniform in r=v_2(n), or a proved absolute cutoff with a feasible exhaustive certificate. The current bound leaves r unbounded; checking finitely many powers of two does not settle i=3. If the n-2 approach fails, record the exact obstruction, a refuting example if available, and what a different approach must overcome before launching another model run.

## What can be reused and what cannot

Import Formal.Library.BinomialCoefficients and inspect named declarations: digit_carry, small_index_carry, block_prime, counterexample_forces_smooth_block, residue_route_fails. Their verification artifacts are in experiments/699-continuation/. These certify consequences of published mathematics, not a solution to #699. The smoothness condition is necessary only.

Conjecture D (a universal units-digit witness) is REFUTED at (10,3,5), which satisfies #699 with p=3. Do not try to prove it or strengthen p>=i to p>i. The general units-digit test can find i<p<=j, e.g. (16,3,7,p=5); only the block-prime version requires p>j. Equality p=i and higher digits remain essential.

Preserve the published floor of 4.17e19 candidate triples (reported n<=10^7); do not spend a generic search rechecking it or replace it with a smaller numerical screen. The claim that 4096 divides an i=3 counterexample is conditional on BOTH the unformalized localization argument and that third-party search. It is not a newly certified search result.

Record assistance, verification status and failed routes in the Atlas. Finishing i=3 is partial progress; i>=4 is still part of the full target.
