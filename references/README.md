# Reference-assisted proof fixtures

Erdos532.lean adapts the community proof from
https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos532.lean
(downloaded in the earlier session). Original file credits Neil Hindman (informal)
and David Wärn (formal); attribution comments are retained. The collection notes
that externally sourced files use Apache-2.0.

The harness adapter removes zero from the resulting infinite set to match the
frozen statement in runs/20260907-203009-erdos532/state.json. Imports are narrowed
to the installed Mathlib modules. This is a reference-assisted integration
fixture, NOT a newly discovered proof or an autonomous harness success.


Erdos370.lean is an assistant-written proof using n=(6t+8)(6t+10).
The informal route n=m²−1 is recorded in problems/erdos_370.json from
https://www.erdosproblems.com/370. This proof chooses m=6t+9 and bounds every
prime divisor by 3t+5 using explicit factors of n and n+1. It uses the
all-prime-divisors formulation of the largest-prime-factor bound, avoiding
real square roots. The file compiled without warnings or sorry, using only
propext, Classical.choice, and Quot.sound. It is assistant-assisted, not a
fresh autonomous CLI solve. It was not copied from the community Lean proof.
