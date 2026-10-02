---
problem: 455
updated: 2026-10-02
run: 20261001-230105-000000-erdos455
outcome: partial
solved: false
certified: 2
cost_usd: 18.99
---

## What the problem asks

A prime is a whole number above 1 that only 1 and itself divide evenly, such as 2, 3, 5 or 7. Take an endless list of primes in increasing order, q_1 < q_2 < …. A gap is the difference between one prime in the list and the next. The rule is that gaps never shrink: each gap is at least as big as the one before. The question is whether such a list must outgrow every fixed multiple of n², the square of a prime's position n in the list. Put another way: must q_n divided by n² eventually pass every number? The catalogue lists the problem as open. It also says no finite computation can settle it.

## What we tried

This was a research run: an automated attempt to build a proof by splitting the problem into smaller claims, each checked by Lean, a program that verifies proofs step by step. Before any Lean work, a discovery stage wrote twelve informal attempts in three independent draws. Every attempt judged the answer "yes", so the run worked only toward "yes". None of them was a complete proof that the automatic referee accepted.

The run was allowed six cycles of planning and proving. It ran three, then stopped, because two cycles in a row settled nothing new. When the one hard claim failed in Lean, the harness tried a fresh informal attack on that claim alone. It told that attack what Lean had already proved. This found no proof either. The cost was $18.99 of a $40 cap. A human chose the problem and the settings. The exact statement came from formal-conjectures, an outside collection of formal statements. The run was also given summaries of six papers and the problem's forum discussion. It was given no proof ideas beyond those.

## What we found

The problem is not solved. Lean certified two facts, and both passed the project's checks: the proof was re-checked by Lean's kernel, it uses only the standard axioms, and it has no unfinished steps.

- **The gap bound.** Take any finite run of primes whose gaps never shrink. Then the i-th gap is at least i/6. Adding the gaps up shows that q_n is at least about n²/12, so q_n/n² can never fall below roughly 1/12. Richter proved a stronger version of this in 1976, with 0.352 in place of 1/12. So this is a machine-checked proof of a weaker form of a known result, not new mathematics.
- **A bridge.** If the gaps never shrink, the distance from q_k to q_n is at least (n − k) times the gap at k.

With these, the problem reduces to one claim. Fix any number C. For large n, there is no run of about n/2 primes below C·n² whose gaps never shrink and stay at most 2Cn. This claim is as hard as the problem itself. The harness tried three times to split it into easier pieces. Each time, a separate automatic judge pointed out that the pieces were the same claim in new words, because the gap bound already supplies the extra conditions for free.

## What would move it

The missing step is a proof that the gaps skip almost every even number. Among the even numbers up to x, the ones that actually occur as gaps must be a vanishing fraction as x grows. That would take a sieve, meaning a counting method strong enough to bound long, nearly square-shaped patterns of primes uniformly. The informal attempts also suggest that tricks based only on a few fixed small primes cannot work; this was not checked. A future run starts from this run's notes, kept in the problem's campaign blackboard.

*Corrected by hand on 2026-10-02 from the automatic brief of run `20261001-230105-000000-erdos455`. The automatic version said six cycles had run, where three ran, and it left out the gap bound. A machine-checked proof certifies the statement it names, not the problem. Nothing here has had independent human review.*
