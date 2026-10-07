# erdosproblems.com #120: problem page and forum thread (fetched 2026-10-06T16:06:54Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 We had formalised this statement and also Problem 94 from Green’s open problem set (and also Erdős problem 120) and accidentally forgot to require the set to be measurable, while still requiring a positive volume. A Google DeepMind prover agent found a Lean proof demonstrating that omitting the strict 'MeasurableSet' assumption (i.e. only asking for a set of positive outer Measure) in the specific problem that is also Green’s open problem 94, allows for an explicit counterexample. By treating $\mathbb{R}$ as a vector space over $\mathbb{Q}$, the formalization verified that the $\mathbb{Z}$-span of a Hamel basis entirely avoids affine copies of the sequence $\{1, \frac12, \frac14, \dots\}$. Because coordinates over this basis are unique, repeatedly halving them forces any sequence $a \cdot 2^{-n} + b$ with $a \neq 0$ to eventually leave the set. This pathological set possesses strictly positive outer measure, but it is not a measurable set. Details can be found in the formal proof here: 
https://github.com/google-deepmind/formal-conjectures/blob/153d79d6c82c76fe1bee860742af800840c974d9/FormalConjectures/GreensOpenProblems/94.lean#L174
See also https://github.com/google-deepmind/formal-conjectures/pull/3526 
This variant is not explicitly mentioned here, but it might be interesting nonetheless. Perhaps this is a one of the special cases previously known, pointers to the literature would be welcome!
 Moritz Firsching
 — 10:13 on 14 Mar 2026
 👍
 1
 📝
 0
 🤖
 0
 De Reyna (1983) proved this positive outer measure variant with the stronger result, only requiring that $|A| \ge 3$ (!). However, de Reyna's proof is different, using transfinite induction. This is found by GPT-5.4 Thinking.
 Nat Sothanaphan
 — 15:07 on 14 Mar 2026
 👍
 1
 📝
 0
 🤖
 0
 An analog question of this problem (which was constructed by Kolountzakis and Papageorgiou) has been solved in affirmative by X. Gao, Y. Mooroogen and C. H. Yip in this paper
 Alfaiz
 — 06:23 on 07 Nov 2025
 👍
 0
 📝
 0
 🤖
 0