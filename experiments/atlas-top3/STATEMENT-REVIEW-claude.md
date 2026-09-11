# Independent statement review — #649, #105, #275

Reviewer: Claude Opus 5 session of 2026-09-10, continuing the Codex `atlas-top3` experiment.
This is a **second-assistant semantic read of the frozen Lean statements against the erdosproblems.com
statements**. It is NOT the independent human review those runs still require; `claimEligible` stays false.

Method: fetch each problem page with the harness's own parser, read the frozen theorem and its supporting
definitions out of `knowledge/solved/Erdos<n>.lean`, and check quantifier order, domain, direction
(claim vs negation) and non-vacuity by hand. No proof body was re-derived; mechanical correctness is the
Lean compiler's job and is covered by the replay.

## #649 — greatest prime factors of consecutive integers · site: DISPROVED (Lean)

Site asks: for any two primes p, q is there an integer n with P(n) = p and P(n+1) = q?

`IsGreatestPrimeFactor649 n p := 2 ≤ n ∧ p.Prime ∧ p ∣ n ∧ ∀ r prime, r ∣ n → r ≤ p` is exactly
"p is the greatest prime factor of n", and the theorem is the negation of the universally quantified
question. Direction correct, quantifier order correct, definition faithful.

**Domain caveat, confirmed and unchanged:** the theorem ranges over `n : ℕ` with `2 ≤ n`. Under a
negative-integer reading with P(|n|), n = −8 realizes p = 2, q = 7 and the counterexample would fail.
This caveat is genuine, but the positive reading is the site's own: its discussion disproves the
question using precisely p = 2, q = 7 and "there are no solutions to 2^k ≡ −1 (mod 7)". So the
formalization matches the source's intended reading. Verdict: faithful.

The saved proof follows the same route: P(n) = 2 forces n = 2^k, then 7 ∣ 2^k + 1 contradicts
2^k mod 7 ∈ {1, 2, 4}.

## #105 — a line with two points of A and none of B · site: DISPROVED (Lean), $50

Site asks: A, B ⊂ ℝ² disjoint, |A| = n, |B| = n − 3, A not collinear — must some line meet A twice and B never?

The theorem exhibits a counterexample: `∃ n A B` with `A.card = n`, `B.card = n - 3`, `Disjoint A B`,
A not all on one line, and every line through two distinct points of A containing a point of B. That is
the exact negation of the site's universally quantified question, and a single n suffices to disprove it.
Lines are encoded as `a·x + b·y = c` with `a ≠ 0 ∨ b ≠ 0`, which is every line and no degenerate "line".
The witness is n = 9, so nine points of A and six of B, and 9 − 3 = 6 makes the natural subtraction safe.
Verdict: faithful.

## #275 — a covering system of r congruences · site: PROVED (Lean)

Site: if a finite system of r congruences {a_i mod n_i}, moduli not necessarily distinct, covers 2^r
consecutive integers then it covers all integers.

The theorem quantifies over all r, all `a : Fin r → ℤ`, all `n : Fin r → ℕ` with every modulus positive;
"covers 2^r consecutive integers" is `∃ s, ∀ k < 2^r, ∃ i, n i ∣ (s + k − a i)`, i.e. the block
s, …, s + 2^r − 1; the conclusion is `∀ x : ℤ, ∃ i, n i ∣ (x − a i)`. Moduli repeat freely because `n`
is an arbitrary function. Universally quantified, affirmative direction, no hidden finiteness.
Verdict: faithful.

## Not covered by this review

Whether each *proof* is mathematically correct beyond what Lean checks; the operator-supplied literature
context that shaped these formalizations (recorded in REPORT.md); and independent human review.
