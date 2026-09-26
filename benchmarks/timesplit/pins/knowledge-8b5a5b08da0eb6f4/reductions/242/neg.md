# Checked structural reductions — Erdős #242

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## decomposition

**If m > 2 divides n and 4/m = 1/x+1/y+1/z with 1 ≤ x < y < z, then 4/n = 1/(kx)+1/(ky)+1/(kz) with k = n/m and kx < ky < kz. So every minimal counterexample n > 2 is an odd prime ≥ 5.**

Multiplying all denominators by k divides both sides by k and keeps strict order. Any n > 2 either is divisible by 4, or has an odd prime factor p ≥ 3; the case n = 4 is 1/2+1/3+1/6 and p = 3 is 1/1+1/4+1/12. So a composite or even n inherits a solution from a smaller m > 2, and a minimal counterexample is prime and not 2 or 3.

*Consequence:* A counterexample search (the --open / negation direction) only needs to test primes. A proof of the positive direction only needs to handle primes, via the scaling lemma.

*Lean:* stated

```lean
theorem reduction_1 : (∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔ (∀ p : ℕ, p.Prime → 5 ≤ p → ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) := by
  sorry
```
