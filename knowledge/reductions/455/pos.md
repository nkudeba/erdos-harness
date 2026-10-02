# Checked structural reductions — Erdős #455

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## parity

**If q is strictly increasing with every q n prime, then q n is odd for every n >= 1, so every gap d_n = q(n+1) - q(n) with n >= 1 is even; only d_0 can be odd (and only when q 0 = 2).**

For n >= 1 we have q n > q 0 >= 2, and a prime greater than 2 is odd. So for n >= 1 the gap d_n is a difference of two odd numbers, hence even. d_0 is odd exactly when q 0 = 2.

*Consequence:* Gap search can range over even values only, after the first step. This halves the gap alphabet, and with monotone gaps it gives d_n >= 2 for all n >= 1.

*Lean:* stated

```lean
theorem reduction_1 : ∀ q : ℕ → ℕ, StrictMono q → (∀ n, (q n).Prime) → ∀ n, 1 ≤ n → Odd (q n) := by
  sorry
```

## forced

**Let d >= 1 and let p be the least prime not dividing d. Then any arithmetic progression a, a+d, ..., a+(k-1)d of primes has k <= p. Consequently, in a sequence with nondecreasing gaps, a gap value e occupies one block of consecutive indices of length at most p(e) - 1.**

Suppose k >= p+1. Since p does not divide d, the first p terms cover every residue mod p, so some term a+id with 0 <= i <= p-1 equals p. If i = 0, then the term a+pd = p(1+d) is composite. If i >= 1, then a = p - id is a prime smaller than p, so it divides d by the minimality of p, and hence it divides a+id = p, which is impossible. Separately, monotone gaps make each gap value occupy a single block, and a block of m equal gaps gives m+1 primes in arithmetic progression.

*Consequence:* Gap multiplicities are capped: m(e) <= p(e) - 1. Any gap not divisible by 3 appears at most twice; a gap divisible by 6 but not by 5 appears at most 4 times; and so on. Search can prune any run longer than this immediately. In the counting argument this tightens the attempt's bound of 2p(e) - 2 to p(e) - 1.

*Lean:* stated

```lean
theorem reduction_2 : ∀ a d k p : ℕ, 0 < d → p.Prime → ¬ p ∣ d → (∀ r : ℕ, r.Prime → r < p → r ∣ d) → (∀ i, i < k → (a + i * d).Prime) → k ≤ p := by
  sorry
```

## decomposition

**If the gaps d_i = q(i+1) - q(i) of a strictly increasing sequence are nondecreasing, then (n-k)*d_k <= q(n) - q(k) for all k <= n. Hence q(n) <= C n^2 forces d_k <= C n^2/(n-k), in particular d_k <= 2Cn for every k <= n/2.**

q(n) - q(k) = d_k + d_{k+1} + ... + d_{n-1}, a sum of n-k terms. Each term is at least d_k because the gaps are nondecreasing. Taking k <= n/2 gives n-k >= n/2.

*Consequence:* This is the exact bridge from the negation (q_n <= C n^2 infinitely often) to a finite configuration: at least about n/2 primes in [1, C n^2] whose gaps are nondecreasing and bounded by 2Cn. Any counterexample search should enumerate convex prime chains with bounded gaps. Any proof needs exactly an upper bound for such chains (the open Conjecture G2).

*Lean:* stated

```lean
theorem reduction_3 : ∀ q : ℕ → ℕ, StrictMono q → (∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) → ∀ k n, k ≤ n → (n - k) * (q (k + 1) - q k) ≤ q n - q k := by
  sorry
```
