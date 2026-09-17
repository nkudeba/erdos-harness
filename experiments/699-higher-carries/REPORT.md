# Attempt at the remaining #699 argument, 2026-09-12

**Outcome: no full proof or counterexample. Claim eligible: false.** This is an operator-assisted Codex argument, with an elementary necessary condition for the i=3 slice. No novelty claim is made. No paid harness invocation was launched; session cost is unavailable. A live forum refresh failed; the available September 11 cache was retained, and the failed refresh response was saved separately.

## The reduction for even n and i=3

Assume a counterexample with i=3 and 4≤j≤n/2. Put A=C(n,3), B=C(n,j). The counterexample assumption says gcd(A,B) has no odd prime factor. Every odd divisor of A is therefore coprime to B.

Write n=2^r a with a odd. Put g=gcd(a,3), c=2^r g, and m=a/g, so n=cm. Also put e=gcd(n−1,3) and b=(n−1)/e. Here n is even, so m and b are odd positive divisors of A=n(n−1)(n−2)/6. Thus both are coprime to B.

The exact identities

    n C(n−1,j−1) = j B
    n(n−1) C(n−2,j−2) = j(j−1) B

give m|j and b|j(j−1) by coprime cancellation. Write j=km, with 1≤k≤c/2. Since cm=n≡1 mod b, multiplication of the second divisibility by c² gives

    b | k(k−c), hence b | k(c−k).

The latter is positive. Consequently

    b ≤ k(c−k) ≤ c²/4,
    4(n−1) ≤ e c².

If 3|n then g=3 and e=1; otherwise g=1 and e≤3. In either case

    n ≤ (9/4)·4^r + 1.

A slightly sharper form when 3 does not divide n is n≤(3/4)·4^r+1. The cancellation argument is an ordinary mathematical proof, not yet formalized end to end. `Bound.lean` is a draft intended to check only the final algebraic localization inequality under the explicitly listed hypotheses; it is not a Lean proof of the whole binomial reduction.

## Odd n cannot be a counterexample for i=3

For odd n, put m=n/gcd(n,3). This is an odd divisor of A. The first identity again forces m|j. If 3 does not divide n, this would force n|j, impossible. Otherwise n=3m and j=m (as 0<j≤3m/2).

Now d=n−2 is an odd divisor of A and is coprime to B. The order-three identity

    n(n−1)(n−2) C(n−3,j−3) = j(j−1)(j−2) B

forces d|j(j−1)(j−2). Multiply by 27 and substitute j=m, 3m=n. Modulo d=n−2 this gives

    d | n(n−3)(n−6) ≡ 2·(−1)·(−4) = 8.

Since d is odd and n≥8, this is impossible. This argument is written and algebraically justified here, but has not been formally checked as a whole in Lean.

## What this does and does not settle

For a fixed r=v₂(n), the i=3 slice reduces to a finite n-range. This is not an absolute cutoff because r can grow without bound. In particular n=2^r satisfies the resulting upper bound for all r≥1; the inequality alone cannot dispose of this family.

Conditional on the recorded third-party exhaustive check through n=10^7 being correct, a counterexample with i=3 must have v₂(n)≥12, hence 4096|n: for r≤11 the bound is at most 9,437,185. This uses the existing published check and is not a newly verified search result. The i≥4 cases also remain unresolved by this argument.

The exact-integer script checks the factorization and cancellation implications for even n from 8 through 800. It checks the final inequality on 22 pairs satisfying the intermediate divisibility conditions, rather than validating it only under an empty set of actual counterexamples. This is a check of the derivation, not a new counterexample search or search floor. The first version mistakenly applied the even-n factor b to odd n; its parity assertion caught that, and the odd-n argument above handles those separately.

## Verification outcome

The numerical implication checks passed. The separate Lean check of `Bound.lean` reached its 180-second wall limit (exit 142) without producing a result. Therefore no new theorem from this attempt is labelled mechanically verified or added to the shared library. The mathematical derivation above is a written proof for review, not an end-to-end formal certificate.
