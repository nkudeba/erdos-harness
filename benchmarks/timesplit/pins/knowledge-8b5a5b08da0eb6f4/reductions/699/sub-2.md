# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## forced

**If some integer m with n-i < m <= n has a prime factor q > j, then q divides both C(n,i) and C(n,j) and q >= i, so (n,i,j) satisfies the statement; hence a counterexample (n,i,j) forces every one of the i consecutive integers n-i+1, ..., n to be j-smooth (all prime factors <= j).**

Let q > j be prime with q | m, n-i < m <= n, and put s = n - m, so 0 <= s < i. For any k with s < k < q we have k mod q = k and (n-k) mod q = q + s - k >= q - (q-1) ... concretely k + (n-k mod q) = q + s >= q, so adding k and n-k in base q produces a carry in the units digit, and by Legendre's formula v_q(C(n,k)) counts exactly such carries, giving q | C(n,k). Both k = i and k = j satisfy s < k < q (since s < i < j < q), so q divides gcd(C(n,i), C(n,j)), and q > j > i gives q >= i.

*Consequence:* A counterexample search may skip every n for which any of n-i+1, ..., n has a prime factor exceeding j — in particular, for i >= 2 both n and n-1 must be j-smooth, and for i >= 2 neither n nor n-1 may be prime. Since j-smooth numbers have vanishing density, this is also the elementary source of 'only finitely many n for fixed i < j'. On the proof side it reduces the theorem to the case where n-i+1, ..., n are all j-smooth (exactly the hypothesis shape of the frozen statement erdos_699_sub8_1, which this argument proves outright).

## equivalent-form

**For a prime p and 0 <= k <= n, p divides C(n,k) if and only if there exists t >= 1 with (n mod p^t) < (k mod p^t); so the whole problem is a statement about base-p digits of n, i and j rather than about large integers.**

Legendre's formula gives v_p(C(n,k)) = sum over t>=1 of (floor(n/p^t) - floor(k/p^t) - floor((n-k)/p^t)), and each summand is 0 or 1, being 1 exactly when the fractional parts of k/p^t and (n-k)/p^t sum to at least 1. That happens exactly when (k mod p^t) + ((n-k) mod p^t) >= p^t, which, since (k mod p^t) + ((n-k) mod p^t) equals (n mod p^t) or (n mod p^t) + p^t, is equivalent to (n mod p^t) < (k mod p^t). Hence p | C(n,k) iff some t gives that strict inequality.

*Consequence:* Any search can test a triple (n,i,j) with only O(log n) modular comparisons per prime p in [i, n], never building binomial coefficients; and 'no prime p >= i divides gcd' becomes the purely arithmetic condition: for every prime p with i <= p <= n, either (n mod p^t) >= (i mod p^t) for all t, or (n mod p^t) >= (j mod p^t) for all t. This is the natural encoding for a SAT/constraint formulation and for a Lean proof via Nat.Prime.dvd_choose-style digit lemmas.

## decomposition

**The case i = 1 of the problem is unconditionally true, because gcd(n, C(n,j)) > 1 for every 1 <= j <= n/2 (n >= 2); more generally for i <= 2 the requirement 'p >= i' is vacuous, so the statement there is exactly 'gcd(C(n,i),C(n,j)) > 1' and all the content of the problem lies in i >= 3.**

From j*C(n,j) = n*C(n-1,j-1) we get n | j*C(n,j); if gcd(n, C(n,j)) were 1 then n | j, impossible since 1 <= j <= n/2 < n. So gcd(n, C(n,j)) = gcd(C(n,1), C(n,j)) has a prime factor p, and p >= 1 = i holds automatically. For i = 2 every prime p satisfies p >= 2, so no size condition on p remains.

*Consequence:* Search and proof may assume i >= 3 (the i = 1 branch is closed by a two-line argument, and the i = 2 branch asks only that two binomial coefficients are not coprime). This removes the whole i = 1 row from any counterexample enumeration and matches the recorded near-counterexamples, all of which have i >= 2.
