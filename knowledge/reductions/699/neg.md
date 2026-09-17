# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## forced

**If some prime p satisfies j < p <= n and (n mod p) < i, then p >= i, p divides C(n,i) and p divides C(n,j); hence a counterexample (n,i,j) must satisfy (n mod p) >= i for EVERY prime p with j < p <= n.**

By Legendre's formula v_p(C(n,m)) = sum_{k>=1} (floor(n/p^k) - floor(m/p^k) - floor((n-m)/p^k)), and each summand is 1 exactly when (n mod p^k) < (m mod p^k), else 0. For a prime p > j > i we have i mod p = i and j mod p = j, so the single condition (n mod p) < i already gives a carry at level k=1 for both m=i and m=j, i.e. p | C(n,i) and p | C(n,j). Since p > j > i, the requirement p >= i is automatic.

*Consequence:* The existential over primes is replaced by a pure residue test that needs no binomial coefficients: any n admitting a prime p in (j,n] with n mod p < i is instantly cleared. A counterexample search may enumerate n, compute n mod p for the primes in (j,n], and reject n as soon as one residue is < i; this kills the overwhelming majority of n at cost O(pi(n)) with no big-integer arithmetic at all.

## forced

**If there is a prime p with n-i < p <= n then the statement holds for (n,i,j) for every j; hence a counterexample requires i <= n - P(n), where P(n) is the largest prime <= n, i.e. the prime gap immediately below n must be at least i.**

This is the special case p > n/2 of the residue criterion: for such p, n mod p = n-p < i, and p > n-i >= n/2 >= j > i, so p is counted by the previous reduction. Directly: v_p(n!) = 1, while v_p(i!) = v_p((n-i)!) = 0 because i <= n/2 < p and n-i < p, so p | C(n,i) exactly once, and likewise n-j <= n-i < p gives p | C(n,j).

*Consequence:* A counterexample can only live at an n sitting at the far end of a prime gap of length >= i. For i >= 2 this alone removes every n with n or n-1 prime; empirically it cuts the candidate n by more than an order of magnitude and, combined with i < j <= n/2, forces i to be bounded by the observed gap below n (about O(log^2 n) in the searched range), so the search is really over (n, gap) pairs, not over all (n,i).

## substitution

**For a prime p and 0 <= m <= n, v_p(C(n,m)) = #{k >= 1 : (n mod p^k) < (m mod p^k)}; in particular p | C(n,m) if and only if (n mod p^k) < (m mod p^k) for some k with p^k <= n.**

Legendre's formula gives v_p(C(n,m)) = sum_{k>=1} (floor(n/p^k) - floor(m/p^k) - floor((n-m)/p^k)). Writing n = m + (n-m), the k-th summand is 1 if (m mod p^k) + ((n-m) mod p^k) >= p^k and 0 otherwise; in the first case n mod p^k equals that sum minus p^k, which is < m mod p^k, and in the second case n mod p^k equals the sum, which is >= m mod p^k. For p^k > n both sides reduce to n >= m, so only k with p^k <= n can contribute.

*Consequence:* Every divisibility test in the problem becomes a residue comparison on n, i, j modulo prime powers <= n — no binomial coefficients need ever be formed. A search over n up to 10^7 or beyond becomes feasible in machine arithmetic, and the target itself reads: for all n,i,j there is a prime p in [i,n] and exponents k,l with n mod p^k < i mod p^k and n mod p^l < j mod p^l.

## decomposition

**The case i = 1 of the statement is unconditionally true: for every n and every j with 2 <= j and 2j <= n, gcd(n, C(n,j)) > 1, so some prime p >= 1 divides both C(n,1) and C(n,j). Hence a counterexample must have i >= 2.**

From j*C(n,j) = n*C(n-1,j-1) we get n | j*C(n,j). If gcd(n, C(n,j)) were 1 then n | j, impossible because 0 < j <= n/2 < n. So gcd(n, C(n,j)) has a prime factor, and every prime is >= i = 1.

*Consequence:* The base case i = 1 is closed by a two-line elementary argument and needs no search and no Sylvester-Schur; both the search stage and any Lean proof may assume i >= 2 (hence n >= 2j >= 6). Combined with the prime-gap constraint, i >= 2 already forces n and n-1 both composite.
