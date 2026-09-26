# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## equivalent-form

**For i <= 2 the target is equivalent to the purely arithmetic condition gcd(C(n,i), C(n,j)) > 1.**

Every prime is >= 2 >= i when i <= 2, so the side condition p >= i is vacuous and the existential asks only for some prime dividing the gcd. A prime divides the gcd exactly when the gcd exceeds 1. Hence the frozen statement for i <= 2 says nothing more than gcd(C(n,i), C(n,j)) != 1.

*Consequence:* The p >= i / p > i distinction (the flagged high-risk confusion) is irrelevant in the frozen sub-statement: no counterexample search needs to track the size of p at all, and a Lean proof only has to exhibit ANY common prime factor. A search may test gcd(C(n,i),C(n,j)) == 1 as the counterexample predicate.

## forced

**For every 1 <= j < n there is a prime p dividing n with v_p(j) < v_p(n), and every such p divides C(n,j); in particular gcd(n, C(n,j)) > 1, which settles the case i = 1 completely.**

From j*C(n,j) = n*C(n-1,j-1) we get v_p(j) + v_p(C(n,j)) = v_p(n) + v_p(C(n-1,j-1)) >= v_p(n), so v_p(j) < v_p(n) forces p | C(n,j). Such a p exists because otherwise v_p(j) >= v_p(n) for all p | n, i.e. n | j, impossible for 0 < j < n. Since C(n,1) = n, this prime divides gcd(C(n,1), C(n,j)).

*Consequence:* The i = 1 branch of the frozen statement is proved outright (no search needed), and for i = 2 it supplies an explicit candidate prime p | n: it works immediately whenever it can be taken odd (then p | n | n(n-1) so p | C(n,2)) or whenever p = 2 and 4 | n.

## decomposition

**For i = 2 (so 3 <= j, 2j <= n), unless n == 2 (mod 4) AND j = n/2, some prime dividing n divides both C(n,2) and C(n,j); hence the entire i = 2 case collapses to the single family n == 2 (mod 4), j = n/2.**

Write n = 2^a * m with m odd. If m does not divide j, some odd prime p | n has v_p(j) < v_p(n), so p | C(n,j) by the previous reduction and p | n(n-1)/2 = C(n,2) since p is odd and p | n. If m | j then j = t*m with t <= 2^(a-1) (from 2j <= n), so v_2(j) = v_2(t) <= a-1 < a = v_2(n), giving 2 | C(n,j); and if a >= 2 then v_2(C(n,2)) = v_2(n)-1 >= 1, so 2 works. The leftover cases are a = 0 (then m = n | j < n, impossible) and a = 1, where m | j and j <= m force j = m = n/2.

*Consequence:* A counterexample search for i = 2 may restrict to n == 2 (mod 4) with 2j = n, i.e. a one-parameter family instead of a two-parameter one, and a Lean proof splits into a uniform 'odd or 4|n or j<n/2' branch plus the single central-binomial branch.

## forced

**If n == 2 (mod 4) and n >= 6, then every odd prime p dividing n-1 divides both C(n,2) and C(n,n/2); such a p exists because n-1 is odd and >= 5.**

Put m = n/2 (odd). p | n-1 = 2m-1 gives p | m(2m-1) = C(n,2). Also 2m == 1 (mod p) forces m == (p+1)/2 (mod p), so m mod p >= p/2 and therefore floor(2m/p) = 2*floor(m/p) + 1; by Legendre's formula v_p(C(2m,m)) = sum_k (floor(2m/p^k) - 2*floor(m/p^k)) >= 1, so p | C(n,n/2).

*Consequence:* Together with the previous three reductions this closes the frozen i <= 2 statement with no search at all: the witness prime is (i=1, or i=2 with n odd / 4|n / j<n/2) a prime divisor of n, and otherwise any odd prime divisor of n-1. It also confirms the site's remark that the case n = 2j is provable.
