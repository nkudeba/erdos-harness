# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## forced

**If some prime p satisfies n - i < p <= n, then that p already witnesses the statement for (n,i,j) for EVERY j with i < j <= n/2; hence a counterexample requires all of n-i+1, n-i+2, ..., n to be composite.**

Since i < j <= n/2 we have n - i > n/2, so any prime p in (n-i, n] satisfies n/2 < p <= n and in particular p > i and p > j. In base p the number n has digits (1, n-p) and any m < p has digits (0, m), so by Kummer's carry rule p divides C(n,m) exactly when m > n - p. Both i and j exceed n - p (because p > n - i > n - j), so p divides C(n,i) and C(n,j), and p > i.

*Consequence:* A search may discard every n for which the half-open interval (n-i, n] contains a prime; equivalently only n sitting at the top of a prime gap of length at least i can be a counterexample. This explains every known near-miss: for (n,i) = (10,3), (16,2), (28,5), (28,3), (244,3), (512,2), (2048,2), (2188,3) the numbers n-i+1..n are all composite. It also gives a complete proof for all n with a prime in that window, reducing the open problem to prime-gap tops.

## decomposition

**The case i = 1 of the statement is unconditionally true, so the problem reduces to i >= 2 (and hence n >= 2j >= 6).**

From j*C(n,j) = n*C(n-1,j-1) we get that n/gcd(n,j) divides C(n,j). Since 1 <= j <= n/2 < n we have n does not divide j, so n/gcd(n,j) > 1 and any prime p dividing it divides both n = C(n,1) and C(n,j). Such a p satisfies p >= 1 = i, which is all the statement demands when i = 1.

*Consequence:* Removes an entire slice of the parameter space from both search and proof; the Lean proof can dispose of i = 1 by exhibiting a prime factor of n/gcd(n,j), and every counterexample search may start at i = 2. Combined with the prime-gap reduction it means counterexamples need at least two consecutive composites ending at n.

## equivalent-form

**The statement is equivalent to a finite base-p digit condition: there exists a prime p with i <= p <= n such that NEITHER i NOR j is digitwise dominated by n in base p (i.e. some base-p digit of i exceeds the corresponding digit of n, and likewise for j).**

Every prime factor of C(n,m) is at most n, so primes p > n can be ignored in the existential. By Lucas' theorem, p does not divide C(n,m) exactly when each base-p digit of m is <= the corresponding base-p digit of n; so p | C(n,m) exactly when some digit of m exceeds the matching digit of n.

*Consequence:* Turns the search from big-integer gcd computation into a digit comparison over the O(n/log n) primes p in [i,n], costing O(log n) per prime with no large arithmetic: a candidate (n,i,j) can be refuted or confirmed in microseconds, and the whole problem becomes a statement about base-p digit patterns of n, i, j rather than about binomial coefficients.
