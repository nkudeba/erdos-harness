# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## forced

**If p is prime, i < p, i <= n and n mod p < i, then p divides C(n,i).**

C(n,i) = (n(n-1)...(n-i+1))/i!, and since i < p the denominator i! is coprime to p. Writing r = n mod p, the integer n - r is a multiple of p and satisfies n - i + 1 <= n - r <= n because r < i, so p divides one of the i consecutive factors of the numerator. Hence v_p(C(n,i)) >= 1.

*Consequence:* This is exactly the frozen sub-lemma erdos_699_sub6_1 and it is the engine of every other reduction here: it converts the divisibility question into a purely arithmetic condition on n mod p. A search need never factor a binomial coefficient: for any prime p > i it suffices to compute n mod p.

## forced

**Any counterexample triple (n,i,j) with 1 <= i < j, 2j <= n must satisfy n mod p >= i for EVERY prime p with j < p <= n.**

Let p be a prime with j < p <= n and suppose n mod p < i. Since i < p and i <= n, the previous lemma gives p | C(n,i); since also n mod p < i < j < p and j <= n, the same lemma gives p | C(n,j). Then p divides the gcd and p > j > i, so p >= i and the triple is not a counterexample.

*Consequence:* Candidate counterexamples are screened by a sieve, not by binomial arithmetic: for fixed i and j, n survives only if n mod p >= i for all primes p in (j, n]. Equivalently, for each k >= 1, n must avoid the union of intervals ((n-i)/k, n/k] restricted to primes above j. This is a cheap, purely arithmetic necessary condition that any search stage should assert before touching C(n,i).

## forced

**Any counterexample triple (n,i,j) forces the interval (n-i, n] to be prime-free, i.e. none of n-i+1, n-i+2, ..., n is prime.**

If p is a prime with n-i < p <= n then p > n-i > n/2 >= j (using i < j <= n/2), and n mod p = n - p < i. By the previous reduction such a prime cannot exist in a counterexample. Concretely, p divides C(n,i) and C(n,j) because p divides one of the top i (resp. j) descending factors while p exceeds both i and j, so p is coprime to i! and j!.

*Consequence:* A search over n can discard n immediately unless the i integers below and including n are all composite; for i = 2 or 3 this alone rules out the overwhelming majority of n (and mirrors why known exceptional n are powers of 2 and similar). More generally the same argument with n mod p = n - 2p, n - 3p, ... forbids primes in ((n-i)/k, n/k] for each k >= 1 with n/k > j.

## decomposition

**The case i = 1 of the problem is unconditionally true, because gcd(n, C(n,j)) > 1 for every 0 < j < n; so the problem reduces to i >= 2.**

From j*C(n,j) = n*C(n-1,j-1) we get v_p(j) + v_p(C(n,j)) = v_p(n) + v_p(C(n-1,j-1)) >= v_p(n) for every prime p, so v_p(j) < v_p(n) forces p | C(n,j). If no prime p | n had v_p(j) < v_p(n), then p^{v_p(n)} | j for all p | n, i.e. n | j, impossible for 0 < j < n. Hence some prime p divides both n = C(n,1) and C(n,j), and any prime satisfies p >= 1 = i.

*Consequence:* The universally quantified statement may be split as: i = 1 (proved outright by the identity above) and i >= 2 (the real content). A Lean proof can dispose of i = 1 with the descending-factorial identity, and a search may restrict to 2 <= i < j <= n/2, which also makes the prime-free-interval condition of the previous reduction non-trivial.
