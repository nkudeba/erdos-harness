# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## equivalent-form

**For every prime p with j < p, p divides gcd(C(n,i),C(n,j)) if and only if n mod p < i; consequently such a p is automatically a valid witness (p > j > i), and the target for (n,i,j) fails only if BOTH (a) every prime p with j < p <= n satisfies n mod p >= i, and (b) no prime p in [i,j] divides both binomials.**

Since i < j < p, both i and j are single base-p digits (all higher digits zero), so Lucas' theorem gives C(n,i) = C(n mod p, i) and C(n,j) = C(n mod p, j) modulo p. Hence p | C(n,i) iff n mod p < i and p | C(n,j) iff n mod p < j, and as i < j the conjunction is exactly n mod p < i. Primes p > n divide neither binomial (all prime factors of C(n,k) are at most n) and also satisfy n mod p = n >= i, so the equivalence is consistent there too.

*Consequence:* The infinite 'large prime' half of the search collapses to arithmetic on residues of n: no binomial coefficients need be computed for p > j. A counterexample search only has to (i) test the residue condition n mod p >= i for the primes in (j,n], and (ii) do real p-adic work (Kummer carries) for the few primes in [i,j]. It also shows the large-prime part is monotone in j (a witness p > j also serves every j' <= j), so for fixed (n,i) the hardest case is j = floor(n/2), which is the order in which j should be attacked.

## forced

**If for some integer m >= 1 there is a prime p with (n-i)/m < p <= n/m and p > j, then the target holds for (n,i,j); in particular any counterexample (n,i,j) requires the interval (n-i, n] to contain no prime at all, and the interval ((n-i)/2, n/2] to contain no prime greater than j.**

n mod p < i is equivalent to the existence of m >= 1 with n - i < m*p <= n (take m = floor(n/p)), i.e. p lies in ((n-i)/m, n/m]. By the previous reduction any such prime with p > j divides both binomials and is >= i, so it is a witness. For m = 1 the prime lies in (n-i, n]; since n >= 2j and j > i we have n - i >= 2j - i > j, so such a prime automatically exceeds j.

*Consequence:* A counterexample must sit inside a prime gap: no prime in (n-i, n], no prime > j in ((n-i)/2, n/2], and so on for each m. This is a cheap arithmetic screen that kills almost every (n,i,j) before any binomial coefficient is computed, and it explains why only finitely many n can be counterexamples for fixed i < j (the required simultaneous prime-free intervals become impossible). It also gives the correct enumeration order: sieve n, reject unless (n-i,n] is prime-free, only then test the small primes in [i,j].

## decomposition

**The case i = 1 of the target is unconditionally true: for every n and every j with 1 < j and 2j <= n, the integer d = n/gcd(n,j) is greater than 1 and divides both C(n,1) = n and C(n,j), so any prime p dividing d is a witness (and p >= 1 = i trivially).**

From j*C(n,j) = n*C(n-1,j-1) we get n | j*C(n,j), hence (n/gcd(n,j)) | C(n,j); also (n/gcd(n,j)) | n by definition. Since 1 <= j <= n/2 < n, n does not divide j, so n/gcd(n,j) > 1 and has a prime factor. That prime divides gcd(C(n,1),C(n,j)) and every prime is >= 1.

*Consequence:* The outer induction/search may assume i >= 2 throughout, removing an entire infinite family of pairs from both the counterexample search and the Lean proof obligation. In Lean this is a short standalone lemma (Nat.succ_mul_choose_eq / Nat.choose_symm_diff style) that discharges the i = 1 branch before any prime machinery.

## substitution

**When i itself is prime, the smallest admissible prime p = i divides C(n,i) if and only if the base-i digit of n in position 1 is zero, i.e. iff floor(n/i) mod i = 0; when i is not prime, no prime equal to i exists and every witness satisfies p > i.**

In base p = i the number i has digits (1,0), so Lucas' theorem gives C(n,i) congruent to C(n_1,1)*C(n_0,0) = n_1 modulo p, where n_1 = floor(n/p) mod p. Hence p | C(n,i) exactly when that digit vanishes. This is the only prime equal to i, and all other admissible primes are strictly larger than i.

*Consequence:* The boundary prime p = i, which is precisely where the target (p >= i) differs from the false strict variant (p > i), is decided by a single digit of n in base i — no binomial coefficient needed. All nine known strict-variant failures have their largest gcd-prime equal to i, so a search must test p = i via this digit condition (plus a Kummer carry test for C(n,j)) before declaring a counterexample; omitting it would reproduce the false strict statement.
