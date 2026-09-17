# Checked structural reductions — Erdős #699

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## decomposition

**The case i = 1 of the target is unconditionally true: for every n and every j with 2 <= j and 2*j <= n, the integer d = n / gcd(n, j) satisfies d > 1, d | n = C(n,1) and d | C(n,j), so any prime divisor of d is a prime p >= 1 dividing gcd(C(n,i), C(n,j)).**

From the absorption identity j * C(n,j) = n * C(n-1,j-1) we get n | j * C(n,j), hence (n/gcd(n,j)) | C(n,j) because n/gcd(n,j) is coprime to j/gcd(n,j). Also n/gcd(n,j) divides n trivially, and it exceeds 1 because gcd(n,j) <= j < n. Since i = 1 imposes no lower bound on p beyond p >= 1, any prime factor of n/gcd(n,j) is a valid witness.

*Consequence:* The whole i = 1 slice is removed from the search and from the proof: a counterexample must have i >= 2. For a Lean proof this splits the theorem into a trivial branch (i = 1, witness = any prime factor of n/gcd(n,j)) and the real branch i >= 2.

## forced

**If there exists a prime p with j < p <= n and (n mod p) < i, then the target holds for (n,i,j) with that witness p; hence any counterexample (n,i,j) must satisfy (n mod p) >= i for EVERY prime p in the interval (j, n].**

By the window argument of the previous reduction, for a prime p > i we have p | C(n,i) exactly when (n mod p) < i, and for a prime p > j we have p | C(n,j) exactly when (n mod p) < j. If p > j > i and (n mod p) < i then both conditions hold, and p > j > i gives p >= i, so p is a legitimate witness.

*Consequence:* A counterexample search never needs binomial coefficients: sieve the primes in (j, n] and reject n as soon as one of them has n mod p < i. Concretely, since i < j <= n/2, this kills the vast majority of (n,i,j) triples by pure residue arithmetic, leaving only n whose residues modulo all large primes are uniformly >= i.

## forced

**If the half-open interval (n-i, n] contains a prime p, then the target holds for (n,i,j) for every j with i < j <= n/2; hence in any counterexample all of n-i+1, n-i+2, ..., n are composite (in particular n itself is composite, and for i = 2 both n-1 and n are composite).**

A prime p with n-i < p <= n satisfies n mod p = n - p < i (since p > n-i and p <= n forces the quotient to be 1, as 2p > 2(n-i) > n because i < n/2). Then p > n - i > n/2 >= j > i, so p > j, and by the window criterion p divides both C(n,i) and C(n,j) with p >= i.

*Consequence:* Counterexample candidates n are confined to the starts of prime gaps: for i = 2 one needs two consecutive composites ending at n, for i = 5 five consecutive composites ending at n. This explains why the known near-misses sit at n = 16, 28, 512, 2048, 2188 (all with a composite run ending at n), and turns the outer loop of any search into an enumeration of prime gaps rather than of all integers.
