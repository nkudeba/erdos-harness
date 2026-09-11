# Checked structural reductions — Erdős #273

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## parity

**Every admissible modulus m = p-1 (p >= 5 prime) is even, so each class a mod m lies entirely inside one parity class; consequently a covering system with distinct admissible moduli is EXACTLY a pair of covering systems of Z with distinct moduli drawn from H = {(p-1)/2 : p >= 5 prime}, using two DISJOINT subsets of H (the even-residue classes halve to one, the odd-residue classes to the other), and conversely any two such disjoint covering systems double back to a solution.**

For p >= 5 prime, p is odd, so m = p-1 is even and n == a (mod m) forces n == a (mod 2): a class with even a contains only even integers and one with odd a only odd integers. Hence the even integers n = 2t must be covered by the even-a classes, and 2t == a (mod m) is equivalent to t == a/2 (mod m/2), giving a covering system of Z with moduli m/2; the odd integers n = 2t+1 give the second one with moduli m/2 as well. The two halved modulus sets are disjoint because the original m_i are distinct, and reversing the two substitutions turns any pair of coverings with disjoint moduli in H back into a single system with distinct moduli 2h = p-1.

*Consequence:* The search target is not one covering system but two, from a common sparse pool with no shared modulus. In halved coordinates the pool is H = {2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,33,35,36,...} and each of the two systems separately needs reciprocal sum >= 1, so the whole solution needs sum_{h used} 1/h >= 2 over DISTINCT elements of H (equivalently sum_i 1/m_i >= 1 with each parity half >= 1/2). Any search should enumerate in halved coordinates and enforce disjointness, and any impossibility proof may assume min-modulus >= 2 systems over H.

## forced

**For every prime q and every admissible modulus m = p-1 with m > q-1, we have m not== q-1 (mod q); in particular every admissible modulus is == 0 or 4 (mod 6) (never == 2 mod 6, never odd), and every halved modulus h = (p-1)/2 satisfies h == 0 or 2 (mod 3), i.e. h is never == 1 (mod 3).**

If m is admissible then m+1 = p is prime; if in addition m+1 > q then q does not divide m+1, i.e. m not== -1 == q-1 (mod q). Taking q = 2 (using m >= 4 > 1) gives m even, and q = 3 (using m >= 4 > 2) gives m not== 2 (mod 3), so m == 0 or 4 (mod 6). Halving, h = m/2 is never == 1 (mod 3).

*Consequence:* A concrete sieve on the candidate modulus pool before any search: from the even numbers only those == 0 or 4 mod 6 survive (8, 14, 20, 26, 32, 38 are all killed at once, as are all odd values), and in halved coordinates 4, 7, 10, 13, 16, 19, 22, 25 are killed. The same rule with q = 5, 7, 11, 13 prunes further (m not== 4 mod 5 once m > 4, etc.). This shrinks the branching factor of the covering search and lets a proof stage assume, without any primality reasoning, that every modulus lies in a fixed union of residue classes.

## forced

**Combining the parity split with distinctness: the set S of halved moduli actually used is a set of DISTINCT elements of H = {(p-1)/2 : p >= 5 prime} with sum_{h in S} 1/h >= 2; since the 17 smallest elements of H have reciprocal sum < 2, any solution of erdos_273 must use at least 18 distinct moduli, and must use some halved modulus h >= 35, i.e. some modulus m = p-1 >= 70 with p >= 71.**

By the parity reduction the even-residue and odd-residue classes give two covering systems of Z whose halved modulus sets are disjoint subsets of H, and a covering system has natural density sum >= 1, so each contributes reciprocal sum >= 1 and the disjoint union S satisfies sum 1/h >= 2. If |S| <= 17 then sum_{h in S} 1/h is at most the sum of the reciprocals of the 17 smallest elements of H, which is 1.9984... < 2. Likewise if every h in S were <= 33 then S would be contained in those same 17 smallest elements, again giving sum < 2.

*Consequence:* Hard lower bounds a search can use as pruning and a certificate builder must satisfy: k >= 18 in the frozen statement, at least one prime p >= 71 among the p_i, and any partial candidate whose remaining reciprocal budget cannot reach 2 in halved coordinates can be abandoned immediately. It also rules out all 'small' certificate attempts (e.g. anything confined to divisors of 360 with p >= 5) without running a search.

## symmetry

**The affine group acts on solutions: if (a_i mod m_i) is a covering system with moduli m_i and u is any integer coprime to L = lcm(m_i), then (u*a_i + c mod m_i) is again a covering system with the same moduli, for every integer c; in particular one may assume without loss of generality that a_i is in [0, m_i) and that a_j = 0 for any one chosen index j.**

n == u*a_i + c (mod m_i) holds if and only if u^{-1}(n - c) == a_i (mod m_i), and since gcd(u, m_i) = 1 the map n -> u^{-1}(n - c) is a bijection of Z/m_i and of Z. So the transformed system covers exactly the image of the covered set under a bijection of Z, hence covers Z if and only if the original does. Taking u = 1 and c = -a_j normalises one residue to 0.

*Consequence:* The certificate search may fix one residue (the one belonging to the smallest modulus) to 0 and quotient by the multiplier group, cutting the residue search space by a factor of m_min * phi(L)-ish; and a Lean proof of the affirmative direction may present a normalised witness. It also means the negative direction may assume any convenient normalisation of one class.
