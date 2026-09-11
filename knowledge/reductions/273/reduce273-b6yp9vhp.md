# Checked structural reductions — Erdős #273

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## decomposition

**Every admissible modulus m = p-1 (p>=5 prime) is even, so a system S covers Z if and only if BOTH halved systems cover Z: {(a/2, m/2) : (a,m) in S, a even} and {((a-1)/2, m/2) : (a,m) in S, a odd}; hence a solution is exactly a pair of covering systems whose moduli are distinct elements of H2 = {(p-1)/2 : p>=5 prime} and whose two modulus sets are disjoint.**

For p>=5 prime, p is odd so m = p-1 is even. If m is even, every n with m | n-a has the same parity as a, so each congruence class lies wholly in one parity class. Writing n = 2k (resp. n = 2k+1), m | n-a with a even (resp. odd) is equivalent to (m/2) | k - a/2 (resp. k - (a-1)/2); distinctness of the m gives distinctness of all the m/2, so the two halves use disjoint modulus sets.

*Consequence:* The search target is not one covering system but TWO simultaneous covering systems with moduli drawn from H2 = {2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,33,35,...} with no modulus reused between them. This halves all moduli (smaller lcm, far cheaper SAT encodings) and immediately explains why the problem is hard: the cheap small moduli can be used only once, by one of the two halves.

## parity

**Every admissible modulus m = p-1 with p>=5 prime satisfies m = 0 or 4 (mod 6); equivalently the halved modulus m/2 is never congruent to 1 mod 3, so H2 contains none of 1,4,7,10,13,16,...**

m is even since p is odd. If m = 2 (mod 3) then p = m+1 = 0 (mod 3), forcing p = 3, contradicting p >= 5. So m is even and m is 0 or 1 mod 3, i.e. m = 0 or 4 mod 6, and then m/2 is 0 or 2 mod 3.

*Consequence:* Moduli 8,14,20,26,32,38,44,... (all m = 2 mod 6) are inadmissible and must be deleted from every candidate list; in the halved picture of reduction 1 the moduli 4,7,10,13,... are unavailable, so standard covering constructions that rely on the chain 2,4,8,16 are blocked at the second step. A SAT/search encoding should enumerate only m in {4,6,10,12,16,18,22,28,30,36,40,42,46,...}.

## forced

**Any S satisfying the theorem contains at least 18 congruences.**

By reduction 1 the halved moduli form two covering systems with pairwise distinct moduli drawn from H2; a covering system has sum of reciprocals of its moduli at least 1 (the union of the classes has density at most the sum of the densities, and must be all of Z), so the total sum of 1/m' over ALL halved moduli is at least 2. The 17 smallest elements of H2 are 2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,33 whose reciprocals sum to 1.99835... < 2, so at least 18 distinct halved moduli, i.e. at least 18 congruences, are needed.

*Consequence:* Any finite-certificate search may reject outright every candidate with fewer than 18 congruences, and must allow moduli at least up to 70 = 71-1 (since the 18th element of H2 is 35). It also gives a usable rejection filter mid-search: sum of 2/m over the chosen moduli must reach 2, not merely sum of 1/m reaching 1.
