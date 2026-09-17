# Checked structural reductions — Erdős #273

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## decomposition

**Every admissible modulus m = p-1 (p >= 5 prime) is even, so the system splits by the parity of its residues: writing S = {(p-1)/2 : p >= 5 prime} = {2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,...}, a covering system with distinct moduli of the form p-1 exists iff the halved moduli can be partitioned into two DISJOINT sets, each of which is the modulus set of a covering system of Z with distinct moduli drawn from S.**

p >= 5 is odd, so m = p-1 is even and M = m/2 >= 2. A class n = a (mod m) with m even forces n = a (mod 2), so it lies entirely in one parity class; putting n = 2t, a = 2b (resp. n = 2t+1, a = 2b+1) the congruence becomes exactly t = b (mod M). Hence the even-residue classes cover Z iff they cover all even n, likewise for the odd ones, and conversely doubling any two covering systems with disjoint modulus sets from S and offsetting one by 1 rebuilds a covering system with distinct moduli p-1.

*Consequence:* The target is not one covering system but two simultaneous ones over a shared, non-repeating pool: the search space is a 2-colouring of the chosen halved moduli, each colour class independently required to cover Z. Each colour class needs sum of 1/M >= 1 over its own moduli, so the total halved reciprocal sum must be >= 2 (equivalently sum 1/m >= 1 in the original moduli). Crucially modulus 4 (halved 2) can serve only ONE of the two parts, so the other part must cover Z using halved moduli >= 3 from S only. All search/encoding should be done in the halved pool S, never in the pool {p-1}.

## parity

**Every admissible modulus m = p-1 with p >= 5 prime satisfies m = 0 or 4 (mod 6); equivalently m is even and m is never 2 (mod 3), and the halved modulus M = (p-1)/2 is never 1 (mod 3).**

For p >= 5 prime, p is not divisible by 2 or 3, so p = 1 or 5 (mod 6). If p = 1 (mod 6) then m = p-1 = 0 (mod 6); if p = 5 (mod 6) then m = 4 (mod 6). Halving, M = m/2 is 0 or 2 (mod 3), never 1 (mod 3).

*Consequence:* The candidate pool is thinner than 'even numbers': 8, 14, 20, 26, 32, 38, 44, ... are excluded on residue grounds alone (before primality), and in the halved pool every M = 1 (mod 3) -- 1, 4, 7, 10, 13, 16, 19, 22, 25, ... -- is unavailable. A solver encoding should restrict the modulus pool by this congruence filter first, and any density/counting argument may assume it. Note the pool still contains all needed multiples of 3, so no further parity-style splitting follows from this.

## forced

**Each parity part separately obeys the density bound: sum over the even-residue classes of 2/m >= 1 and sum over the odd-residue classes of 2/m >= 1, hence sum over all classes of 1/m >= 1; since the 17 smallest admissible moduli 4,6,10,12,16,18,22,28,30,36,40,42,46,52,58,60,66 have reciprocal sum 0.9992 < 1, any solution uses at least 18 congruences, and if modulus 4 is not used it needs at least 40 congruences.**

A class a (mod m) has natural density 1/m, so a family covering Z has reciprocal sum at least 1; applying this to each of the two halved covering systems produced by the parity split gives sum 1/(m/2) >= 1 per part. Because the moduli are distinct, the largest achievable reciprocal sum on k classes is the sum of the k largest reciprocals in the admissible pool, so k must be large enough for that maximum to reach 1. Dropping 4 from the pool makes the greedy maximum reach 1 only after 40 terms.

*Consequence:* Cardinality lower bounds a solver can assert directly, and a strong incentive to include the small moduli: any encoding limited to fewer than 18 congruences is UNSAT by arithmetic alone, and any encoding that omits modulus 4 needs at least 40 congruences (so lcm-bounded searches omitting 4 are hopeless at small sizes). Combined with the parity split, the reciprocal budget must be split into two halves each reaching 1 in halved units.

## symmetry

**The solution set is invariant under the translations n -> n + c (c in Z) and under n -> -n: if (a_i mod m_i) is a covering system then so are (a_i + c mod m_i) and (-a_i mod m_i), with the same multiset of moduli; hence one may assume without loss of generality that the residue attached to any single chosen class (e.g. the smallest used modulus) is 0.**

n is covered by (a_i + c mod m_i) exactly when n - c is covered by (a_i mod m_i), and translation is a bijection of Z, so covering is preserved; likewise n is covered by (-a_i mod m_i) exactly when -n is covered by the original. Neither map touches the moduli, so the constraints 'distinct' and 'of the form p-1' are untouched.

*Consequence:* In any search or SAT encoding, fix the residue of one designated class (say the class of the smallest used modulus) to 0, cutting the residue search space by a factor equal to that modulus, and optionally impose a lexicographic tie-break under the reflection a -> -a to halve it again.
