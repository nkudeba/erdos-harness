# Checked structural reductions — Erdős #273

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## parity

**Every admissible modulus m = p-1 (p >= 5 prime) is even, so each congruence class a_i mod m_i lies entirely inside one parity class; consequently any such covering system splits into the sub-family with a_i even, which must cover all even integers, and the sub-family with a_i odd, which must cover all odd integers, and after the substitutions n = 2t (resp. n = 2t+1) each half becomes a covering system of Z with DISTINCT moduli m_i/2 = (p-1)/2 >= 2, the two half-modulus sets being disjoint.**

For p >= 5 prime, p is odd, so m = p-1 is even and n ≡ a (mod m) forces n ≡ a (mod 2); hence a class with a even contains no odd integer and vice versa. Writing m = 2m' and, for a even, a = 2a', we get 2t ≡ 2a' (mod 2m') iff t ≡ a' (mod m'); for a odd, 2t+1 ≡ a (mod 2m') iff t ≡ (a-1)/2 (mod m'). Injectivity of i ↦ m_i is global, so no modulus occurs in both halves, and halving is injective, so the two sets of half-moduli {(p-1)/2} are disjoint and each is a set of distinct integers >= 2 (p >= 5 gives (p-1)/2 >= 2).

*Consequence:* The search target is not one covering system but TWO covering systems of Z with distinct moduli drawn from H = {(p-1)/2 : p >= 5 prime} = {2,3,5,6,8,9,11,14,15,18,20,...}, using DISJOINT modulus sets. A search may therefore work at half the lcm, enumerate pairs of disjoint subsets of H, and any impossibility proof only needs to rule out two disjoint covering systems over H.

## forced

**Every admissible modulus m = p-1 (p >= 5 prime) satisfies m ≡ 0 or 4 (mod 6); no integer m ≡ 2 (mod 6) is admissible, equivalently every half-modulus (p-1)/2 is ≡ 0 or 2 (mod 3) and never ≡ 1 (mod 3).**

If m ≡ 2 (mod 6) then m+1 ≡ 3 (mod 6), so 3 divides m+1 and m+1 > 3, hence m+1 is composite and m is not of the form p-1 with p >= 5 prime. Conversely m = p-1 is even (p odd) and p is not divisible by 3, so p ≡ 1 or 2 (mod 3) and m ≡ 0 or 1 (mod 3), which together with m even gives m ≡ 0 or 4 (mod 6). Dividing by 2, the half-modulus m/2 is ≡ 0 or 2 (mod 3).

*Consequence:* The candidate modulus pool is thinned by an arithmetic filter that needs no primality test: drop 2,8,14,20,26,32,38,... (mod 6 = 2) at the top level, and drop 1,4,7,10,13,16,19,... (mod 3 = 1) from the half-modulus pool H of reduction 1. In particular the half-system may never use moduli 4, 7, 10, 13, 16, which removes the cheapest small-modulus covering constructions.

## decomposition

**A finite family of classes (a_i mod m_i) covers all of Z if and only if it covers the finitely many integers 0,1,...,L-1 where L = lcm(m_i); so the affirmative direction is a finite check of exactly L cases, and by reduction 1 it is two independent finite checks of L/2 cases each.**

Each predicate n ≡ a_i (mod m_i) is periodic with period m_i, hence the disjunction over i is periodic with period L = lcm(m_i). A periodic predicate holds for all integers iff it holds on one full period, e.g. on {0,...,L-1}.

*Consequence:* A search certifies a candidate by a single residue sweep modulo L (or two sweeps of length L/2 after the parity split), never by testing an unbounded range; and a Lean proof of the affirmative direction reduces to a decidable finite check modulo L.

## forced

**In any covering system all of whose moduli are even, the classes with even residue satisfy sum of 1/m_i >= 1/2 and the classes with odd residue satisfy sum of 1/m_i >= 1/2 separately (so the total is >= 1); equivalently each half-system of reduction 1 has sum of 2/m_i >= 1 over its own, disjoint, modulus set.**

By reduction 1 the even-residue classes must cover every even integer; after n = 2t they become classes modulo m_i/2 covering all of Z, and a finite union of classes mod m' covering Z must have natural densities summing to at least 1, i.e. sum 1/(m_i/2) >= 1, i.e. sum 1/m_i >= 1/2. The same argument applies to the odd-residue classes, and the two index sets are disjoint.

*Consequence:* A search over subsets of the admissible moduli {4,6,10,12,16,18,22,28,30,36,...} can prune immediately: it must pick two DISJOINT sub-collections, each with reciprocal sum at least 1/2. Since 1/4+1/6+1/10+1/12 = 0.6 already, the two halves compete for the few small moduli, and any branch whose remaining reciprocal budget cannot reach 1/2 twice is dead.
