# Checked structural reductions — Erdős #7

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## symmetry

**The affine group acts on solutions: if (a_i mod m_i)_{i<k} is a distinct odd covering system with L = lcm(m_i), then for every v in Z and every u coprime to L the family (u*a_i + v mod m_i) is again a distinct odd covering system with the same moduli; in particular one may assume WLOG that the residue attached to any one chosen modulus (say the smallest) is 0.**

Since m_i divides L, u is invertible mod m_i, so x = a_i (mod m_i) holds iff u*x+v = u*a_i+v (mod m_i); hence the map x -> u*x+v is a bijection of Z (resp. Z/L) carrying the i-th class exactly onto the i-th transformed class. A bijection carries a cover of Z onto a cover of Z, and the moduli are untouched, so oddness and distinctness are preserved. Taking u=1, v=-a_{i0} normalises the residue of index i0 to 0.

*Consequence:* A search over residue vectors may fix one coordinate (a_{i0}=0), dividing the residue search space by m_{i0}, and may further quotient by the multiplicative action of (Z/L)^* that stabilises that normalisation. A proof may likewise assume the class of the smallest modulus is 0 mod m_{i0} without loss of generality.

## forced

**The reciprocal sum of the moduli of any covering system is at least 1; with DISTINCT ODD moduli all > 1 this forces at least 7 congruences and forces the largest modulus to be at least 15.**

The class a_i mod m_i has natural density 1/m_i, and a finite union of sets of density d_i has density at most sum d_i, so covering Z forces sum 1/m_i >= 1. The six largest reciprocals available from distinct odd moduli > 1 are 1/3+1/5+1/7+1/9+1/11+1/13 = 0.9551... < 1, so k >= 7; and the same sum is the total available if every modulus is at most 13, so some modulus is >= 15.

*Consequence:* Any search may hard-assert k >= 7 and max modulus >= 15, and may prune every partial modulus set whose reciprocal sum plus the best possible completion stays below 1. In Lean this is the pool/density route already certified as Erdos.Covering.CongruenceFamily.density and pool_bound.

## forced

**The moduli of a covering system cannot be pairwise coprime; hence in an odd covering system some odd prime p divides at least two distinct moduli.**

If the m_i are pairwise coprime then by the Chinese Remainder Theorem the conditions x != a_i (mod m_i) are independent modulo L = prod m_i, so exactly prod (m_i - 1) > 0 residues mod L avoid every class. Such a residue is uncovered, so the family is not a covering system.

*Consequence:* Any candidate modulus set must contain a repeated prime factor, so the lcm L satisfies L < prod m_i strictly; a search may discard every pairwise-coprime modulus set before assigning residues, and a proof may assume some odd prime divides two moduli.

## forced

**Passing to an irredundant subfamily (WLOG, since deleting a redundant class keeps the moduli distinct and odd), for EVERY prime p dividing L = lcm of the moduli, at least p of the used moduli are divisible by p^a where p^a is the exact power of p in L; consequently the number of congruences is at least the largest prime factor of L, and the number of divisors of L/p^a is at least p for every p | L.**

Pick j with p^a | m_j and an x covered only by class j (irredundancy). Every class with p^a not dividing m_i has m_i | L/p, so that class is invariant under adding L/p; since none of them covers x, none covers any of the p elements of x + {0, L/p, ..., (p-1)L/p}. Each class with p^a | m_i meets that coset at most once (two elements differ by j*L/p with 0<j<p, whose p-adic valuation a-1 is below that of m_i, so m_i cannot divide the difference), so at least p such classes, hence at least p such distinct moduli, are needed.

*Consequence:* A direct screen on candidate lcms L: for each prime p | L the number of divisors of L/p^{v_p(L)} must be at least p, and the total number of congruences must be at least the largest prime factor of L. For odd L this kills every L whose largest prime factor is big relative to the divisor count of the rest, and it forces at least 3 moduli divisible by 3^{v_3(L)}, at least 5 divisible by 5^{v_5(L)}, etc. It also fixes the exact set of moduli that must be present at each top prime power, removing those choices from the search.
