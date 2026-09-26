# Checked structural reductions — Erdős #7

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## forced

**If a covering system has distinct moduli m_1,...,m_k all odd and >1, then its lcm L is an ODD ABUNDANT number: sigma(L) >= 2L; in particular L >= 945 = 3^3*5*7 and 3 | L for every candidate lcm below 945^-type range (see the companion reduction).**

Each congruence class a_i mod m_i has density 1/m_i, and a covering of Z forces sum_i 1/m_i >= 1 (union bound on densities in an interval of length L). Every modulus divides L = lcm(m_i), the moduli are distinct and all >1, so sum_i 1/m_i <= sum_{d|L, d>1} 1/d = sigma(L)/L - 1. Combining, sigma(L)/L - 1 >= 1, i.e. sigma(L) >= 2L; since all m_i are odd, L is odd, and the smallest odd abundant number is 945. (Equality sum_i 1/m_i = 1 would force an exact cover with distinct moduli, excluded by the library's not_exact_of_distinctModuli, so the inequality is in fact strict; the weaker non-strict form above is what is claimed here.)

*Consequence:* Candidate lcms are not arbitrary odd numbers but exactly the odd abundant numbers: 945, 1575, 2205, 2835, 3465, 4095, 4725, 5355, 5775, 5985, ... Any enumeration over lcm values may skip all others outright, and inside a fixed L the reciprocal screen sum_{i used} 1/m_i >= 1 is a linear (pseudo-Boolean) constraint over the used-modulus indicators, with slack sigma(L)/L - 2 telling how many divisors may be left unused.

## symmetry

**The affine group acts on solutions: if {a_i mod m_i} is an odd distinct covering system with lcm L, then for every integer t and every u coprime to L the family {u*a_i + t mod m_i} is again one, with the same multiset of moduli.**

Each m_i divides L, so gcd(u, m_i) = 1 and the map x -> u*x + t sends the class a_i mod m_i bijectively onto the class u*a_i + t mod m_i. It is a bijection of Z, so it carries the union of the classes onto the union of the images; the union is all of Z iff its image is. The moduli are untouched, so distinctness and oddness are preserved.

*Consequence:* In any search the residue of one chosen modulus may be fixed without loss of generality (translate by -a to make it 0), cutting the space by a factor equal to that modulus; the further (Z/L)^* action can be quotiented on top of that, typically another factor of phi(L)/(order of the stabiliser).

## forced

**An odd distinct covering system has at least 7 congruences (k >= 7), and its moduli cannot all be at least 15: the six smallest admissible moduli 3,5,7,9,11,13 already have reciprocal sum 1/3+1/5+1/7+1/9+1/11+1/13 = 0.9553... < 1.**

Covering forces sum_i 1/m_i >= 1 (density union bound). The moduli are distinct odd integers >1, so any six of them have reciprocal sum at most that of the six smallest such integers, namely 3,5,7,9,11,13, whose sum is 9553/10010 < 1. Hence six congruences can never suffice, so k >= 7.

*Consequence:* Gives a cardinality lower bound for any solver encoding, and, combined with the divisor constraint m_i | L, forces small divisors to be used: within a fixed L the unused-divisor slack is sigma(L)/L - 2, so any divisor d with 1/d > slack is mandatory (e.g. for L = 945, sigma/L = 1920/945 = 2.0317, slack 0.0317, so every divisor d < 31.5 -- i.e. 3,5,7,9,15,21,27 -- must be used).
