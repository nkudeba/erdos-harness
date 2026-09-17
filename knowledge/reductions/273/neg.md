# Checked structural reductions — Erdős #273

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## parity

**Since every admissible modulus m = p-1 (p>=5 prime) is even and >=4, a family of congruences with distinct admissible moduli covers Z if and only if, after halving, the sub-family with even residues covers Z and the sub-family with odd residues covers Z; hence the problem is EQUIVALENT to: do there exist two covering systems of Z, with distinct moduli, whose modulus sets are disjoint subsets of H = {h >= 2 : 2h+1 is prime}?**

p >= 5 prime is odd, so m = p-1 is even and m >= 4; therefore the class a mod m lies entirely inside one parity class of Z. Writing n = 2t, the congruence n ≡ a (mod m) with a even is equivalent to t ≡ a/2 (mod m/2), and with n = 2t+1 and a odd it is equivalent to t ≡ (a-1)/2 (mod m/2); congruences of the other parity contribute nothing to that half. Halving is injective on the even moduli, so global distinctness of the m_i is exactly disjointness-plus-distinctness of the two halved modulus sets, and each halved modulus m/2 = (p-1)/2 is >= 2 and lies in H.

*Consequence:* One covering system is not enough: a certificate must exhibit TWO covering systems of Z with distinct moduli, drawn from disjoint subsets of H = {2,3,5,6,8,9,11,14,15,18,20,21,23,26,29,30,33,35,...}. This is exactly why Selfridge's divisors-of-360 example fails here: it uses p=3, i.e. modulus 2, i.e. the halved modulus h=1, which trivialises one half and is forbidden. A search should work in the halved variables h_i in H with a parity bit per congruence, not in the original moduli.

## forced

**Every admissible modulus m = p-1 with p >= 5 prime satisfies m ≡ 0 or 4 (mod 6); equivalently no admissible modulus is ≡ 2 (mod 6), and every halved modulus h = (p-1)/2 satisfies h ≢ 1 (mod 3).**

A prime p >= 5 is coprime to 6, so p ≡ 1 or 5 (mod 6), whence m = p-1 ≡ 0 or 4 (mod 6). Halving, h = m/2 ≡ 0 or 2 (mod 3), so h ≡ 1 (mod 3) never occurs. (This is a necessary, not sufficient, condition: primality of m+1 is still required.)

*Consequence:* The pool is pre-filtered by a one-line arithmetic test before any primality check: moduli 8,14,20,26,32,38,44,... (all ≡ 2 mod 6) are excluded outright, and in the halved formulation the moduli 4,7,10,13,16,19,... (≡ 1 mod 3) are excluded. Combined with the parity reduction, both halved covering systems must draw their moduli from the 2-of-3 residue classes {0,2} mod 3, so a fibre argument at d=3 sees only moduli with 3 | h or h ≡ 2 (mod 3).

## decomposition

**For any covering family {(a_i, m_i)} with L = lcm(m_i), and for EVERY divisor d of L and EVERY residue r mod d, the fibre inequality  sum over { i : a_i ≡ r (mod gcd(m_i,d)) } of gcd(m_i,d)/m_i  >=  1  must hold.**

Restrict to the arithmetic progression n ≡ r (mod d), which has density 1/d. The class a_i mod m_i meets it in a progression of density 1/lcm(m_i,d) when a_i ≡ r (mod gcd(m_i,d)), and is disjoint from it otherwise. Covering that fibre forces sum_{compatible i} 1/lcm(m_i,d) >= 1/d, and multiplying by d gives sum gcd(m_i,d)/m_i >= 1.

*Consequence:* Gives a family of cheap linear necessary conditions to assert before any search. With d = 2 and all m_i even it specialises to the parity density bound: the congruences with even residues satisfy sum 2/m_i >= 1 and likewise for the odd ones (so each parity block alone has sum 1/m_i >= 1/2). With d = 4 it separates moduli with 4 | m (i.e. p ≡ 1 mod 4) from those with m ≡ 2 mod 4 (p ≡ 3 mod 4); with d = 3 and d = 6 it constrains how many moduli divisible by 6 are available. Any candidate modulus multiset failing one of these is rejected in milliseconds instead of being handed to a solver.

## symmetry

**The set of covering families is invariant under the translations a_i -> a_i + c (all i, any fixed c in Z) and under the reflection a_i -> -a_i, both of which leave the multiset of moduli unchanged; hence one may assume without loss of generality that the residue attached to the smallest used modulus is 0.**

n ≡ a_i + c (mod m_i) holds for all n in a set S if and only if n ≡ a_i (mod m_i) holds for all n in S - c, and Z - c = Z; likewise n ≡ -a_i (mod m_i) covers Z iff n ≡ a_i (mod m_i) covers Z under n -> -n. Neither map touches the moduli, so admissibility (m_i = p-1) and distinctness are preserved. Translating by -a_{i0} sends the residue of the smallest modulus to 0.

*Consequence:* Cuts the search space by a factor of m_min * 2 and removes the trivial symmetry orbit that otherwise makes a solver re-discover the same certificate m_min times. Note the translation by an odd c SWAPS the two parity blocks of the parity reduction, so the two halved covering systems may be assumed interchangeable: WLOG the block containing the smallest modulus is the even-residue block.
