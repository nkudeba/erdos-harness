Operator-supplied informal route; no external Lean proof was used.
Source: Balister, Bollobás, Morris, Sahasrabudhe, Tiba, “Covering intervals with arithmetic progressions”, https://par.nsf.gov/servlets/purl/10165575 .

The short proof uses sparse polynomials, not a simple parity induction. Let q be the lcm of the positive moduli and ω a primitive q-th root of unity. Encode the union of progressions as zeros, on powers of ω, of the product over i of (X^(q/n_i) - ω^(a_i*q/n_i)). Expanding the product yields at most 2^r monomials (degrees may collide). Translates P(ω^(-m) X) belong to the span of those monomials, which has dimension at most 2^r.

If there is an uncovered integer, periodicity and translating the covered interval give a first positive uncovered index s after the 2^r covered indices. The 2^r+1 translates with m=0,...,2^r are linearly independent: in a dependence, take the first nonzero coefficient l and evaluate at ω^(s+l); all later translate terms vanish by minimality of s, while the l-th term does not. This contradicts the dimension bound.

Formal burdens: primitive-root/congruence equivalence (including negative integers), lcm divisibility, a sparse-support cardinality bound, closure of the span under scaling X, and the triangular evaluation independence argument. A generic finite-dimensional shift-orbit lemma may reduce later formal work. Do not replace the target by a finite instance or assume the covering theorem itself.
