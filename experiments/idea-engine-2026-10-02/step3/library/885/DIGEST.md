# erdosproblems.com #885: problem page and forum thread (fetched 2026-10-06T16:08:24Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 TL;DR — Two partial constructions on the square-sum / factor-difference side of Erdős #885.
Neither resolves k = 5; both come with independently rerunnable certificates.
Repo (both PDFs + three stdlib-only Python scripts, exit 0 = pass):
https://github.com/zoahdev/erdos885-square-sum
--------------------------------------------------------------------------
1) A NEW EXPLICIT 5x4 SQUARE-SUM PAIR
--------------------------------------------------------------------------
 A = {202720644, 827712900, 1476864900, 494706564, 80729856900}
 B = {0, 358400700, 1398239500, 17139008700}
All 20 sums are squares; the roots (rows = A in the displayed order, columns = B) are
 14238 23688 40012 131688
 28770 34440 47180 134040
 38430 42840 53620 136440
 22242 29208 43508 132792
 284130 284760 286580 312840
Two things make this more than "another example":
 (a) It is NOT affinely equivalent to the Mausberg packet. For ordered shifts
 b0 < b1 < b2 < b3 the invariant
 lambda(B) = (b0-b2)(b1-b3) / ((b0-b3)(b1-b2))
 equals 541359200/411195147 here, versus 951142/921557 for Mausberg's.
 (b) Exhaustive certificate: no fifth integer shift works for these five columns.
 With a = 202720644 and c = 494706564,
 c - a = 291985920 = 2^9 * 3^2 * 5 * 19 * 23 * 29
 has 192 parity-compatible factor pairs (x-y)(x+y) = c - a, and testing the
 other three columns leaves exactly the four displayed shifts.
--------------------------------------------------------------------------
2) WHERE IT COMES FROM: THE SPECIALIZATION m = -8/19
--------------------------------------------------------------------------
In Choudhry's rational 5x3 family, fix (f,g,u1,u2,v1,v2) = (4,1,2,1,3,1) and keep one
parameter m in Q; the five columns and three shifts are then explicit polynomials in m,
and all 15 sums are rational squares identically in m. Elliptic-curve addition on the
curve through columns (a1,a3,a5) produces a candidate fourth shift b4 as an explicit
rational function of m. The two remaining conditions reduce to:
 F2(m) and F4(m) must be rational squares,
with F2, F4 explicit degree-8 polynomials. Their fiber product
 y^2 = F2(m), z^2 = F4(m)
has GENUS 13 (Riemann-Hurwitz: 2g - 2 = 4(-2) + 16*2), and
 F2 - F4 = 24(m+4)(4m+1)(9m+4)(16m+1) * D^2, D = 97m^2 - 8m - 8.
At m = -8/19:
 F2 = (35668080/130321)^2, F4 = (32892048/130321)^2,
 b4 = -15740769200/1172889.
Search: all reduced m = p/q with 0 < |p| <= 20000 and 1 <= q <= 20000 — 486,361,582
values, sieved modulo eight primes then tested by exact integer square root. There were
NINE simultaneous-square hits; eight of them
 +-1/2, +-1/3, -4/35, 28/85, 20/89, -20/109
force b4 = 0 (degenerate). The ONLY hit producing a new shift is m = -8/19.
(Bounded computation, not a global uniqueness theorem.)
--------------------------------------------------------------------------
3) WHY COMPLETENESS IS HARD HERE
--------------------------------------------------------------------------
Rational extensions of the fixed grid admit a complete two-square parametrization; each
pair of further entries gives a genus-3 hyperelliptic curve w^2 = Q_a(r) Q_b(r). Over all
36 natural models (6 row-extension, 30 column-extension), exact rational-point enumeration
through naive height 10^6 returns 42 and 34 affine points respectively — all of which
reduce to the displayed A and B. Exact 2-descent gives minimum total Jacobian ranks 13 and
11, BOTH ABOVE THE GENUS, so none of the 36 models satisfies the Chabauty inequality.
(Kani-Rosen splits these Jacobians into three elliptic factors.) A completeness proof
would need a covering / Mordell-Weil sieve or quadratic Chabauty input.
--------------------------------------------------------------------------
4) SECOND PAPER: A MOVING LIFT CURVE WITH SPLIT JACOBIAN (13pp)
--------------------------------------------------------------------------
Starting from the four-shift packet (0, 79200, 227205, 1258560) with square abscissae
18, 234, 346, 514, the simultaneous first-lift conditions form a genus-3 hyperelliptic
curve carrying a Klein four-group of involutions. All three elliptic quotients are given,
and the Jacobian is PROVED isogenous over Q to their product (via invariant differentials).
Exact 2-descent on two rational fibers gives factor ranks (5,3,4) and (5,5,6), hence
JACOBIAN RANKS 12 AND 16; Magma independently confirms both. Good-prime sieves and exact
reconstruction exclude nondegenerate second lifts in four finite Mordell-Weil coefficient
boxes (including 32,482,404 representations on a rank-three factor). On the exceptional
nondegenerate fiber m = -13364 the complete lift is a genus-9 (Z/2Z)^3-cover whose
Jacobian splits into nine elliptic curves of TOTAL RANK 29.
--------------------------------------------------------------------------
VERIFICATION
--------------------------------------------------------------------------
https://github.com/zoahdev/erdos885-square-sum holds both PDFs and three self-contained
scripts (stdlib only; exit 0 = all checks pass). verify_specialization.py redoes m = -8/19
in exact rational arithmetic (fractions.Fraction, no floating point): the 15 base sums,
b4, F2 and F4, the identities a2 + b4 = 4*F2/D^2 and a4 + b4 = 4*F4/D^2, lambda(B), and
the 192 factor pairs. It carries a NEGATIVE CONTROL: at m = +8/19 the values F2, F4 are
not rational squares, so the sign of the specialization is forced.
--------------------------------------------------------------------------
RELATED WORK (all partial; none resolves k = 5)
--------------------------------------------------------------------------
- sammausberg (2026-04-19): the four-shift packet, and
 D(79200) n D(227205) n D(1258560) = {36, 468, 692, 1028}.
- Aleksanndr_NFA (2026-09-23): reformulation, the genus-one curve behind three common
 differences, an explicit k = 4 example, and a search over 8410 primitive triples finding
 no five numbers sharing four differences.
- Choudhry (arXiv:2508.07806): rational (m,n) = (3,3), (5,3), (4,4) families.
I also independently recomputed the D-intersection above (certificates 1100x72,
1215x187, 1748x720). Note the follow-up comment listing 1029 is a typo: 1029^2 + 4*79200
= 1375641 is not a square, so 1029 is not in D(79200).
--------------------------------------------------------------------------
WHAT IS NOT CLAIMED
--------------------------------------------------------------------------
No 5x5 grid, and no anchored 6x5 configuration; Erdős #885 at k = 5 remains open.
Yicheng Pan — [email protected]
Feedback, counterexamples and prior-art pointers are very welcome.
 yichengpan
 — 13:49 on 29 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 A reformulation, the curves behind it, and a small explicit $k=4$ example.
1. Reformulation. $d\in D(N)$ iff $4N+d^2=s^2$ is a square (then $N=b(b+d)$ with $b=(s-d)/2$). So $k$ numbers with $k$ common differences give $k+1$ rationals $u_0=0$, $u_i=4N_i$ and $k$ rationals $v_j=d_j^2$ such that every $u_i+v_j$ is a square. Conversely, if $u_0<u_1<\dots<u_k$ and distinct $v_1,\dots,v_k$ are rationals with every $u_i+v_j$ a positive square, then shifting by $u_0$ and scaling by a suitable square gives integers $N_1<\dots<N_k$ with $k$ common nonzero differences. So the case $k$ of this problem is equivalent to finding a $(k+1)\times k$ rational "sumset of squares". That is the problem studied by Choudhry in arXiv:2508.07806, which gives families for $(m,n)=(3,3),(5,3),(4,4)$. Bremner's $k=4$ corresponds to $(5,4)$, and $k=5$ needs $(6,5)$.
2. Curves. For three fixed columns $d_1,d_2,d_3$ the admissible rows are the rational points of the genus one curve $y^2=t^4+(2A-4B)t^2+A^2$ with $A=d_1^2-d_2^2$ and $B=d_1^2-d_3^2$, via $a=(t+A/t)/2$ and $u=a^2-d_1^2$. The point giving $u=0$ is always there, which is why three common differences are easy to get in quantity. A fourth column is a condition of the same shape on any three rows, so candidates for it come from rational points of another quartic of the same type, tested against the remaining rows.
3. Data. I searched all 8410 primitive triples with $d_j\le 40$ this way: row points of naive height at most $2000$, the first $14$ rows on each curve, fourth-column points of height at most $800$ (PARI's hyperellratpoints). This finds many $k=4$ configurations and no five numbers sharing four differences. The smallest $k=4$ example it gave is
$N = 515504,\ 3542528,\ 6010004,\ 19523504$ with common differences $872,\ 4328,\ 5003,\ 11672$:
$515504 = 44\cdot 11716 = 101\cdot 5104 = 116\cdot 4444 = 404\cdot 1276$,
$3542528 = 296\cdot 11968 = 629\cdot 5632 = 704\cdot 5032 = 1496\cdot 2368$,
$6010004 = 494\cdot 12166 = 1001\cdot 6004 = 1106\cdot 5434 = 2054\cdot 2926$,
$19523504 = 1484\cdot 13156 = 2576\cdot 7579 = 2756\cdot 7084 = 4004\cdot 4876$.
Direct divisor enumeration confirms that these four numbers share exactly these four differences. A Lean proof of the $k=4$ case from an explicit witness is in formal-conjectures PR #6509