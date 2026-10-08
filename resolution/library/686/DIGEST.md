# erdosproblems.com #686: problem page and forum thread (fetched 2026-10-08T17:39:31Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Following Vjeko Kovač's expansion argument for even $k$ (his comment on $N=4$, $k=6$), here are the cases $N=4$ and $N=25$ for $k=8$ and $k=12$, with explicit bounds. Write $F_k(a)=(a+1)\cdots(a+k)$ and $N=t^2$.
**1. $k=8$: $4$ and $25$ are not $8$-representable.** Put $X=2m+9$, $Y=2n+9$. Then $2^8F_8(a)=H(X)=(X^2-1)(X^2-9)(X^2-25)(X^2-49)=G(X)^2-(64X)^2$ with $G=X^4-42X^2+105$. So $F_8(m)=t^2F_8(n)$ becomes $\Delta S=4096(X^2-t^2Y^2)$, where $\Delta=G(X)-tG(Y)\in\mathbb{Z}$ and $S=G(X)+tG(Y)$. From $(X^2-49)^4\le H(X)=t^2H(Y)<t^2Y^8$ we get $X^2<t^{1/2}Y^2+49<t^2Y^2$, so the right side is negative, $\Delta\ne0$ and $|\Delta|\ge1$. Hence $tG(Y)<S\le 4096t^2Y^2$, i.e. $Y^4-(4096t+42)Y^2+105<0$, so $Y^2<4096t+42$. That gives $n\le 40$ for $t=2$ and $n\le 67$ for $t=5$, and an exact search over these ranges finds no solution.
**2. $k=12$: $4$ and $25$ are not $12$-representable.** Now $X=2m+13$, $Y=2n+13$, $G=X^6-143X^4+4147X^2-24453$. The remainder is no longer a square: $G^2-H=5184\,r(X^2)$ with $r(w)=429w^2-14274w+94501$. From $X^2<t^{1/3}Y^2+121$ and $r(sv+121)-t^2r(v)=-(\alpha v^2-\beta v-\gamma)$, where $s=t^{1/3}$, $v=Y^2$, $\alpha=429(t^2-t^{2/3})$, $\beta=89544t^{1/3}+14274t^2$, $\gamma=4648336-94501t^2$, the right side $5184[r(X^2)-t^2r(Y^2)]$ is negative as soon as $Y\ge15$, for every $t\ge2$. The same argument then gives $(2n+13)^2<2223936\,t+143$, i.e. $n\le1048$ for $t=2$ and $n\le1660$ for $t=5$. An exact search over these ranges (which also covers $n=0$, i.e. $Y=13$) finds only $F_{12}(4)=4F_{12}(3)$, which violates $m\ge n+12$.
**3. Why the clean form stops at $k=8$.** Let $G_k$ be the polynomial part of $\sqrt{H_k}$ and $R_k=G_k^2-H_k$, so $\deg R_k\le k/2-1$. Then $R_k$ is a perfect square iff $\{\pm1,\pm3,\dots,\pm(k-1)\}$ splits into two halves with equal first $\lceil (k/2-1)/2\rceil$ elementary symmetric functions. Among even $k\le 30$ this happens only for $k=2,4,8$. For other even $k$ one still gets an effective bound for each fixed $k$, after a sign threshold, but not one uniform in $k$.
**4. A small remark.** If $F_k(m)=NF_k(n)$ with $m\ge n+k$, then $[m+1,m+k]$ contains no prime $p>N$: such a $p$ exceeds every $n+i$, so $p\nmid F_k(n)$, hence $p\mid N$. So a representation of $4$ needs a prime gap of length $\ge k+1$ just after $m$.
Verification script (exact integer arithmetic):
from math import prod
F = lambda a, k: prod(a + i for i in range(1, k + 1))
for k, ranges in ((8, ((2, 40), (5, 67))), (12, ((2, 1048), (5, 1660)))):
 for t, nmax in ranges:
 sols, m = [], 0
 for n in range(nmax + 1):
 T = t*t*F(n, k)
 while F(m, k) < T: m += 1
 if F(m, k) == T: sols.append((n, m))
 print(k, t, sols) # only (8: none), (12, t=2: [(3, 4)], inadmissible)
Disclosure: this work was done with AI assistance (Claude, Anthropic). The proofs were re-checked independently, and the computations use exact integer arithmetic. A full write-up is available on request.
 IRAMBONA
 — 04:29 on 05 Oct 2026
 👍
 0
 📝
 0
 🤖
 0
 Since we have reduced the problem to the $N$ being square case, it turns out there is some interesting literature concerning $n=0$, i.e. binomial coefficients that are squares.
Lucas' square-pyramid problem shows that $\binom{50}{3} = 140^2$ is the only nontrivial solution when $k=3$ ($n=0$, square $N$).
Erdos proved that $\binom{m}{k} = n^\ell$ has no solution when $\ell \ge 2$ and $4 \le k \le m-4$. This rules out $k \ge 4$ as well.
Hence, $N = 140^2$ is the *only* square with a representation with $k \ge 3$ and $n=0$.
 Nat Sothanaphan
 — 16:14 on 18 Mar 2026
 👍
 3
 📝
 0
 🤖
 0
 Following up with a small amount of computational data for Problem 686.
For 'k=3', writing 'X = m+2' and 'Y = n+2' gives
'X^3 - X = N(Y^3 - Y).'
Using SageMath's 'EllipticCurve_from_cubic' with the rational point '(1:1:1)', I obtained the following Weierstrass models:
| 'N' | Cremona label | rank | torsion |
|---|---|---|---|
| '4' | '135a1' | '1' | trivial |
| '9' | '19440s1' | '2' | trivial |
| '16' | '9180a1' | '2' | trivial |
| '25' | '140400dd1' | '2' | trivial |
| '49' | '105840cu1' | '2' | trivial |
| '64' | '16380d1' | '2' | 'Z/2Z' |
| '81' | conductor '797040' | '3' | trivial |
All seven curves have positive rank. On the original cubic, a direct search for 'Y in [-50,500]' gives:
- 'N=9': admissible point '(X,Y) = (27,13)', i.e. '(m,n) = (25,11)'.
- 'N=16': admissible point '(X,Y) = (15,6)', i.e. '(m,n) = (13,4)'.
- 'N=4': the nontrivial point '(X,Y) = (3,2)', but it is not admissible.
- 'N in {25,49,64,81}': only the 9 trivial points '{-1,0,1}^2'.
Important caveat: the birational map to the Weierstrass model does not preserve integrality in general. For example, the known 'N=16' solution '(X,Y) = (15,6)' maps to a non-integral Weierstrass point. So integral points on the Weierstrass model do not by themselves prove non-representability on the original cubic.
For 'k=5' and 'N=4', let
'F(t) = (t+1)(t+2)(t+3)(t+4)(t+5).'
Then 'F(x) = 4F(y)' has no rational points at infinity, since this would require a rational root of 'u^5 - 4', which is irreducible over 'Q'. A brute-force search for '|x|, |y| <= 10000' finds only the 25 trivial zero-product points '{-5,-4,-3,-2,-1}^2', and no admissible solutions.
A congruence obstruction also cannot prove non-representability here. For every modulus 'M', the congruence
'F(m) ≡ 4F(n) (mod M)'
has admissible solutions with 'm >= n+5': for 'M >= 5', take 'n = M-1' and 'm = 3M-5', so 'F(n) ≡ F(m) ≡ 0 (mod M)' and 'm-n = 2M-4 >= 6'; for 'M <= 4', the pair '(n,m) = (0,5)' already works.
For 'N=4', this leaves the following status:
| 'k' | status | method |
|---|---|---|
| '2' | not representable | Tao |
| '3' | no admissible solution found for 'Y <= 500' | direct search on 'X^3-X = 4(Y^3-Y)'; '135a1' has rank '1' |
| '4' | not representable | natso26 |
| '5' | no admissible solution found for '|x|,|y| <= 10000' | direct search; no congruence obstruction exists |
| '6' | not representable | Vjeko |
AI disclosure: the computations were run in SageMath/CoCalc. The computational claims above were checked by me.
 MalekZ
 — 15:58 on 15 Mar 2026
 👍
 2
 📝
 0
 🤖
 0
 I did some computations (in Python) for $3 \leq k \leq 100$ and $N=a^2$ (there is some overlap with MalekZ's searches from below, only I searched up to larger values of $N$). The only results were (in the format $a^2 : (k, n, m)$, starting the products at exactly $n$ and $m$):
$3^2 : (3, 12, 26)$
$4^2 : (3, 5, 14)$
$70^2 : (3, 2, 48)$
$140^2 : (3, 1, 48)$
$1189^2 : (3, 14, 1680)$
$1798^2 : (3, 90, 13454)$
$4756^2 : (3, 5, 1680)$
$6214^2 : (3, 168, 57120)$
$2378^2 : (4, 33, 1680)$
Search bounds :
$k = 3$ : $n \leq 1000, a \leq 1000000$ or $n \leq 10000, a \leq 400000$
$k = 4$ : $n \leq 200, a \leq 50000$ (search aborted since it would be more efficient to search among solutions for $k=2$)
$k = 5$ : $n \leq 10000, a \leq 250000$
$k = 6$ : $n \leq 10000, a \leq 250000$
$7 \leq k \leq 100$ : $n \leq 1000, a \leq 1000$
This makes me wonder if there are a finite number of representable squares for $k\geq 3$.
 vilc
 — 15:41 on 15 Mar 2026
 👍
 3
 📝
 0
 🤖
 0
 For the 'k=3' case, writing 'X=m+2' and 'Y=n+2', Problem 686 becomes
'X^3 - X = N(Y^3 - Y),'
with admissibility conditions 'Y >= 2' and 'X >= Y+3'.
I checked the square values 'N in {4,9,16,25,49,64,81}' from two angles:
| N | Elliptic curve data | Original cubic search |
|---|---|---|
| 4 | '135a1', rank '1' | only nontrivial point found was '(X,Y)=(3,2)', not admissible |
| 9 | '19440s1', rank '2' | admissible point '(27,13)' giving 'm=25, n=11' |
| 16 | '9180a1', rank '2' | admissible point '(15,6)' giving 'm=13, n=4' |
| 25 | '140400dd1', rank '2' | no admissible point found in my search |
| 49 | '105840cu1', rank '2' | no admissible point found in my search |
| 64 | '16380d1', rank '2' | no admissible point found in my search |
| 81 | rank '3' on a Weierstrass model | no admissible point found in my search |
The important caveat is that my first proof strategy here was wrong: the birational map from the cubic 'X^3-X=N(Y^3-Y)' to a Weierstrass model does not preserve integrality in general. For example, for 'N=16', the admissible cubic point '(15,6)' maps to a non-integral point on the Weierstrass model. So 'integral_points()' on the Weierstrass model is not enough to prove that the original cubic has no admissible integer points.
What I can say safely is:
1. These 'k=3' curves all have positive rank, so the obstruction is not “no rational points.”
2. A brute-force search on the original cubic found the expected admissible points for 'N=9,16'.
3. The same search found no admissible points for 'N=4,25,49,64,81' up to my search bounds ('Y <= 500', and separately 'n <= 50,000').
So this is only computational evidence, not a proof, for the stuck values at 'k=3'.
If anyone knows a clean way to compute integral points directly on the cubic model 'X^3-X=N(Y^3-Y)' for these specific 'N' (for example via 