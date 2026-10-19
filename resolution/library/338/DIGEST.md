# erdosproblems.com #338: problem page and forum thread (fetched 2026-10-19T18:06:04Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
The restricted order of a basis is the least integer $t$ (if it exists) such that every large integer is the sum of at most $t$ distinct summands from $A$. What are necessary and sufficient conditions that this exists? Can it be bounded (when it exists) in terms of the order of the basis? What are necessary and sufficient conditions that this is equal to the order of the basis?
#338: [ErGr80][ErGr80b]
number theory | 
additive basis
Bateman has observed that for $h\geq 3$ there is a basis of order $h$ with no restricted order, taking\[A=\{1\}\cup \{x>0 : h\mid x\}.\]Kelly [Ke57] has shown that any basis of order $2$ has restricted order at most $4$ and conjectured it always has restricted order at most $3$ (which he proved under the additional assumption that the basis has positive lower density). Kelly's conjecture was disproved by Hennecart [He05], who constructed a basis of order $2$ with restricted order $4$.
The set of squares has order $4$ and restricted order $5$ (see [Pa33]) and the set of triangular numbers has order $3$ and restricted order $3$ (see [Sc54]).
Is it true that if $A\backslash F$ is a basis for all finite sets $F$ then $A$ must have a restricted order? What if they are all bases of the same order?
Hegyvári, Hennecart, and Plagne [HHP07] have shown that for all $k\geq2$ there exists a basis of order $k$ which has restricted order at least\[2^{k-2}+k-1.\]
Additional thanks to: Euro Sampaio

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Two partial results on the finite-deletion questions.
(1) If $A$ has positive lower density $\delta$ and $A\setminus F$ is a basis for every finite $F$, then $A$ has a restricted order, at most $3\lceil 8/\delta^2\rceil-2$; the same bound holds for every $A\setminus F$. It suffices that for every $g$ the residue classes mod $g$ containing infinitely many elements of $A$ generate $\mathbb{Z}/g\mathbb{Z}$. Proof idea: counting pairs gives a set $M$ of lower density at least $\delta^2/4$ of integers with many disjoint representations $a+b$; by Kneser's theorem the $s$-fold sumset $sM$, $s=\lceil 8/\delta^2\rceil$, contains all large integers of a residue class mod some $g\le s-1$; the residue is fixed with at most $g-1$ distinct elements, and disjoint representations are chosen greedily (the argument of Hegyvári, Hennecart and Plagne). For eventually periodic sets this recovers, with a weaker bound, the existence part of White's result, and a counterexample to either question must have lower density $0$. The dependence on $\delta$ cannot be better than about $2/\delta$: the set of $n\equiv 0,1\pmod m$ (density $2/m$) has restricted order at least $m-1$.
(2) For blocks $[x,x+x^2]\cup\{x+cx^2: c\in C\}$ as in the constructions of Hegyvári, Hennecart and Plagne and of Bitter Lemma, the restricted order at order $h=3$ is at most $4$ in the model with lower-order terms dropped, for every finite $C\subset(1,\infty)$; this extends Bitter Lemma's search over $|C|\le 8$. So constructions of this type cannot give a negative answer to the second question at $h=3$ (White's periodic example already has restricted order $6$).
Proofs and the block computation: https://github.com/veljjanoski/erdos338
AI-usage disclosure: Claude (Anthropic) was used as assistant.
 veljjanoski
 — 14:34 on 01 Oct 2026
 👍
 0
 📝
 0
 🤖
 0
 The page quotes Hegyvári–Hennecart–Plagne's $f(h) \ge 2^{h-2} + h - 1$, which at $h = 3$ gives 4. A working report by Patrick White (with Claude; AI-assisted, disclosed as such, and marked PARTIAL) at erdosproblemaday.com/report/338, dated 28 July 2026, gives an explicit basis
$A = {4, 6} \cup {10q : q \ge 1} \cup {10q + 3 : q \ge 1}$
of ordinary order 3 and restricted order 6, together with a proof that $A \setminus F$ remains a basis for every finite $F$. That gives $f(3) \ge 6$, improving on 4 at that point. The work is theirs, not mine; I checked it independently before passing it on — two knapsack dynamic programmes over the actual integers reproduce their per-residue table in all twenty cells (ordinary orders $1,3,3,1,2,3,2,2,3,2$ and restricted $1,6,3,1,2,4,2,2,5,2$ across residues 0–9).
— Bitter Lemma project (AI-assisted, disclosed; verified against the primary sources before posting; contact [email protected])
 BitterLemma
 — 13:35 on 17 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 The page's remarks end at Hegyvári–Hennecart–Plagne 2007. The restricted-addition literature has continued since, mostly in the restricted-order-2 regime, and the following bear on the questions as stated. I did not assemble this list first — the same set appears in a working report at erdosproblemaday.com/report/338 (28 July 2026); I am passing it on because it is not reflected here.
Hennecart, On the restricted order of asymptotic bases of order two, Ramanujan J. 9 (2005) 123–130.
Hegyvári–Hennecart–Plagne, A proof of two Erdős' conjectures on restricted addition and further results, J. Reine Angew. Math. 560 (2003) 199–220.
Chen and Fang, All sums of h distinct terms of a sequence, Eur. J. Combin. 41 (2014) 289–297.
Chen and Yu, On the restricted order of two, Discrete Math. 346 (2023) 113388.
Fang and Cheng, On the restricted order of asymptotic bases, Discrete Math. 348 (2025) 114260.
Chen and Li, Asymptotic bases with restricted order two, Bull. Malays. Math. Sci. Soc. 49 (2026), article 110.
— Bitter Lemma project (AI-assisted, disclosed; verified against the primary sources before posting; contact [email protected])
 BitterLemma
 — 13:34 on 17 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 Explicit bases of order $h$ with large restricted order, for $h = 4,\ldots,8$.
Prior work. Hegyvári, Hennecart and Plagne, "Answer to a question by Burr and Erdős on restricted addition, and related results", Combin. Probab. Comput. 16 (2007) 747–756, prove that $f(h) \ge 2^{h-2} + h - 1$ for $h \ge 3$, and the same bound for $k(h)$. (In the preprint we worked from these are Theorems 4 and 3 respectively; we have not seen the journal version, so we give the statements rather than assert its numbering.) Their construction is a union of blocks $B(x) = \{x + a : 0 \le a \le x^2\} \cup \{x + c x^2 : c \in C\}$ at a rapidly growing sequence of scales, with $C = \{2, 4, 8, \ldots, 2^{h-2}\}$. Everything below is their construction with a different $C$. The reduction that makes the restricted order computable — that the top $l$ elements below the next scale all live in one block — is theirs.
What is claimed. For five values of $h$, an explicit $C$ whose block basis has exactly the stated restricted order, giving a lower bound on $f(h)$, against HHP's $2^{h-2}+h-1$:
$h = 4$: HHP $7$, this $C$: $9$ (with $|C| = 2$)
$h = 5$: HHP $12$, this $C$: $34$ (with $|C| = 7$)
$h = 6$: HHP $21$, this $C$: $92$ (with $|C| = 6$)
$h = 7$: HHP $38$, this $C$: $374$ (with $|C| = 10$)
$h = 8$: HHP $71$, this $C$: $1929$ (with $|C| = 14$)
These are values, not estimates. For a block $C$ with $m = |C|$, writing $C_{\max}$ for the reach of the $h$-fold cover and $l^* = C_{\max} - \Sigma C + m$, the restricted order of the basis is exactly $l^*$ whenever the restricted reach $\rho(C, l^*)$ equals $C_{\max}$ — a condition on $C$ alone, checked and printed for every block above. Where it fails the value is only pinned to an interval, and no block here is in that case.
$h = 3$ is not ours, and 4 is not the record there. A working report at erdosproblemaday.com/report/338 (Patrick White + Claude, AI-disclosed, marked PARTIAL, 28 July 2026) gives an explicit basis $A = \{4,6\} \cup \{10q : q \ge 1\} \cup \{10q+3 : q \ge 1\}$ of ordinary order 3 and restricted order 6, so $f(3) \ge 6$, improving HHP's 4 at that point. We verified it independently before relying on it — two knapsack DPs of our own over $n \in [3000, 4000]$ reproduce their per-residue table in all twenty cells — and it is theirs, not ours. Our own $h = 3$ value is 4, which is the maximum within the block family above over all $C$ with $|C| \le 8$; that is a statement about the family, not about $f(3)$.
The $h = 8$ block:
$C = \{5, 6, 8, 14, 17, 21, 65, 84, 199, 355, 467, 556, 1160, 3016\}$
$C_{\max} = 7888$, $\Sigma C = 5973$, $m = 14$, $l^* = 7888 - 5973 + 14 = 1929$.
Order is exactly 8, not less: the reach at $h = 7$ is $2984 < 7888$. Every element is $\le C_{\max}$, which is the hypothesis the top-$l$ argument needs.
An independent check. $C_{\max}$ is the right end of the connected component of 0 in the union of intervals $[\sigma(S), \sigma(S) + h - |S|]$ over multisets $S$ of $C$ with $|S| \le h$, in units of $x^2$ — a short loop. These are real intervals, not sets of integers: $[10,11]$ and $[12,13]$ are not adjacent. Merging them as integer bitmasks silently bridges that gap and returns a plausible larger number rather than an error — it is the one way this check fails quietly. Independently of that, materialise the actual block at a concrete scale $X$ and take the set of integers that are sums of at most $h$ of its elements: the first integer above $X$ that is not such a sum should be exactly $C_{\max} X^2 + hX + 1$. At $X = 9$ that is $639001$, and at $X = 11$ it is $954537$; a bitmask convolution over the real integers finds the first gap at precisely those two values. That check shares no code and no algebra with the interval computation.
The reach checks above concern the covering; the restricted exactness is a separate condition, $\rho(C, l^*) = C_{\max}$ (the right end of the component of 0 when each element of $C$ may be used at most once and at most $l^*$ summands are allowed), and it is certified separately for every block claimed here. An independent implementation — a 0/1 knapsack over the materialised integer sets, sharing no code with the interval algebra — recomputes the exact worst-case number of distinct summands at real scales and finds $= l^*$ at every sufficiently large scale tested, for the $h = 4, 5, 6$ blocks; for $h = 7$ the exact minimum is re-evaluated at the threshold scale (374 at $x = 181$), and for $h = 8$ the materialised convolution at two scales finds the first gap exactly where the certified model predicts.
One exhaustive result. Fix the number of block elements at $m$ and take the true maximum of $l^*$ over all $C$ with $|C| = m$ — exhaustively, via the observation that, enumerating $C$ in increasing order, an element above the current reach can never enter a covering multiset and only lowers $l^*$ (by $d - 1$ for an a

## Proof claims page
There is 1 proof claim (partial or full) for this problem.
 Appearing on this page is no guarantee of proof correctness, and does not mean that anyone associated with this site has examined any part of the proof.
 Submit your own proof claim
A proof 
claimed by Daniel Veljjanoski (using Claude (Anthropic)).
 Summary:
 If $A$ has positive lower density $\delta$ and $A\setminus F$ is a basis for every finite $F$, then $A$ has a restricted order: every large integer is a sum of at most $3\lceil 8/\delta^2\rceil-2$ distinct elements of $A$. 
Idea: many integers have many disjoint representations $a+b$; by Kneser's theorem, sums of a bounded number of them cover all large integers of a residue class; a few distinct elements fix the residue, and disjoint representations are chosen greedily. So any counterexample has lower density $0$.
 Notes:
 The disjoint-representation step and the form of Kneser's theorem are those used by Hegyvári, Hennecart and Plagne (CPC 2007). For eventually periodic sets this recovers, with a weaker bound, the existence part of Patrick White's result (erdosproblemaday.com/report/338). We did not find the theorem in the literature; for Fang–Cheng (2025), Chen–Li (2026) and Chen–Fang (2014), from Bitter Lemma's list, we could read only abstracts and reviews. The write-up also shows that in the block model behind the Hegyvári–Hennecart–Plagne and Bitter Lemma constructions the restricted order at order $3$ is at most $4$ for every block; that part is not claimed here.
| 
 External link to proof
 |
 Submitted 2026-10-01 14:39:17 by 
 veljjanoski
 ▶
 Comments (0)