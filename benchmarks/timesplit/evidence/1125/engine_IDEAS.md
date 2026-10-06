# Research engine: problem 77933, run 20261006-021530-371610-discover-erdos77933

Spend $13.0439; 16 claim(s); 1 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] r1s3/C1 PROVED ANALOGUE
**Statement.** Let G_1 ⊂ G_2 ⊂ … be subgroups of R with G_n ⊂ (1/w_n)Z, positive integers w_1<w_2<… (strictly increasing is enough; ≤ also works), and X=∪G_n. Let n(x)=min{n: x∈G_n} and λ(x)=w_{n(x)}·x ∈ Z. Define f(x)=2^{λ(x)} for x∈X, x>0, and f(x)=x for x∈X, x≤0. Then 2f(a) ≤ f(a+h)+f(a+2h) for all a∈X and h∈X with h>0. In particular, with G_n=(1/n!)Z, w_n=n!, X=Q: f(1/3)=2^2 > f(1/2)=2^1, so f is a non-monotone solution on Q. With G_n=2^{-n}Z, X=Z[1/2]: λ(x) is the odd numerator, and f(3/4)=2^3 > f(1)=2.
**Beyond.** B6 and K13 treat "the Q- or dyadic-version has a non-monotone solution" as open. This settles it: yes. So B6 holds unconditionally: every proof of the R-statement must use uncountability, for example via Baire as in K6/K7.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "A valid, elementary construction of a non-monotone solution on Q and on Z[1/2] (via the potential 2^{w_{n(x)} x}), which closes the countable route of K13 and makes the uncountability barrier B6 unconditional; I know no published source for it, though competition solutions to this problem may contain a similar Q-example.", "panel": [{"verdict": "new", "cite": null, "significance": 2, "why": "A valid, elementary construction of a non-monotone solution on Q and on Z[1/2] (via the potential 2^{w_{n(x)} x}), which closes the countable route of K13 and makes the uncountability barrier B6 unconditional; I know no published source for it, though competition solutions to this problem may contain a similar Q-example."}, {"verdict": "new", `
**Proof or evidence.**

Write lev(x)=n(x).
(P1) For x>0 we have λ(x)≥1, since λ(x) is an integer and >0.
(P2) Key lemma. Let 0<a<s in X with λ(s) ≤ λ(a). Then lev(s)<lev(a). Let m=(a+s)/2 and c=2s−a. Then λ(m)>λ(a) and λ(c)>λ(a).
 Proof. If lev(s) ≥ lev(a), then w_{lev s} ≥ w_{lev a}, so λ(s)=s·w_{lev s} ≥ s·w_{lev a} > a·w_{lev a} = λ(a), a contradiction. So k:=lev(a) > lev(s), and s∈G_{k-1}.
 For c: c=2s−a∈G_k. If c∈G_{k-1}, then a=2s−c∈G_{k-1}, a contradiction. So lev(c)=k, and λ(c)=w_k·c = w_k(a+2(s−a)) > w_k·a = λ(a).
 For m: if lev(m)<k, then m∈G_{k-1}, so a=2m−s∈G_{k-1}, a contradiction. So lev(m) ≥ k and w_{lev m} ≥ w_k. Since m>a>0, λ(m) ≥ w_k·m > w_k·a = λ(a). (m may lie outside G_k when 2∤…; only lev(m)≥k is used, and m∈X because X is a group containing a+s... see note.)
 Note: m∈X is needed only when m is a point of the triple. In the triple (a,b,c), b∈X is given.
(P3) Triples. Let a∈X, h∈X, h>0, b=a+h, c=a+2h.
 Case a≤0: f(a)=a≤0. Each of f(b), f(c) is either the value itself, when it is ≤0 and >a, or ≥2>0 by (P1). In both cases it is ≥ f(a), so f(b)+f(c) ≥ 2f(a).
 Case a>0, so b,c>0 and λ is an integer at all three points.
  (i) λ(b) ≥ λ(a) and λ(c) ≥ λ(a): then 2^{λb}+2^{λc} ≥ 2·2^{λa}.
  (ii) λ(b)<λ(a): apply (P2) with s=b. Then 2s−a=c, so λ(c) ≥ λ(a)+1 and 2^{λc} ≥ 2·2^{λa}.
  (iii) λ(c)<λ(a): apply (P2) with s=c. The midpoint is b, so λ(b) ≥ λ(a)+1, and the same conclusion holds.
 This proves the claim. For Q: G_n=(1/n!)Z, and Q=∪G_n. f(1/3): n=3, λ=6/3=2. f(1/2): n=2, λ=2/2=1.
CHECK: q_check.py tested, in exact big-integer arithmetic, all 6105 pairs (a<b) from {p/q: q≤8, −2≤p/q≤3} with c=2b−a, plus 20000 random triples. 0 failures.

## [valid-restatement] deep/C1 PROVED OTHER
**Statement.** If f: R→R satisfies 2f(x) ≤ f(x+h)+f(x+2h) for all x∈R and all h>0, then f is nondecreasing.
**Beyond.** Resolves CORE outright. K5 and K6 needed regularity, and K7 and K12 only gave constraints. Barriers B1–B6 are respected: the argument uses infinitely many finite certificates (B1), density of steps (B2), and uncountability of R (B6). It never intersects translates of category or measure sets (B3, B4).
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "The claim (every solution is nondecreasing) is exactly an affirmative answer to the problem and to its CORE, so it is equivalent to solving the problem; it needs maximal scrutiny, especially on where it uses the uncountability of R given that the Q/dyadic analogue is open (B6) and how it avoids the 2-adic sparse-offset obstruction (B3).", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "The claim (every solution is nondecreasing) is exactly an affirmative answer to the problem and to its CORE, so it is equivalent to solving the problem; it needs maximal scrutiny, especially on where it uses the uncountability of R given that the Q/dyadic analogue is open (B6) and how it avoids the 2-adic sparse`
**Proof or evidence.**

Write (H) for the hypothesis. For ρ∈R let L_ρ={u: f(u)<ρ}.

Step 1 (reflection closure; K12). If p<q′ are in L_ρ, then 2p−q′∈L_ρ.
Apply (H) with base x=2p−q′ and h=q′−p>0. Then x+h=p and x+2h=q′, so 2f(x) ≤ f(p)+f(q′) < 2ρ.
Corollary 1a. If q and q+d (d>0) are in L_ρ, then q−jd∈L_ρ for all j ≥ −1.
By induction, apply Step 1 to p=q−jd and q′=q−(j−1)d. Both lie in L_ρ, and 2p−q′=q−(j+1)d.

Step 2 (halving; K2). Let x<y with f(x)>f(y), d=y−x and δ=f(x)−f(y)>0. Put x_k=y−d2^{−k}. Then f(x_k) ≥ f(y)+2^kδ.
Apply (H) with base x_k and h=(y−x_k)/2>0. The points are x_k+h=x_{k+1} and x_k+2h=y. This gives f(x_{k+1})−f(y) ≥ 2(f(x_k)−f(y)). Induct on k.

Step 3 (DST, new). Suppose f(a)>ρ, d>0, and q, q+d∈L_ρ with q>a. Then f(a+2d)−ρ > 4(f(a)−ρ).
Let j=⌈(q−a)/d⌉−1 ≥ 0 and t=q−jd. Then a<t≤a+d.
- By Corollary 1a, t, t′:=t+d and t−d all lie in L_ρ.
- If t=a+d, then a=t−d∈L_ρ, which contradicts f(a)>ρ. So a<t<a+d.
- Apply (H) with base a and h=t−a>0. The points are t and b:=2t−a. Then 2f(a) ≤ f(t)+f(b) < ρ+f(b), so f(b) > 2f(a)−ρ.
- Apply (H) with base b and h′=t′−b=a+d−t>0. Then b+h′=t′ and b+2h′=2t′−b=a+2d. So 2f(b) ≤ f(t′)+f(a+2d) < ρ+f(a+2d).
- Hence f(a+2d) > 2f(b)−ρ > 4f(a)−3ρ.
The identities were also checked symbolically (check_dst.py, part A).

Step 4 (Chain Lemma, new). Suppose f(a)>ρ, and q_0<q_1<…<q_K all lie in L_ρ with q_K−q_0 < q_0−a. Then f(a+2(q_K−q_0)) − ρ > 4^K(f(a)−ρ) for K ≥ 1.
Put a_i=a+2(q_i−q_0). For i<K we have a_i−q_i = (a−q_0)+(q_i−q_0) ≤ (a−q_0)+(q_K−q_0) < 0, so a_i<q_i.
By induction, f(a_i)−ρ > 4^i(f(a)−ρ) for i ≥ 1 (and equality at i=0), so f(a_i)>ρ.
Step 3 applied to (a_i, q_i, d=q_{i+1}−q_i) gives f(a_{i+1})−ρ > 4(f(a_i)−ρ), since a_i+2d=a_{i+1}.
The endpoint a+2(q_K−q_0) depends only on q_0 and q_K, not on K or on the intermediate points.

Step 5 (accumulation implies density). Suppose A⊂L_ρ is infinite and bounded, with an accumulation point z. Then L_ρ meets every interval (u,v) with u<v≤z.
Take a strictly monotone sequence p_n∈A with p_n→z.
- If (p_n) increases: for u<v<z, pick n with p_n>v, then m>n with p_m−p_n<v−u. By Cor. 1a (q=p_n, d=p_m−p_n), the progression p_n−j(p_m−p_n), j ≥ 0, lies in L_ρ. It starts above v, goes to −∞, and has step <v−u, so it hits (u,v). Intervals with v=z contain (u,v′) with v′<z.
- If (p_n) decreases: pick n with p_n−p_{n+1}<v−u. The progression p_{n+1}−j(p_n−p_{n+1}) lies in L_ρ, starts at p_{n+1}>z ≥ v, and hits (u,v).

Step 6 (conclusion). Suppose x<y and f(x)>f(y).
- Since [y,y+1]=∪_{N∈N} (L_N∩[y,y+1]) is uncountable, some A=L_N∩[y,y+1] is infinite. Fix such an N and put ρ=N.
- A has an accumulation point z∈[y,y+1].
- By Step 2 choose k with f(y)+2^kδ>ρ, and put a=x_k<y≤z, so f(a)>ρ.
- By Step 5, L_ρ is dense in (a,z). Pick q_0∈L_ρ∩(a,z) and q*∈L_ρ∩(q_0, min(z, 2q_0−a)). Then q*−q_0<q_0−a.
- By density, (q_0,q*) contains infinitely many points of L_ρ. For every K choose K−1 of them, q_1<…<q_{K−1}, and let q_K=q*.
- Step 4 gives f(a+2(q*−q_0)) > ρ+4^K(f(a)−ρ) for every K. The right side tends to ∞ while the left side is a fixed real number. Contradiction.
Hence f is nondecreasing. ∎

Remarks for the referee:
- Every use of (H) is listed with h>0: Step 1 (h=q′−p), Step 2 (h=(y−x_k)/2), Step 3 (h=t−a and h′=a+d−t).
- The degenerate case t=a+d is excluded by f(a)>ρ, and this matters: in the random exact tests, 38 of 3000 arbitrary configurations hit a_i∈{progression}. In a real solution that would force f(a_i)<ρ, which contradicts the invariant.
- Alternative to Step 5: an uncountable A⊂R has a point q_0∈A that accumulates from the right, since the exceptions inject into Q via x↦ a rational in the empty gap to the right of x. With q_0∈A, take q*∈A∩(q_0,2q_0−a). This version needs "uncountable" (true for some L_N∩[y,y+1]), while Step 5 needs only "infinite".
- Choice used: only countable choice (a countable union of finite sets is countable; choosing sequences).

## [valid-routine] r1s1/C1 PROVED STRUCTURE
**Statement.** Let f:R->R satisfy 2f(x) <= f(x+h)+f(x+2h) for all x, h>0. For every z in R, every rho>0 and every nonempty open interval I ⊂ (-inf,z), the set {x in I : f(x) < f(z)+rho} is nonmeager.
**Beyond.** K7 only gives liminf_{e->0+} f(z-e) < inf (a sequence). K12 gives density of SOME S_N. C1 gives nonmeagerness in every interval, at levels arbitrarily close to f(z), at every z. For monotone f the set is all of (-inf,z); C1 is a category shadow of monotonicity holding for all solutions.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "Assuming failure gives f ≥ f(z)+ρ on a comeager set; iterating midpoints toward z gives f ≥ f(z)+2^kρ on comeager sets accumulating at z, and the K7-style reflection with Banach category localization then forces f(p)=∞. It is a modest category strengthening of K7 that does not get past the sparse-offset or regularity barriers.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published source is known for this exact statement; the closest literature (Kemperman ~1969, Laczkovich on Kemperman's inequality, cited from memory) covers measurable and Baire-property solutions. It is not equivalent to the problem, because everywhere-nonmeager sets can avoid the required pattern x+h, x+2h, and it likely follows`
**Proof or evidence.**

Step 0 (Banach). If X ⊂ (u,v) is nonmeager in (u,v), there is a subinterval I' on which X is "everywhere nonmeager" (nonmeager in every open subinterval). [Let O = union of open subintervals where X is meager; X∩O is meager (Banach category thm). If O were dense in (u,v), X ⊂ (X∩O) ∪ ((u,v)\O) with the latter closed nowhere dense: X meager, contradiction. So some I' misses O.]
Step 1 (Lemma B+). Fix z. Claim: there are M and eta'>0 such that L_M = {e in (0,eta') : f(z-e) <= M} is nonmeager in every open subinterval of (0,eta').
 Since (z,z+1) = U_n S_n∩(z,z+1), S_n={f<=n}, by Baire some S_n is nonmeager there; by Step 0 there is I'=(i1,i2) ⊂ (z,z+1) with S_n∩I' everywhere nonmeager in I'. Choose p with (p+z)/2 in I' and put eta' = p+z-2 i1 > 0. The set E = p+z-2(S_n∩I') is (affine image) everywhere nonmeager in p+z-2I' ⊇ (0,eta').
 Suppose the claim fails for this eta': then for every M there is (al,be) ⊂ (0,eta') with L_M∩(al,be) meager, i.e. A_M = {e: f(z-e) > M} comeager in (al,be). E∩(al,be) is nonmeager, so it meets A_M: there is e in (al,be) with f(z-e) > M and t := (p+z-e)/2 in S_n∩I'. Since z-e < z < t, the hypothesis at x=z-e, h=t-x (reflection K3) gives f(p) = f(2t-(z-e)) >= 2f(z-e) - f(t) >= 2M - n. M arbitrary => f(p)=inf, impossible.
Step 2 (dyadic transport). Let g(u)=f(z-u)-f(z). Hypothesis at x=z-u, h=u/2: 2f(z-u) <= f(z-u/2)+f(z), i.e. g(u/2) >= 2g(u) (any sign). Hence g(2^k e) <= 2^{-k} g(e). WLOG M >= f(z). For e in L_M: f(z-2^k e) <= f(z) + (M-f(z))2^{-k}.
Step 3. 2^k L_M is nonmeager in every open subinterval of (0,2^k eta'). So {x in (z-2^k eta', z) : f(x) <= f(z)+(M-f(z))2^{-k}} is nonmeager in every open subinterval of (z-2^k eta', z). Given rho and a bounded I ⊂ (-inf,z), pick k with (M-f(z))2^{-k} < rho and z-2^k eta' < inf I. (Unbounded I contains a bounded one.) QED.

## [valid-routine] r1s1/C2 PROVED STRUCTURE
**Statement.** For every solution f, every c, and every open interval (a,b): if {x in (a,b): f(x) <= c} is comeager in (a,b), then f(x) <= c for ALL x < b. Consequently f is nondecreasing on (-inf,b).
**Beyond.** K5 needs f bounded above on an interval (every point). C2 needs boundedness only on a comeager set and concludes the bound everywhere to the left. Also re-derives K6 (BP case) in one line.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "Choosing h so that x+h and x+2h both land in the comeager set {f<=c}, then doubling the interval leftward, gives the bound everywhere to the left of b; monotonicity is then just K5. It is a slight Baire-category refinement of K5/K6 and leaves the core case, where every level set is meager on every interval, untouched.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "Choosing h so that x+h and x+2h both land in the comeager set {f<=c}, then doubling the interval leftward, gives the bound everywhere to the left of b; monotonicity is then just K5. It is a slight Baire-category refinement of K5/K6 and leaves the core case, where every level set is meager on every interval, untouched."}, {"verdict": "rout`
**Proof or evidence.**

Let S={f<=c}. (i) Closure: if p<q are in S then x=2p-q is in S (hypothesis at x, h=q-p: 2f(x) <= f(p)+f(q) <= 2c).
(ii) Step: if S is comeager in (al,be) then (2al-be, al) ⊂ S. For x in (2al-be, al), let P=(al,(be+x)/2), nonempty since x>2al-be. The map p -> 2p-x sends P homeomorphically onto (2al-x, be) ⊂ (al,be) (as x<al). So {p in P: p in S} and {p in P : 2p-x in S} are both comeager in P, hence share a point p; q=2p-x > p (as p>x). By (i), x in S.
(iii) Every x in (2a-b, b) is in S: choose al' with max(a,x) < al' < (x+b)/2 (possible since x>2a-b and x<b). S is comeager in (al',b) and x in (2al'-b, al'); apply (ii).
(iv) So S ⊇ (2a-b,b), i.e. S is (fully, hence comeager) on (a_1,b) with a_1=2a-b, length 2(b-a). Iterating, a_k = b-2^k(b-a) -> -inf, so S ⊇ (-inf,b).
(v) f <= c on (-inf,b); if x<y<b were a bad pair, K4 makes f unbounded above on (y,b), contradiction. QED.

## [valid-routine] r1s1/C3 PROVED QUANT
**Statement.** For every solution f, s in R, e>0, n>=1: if delta=f(s-e)-f(s)>0 then f(s-e/n)-f(s) >= c_n delta, c_n = 3/(2(1-(-1/2)^n)) >= 1 (c_1=1,c_2=2,c_3=4/3, c_n->3/2). Hence B_s={e>0: f(s-e)>f(s)} is closed under e->e/n, and with K2: f(s-e/(n2^k)) >= f(s)+2^k c_n delta. For the normalized pair: f(1-1/(n2^k)) >= 2^k c_n and f(1+1/(n2^k)) >= 2^{k+1} c_n.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "The bound comes from finitely many applications of the hypothesis along an n-step arithmetic progression (a linear recursion with roots 1 and -1/2), directly generalizing the halving lemma K2. The resulting offsets e/(n2^k) are still countable, so the claim stays inside barriers B1/B3 and does not touch the core continuum blow-up problem.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "A short finite-chaining lemma extending the dyadic halving K2 to all subdivisions e/n with explicit bounded constants; I know no published source, but it only enlarges the countable set of blow-up offsets to rational multiples, so it weakens the 2-adic form of B3 without reaching the continuum blow-up the core requires."}`
**Proof or evidence.**

g_k=f(s-k e/n). Hypothesis at x=s-(k+2)e/n, h=e/n: g_{k+2} <= (g_{k+1}+g_k)/2. Positive coefficients => by induction g_k <= G_k, G the equality solution with G_0=g_0,G_1=g_1: G_k = g_0+(g_1-g_0)(2/3)(1-(-1/2)^k). With k=n: f(s)+delta = g_n <= f(s)+(f(s-e/n)-f(s))/c_n. Right side: reflection f(s+u) >= 2f(s-u)-f(s). (Checked numerically, see Data.)

## [valid-routine] r1s1/C4 PROVED NEGATIVE
**Statement.** The sublevel information produced by A1+C1 cannot by itself close the argument: there is V ⊂ (0,inf), nonmeager in every subinterval of (0,inf), closed under v->nv (n in N), v->2v, and (v1,v2)->2v1-v2 for v1>v2>0, with 1 not in V. Namely V = H∩(0,inf), H a Q-hyperplane of R (Hamel) with 1 not in H.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard Hamel-hyperplane facts (countable-index Q-subspace is nonmeager everywhere; Banach category theorem), e.g. Oxtoby 'Measure and Category'; Kuczma 'An Introduction to the Theory of Functional Equations and Inequalities'", "why": "A Q-hyperplane avoiding 1 is trivially closed under the listed Q-affine operations and is nonmeager in every interval by countable index plus the Banach category theorem. The claim just restates the memo's Hamel barrier B5 for sublevel sets and gives no new information about f.", "panel": [{"verdict": "routine", "cite": "Standard Hamel-hyperplane facts (countable-index Q-subspace is nonmeager everywhere; Banach category theorem), e.g. Oxtoby 'Measure and Category'; Kuczma 'An Introduction to the Theory of F`
**Proof or evidence.**

(none)

## [valid-routine] r1s1/C2r PROVED STRUCTURE
**Statement.** Let $f:\mathbb{R}\to\mathbb{R}$ satisfy $2f(t)\le f(t+h)+f(t+2h)$ for all $t\in\mathbb{R}$ and all $h>0$. Suppose $x<y$ and $f(x)>f(y)$. Then for every $c\in\mathbb{R}$ and every nonempty open interval $(a,b)$ with $b>y$, the set
$$E=\{t\in(a,b): f(t)>c\}$$
is not meager. Since $(a,b)$ is open in $\mathbb{R}$, meager in $\mathbb{R}$ and meager in $(a,b)$ mean the same thing here. Because every subinterval $(a',b')$ with $b'>y$ is itself such an interval, $E\cap(a',b')$ is nonmeager for all of them.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "If {f>c} were meager in an interval J right of y, then {f≤c} would be comeager there; K4 applied with a bad pair ending inside J gives a uniform blow-up threshold, and its translates G+d'2^{-k} would have to miss a comeager set on an overlap, which Baire forbids — the same argument as K6. It sharpens K12's density statement to non-meagerness but does not address the dyadic-to-continuum core (B3).", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "If {f>c} were meager in an interval J right of y, then {f≤c} would be comeager there; K4 applied with a bad pair ending inside J gives a uniform blow-up threshold, and its translates G+d'2^{-k} would have to miss a comeager set on an overlap, which Baire forbi`
**Proof or evidence.**

Write $d=f(x)-f(y)>0$.

**Lemma 1 (unboundedness to the left of $y$).**
- Define $x_0=x$ and $x_{n+1}=(x_n+y)/2$.
- Then $x\le x_n<y$ for every $n$.
- **Claim:** $f(x_n)-f(y)\ge 2^n d$ for every $n$.
- The case $n=0$ is the definition of $d$.
- For the step, apply the hypothesis at $t=x_n$ with $h=(y-x_n)/2>0$. This gives $2f(x_n)\le f(x_{n+1})+f(y)$.
- Rearranging, $f(x_{n+1})-f(y)\ge 2\,(f(x_n)-f(y))\ge 2^{n+1}d$.
- Hence $\sup_{t<y} f(t)=+\infty$.

**Lemma 2 (one Baire step).**
- Let $p<q$ and $c\in\mathbb{R}$, and suppose $N=\{t\in(p,q): f(t)>c\}$ is meager.
- **Claim:** $f(t)\le c$ for every $t\in(2p-q,\,q)$.
- Fix such a $t$ and set $I_t=\big(\max(0,p-t),\,(q-t)/2\big)$.
- $I_t$ is a nonempty open interval:
  - $0<(q-t)/2$ because $t<q$;
  - $p-t<(q-t)/2$ because $t>2p-q$.
- For $h\in I_t$, both $t+h$ and $t+2h$ lie in $(p,q)$:
  - $p<t+h<t+2h$, since $h>p-t$ and $h>0$;
  - $t+2h<q$, since $h<(q-t)/2$.
- Let $A=\{h\in I_t: t+h\in N\}=I_t\cap(N-t)$ and $B=\{h\in I_t: t+2h\in N\}=I_t\cap\tfrac12(N-t)$.
- Both $A$ and $B$ are meager, because the maps $s\mapsto s-t$ and $s\mapsto (s-t)/2$ are homeomorphisms of $\mathbb{R}$, which preserve meagerness, and subsets of meager sets are meager.
- By the Baire category theorem, the nonempty open set $I_t$ is not meager. So there is some $h\in I_t\setminus(A\cup B)$.
- For this $h$, the points $t+h$ and $t+2h$ lie in $(p,q)\setminus N$. So $f(t+h)\le c$ and $f(t+2h)\le c$.
- Therefore $2f(t)\le f(t+h)+f(t+2h)\le 2c$, that is, $f(t)\le c$.

**Main argument.**
- Suppose, for contradiction, that $E=\{t\in(a,b):f(t)>c\}$ is meager, where $a<b$ and $b>y$.
- Put $p_0=a$ and $p_{k+1}=2p_k-b$. Then $b-p_{k+1}=2(b-p_k)$, so $b-p_k=2^k(b-a)\to\infty$.
- **Claim:** $f\le c$ on $(p_k,b)$ for every $k\ge1$.
  - For $k=1$: by hypothesis $\{t\in(p_0,b):f>c\}=E$ is meager, so Lemma 2 gives $f\le c$ on $(p_1,b)$.
  - Step: if $f\le c$ on $(p_k,b)$, then $\{t\in(p_k,b):f(t)>c\}=\varnothing$ is meager. Lemma 2 then gives $f\le c$ on $(2p_k-b,b)=(p_{k+1},b)$.
- Since $p_k\to-\infty$, it follows that $f\le c$ on $(-\infty,b)$.
- But all the points $x_n$ from Lemma 1 lie in $[x,y)\subset(-\infty,b)$, and $f(x_n)\ge f(y)+2^n d$. Choosing $n$ with $f(y)+2^n d>c$ gives a contradiction.
- Hence $E$ is nonmeager.
- The parenthetical version for subintervals is the same statement applied to $(a',b')$ with $b'>y$. ∎

Remark: the argument only uses $x_n\in(-\infty,b)$, so it works verbatim for $b\ge y$.

## [valid-routine] r1s2/C2 PROVED STRUCTURE
**Statement.** Let P ⊂ R be finite with 0, 1 ∈ P. Let ψ: (1,∞) → [1,∞) be nondecreasing, and let M ≥ 2·max{1/(1−x) : x ∈ P, x < 1}. Define f(x) = 1/(1−x) for x < 1, f(1) = 0, and f(x) = M·ψ(x) for x > 1. Then:
(i) f is a solution on P, and f(0) − f(1) = 1. (This is a constructive proof of K8.)
(ii) If F ⊆ (−∞,1] is finite and 0, 1 ∈ F, then D(P,F) ≥ 1/L_F for every finite P ⊇ F, where L_F = max_{q∈F, q<1} 1/(1−q) ≥ 1. Hence dist_1(e, K∩R^F) ≥ 1/L_F > 0.
(iii) Residual law. Let g = e + r ∈ K. Then r((1,∞)) ≥ 0, and r([t,∞)) ≥ 0 for every t > 1. If moreover r((1,∞)) = 0 (for example, if r vanishes on (1,∞)), then Σ_{x<1} r(x)/(1−x) ≥ 1. The depth-k halving tree g_k = e + 2^{−k}(δ_{1−2^{−k}} − δ_1) attains equality.
**Beyond.** K8 says e ∉ K, and its proof is a non-constructive Farkas argument. C2 gives an explicit finite solution valid for all P at once, with values on {x<1} independent of P. That yields quantitative lower bounds that K8 cannot give: closure, not just membership, fails for every F ⊆ (−∞,1]. It also yields a sharp mass law for residuals.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "The explicit witness f=1/(1−x) left of 1 (saturating the halving step), plus a large nondecreasing tail right of 1, is a direct check that makes the Farkas argument K8 constructive; the distance and residual-mass bounds are standard LP-duality pairings against it. It stays entirely within the finite-certificate setting that barrier B1 already rules out as a route to the problem, so it makes no progress on the core.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "The explicit witness f=1/(1−x) left of 1 (saturating the halving step), plus a large nondecreasing tail right of 1, is a direct check that makes the Farkas argument K8 constructive; the distance and residual-mass bounds are standard LP-duali`
**Proof or evidence.**

(i) Take an AP a < b = a+h < c = a+2h in P. Note f ≥ 0 everywhere, since 1/(1−x) > 0 for x < 1.
- Case c < 1. f is increasing on (−∞,1), so f(a) < f(b) and f(a) < f(c).
- Case c = 1. Then b = (a+1)/2, so 1−b = (1−a)/2 and f(b) = 2/(1−a) = 2f(a). With f(c) = 0 this is an equality.
- Case c > 1 and a < 1. Then f(c) = Mψ(c) ≥ M ≥ 2f(a), and f(b) ≥ 0.
- Case a = 1. Then 2f(a) = 0 ≤ RHS, since f ≥ 0.
- Case a > 1. f = Mψ is nondecreasing on (1,∞).
f(0) = 1 and f(1) = 0. Exact check: 300 random P (including the points 1 ± 2^{−k}), with a nonconstant ψ, found 0 violations (check.py).
(ii) On F, 0 ≤ f ≤ L_F, and f(0) − f(1) = 1. So f/L_F is admissible in the LP of C1(c), and D(P,F) ≥ 1/L_F. Since K∩R^F = ∪_P (K_P∩R^F), the distance bound follows from C1(c).
(iii) Let P be the union of the generator supports of g, so g ∈ K_P. For f as in (i), ⟨g,f⟩ ≥ 0, since this is a positive combination of the hypothesis on P. So ⟨r,f⟩ ≥ −⟨e,f⟩ = f(0) − f(1) = 1, i.e.
  Σ_{x<1} r(x)/(1−x) + M·Σ_{x>1} r(x)ψ(x) ≥ 1 for every admissible M and ψ.
- Letting M → ∞ gives Σ_{x>1} r(x)ψ(x) ≥ 0 for every nondecreasing ψ ≥ 1.
  - ψ ≡ 1 gives r((1,∞)) ≥ 0.
  - ψ = 1 + λ·1_{[t,∞)} with λ → ∞ gives r([t,∞)) ≥ 0.
- If r((1,∞)) = 0, take ψ ≡ 1. The M-term vanishes, leaving Σ_{x<1} r(x)/(1−x) ≥ 1.
For g_k the residual is r = 2^{−k}(δ_{1−2^{−k}} − δ_1), and 2^{−k}·(1/2^{−k}) = 1.
That g_k ∈ K: g_k = 2^{−k} Σ_{j<k} 2^{k−1−j} γ(a_j, (1−a_j)/2) with a_j = 1−2^{−j}. This telescopes: interior coefficients cancel, giving coefficient 1·2^{−k} at a_k, −1 at 0, and 1−2^{−k} at 1.
MEANING FOR A2: the FIRST STEP plan was to move the 2^{−k} mass at 1−2^{−k} onto points of a dense sublevel set. A residual kept in (−∞,1] cannot be shrunk in the weight 1/(1−x): mass ε must sit within distance O(ε) of 1. Any residual that is weak-*-small against every test function must therefore put mass on (1,∞), and there (iii) shows its tails r([t,∞)) are ≥ 0. This is exactly where K4 says a counterexample is unbounded on every interval.

## [valid-routine] r1s2/C1 PROVED REDUCTION
**Statement.** (a) CORE (no solution has f(0) > f(1)) ⟺ e ∈ cl_{σ(R^(R),R^R)} K.
(b) Every σ(R^(X),R^X)-convergent sequence (g_n) has all supports inside one finite set F, and it converges coordinatewise.
(c) For finite F ⊆ P with 0, 1 ∈ F: dist_1(e, K_P∩R^F) = D(P,F) := max{f(0)−f(1) : f a solution on P, |f| ≤ 1 on F}.
(d) Hence e is the limit of a sequence in K ⟺ ∃ finite F with inf_P D(P,F) = 0. In that case every solution f on R satisfies f(0) − f(1) ≤ max_F|f| · inf_P D(P,F) = 0. A sequential certificate would therefore prove CORE, with this quantitative form.
**Beyond.** makes the A2 angle computable. Sequential Ky Fan certificates are exactly the LP quantity inf_P D(P,F) on finite point sets.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "Parts (a)-(d) are standard bipolar/Hahn–Banach duality, the textbook fact that weakly convergent sequences in R^(X) are finitely supported, and finite LP duality; (a) is just the dual restatement of CORE. The sequential criterion is only sufficient, and since its finite point sets live in countable subgroups it is exposed to barriers B1/B6, so it does not advance the core.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "Parts (a)-(d) are standard bipolar/Hahn–Banach duality, the textbook fact that weakly convergent sequences in R^(X) are finitely supported, and finite LP duality; (a) is just the dual restatement of CORE. The sequential criterion is only sufficient, and since its finite point sets li`
**Proof or evidence.**

(a) The dual of (R^(R), σ) is R^R. A solution f with f(0) > f(1) is a functional that is ≥ 0 on K and < 0 at e. Hahn–Banach separation of the point e from the closed convex cone cl K gives such an f when e ∉ cl K. Conversely, if such an f exists, the weak-* open set {φ : ⟨φ,f⟩ < 0} contains e and misses K.
(b) Gliding hump. Suppose the supports are not inside one finite set. Then for every finite U and every N, some g_n with n ≥ N has a support point outside U. Choose n_1 < n_2 < … and x_j ∈ supp g_{n_j} with x_j ∉ U_j := ∪_{i<j} supp g_{n_i}. Define f(x_j) recursively so that |⟨g_{n_j}, f⟩| ≥ j; this is possible because g_{n_j}(x_j) ≠ 0 and only x_1..x_j have been assigned. Put f = 0 elsewhere. Later points x_{j'} (j' > j) lie outside supp g_{n_j}, so ⟨g_{n_j}, f⟩ is unaffected by them. Then ⟨g_n, f⟩ is unbounded, contradicting convergence. With supports inside a fixed finite F, σ-convergence is coordinatewise convergence in R^F.
(c) C := K_P∩R^F is a projection of a polyhedral cone, hence closed and finitely generated. By minimax (Sion, with φ ranging over the compact ‖φ‖_∞ ≤ 1):
  min_{g∈C} ‖e−g‖_1 = max{⟨φ,e⟩ : ‖φ‖_∞ ≤ 1, φ ∈ −C*}.
Now (K_P∩L)* = K_P* + L^⊥ for the subspace L = R^F × 0, where the sum is closed because it is polyhedral. So C* is exactly the set of restrictions to F of solutions on P. Putting f = −φ gives (c).
(d) Combine (b) and (c): if g_n → e, then all g_n lie in K∩R^F = ∪_P (K_P∩R^F) for one finite F, so inf_P D(P,F) = 0. Conversely, if inf_P D(P,F) = 0, take g_n ∈ K_{P_n}∩R^F with ‖e − g_n‖_1 → 0; this sequence converges to e. For the quantitative form, a global solution f restricts to a solution on each P, so f(0) − f(1) ≤ max_F|f| · D(P,F) for every P.
Remark (countable X, not used in the claims): R^X is Fréchet–Montel, and for countable dimension the finest locally convex topology equals the finite topology (Kakutani–Klee). So for the Q-version, cl K is reached by transfinitely iterating "∪_F closure in R^F". Level 1 of this iteration is the sequential closure in (d).

## [unjudged] deep/C2r PROVED STRUCTURE
**Statement.** Let G ⊂ ℝ be an additive subgroup with G/2 ⊂ G. Let f: G → ℝ satisfy

(H) 2f(z) ≤ f(z+h) + f(z+2h) for all z ∈ G and all h ∈ G with h > 0.

Suppose x < y are in G with f(x) > f(y). Then for every real N and every real B, the set {g ∈ G ∩ [y,B] : f(g) < N} is finite.
**Beyond.** Refines B6 and r1s3/C1b. Every non-monotone solution on a countable 2-divisible group must have f→∞ (cofinitely) on bounded sets to the right of y, exactly as in the r1s3 example. This also explains why C1 above must use uncountability (B6).
**Referee.** `{"error": "claude -p returned an error result (engine-referee): success: You've hit your weekly limit · resets 9am (America/Toronto)"}`
**Adversary.** `{"error": "claude -p returned an error result (engine-adversary): success: You've hit your weekly limit · resets 9am (America/Toronto)"}`
**Proof or evidence.**

Notation. Fix N and put S = {g ∈ G : f(g) < N}. Let d = y − x > 0 and D = f(x) − f(y) > 0. All points below lie in G, since G is a group and G/2 ⊂ G.

**Lemma 1 (blow-up left of y).** Let x_k = y − d·2^{−k}. Then f(x_k) ≥ f(y) + 2^k·D for all k ≥ 0.

*Proof.* For k = 0 we have x_0 = x and f(x) = f(y) + D. For the inductive step, apply (H) at x_k with h = d·2^{−k−1}, which lies in G and is positive. Then x_k + h = x_{k+1} and x_k + 2h = y. So 2f(x_k) ≤ f(x_{k+1}) + f(y). Hence f(x_{k+1}) ≥ 2f(x_k) − f(y) ≥ f(y) + 2^{k+1}·D. ∎

Choose J with f(y) + 2^J·D > N, and set x* = x_J. Then x* ∈ G, x* < y, and f(x*) > N.

**Lemma 2 (closure).** Suppose u < w are both in S, and let δ = w − u. Then 2u − w ∈ S. Consequently w − kδ ∈ S for every integer k ≥ 0.

*Proof.* Apply (H) at 2u − w with h = δ. This gives 2f(2u − w) ≤ f(u) + f(w) < 2N.
- For the consequence, the cases k = 0 and k = 1 hold by hypothesis.
- If w − (k−1)δ and w − kδ both lie in S, apply the first part to the pair w − kδ < w − (k−1)δ. This yields w − (k+1)δ ∈ S. ∎

**Lemma 3 (move).** Suppose c ∈ G has f(c) > N. Suppose u < w are in S with δ = w − u and c + δ ≤ u. Then f(c + 2δ) − N > 4(f(c) − N).

*Proof.*
1. The half-open interval [(w−c−δ)/δ, (w−c)/δ) has length 1, so it contains exactly one integer k. Since w − c − δ = u − c ≥ δ, this k satisfies k ≥ 1.
2. Let s = w − kδ. Then c < s ≤ c + δ, and s ∈ S by Lemma 2.
3. If s = c + δ, then c = w − (k+1)δ ∈ S, contradicting f(c) > N. So c < s < c + δ.
4. Let s' = s + δ = w − (k−1)δ. Then s' ∈ S, because k − 1 ≥ 0.
5. Apply (H) at c with h = s − c > 0. This gives 2f(c) ≤ f(s) + f(c_1) < N + f(c_1), where c_1 = 2s − c. Hence f(c_1) − N > 2(f(c) − N).
6. We have c_1 = s + (s − c) < s + δ = s'. Apply (H) at c_1 with h = s' − c_1 > 0. This gives 2f(c_1) ≤ f(s') + f(2s' − c_1) < N + f(2s' − c_1).
7. Note that 2s' − c_1 = c + 2δ. So f(c + 2δ) − N > 2(f(c_1) − N) > 4(f(c) − N). ∎

**Lemma 4 (chain).** Suppose f(x̂) > N. Suppose s_0 > s_1 > … > s_L are points of S with x̂ ≤ 3s_L − 2s_0. Then f(x̂ + 2(s_0 − s_L)) − N > 4^L·(f(x̂) − N).

*Proof.* Set c_i = x̂ + 2(s_0 − s_i). We show by induction on i that f(c_i) − N > 4^i·(f(x̂) − N); in particular f(c_i) > N.

To get from c_{i−1} to c_i, apply Lemma 3 with c = c_{i−1}, u = s_i, w = s_{i−1}. Its hypothesis c_{i−1} + (s_{i−1} − s_i) ≤ s_i is equivalent to x̂ + 2s_0 − s_{i−1} ≤ 2s_i. This holds because:
- x̂ + 2s_0 − s_{i−1} < x̂ + 2s_0 − s_i, since s_{i−1} > s_i;
- x̂ + 2s_0 − s_i ≤ 2s_i, since x̂ + 2s_0 ≤ 3s_L ≤ 3s_i.

Lemma 3 then gives f(c_i) − N > 4(f(c_{i−1}) − N). ∎

**Main argument.** Suppose T = S ∩ [y,B] is infinite.

*Step 1: a convergent sequence in T.* T is bounded, so it contains a strictly monotone sequence (t_n) converging to some c ∈ [y,B]. Let η = c − x*. Then η > 0, since c ≥ y > x*.

*Step 2: a strictly decreasing sequence in S.* We build σ_m ∈ S, strictly decreasing to a limit ℓ with ℓ ≥ x* + η/2.
- If (t_n) is decreasing, take σ_m = t_m and ℓ = c.
- If (t_n) is increasing, pick n_0 with c − t_{n_0} < η/4. Take σ_m = 2t_{n_0} − t_{n_0+m}. These lie in S by Lemma 2, applied to t_{n_0} < t_{n_0+m}. They decrease strictly to ℓ = c − 2(c − t_{n_0}) > c − η/2 = x* + η/2.

*Step 3: the endpoints a and b.* Pick n with σ_n − ℓ < η/16, and set a = σ_n and δ = σ_n − σ_{n+1}. Then 0 < δ < η/16.
- By Lemma 2, applied to σ_{n+1} < σ_n, every a − kδ (k ≥ 0) lies in S.
- Let b be the first of these points with a − kδ < ℓ. Then b ∈ S and ℓ − δ ≤ b < ℓ < σ_m for all m.
- Therefore a − b < η/16 + δ < η/8.
- Hence 3b − 2a = b − 2(a − b) > ℓ − η/16 − η/4 ≥ x* + 3η/16 > x*.

*Step 4: contradiction.* For any L ≥ 1, apply Lemma 4 with x̂ = x* to the chain σ_n > σ_{n+1} > … > σ_{n+L−1} > b, which lies in S. Its condition x* ≤ 3b − 2a holds by Step 3. Put p = x* + 2(a − b); this point does not depend on L. Lemma 4 gives f(p) − N > 4^L·(f(x*) − N) for every L. Since f(x*) − N > 0, this is impossible for the real number f(p).

So T is finite. ∎

## [broken] deep/C2 PROVED STRUCTURE
**Statement.** Let G⊂R be a subgroup with G/2⊂G (for example Q or Z[1/2]). Let f: G→R satisfy (H) for all x∈G and h∈G, h>0, and suppose x<y in G with f(x)>f(y). Then for every N and every B, the set {g∈G∩[y,B]: f(g)<N} is finite.
**Beyond.** Refines B6 and r1s3/C1b. Every non-monotone solution on a countable 2-divisible group must have f→∞ (cofinitely) on bounded sets to the right of y, exactly as in the r1s3 example. This also explains why C1 above must use uncountability (B6).
**Referee.** `{"valid": false, "first_error": "The proof consists only of 'the argument of C1, Steps 1–6, carried out inside G'. C1 is cited only as a statement about f: R→R. Its hypothesis (f defined on all of R, (H) for all real h>0) is not met for f: G→R, and its conclusion (monotonicity) is not the claimed one. So the proof relies on unstated internals of C1's proof (points t, b, t′, q*, q0, the sets L_ρ, the Step 5 density, the Step 6 'f=∞' contradiction), none of which are given or re-proved for G. In particular, Step 5 density of L_ρ∩G is merely asserted ('the same progressions give it'), although the team itself says C1 uses uncountability somewhere and does not show which step that is or that Steps 1–6 avoid it.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

The argument of C1, Steps 1–6, carried out inside G.
- The points a=x_k=y−d2^{−k}, t=q−jd, b, t′, a+2d and the progressions all lie in G, since G is 2-divisible.
- In Step 5, density means density of L_ρ∩G in (−∞,z). The same progressions give it.
- If some {g∈G∩[y,B]: f(g)<N} were infinite, Step 6 would give the contradiction f(a+2(q*−q_0))=∞.
Consistency check: on the Z[1/2] example (r1s3/C1), f(x)=2^{λ(x)} with λ ≥ x·2^{n(x)} for x>0, so the low sets are finite on bounded sets, as C2 requires.

## [broken] deep/C3 PROVED QUANT
**Statement.** Steps 3 and 4 of C1, as stand-alone finite implications.
**Beyond.** new lemma; with Step 5 it gives the theorem.
**Referee.** `{"valid": false, "first_error": "The claim itself: 'Steps 3 and 4 of C1, as stand-alone finite implications' never states what the implications are (no hypotheses, no conclusion, no finite configuration), and no proof is given. The only cited lemma is C1, the theorem these steps are meant to help prove, so using it would be circular. C1's hypothesis also quantifies over all x and h>0, so it does not yield stand-alone finite implications without an unproved extension argument.", "fixable": false}`
**Adversary.** `{"broken": true, "how": "The claim is not a well-formed statement: 'Steps 3 and 4 of C1' are never stated (no hypotheses, no conclusions, no specified finite set of instances of the inequality), and no proof is supplied for what is billed as a new lemma. Nothing can be checked, so nothing is established. The only cited lemma is C1 itself, the theorem these steps are supposed to help prove; using it would be circular. As 'stand-alone finite implications', the steps must be derived from finitely many explicit instances of 2f(x) ≤ f(x+h)+f(x+2h) without invoking C1. No mathematical counterexample was found; C1 alone is a known true result. The defect is the missing statement and the missing (possibly circular) proof.", "severity": "fixable"}`
**Proof or evidence.**

(none)

## [broken] r1s1/C2 PROVED STRUCTURE
**Statement.** If f is a solution with a bad pair x<y (f(x)>f(y)), then for every c in R and every open interval (a,b) with b>y, the set {t in (a,b): f(t) > c} is nonmeager (indeed nonmeager in every subinterval (a',b') with b'>y).
**Referee.** `{"valid": false, "first_error": "No proof is given. The claim (that {f>c} is nonmeager in every interval (a',b') with b'>y) is unsupported. A Baire argument using f(t) <= max(f(t+h), f(t+2h)) would also need an unproved lemma: f must be unbounded above at points arbitrarily close to the left of every point of the relevant region. Nothing derives this from the bad pair f(x)>f(y).", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [not validated] r1s2/C3 CONJECTURED NEGATIVE
**Statement.** For every finite F ∋ 0, 1: inf over finite P ⊇ F of D(P,F) > 0. Stronger form: for dyadic F_j = 2^{−j}Z∩[−A,B], D(P,F_j) = D(F_j,F_j) for every finite P ⊇ F_j.
**Proof or evidence.**

- D(P, F2 = Z/2∩[−1,2]) = 0.5 = D(F2,F2). Tested for P = (1/n)Z ∩ window with n ∈ {16, 24, 32, 40, 48, 60, 64} and windows [−1,2], [−1,3], [−3,4], [−2,4]; also for n = 12 on [−6,8].
- D(P, F3 = Z/4∩[−1,2]) = 0.25 = D(F3,F3) for n = 16, 32, 64.
- D(P, {0,1/2,1}) = 1.
- The upper bounds are already forced inside F: f(3/2) ≥ 2f(1/2) − f(1) ≥ f(1) + 4c gives c ≤ 1/2 for F2, and the analogous chain through 3/4 and 5/4 gives c ≤ 1/4 for F3.
- Refining P never helped. The extremal f blows up only at the point of P just to the right of max F, or of the window's right end.
MECHANISM: C2 handles F ⊆ (−∞,1]. For points of F to the right of 1, K4 only forces blow-up at the auxiliary points (q+1)/2 − 2^{−k−1}, not at q itself, so a finite P can always route the blow-up away from F.
IF TRUE: e lies outside the sequential closure of K. CORE would then need a genuinely transfinite or net closure. For the Q-version, this would be at least level 2 of the Kakutani–Klee iteration.

## [not validated] r1s3/C5 PROVED OTHER
**Statement.** Let W be a Q-subspace, z∉W, V=W⊕Qz. Every 3-AP in V that contains a point of V∖W contains at least two points of V∖W. Hence, if V∖W is enumerated p_0,p_1,…, then each p_n meets only finitely many constraints whose other two points lie in W∪{p_i: i<n}. These are at most 3 triples for each i<n: the AP is fixed by p_n, p_i and the pair of roles. So extending a solution from W to V is an ω-step greedy process with finitely many lower bounds (p_n as middle or right point) and finitely many upper bounds (p_n as base) at each step. An obstruction can only come from an inconsistency that builds up over infinitely many steps. Also, by K4 applied inside the Q-space V together with T2 reflections: if f|W has a bad pair (x,y), then for every q≠0, f restricted to the coset qz+W is unbounded above on every interval of (y,∞). (Proof: take b∈(q/2)z+W with b>y and a_n∈W, a_n↑b with f(a_n)→∞, by K4 in W. Then f(2b−a_n) ≥ 2f(a_n)−f(b)→∞, and 2b−a_n ∈ qz+W decreases to b.)
**Proof or evidence.**

(none)

## [not validated] r1s3/C2 OTHER OTHER
**Statement.** Let f be a solution on a Q-subspace V⊂R with f(x)>f(y) for some x<y in V. Then g(q)=f(x+q(y−x)) is a non-monotone solution on Q. So the T6 route needs the Q-version to be false. By C1 it is.
**Proof or evidence.**

restriction, as in K13.

## Frontier map

=== DIRECTION
TRUE, confidence 0.55. Here TRUE means: every solution f is nondecreasing, which is what Mathlib's `Monotone` asserts.

Evidence for TRUE:
- Every regular class is settled. If f is measurable, has the Baire property, or is locally bounded above at points arbitrarily far to the right, then f is nondecreasing (K5–K7 below).
- Constructions based only on the Q-linear structure of R are provably impossible (K10).

Evidence against TRUE, which is why the confidence is near 1/2:
- No finite set of instances of the hypothesis ever implies f(x) ≤ f(y) (K8). So any proof must be infinitary and must use the reals essentially.
- On Z the statement is false (K9).
- The forced blow-up of a counterexample happens along 2-adically sparse offsets. Those are exactly the patterns that arbitrary, non-measurable sets can realize.

A choice-based counterexample, possibly under CH, is a real possibility. If one exists under CH, the Lean statement is unprovable.

=== KNOWN
Labels used in the Source column:
- "standard": textbook or folklore.
- "derived (memo)": proved in this memo. The proofs are short and were checked here, but I know no published source for them. No published source for the problem itself is known to me.

Normalize a bad pair to x=0, y=1, f(0)=1, f(1)=0 with d=y−x=1, δ=f(x)−f(y)=1. Affine maps in x, and positive affine maps in f, preserve the hypothesis.

| # | Statement | Source | Method |
|---|---|---|---|
| K1 | Solutions form a convex cone containing the constants. The cone is closed under max, under x ↦ λx+c with λ>0, and under pointwise limits. So a counterexample may be taken with f ≥ 0 and f(1)=0=min f. | derived (memo) | inf of a sum ≥ sum of infs; max(f,0) keeps the bad pair |
| K2 | Halving: if x<y and f(x)>f(y), then f(y−d2^{−k}) ≥ f(y)+2^kδ for all k. | derived (memo) | iterate h=(y−a)/2 |
| K3 | Reflection: f(2t−a) ≥ 2f(a)−f(t) for all a<t. Midpoint: f((a+b)/2) ≥ 2f(a)−f(b) for a<b. | standard | the hypothesis itself |
| K4 | If (x,y) is a bad pair, then for every w>y: f(w+d2^{−k}) ≥ 2f(y)+2^{k+1}δ − f((w+y)/2). Hence f is unbounded above on every open interval contained in (y,∞), and every point of (y,∞) is the right endpoint of a bad pair. | derived (memo) | K2 followed by reflection about t=(w+y)/2 |
| K5 | If f is bounded above on an interval (c,c′), then f is nondecreasing on (−∞,c′). In particular a solution that is locally bounded above (for example upper semicontinuous, or continuous at points arbitrarily far right) is monotone. | derived (memo) | K4 |
| K6 | Measurable solutions, and solutions with the Baire property, are nondecreasing. | derived (memo) | Some set E_N={w: f((w+y)/2) ≤ N} is nonmeager (resp. of positive measure). Then ∩_{k≥K}(E_N+d2^{−k}) is nonempty (resp. limsup of the translates has positive measure). At a point p there, K4 gives f(p)=∞. |
| K7 | Lemma B: for every solution f and every z, liminf_{ε→0+} f(z−ε) < ∞. | derived (memo) | If f(z−ε) → ∞, reflect about t>z to get f(w+ε) ≥ 2f(z−ε)−f((w+z)/2). Baire gives some E_n={w: f((w+z)/2) ≤ n} dense in an interval J. Take w→p− through E_n to force f(p)=∞. Needs no regularity. |
| K8 | No finite certificate: for any finitely many instances of the hypothesis there is f satisfying them with f(1)<f(0). Equivalently, δ_1−δ_0 is not a finite nonnegative combination of δ_{a+h}+δ_{a+2h}−2δ_a. | derived (memo) | Finite Farkas. The rightmost support point must be 1. The rightmost support point q<1 cannot be a base, yet gets positive mass, a contradiction. |
| K9 | On Z (x, h integers) the answer is NO. Example: f(0)=1, f(1)=0, f(n)=n+1 for n≥2, f(n)=n−10 for n<0. | derived (memo) | check cases |
| K10 | If 2f(x) ≤ f(x+h)+f(x+2h) holds for all h≠0, then f is constant. | derived (memo) | apply at both endpoints of a 3-AP |
| K11 | Max version is false: f(x) ≤ max(f(x+h),f(x+2h)) does not force monotonicity. Example: f = 1 − 1_{1}. Weighted endpoints are trivial: λ∈{0,1} in f(x) ≤ λf(x+h)+(1−λ)f(x+2h) gives monotone. | derived (memo) | direct |
| K12 | Level sets: S_N={f≤N} is closed under (p,q) ↦ 2p−q for p<q, so it contains p−n(q−p) for all n≥0. In a counterexample some S_N is dense in (−∞,c) for some c>y, while every {f≥M} is dense in (y,∞). | derived (memo) | hypothesis + Baire + K4 |
| K13 | Countable reduction: g(q)=f(x+q(y−x)) is a solution on Q, and on the dyadics Z[1/2]. So the Q-version implies the R-version. | standard | restriction |

=== BARRIERS
| # | Obstruction | Methods it defeats, and why | What it does not rule out |
|---|---|---|---|
| B1 | Finite-certificate barrier (K8) | Every olympiad-style chaining of finitely many inequalities, and any LP certificate on a finite point set. The cone generated by the hypothesis never contains δ_1−δ_0. | Infinitary arguments: Baire category, measure, compactness or Ky Fan closure of the cone, forcing f(p)=∞ from infinitely many bounds |
| B2 | Lattice barrier (K9) | Any argument that only uses step sizes from a discrete set; non-monotone solutions exist on Z. | Arguments using density of steps |
| B3 | Sparse-offset barrier | Lemma A + Baire (K4/K6) for arbitrary f. The dyadic blow-up f(w+2^{−k}) → ∞ only holds for k ≥ K(w), and K can be 2-adic. Example: K(w) = denominator exponent on Z[1/2]-cosets, with K(r+2^{−k}) → ∞ for every r. So translates of the good sets need not ever meet. | Arguments producing blow-up along a continuum of offsets (K7 then finishes), or using several incommensurable scales jointly |
| B4 | Regularity barrier | Measure, density and Steinhaus-type arguments. For non-measurable sets, A∩(A+t) can be empty and outer measure is not additive. | Pure category (Baire) arguments, which hold for arbitrary sets |
| B5 | Algebraic-construction barrier (K10) | Counterexamples depending only on Hamel/Q-linear data, which ignore order. They force constancy. | Constructions mixing order with Hamel or 2-adic structure, or ω1-recursions under CH |
| B6 | Countability barrier | If the Q- or dyadic-version has a non-monotone solution (open), then no argument confined to a countable subgroup can work. A proof must exploit uncountability as Baire does. | Proofs for R that use Baire |

=== CORE
Show that no f: R→R satisfies the hypothesis with f(0)=1 > f(1)=0. By K1, K4, K7 and K12, such an f may be assumed to have all of the following:
- f ≥ 0;
- f(1−2^{−k}) ≥ 2^k;
- f is unbounded above on every interval of (1,∞);
- f(z−ε) does not tend to ∞ at any z;
- some S_N is dense in (−∞,c) with c>1.

Equivalently, show that a bad pair forces f(z−ε) → ∞ along all ε at some z; K7 then closes the argument.

Why it is hard:
- The hypothesis only produces blow-up along the geometric offsets d2^{−k} and their reflections. Those form countable, algebraically rigid sets.
- Arbitrary sets of reals can dodge countable patterns (B3, B4), and finite arguments are impossible (B1).
- So one must either convert the dyadic blow-up into continuum blow-up, which nobody knows how to do, or build a set-theoretic counterexample that dodges every reflection composition at once.

=== TARGET T1
TYPE: ANALOGUE
STATEMENT: Decide the dyadic version. Does there exist g: Z[1/2]→R with 2g(x) ≤ g(x+h)+g(x+2h) for all dyadic x and all dyadic h>0, and g(0)>g(1)? Conjecture: yes.
BEYOND: K9 settles Z; nothing is known for any dense countable subgroup.
VALUE: A YES pins down B6, so any proof for R must use uncountability, and it supplies the seed for a CH construction (T6). A NO, plus K13, proves CORE.
SIGNIFICANCE: 2
TEST: LP feasibility on the grids 2^{−m}Z∩[−1,4], with f(0)−f(1)=1 and f≥0. Minimise f at fixed points (2, 3/2, 1+2^{−j}) as m grows. Bounded minima suggest YES, because compactness holds once pointwise bounds are uniform.

=== TARGET T2
TYPE: SPECIAL
STATEMENT: Let φ: R→Q^n be Q-linear and F: R×Q^n→R Borel. If f(x)=F(x,φ(x)) satisfies the hypothesis, then f is nondecreasing.
BEYOND: K6 needs f measurable, and K10 only covers order-free f. This class contains the natural "Hamel + order" counterexample candidates, which are non-measurable.
VALUE: It kills the most natural family of counterexamples and forces any counterexample to use ω1-recursion.
SIGNIFICANCE: 2
TEST: none

=== TARGET T3
TYPE: SPECIAL
STATEMENT: Every periodic solution, with no regularity assumed, is constant.
BEYOND: Not covered by K5–K7, since a periodic counterexample would be unbounded on every interval.
VALUE: Periodicity converts the right-propagation of K4 into two-sided recurrence. It is a model case for using global structure without regularity.
SIGNIFICANCE: 1
TEST: none

=== TARGET T4
TYPE: QUANT
STATEMENT: Consider the weighted hypothesis f(x) ≤ λf(x+h)+(1−λ)f(x+2h). There is λ_0>0 such that it forces monotonicity of arbitrary f for every λ∈(0,λ_0); the same should hold near λ=1.
BEYOND: For arbitrary f, monotonicity is known only at λ∈{0,1} (K11). B1 applies at every interior λ.
VALUE: A perturbative proof from an endpoint would be the first infinitary proof for arbitrary f. Its mechanism could then be continued toward λ=1/2.
SIGNIFICANCE: 2
TEST: Grid LP from T1 with weights λ. Check whether forced values blow up as m→∞, and at what rate (1−λ)/λ-dependent exponent.

=== TARGET T5
TYPE: STRUCTURE
STATEMENT: For every solution f and every z, liminf_{ε→0+} f(z−ε) ≤ f(z). This would be a left lower-semicontinuity of the liminf, strengthening K7's "< ∞".
BEYOND: K7 only gives finiteness.
VALUE: Combined with K2 at y it constrains how dyadic spikes interleave with low values. It also attacks CORE via the S_N density of K12.
SIGNIFICANCE: 2
TEST: none

=== TARGET T6
TYPE: CONDITIONAL
STATEMENT: Assume CH. Then there is a non-monotone f: R→R satisfying the hypothesis. The intended route is an ω1-chain of countable Q-subspaces D_α, plus a one-generator extension lemma: any solution on D extends to D+Qz.
BEYOND: No conditional result in either direction is known. ZF+DC+"all sets have the Baire property" proves TRUE by K6, so this would make the problem independent of ZF+DC. It would also show the Lean statement is unprovable.
VALUE: Settles the problem negatively in a standard model of ZFC.
SIGNIFICANCE: 3
TEST: none

=== TARGET T7
TYPE: REDUCTION
STATEMENT: CORE follows from X: "if f(x)>f(y) with x<y, then there is z ≥ y with f(z−ε) → +∞ as ε→0+". The implication is already proved by K7. The target is to prove the weaker X′: "f(z−ε) ≥ c for all ε<ε_0 and all c", via an exhaustion over bad pairs (x′,z) given by K4.
BEYOND: K2 gives blow-up only along ε∈d2^{−k}.
VALUE: X′ ⇒ X ⇒ CORE. It isolates the single missing ingredient: continuum offsets.
SIGNIFICANCE: 2
TEST: none

=== TARGET T8
TYPE: NEGATIVE
STATEMENT: There is (in ZFC) f: R→[0,∞) satisfying every inequality derivable from at most m reflections and midpoints applied to the bad pair (0,1), for every fixed m, while being finite everywhere. So bounded-depth reflection arguments combined with Baire cannot prove CORE.
BEYOND: B3 shows this only for depth 1, via the 2-adic K.
VALUE: It tells the team whether the Baire route (A1) needs unbounded-depth reflection trees.
SIGNIFICANCE: 1
TEST: Symbolic enumeration of depth-m offset sets; check that they lie in d·Z[1/2] + span of reflection points.

=== TARGET T9
TYPE: STRUCTURE
STATEMENT: In any counterexample there is a single N such that S_N={f≤N} is dense in all of R, not only in (−∞,c).
BEYOND: K12 gives density on a left half-line only.
VALUE: Together with "{f≥M} is dense right of y" for all M, this sets up an exact-incidence (Ramsey) contradiction via the left-AP closure of S_N.
SIGNIFICANCE: 1
TEST: none

=== TARGET T10
TYPE: ANALOGUE
STATEMENT: Settle the Q-version, i.e. x, h ∈ Q. Show it is strictly stronger than the dyadic one: some g on Z[1/2] is non-monotone, yet every solution on Q is monotone. Or show both have counterexamples.
BEYOND: Nothing is known for countable dense domains.
VALUE: Locates exactly which steps (odd denominators) carry the rigidity, guiding A1.
SIGNIFICANCE: 2
TEST: The T1 grid LP on (1/(2^a3^b))Z∩[−1,4], compared with dyadic grids at matched size.

=== ANGLE A1
TECHNIQUE: Baire category with multi-scale reflection trees. This is new relative to K4/K6, which use one scale.
IDEA:
- Start from the bad pair. Use reflections about points in a dense sublevel set (K12) to produce bad pairs at scales s·2^{−k} for many s.
- Then show that the scales s with blow-up form a nonmeager set at some fixed point z, which gives continuum blow-up.
- K7 then gives f(p)=∞.
BARRIERS: It must beat B3. It does so because K12 gives a dense S_N to reflect about, so offsets are no longer confined to Z[1/2].
FIRST STEP: For the bad pair (0,1) and any p<q in S_N ∩ (1,c), prove f(1+(q−p)·2^{−k}·r) → ∞ for some fixed r and all large k.

=== ANGLE A2
TECHNIQUE: Ky Fan's consistency theorem for infinite linear systems, i.e. weak-* closure of the cone. Not used in KNOWN.
IDEA: In the dual of R^R, CORE is equivalent to (δ_0−δ_1, 1) lying in the closure of the cone generated by δ_{a+h}+δ_{a+2h}−2δ_a. Construct an approximating net of finite combinations explicitly; the dyadic halving tree truncated at depth k is the prototype. Then show the error terms vanish in the relevant topology on finitely supported vectors.
BARRIERS: B1 is circumvented, because closure rather than membership is all that is needed. B6 decides whether a countable support suffices.
FIRST STEP: Compute the residual of the depth-k halving tree. Show it equals 2^{−k}-weighted mass at 1−2^{−k}. Then find combinations that move that mass onto points of a dense sublevel set.

=== ANGLE A3
TECHNIQUE: Transfinite recursion under CH, using an ω1-chain of countable Q-subspaces (Sierpiński / Erdős–Kakutani style). Not used in KNOWN.
IDEA:
- Build a counterexample on D_0=Q·1, as in T1/T10.
- Extend along D_α ⊂ D_{α+1}=D_α+Qz_α, defining f on the new cosets D_α+qz.
- Use order-dependent shifts so that every cross-coset 3-AP constraint has slack.
BARRIERS: B5 is beaten by making the construction order-dependent. K7 and K12 are necessary conditions the construction must satisfy, and they serve as sanity checks.
FIRST STEP: The one-generator extension lemma: for a countable dense subgroup D, a solution g on D, and z∉D, there is a solution on D+Qz extending g. Try first g = a monotone function plus a 2-adic spike function.

=== ANGLE A4
TECHNIQUE: Ramsey theory of countable colorings of R (Erdős–Kakutani, Komjáth, Schmerl) applied to the ordered pattern. Not used in KNOWN.
IDEA: Color x by ⌈f(x)⌉. The hypothesis says that in every increasing 3-AP a<a+h<a+2h the first color is at most the mean of the other two. Combine with K4: the colors near y from the left are unbounded along dyadics. Classify which ordered linear patterns are countably avoidable in ZFC versus under CH.
BARRIERS: This approach is set-theory-aware by design, so B3 and B4 are its subject matter. B1 is irrelevant to it.
FIRST STEP: Prove or refute in ZFC that some countable coloring of R has no monochromatic set of the form {a, a+h, a+2h} ∪ {a−2^{−k}h : k∈K}, with K infinite and h ranging over a dense set.

=== ANGLE A5
TECHNIQUE: Controlled random walk / optimal stopping, treating f as a supermartingale under adaptive step choice.
IDEA: For any adaptive strategy, f(a) ≤ E f(X_τ) over finite trees. Let S_N be the dense, left-closed sublevel set of K12. The goal is to show some high point a_k=1−2^{−k} can be steered, with all leaves of the tree in S_N, which forces f(a_k) ≤ N.
BARRIERS: Must beat B3. Leaves must hit S_N exactly, which requires additive richness of S_N (A4) or nonmeagerness (Baire).
FIRST STEP: Show that the closure of a nonmeager set S under "a+h, a+2h ∈ S ⇒ a ∈ S" contains a nonmeager subset of every interval to the left of sup S.

=== ANGLE A6
TECHNIQUE: Computation-guided compactness: LP on rational grids plus Tychonoff. Not used in KNOWN.
IDEA: A counterexample exists if and only if there is B: R→[0,∞) such that every finite subsystem has a solution with 0 ≤ f ≤ B and f(0)−f(1)=1. Compute minimal feasible envelopes on dyadic and triadic grids to see whether they stay bounded.
- If they stay bounded: construct B and get a counterexample, on Q first.
- If they blow up at a fixed point: read off the dual certificates, which will supply A2's net.
BARRIERS: B1 says finite grids are always feasible, so the information is in the growth rate, not in feasibility.
FIRST STEP: For m ≤ 12, solve min f(3/2) and min f(2) on 2^{−m}Z∩[−1,4] with f(0)=1, f(1)=0, f≥0. Record growth in m and the dual weights.

## Deep dive

GOAL: **Theorem to prove.** Every f: ℝ → ℝ with 2f(x) ≤ f(x+h) + f(x+2h) for all x and all h > 0 is nondecreasing. So the answer to the problem is **YES**.

**Significance: 3.** This resolves the problem outright. It also corrects the frontier map's assessment that "nobody knows how" to turn the dyadic blow-up into blow-up along a continuum of offsets. The proof gets its continuum of offsets from the *differences of the low set*, not from dyadic scales.

The proof is a validated structural result (C1) plus one new elementary lemma. I checked that lemma here, and I sketch it below. The whole budget should go to making this proof airtight and refereed. If a gap appears, the same plan yields a significance-2 statement as a fallback.
