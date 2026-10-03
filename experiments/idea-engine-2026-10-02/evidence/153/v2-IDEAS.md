# Research engine: problem 153, run 20261002-073216-923101-erdos153

Spend $23.3646; 12 claim(s); 2 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] r2s1/C1 PROVED NEGATIVE
**Statement.** For $n\ge1$ and $D\ge0$, let $\mathcal F(n,D)$ be the set of $w:\{0,\dots,D\}\to[0,1]$ with $\sum w=n$, $w(0)>0$, $w(D)>0$, and $(w\star\tilde w)(d):=\sum_z w(z)w(z+d)\le1$ for every $d\ne0$. Every Sidon $A\subset[0,D]$ with $0,D\in A$ and $|A|=n$ has $1_A\in\mathcal F(n,D)$. Put $W(x)=\sum_{z\le x}w(z)$, $W'(x)=\sum_{z\ge D-x}w(z)$ and $x_j=2^{-j}D$, and define
$\Phi(w)=\sum_{j\ge1,\,x_j\ge n}(\lambda_j^{-2}+\lambda_j'^{-2})$ with $\lambda_j=nW(\lfloor x_j\rfloor)/x_j$ and $\lambda'_j$ defined likewise from $W'$. (This is the G1 functional; edge Cauchy–Schwarz gives $Q(A)\gtrsim\Phi(1_A)$.)
(a) Upper bound. Suppose $0<\delta\le1/2$, $\delta n^2\ge41$ and $n^2\ge3/\delta$, and set $D=\lfloor(1+\delta)n^2\rfloor$. Then some $w\in\mathcal F(n,D)$ has $\sum w^2\le1$ (so also $w\le1$, $w\star\tilde w\le1$ and $w*w\le1$ at every lag) and $\Phi(w)\le2(1+2\delta)^2(\log_2(1/\delta)+4.1)$.
(b) Lower bound. Suppose $n\ge16$, $3n^{-1/2}\le\delta\le1/2$ and $D\le(1+\delta)n^2$. Then every $w\in\mathcal F(n,D)$ has $\Phi(w)\ge(\log_2(1/\delta)-2)/18$.
**Beyond.** This turns B1+B2+B3 into an exact theorem that applies to the assignment's route (iv). Explicit-$\delta$ stability gives exactly $\Theta(\log1/\delta)$ and never $\infty$. The obstruction includes Fourier arguments (Erdős–Turán, Lindström and their refinements): as far as I know, the standard versions use only $|\hat w|^2\ge0$, $0\le r_{A-A}\le1$ off $0$, and $\sum w^2\le n$, all of which hold on $\mathcal F$. This remark was not checked paper by paper; the theorem itself does not depend on it. Hand re-check, done after writing the proof: every inequality in (a) and (b) was re-verified, including the floor effects in $\lambda_j$ and the edge case $n=16$ in $D\ge n^2/2$.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No known source proves this explicit Θ(log 1/δ) barrier for the fractional relaxation, but it formalizes the team's own heuristics B1–B3. The upper bound is essentially routine (ℓ2 slack bounds every pair constraint), and the result only shows one proof route fails rather than advancing the problem.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No known source proves this explicit Θ(log 1/δ) barrier for the fractional relaxation, but it formalizes the team's own heuristics B1–B3. The upper bound is essentially routine (ℓ2 slack bounds every pair constraint), and the result only shows one proof route fails rather than advancing the problem."}, {"verdict": "new", "cite": null, "significance": 1, "why": "A t`
**Proof or evidence.**

(a) Construction. Let $L=\lfloor\delta n^2\rfloor$. Then $2L\le D$, since $\delta\le1/2$. Define $p(z)=\max\big(1,(L/(z+1))^{1/4},(L/(D-z+1))^{1/4}\big)$ on $\{0,\dots,D\}$ and $w=\kappa p$ with $\kappa=n/\sum p$.
- Shape of $p$. On the left block $z\in[0,L-1]$ we have $p=(L/(z+1))^{1/4}$. The right block $[D-L+1,D]$ is the mirror image. Elsewhere $p=1$. The two blocks are disjoint.
- Sums over a block. Since $u\mapsto(L/u)^{1/4}$ is decreasing, $S_1=\sum_{k=1}^L(L/k)^{1/4}$ satisfies $\int_1^{L+1}\le S_1\le\int_0^L$. Hence $\tfrac43(L-L^{1/4})\le S_1\le\tfrac43L$. Likewise $S_2=\sum_{k=1}^L(L/k)^{1/2}\le2L$.
- Bounds on $\sum p$ and $\sum p^2$. Put $M=D+1\ge(1+\delta)n^2$. Then $\sum p\ge M+a$ with $a=\tfrac23L-\tfrac83L^{1/4}$, and $\sum p^2\le M+2L$.
- Claim: $(\sum p)^2\ge n^2\sum p^2$. This gives $\sum w^2=n^2\sum p^2/(\sum p)^2\le1$. To prove it, note that $(M+a)^2/(M+2L)$ is increasing in $M$ (the derivative has the sign of $(M+a)(M+4L-a)>0$). So it suffices to take $M=M_0=(1+\delta)n^2$. There $(M_0+a)^2\ge M_0(M_0+2a)$, and
$M_0+2a-n^2-2Ln^2/M_0\ \ge\ \delta n^2+\tfrac43L-\tfrac{16}3L^{1/4}-2L\ \ge\ \tfrac13\delta n^2-\tfrac{16}3(\delta n^2)^{1/4}\ \ge0,$
using $L\le\delta n^2$ and $(\delta n^2)^{3/4}\ge16$, which holds since $\delta n^2\ge41$.
- The constraints of $\mathcal F$. By Cauchy–Schwarz, $(w\star\tilde w)(d)\le\sum w^2\le1$ and $(w*w)(s)\le1$ for every $d$ and $s$, and $w\le1$. Also $\sum w=n$ and $w(0),w(D)>0$. So $w\in\mathcal F(n,D)$.
- Lower bound on $n\kappa$. From $\sum p\le M+\tfrac23L\le(1+\tfrac53\delta)n^2+1$ and $1/n^2\le\delta/3$ we get $n\kappa=n^2/\sum p\ge1/(1+2\delta)$.
- Lower bounds on $\lambda$. For every $x\ge1$, $W(x)\ge\kappa(x+1)$, so $\lambda(x)\ge n\kappa$. For $1\le x\le L-1$, every one of the $x+1$ terms is at least $(L/(x+1))^{1/4}$. So $W(x)\ge\kappa(x+1)^{3/4}L^{1/4}$, and therefore $\lambda(x)\ge n\kappa(L/x)^{1/4}$.
- Bounding $\Phi$. Here $\lambda(x)^{-2}\le(1+2\delta)^2\min(1,(x/L)^{1/2})$. The number of $j\ge1$ with $x_j\ge L$ is at most $\log_2(D/L)\le\log_2(1/\delta)+0.62$, using $L\ge\tfrac{40}{41}\delta n^2$. The terms with $x_j<L$ form a geometric series of ratio $2^{-1/2}$, whose sum is at most $1/(1-2^{-1/2})<3.42$. The right end is identical by the symmetry $z\mapsto D-z$. Adding up gives the bound. ∎(a)
(b) This is the A2 stability argument rerun on $\mathcal F$; it uses only the axioms of $\mathcal F$.
- Window energy. Let $h=\lceil n^{3/2}\rceil$, $W_y=\sum_{z\in[y,y+h)}w(z)$ and $Y=\{-(h-1),\dots,D\}$. Then $\sum_YW_y=nh$, and
$\sum_YW_y^2=\sum_d(w\star\tilde w)(d)\max(h-|d|,0)\le h\sum w^2+h(h-1)\le nh+h^2,$
because $w\le1$ gives $\sum w^2\le n$.
- Variance. Let $\mu=nh/(D+h)$ and $V=\sum_Y(W_y-\mu)^2$. Then $V/h^2\le n/h+1-n^2/(D+h)\le n/h+\delta+h/n^2\le\delta+3n^{-1/2}\le2\delta$.
- Size of $D$. Also $V\ge0$ gives $D+h\ge n^2h/(n+h)\ge n^2(1-n^{-1/2})$.
- Bound on $W(x)$. Take $x\ge h$ and $Y_x=\{-(h-1),\dots,x\}$. Each $z\le x$ lies in $h$ of these windows, so $\sum_{Y_x}W_y\ge hW(x)$. Cauchy–Schwarz then gives $hW(x)-\mu(x+h)\le\sqrt{(x+h)V}$. Therefore
$W(x)\le\frac{2nx}{D+h}+\sqrt{4\delta x}\le\frac{4x}n+\sqrt{4\delta x}.$
- Edge sparsity. For $x\ge\delta n^2$ (which is $\ge3n^{3/2}\ge h$) we have $\sqrt{4\delta x}\le2x/n$, so $\lambda(x)\le6$.
- Counting scales. Using $D\ge n^2/2$ (valid for $n\ge16$), at least $\log_2(1/\delta)-2$ indices $j\ge1$ have $x_j\ge\delta n^2\ (\ge n)$. Each contributes $\lambda_j^{-2}\ge1/36$. The mirror argument gives the same for $\lambda'_j$. ∎(b)
CONSEQUENCE. Any proof of G1, or of CORE via edge sparsity at $C_0=1+\delta$, must use a property of Sidon indicators that fails for some $w\in\mathcal F$. Examples are integrality of $w$, $r_{A-A}\in\{0,1\}$, or $|A+A|=\binom{n+1}2$ as a support statement. Every linear or quadratic inequality in $w$, and every positive-definiteness inequality for $r_{A-A}$, is useless here. In the extremal weight, $\lambda(x)\asymp(\delta D/x)^{1/4}$ for $x<\delta D$, and the $L^2$ cost is only $O(\delta)$.

## [validated-new] r2s2/C1 PROVED NEGATIVE
**Statement.** - Fix K≥1 and ε∈(0,1/2). There is a function G_{K,ε}(n)→∞ with the following property.
- Let A⊂ℤ be a Sidon set with |A|=n. Suppose A ⊂ R ∪ ⋃_{j=1}^K φ_j(S^{(j)}), where:
  - S^{(j)}⊂[0,m_j) is the integer lift of a planar (Singer) difference set mod m_j=q_j²+q_j+1, with |S^{(j)}|=q_j+1 and q_j ≤ n^{2-3ε};
  - φ_j(s)=M_jσ_j s+c_j, with real M_j≥1, σ_j∈{±1} and c_j∈ℤ;
  - |R| ≤ n^{1-ε}.
- Then Q(A) ≥ G_{K,ε}(n).
**Beyond.** - B7 and the round-1 residue-gluing idea give no such statement.
- This kills the assignment's route (residue gluing of algebraic pieces, with B3-type multiscale end-loading) whenever the number of pieces is bounded.
- It also quantifies the cost: the bound decays only like K^{-2}, so a counterexample needs K→∞ pieces.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No known source treats Sidon sets covered by boundedly many affine Singer images plus a small remainder; it is a structured special case, not CORE, though close to the standard Fourier-flatness argument of B7. It only rules out bounded-K algebraic gluing as a counterexample route and says nothing about general sets with D <= C n^2.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No known source treats Sidon sets covered by boundedly many affine Singer images plus a small remainder; it is a structured special case, not CORE, though close to the standard Fourier-flatness argument of B7. It only rules out bounded-K algebraic gluing as a counterexample route and says nothing about general sets with D <= C n^2."`
**Proof or evidence.**

Normalise min A=0 and put D=max A. Write A(x)=|A∩[0,x]| and λ(x)=nA(x)/x.

*Lemma A (edge Cauchy–Schwarz; any finite A, no Sidon needed).* Q(A) ≥ (1/4)Σ_{k≥0} λ(x_k)^{-2}, where x_k=2^{1-k}D.
- Proof:
  - Let N(x)=|(A+A)∩[0,x]|. Then N(x) ≤ A(x)(A(x)+1)/2 ≤ A(x)², because every sum ≤x uses two elements ≤x.
  - Take the window W_k=(x_k/2,x_k]. We have s_1=0 and s_t=2D ≥ x_k, so the gap intervals [s_i,s_{i+1}] cover W_k.
  - A gap that meets W_k in positive length has s_i<x_k, so at most N(x_k) gaps meet W_k. Their clipped lengths sum to x_k/2.
  - By Cauchy–Schwarz, the squares of the clipped lengths sum to at least x_k²/(4N(x_k)).
  - The windows are disjoint and (Σ pieces)² ≥ Σ pieces², so Σ_i d_i² ≥ Σ_k x_k²/(4A(x_k)²).
  - Since t ≤ n(n+1)/2 ≤ n², we get Q ≥ Σ_k x_k²/(4n²A(x_k)²) = (1/4)Σ_k λ(x_k)^{-2}.

*Lemma B (Singer discrepancy).* For every integer interval I: |S∩I| ≤ min(q+1, |I|/q + √q(1+ln m)).
- Proof:
  - Intersect I with [0,m). This leaves at most m integers, which are distinct residues.
  - For ξ≠0, |Ŝ(ξ)|² = Σ_d r_{S-S}(d)e(dξ/m) = (q+1) + Σ_{d≢0}e(dξ/m) = q.
  - By Fourier inversion, |S∩I| = |I|(q+1)/m + E, where |E| ≤ (√q/m)Σ_{ξ=1}^{m-1}|Î(ξ)|.
  - Bound each term by |Î(ξ)| ≤ 1/sin(πξ/m). Since m is odd, pair ξ with m−ξ and use sin(πu) ≥ 2u on [0,1/2]. This gives Σ ≤ m·H_{(m-1)/2} ≤ m(1+ln m).
  - Finally (q+1)/m < 1/q.

*Step 1 (pointwise loading bound).*
- φ_j^{-1}([0,x]) contains at most x/M_j+1 integers.
- For x ≥ X_0 := n^{2-ε} and n ≥ n_0(ε), the following hold:
  - n|R|/x ≤ 1;
  - n/(q_j x) ≤ 1;
  - n√q_j(1+ln m_j)/x ≤ n^{-ε/2}(4ln n+3) ≤ 1, using m_j ≤ 3n⁴.
- With Y_j := M_j q_j² and min(a,b+c) ≤ min(a,b)+c, we get
  λ(x) ≤ 2K+1 + Σ_j g_j(x), where g_j(x) = min(2n q_j/x, n/(M_j q_j)) ≤ min(2n√Y_j/x, n/√Y_j).
- This uses q_j ≤ √Y_j and M_j q_j ≥ √Y_j.

*Step 2 (corner chain).*
- If D ≥ Cn², the global Cauchy–Schwarz bound gives Q ≥ 4C², so assume D ≤ Cn².
- Sort the Y_j. Set Z_i := clamp(Y_(i), X_0, 2D), with Z_0 = X_0 and Z_{K+1} = 2D.
- Every j has either Y_j ≤ Z_i or Y_j ≥ Z_{i+1}. Case check: suppose Y_j > Z_i ≥ X_0, and write j=(l).
  - If l ≤ i: when Y_(i) ≤ 2D we get Z_i ≥ Y_(i) ≥ Y_j, a contradiction; otherwise Z_i = Z_{i+1} = 2D < Y_j.
  - If l ≥ i+1: when Y_(i+1) < X_0 we get Z_{i+1} = X_0 < Y_j; otherwise Z_{i+1} ≤ Y_(i+1) ≤ Y_j.
- For x ∈ [√(Z_iZ_{i+1}), Z_{i+1}]:
  - if Y_j ≥ Z_{i+1}, then g_j ≤ n/√Z_{i+1};
  - if Y_j ≤ Z_i, then g_j ≤ 2n√Z_i/x ≤ 2n/√Z_{i+1}.
- Hence λ ≤ 3K(n/√Z_{i+1} + 1), so λ^{-2} ≥ Z_{i+1}/(18K²(n²+Z_{i+1})) ≥ u_{i+1}/(18K²(1+2C)), where u_i := Z_i/n².
- The interval contains at least ⌊½log₂(u_{i+1}/u_i)⌋ of the points x_k.

*Step 3 (combine).* By Lemma A, Q ≥ Φ/(72K²(1+2C)), where Φ = Σ_{i=0}^K ⌊½log₂(u_{i+1}/u_i)⌋u_{i+1}.
- The endpoints satisfy u_0 = n^{-ε} and u_{K+1} = 2D/n² ≥ (n-1)/n ≥ 1/2, using D ≥ n(n-1)/2 (distinct differences).
- If Φ ≤ B, then u_i > u_{i+1}·2^{-2B/u_{i+1}-2}.
- The map v ↦ v·2^{-2B/v-2} is increasing. By downward induction, u_0 ≥ v_0(B,K) > 0, where v_{K+1} = 1/2 and v_i = v_{i+1}2^{-2B/v_{i+1}-2}.
- So Φ > B as soon as n^{-ε} < v_0(B,K). Therefore Φ → ∞, and with it Q, uniformly over the class.
- Combining with the case D ≥ Cn²: choose C = C(n) → ∞ slowly. ∎

## [valid-routine] r1s1/C1 PROVED REDUCTION
**Statement.** Let A ⊂ Z be Sidon, |A| = n, min A = 0, max A = D. For x ≥ 0 set E_x = A∩[0,x], T_x = A∩(x,D], and R_x(y) = #{(t1,t2,t3) ∈ T_x^3 : t1+t2-t3 = y}.
(a) R_x(y) = 0 for every y ∈ E_x.
(b) For any μ:[0,x]∩Z → (0,∞), |E_x| ≤ V_x(μ)/min μ^2, where V_x(μ) = Σ_{0≤y≤x} (R_x(y)-μ(y))^2. Also |E_x| ≤ (x+1) - (Σ_{y≤x} R_x)^2 / Σ_{y≤x} R_x^2.
(c) Fix K ≥ 1. Say H(K) holds at x if some constant μ ≥ n/K satisfies V_x(μ) ≤ K μ (x+1). Suppose H(K) holds at L distinct scales x_j = 2^{-j} D (j ≥ 0) with x_j ≥ n. Then Q(A) ≥ L/(64 K^4).
**Beyond.** KNOWN reduces CORE to edge sparsity λ_j = O(1) and records that every pairwise (second-order) input is blocked (B1–B3). C1 reduces edge sparsity to a third-order statement instead: the local variance of r_{T+T-T} at the Poisson level, i.e. local E_3(T) near-minimal to relative precision ~1/n. B2 and B3 do not apply to that statement.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "(a) is the Sidon property, (b) is Chebyshev/Cauchy–Schwarz on the forced zeros of r_{T+T-T} on E_x, and (c) chains this with the already-known edge-sparsity reduction; the hypothesis H(K) directly encodes |E_x| ≲ K^2 x/n, so it is a strictly stronger reformulation of the open edge condition, not progress.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "(a) is the Sidon property, (b) is Chebyshev/Cauchy–Schwarz on the forced zeros of r_{T+T-T} on E_x, and (c) chains this with the already-known edge-sparsity reduction; the hypothesis H(K) directly encodes |E_x| ≲ K^2 x/n, so it is a strictly stronger reformulation of the open edge condition, not progress."}, {"verdict": "routine", "cite": null, "signi`
**Proof or evidence.**

(a) Suppose y ∈ E_x and y = t1+t2-t3 with t_i ∈ T_x. Then y + t3 = t1 + t2. By the Sidon property {y,t3} = {t1,t2} as multisets. So y ∈ T_x, contradicting y ≤ x < min T_x.
(b) By (a), Σ_{y∈E_x} μ(y)^2 = Σ_{y∈E_x} (R-μ)^2 ≤ V_x. For the second form, let Z^c be the set of y ≤ x with R(y) > 0. Cauchy–Schwarz gives (ΣR)^2 ≤ |Z^c| ΣR^2, and |E_x| ≤ (x+1) - |Z^c|.
(c) By (b), A(x_j) := |E_{x_j}| ≤ K μ(x_j+1)/μ^2 ≤ K^2 (x_j+1)/n =: M_j. Since x_j ≥ n, we have 1 ≤ K^2 ≤ M_j ≤ 2K^2 x_j/n.
Let N(x) = #(A+A)∩[0,x]. Every sum a+b ≤ x with a,b ≥ 0 has a,b ∈ E_x, so N(x) ≤ A(x)(A(x)+1)/2 ≤ A(x)^2. Hence N(x_j)+1 ≤ 2M_j^2 ≤ 8K^4 x_j^2/n^2.
Write A+A = {s_1 < ... < s_t} with s_1 = 0 and s_t = 2D. The windows W_j = (x_j/2, x_j] ⊂ [0, 2D] are pairwise disjoint. The gaps [s_i, s_{i+1}] meeting W_j in positive length number at most #(A+A)∩W_j + 1 ≤ N(x_j)+1, and their overlaps with W_j have total length x_j/2. By Cauchy–Schwarz, Σ_i |[s_i,s_{i+1}]∩W_j|^2 ≥ x_j^2/(4(N(x_j)+1)) ≥ n^2/(32K^4).
Each gap satisfies d_i = s_{i+1}-s_i ≥ Σ_j |[s_i,s_{i+1}]∩W_j|, so d_i^2 ≥ Σ_j |[s_i,s_{i+1}]∩W_j|^2. Summing, Σ d_i^2 ≥ L n^2/(32K^4). With t = n(n+1)/2 this gives Q ≥ L n/(16K^4 (n+1)) ≥ L/(32K^4) ≥ L/(64K^4). ∎
Remark: there are ~log_2(D/n) admissible scales. So H(K) at a positive proportion of scales gives Q ≳ log n / K^4, and H(K) at unboundedly many scales gives CORE.

## [valid-routine] r1s1/C2 PROVED NEGATIVE
**Statement.** Let q be a prime and S ⊂ [0, m) (m = q^2+q+1) an integer lift of a Singer perfect difference set, and A = 2S. Then:
- A is Sidon with n = q+1 and D ≤ 2(m-1), so D/n^2 < 2.
- For every x ≥ 0, every odd y ∈ [0,x] satisfies R_x(y) = 0. Hence #{y ≤ x : R_x(y) = 0} ≥ ⌊(x+1)/2⌋.
- H(K) fails at every scale x ≥ 1 once n > 4K^2.
- More generally, if T ⊂ 2Z and E ⊂ 2Z+1, both third-order constraints (E+T)∩(T+T) = ∅ and (E+E-E)∩T = ∅ hold automatically.
- Hence no lemma of the form "Sidon, D ≤ C_0 n^2 ⇒ #holes of T_x+T_x-T_x in [0,x] ≤ K x/n" can hold for C_0 ≥ 2, and neither can H(K). For C_0 ≥ M, the same holds with M·S in place of 2S.
**Beyond.** This is a precise obstruction to the third-order route. A1 can only be effective for C_0 < 2, or else must add the pairwise E–T constraints (E+E)∩(T+T) = ∅ and (E-E)∩(T-T) = {0}. It is not a counterexample to CORE: Q(2S) = 4Q(S) → ∞.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Dilating a Singer Sidon set by 2 (or M) makes all sums even, so odd integers are never represented and parity-based constraints hold trivially; this is the standard local/congruence obstruction, removed by normalising gcd(A-A)=1. It only refutes the team's own unnormalised lemma forms and says nothing about CORE, since Q(2S)=4Q(S)→∞.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Dilating a Singer Sidon set by 2 (or M) makes all sums even, so odd integers are never represented and parity-based constraints hold trivially; this is the standard local/congruence obstruction, removed by normalising gcd(A-A)=1. It only refutes the team's own unnormalised lemma forms and says nothing about CORE, since Q(2`
**Proof or evidence.**

- Dilation preserves the Sidon property.
- T_x ⊂ 2Z, so T_x+T_x-T_x ⊂ 2Z, and R_x vanishes on odd y.
- If H(K) held at x with constant μ ≥ n/K, then V_x ≥ ⌈x/2⌉ μ^2 when x ≥ 1. With V_x ≤ Kμ(x+1) this gives μ ≤ K(x+1)/⌈x/2⌉ ≤ 4K. That contradicts μ ≥ n/K once n > 4K^2.
- The last two claims are parity checks: E+T is odd while T+T is even, and E+E-E is odd while T is even.
- Checked numerically (s2.py): q = 127 and 251, at x ≈ n^{1.5} and x = D/16, give zeros ≈ x/2 (729/1448, 2007/4000, 3951/7859) and Fano 24–58. ∎

## [valid-routine] r1s2/C1 PROVED NEGATIVE
**Statement.** Let $A$ be Sidon and $A=P_1\sqcup\dots\sqcup P_k$ any partition (e.g. $E=A\cap[0,x]$, $T=A\setminus E$). Then:
(a) $E\cap(T+T-T)^{\rm nontriv}=\emptyset$ holds if and only if $(E-T)\cap((T-T)\setminus\{0\})=\emptyset$.
(b) All such constraints over all partitions together say exactly this: the multiset $\bigcup_{i,j}(P_i-P_j)\setminus\{0\}$ has no repeats, i.e. $r_{A-A}(v)\le1$ for $v\ne0$. (This is equivalent to Sidon.)
(c) Continuum consequence. Let $A_n$ have $D=Cn^2$ and profile $h=\sum_i h_i$ (weak limit of the normalised counting measure of $A_n/D$). For every window $W$ of differences and every family of class pairs, the counting constraint $\sum_{(i,j)}|(P_i-P_j)\cap DW|\le D|W|$ has limit $\frac1C\int_W\sum_{(i,j)}h_i*\tilde h_j\le|W|$. This is implied by $h*\tilde h\le C$, which in turn follows from $\|h\|_2^2\le C$.
Hence the B3 profiles $h_\alpha$, with $\|h_\alpha\|_2^2<\infty$ and $C\ge C_h$, satisfy every level-3 positioned counting constraint.
**Beyond.** B3 was stated for pair constraints. This shows the proposed level-3 triple constraints add nothing at the profile level, so the A2 route (triple constraints, then dual certificates, then limit inequalities) cannot beat B3 unless it uses non-density information.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard: Sidon ⇔ r_{A-A}(v)≤1 for v≠0 (e.g. Halberstam–Roth, Sequences, Ch. II; O'Bryant's Sidon bibliography); (c) is Cauchy–Schwarz h*h̃ ≤ ||h||_2^2", "why": "Parts (a)–(b) are algebraic rewritings of the definition of a Sidon set (distinct nonzero differences), and (c) is the weak limit of the resulting counting bound plus Cauchy–Schwarz, so 'level-3' constraints collapse to the pairwise ones already covered by B3. It is a useful internal route-pruning note but not a new or significant result.", "panel": [{"verdict": "routine", "cite": "Standard: Sidon ⇔ r_{A-A}(v)≤1 for v≠0 (e.g. Halberstam–Roth, Sequences, Ch. II; O'Bryant's Sidon bibliography); (c) is Cauchy–Schwarz h*h̃ ≤ ||h||_2^2", "significance": 0, "why": "Parts (a)–(b) are alg`
**Proof or evidence.**

(a) Suppose $y\in E$ and $y+t_3=t_1+t_2$ with $t_i\in T$. Since $y\notin T$, $y\ne t_1,t_2$. Then $y-t_1=t_2-t_3$, and $t_2\ne t_3$ (otherwise $y=t_1$). So this is a nonzero difference shared by $E-T$ and $T-T$. Conversely, any $y-t_1=t_2-t_3\neq0$ gives $y+t_3=t_1+t_2$ with $\{y,t_3\}\ne\{t_1,t_2\}$, because $y\notin T$.
(b) $a-b=c-d\ne0$ with $(a,b)\ne(c,d)$ is a nontrivial additive quadruple, whatever classes $a,b,c,d$ lie in.
(c) The number of pairs $(a,b)\in P_i\times P_j$ with $a-b\in DW$ is $n^2\int_W h_i*\tilde h_j\,(1+o(1))$. By (b) these differences are distinct across all class pairs, so the constraint is $n^2\int_W\sum h_i*\tilde h_j\le D|W|(1+o(1))$, i.e. $\int_W\sum h_i*\tilde h_j\le C|W|$. The left side is $\le\int_W h*\tilde h\le|W|\,\|h\|_2^2$, by Cauchy–Schwarz $h*\tilde h(v)\le\|h\|_2^2$. So it holds once $C\ge\|h\|_2^2$. ∎ (This is the same budget as the local-energy constraint, which gives $\|h\|_2^2\le C$.)

## [valid-routine] r2s4/C1 PROVED NEGATIVE
**Statement.** Let $p\ge5$ be prime and $\eta>0$. Let $L$ be an even integer with $(3+\eta)p\le L\le(3+\eta)p+2$, and set $A=\{a_i=i+L j_i:0\le i<p\}$ with $j_i=i^2\bmod p\in[0,p)$. Then all of the following hold.
- (a) $A$ is Sidon and $n=|A|=p$.
- (b) $\min A=0$ and $D=\max A\le(p-1)(L+1)$, so $D/n^2\le3+\eta+3/p$.
- (c) $\gcd(A-A)=1$.
- (d) Let $J=[2p-1,\,L-p]$, so $|J|=L-3p+2\ge\eta p+2$. For every $T\subseteq A$, no $y$ with $y\bmod L\in J$ lies in $A+A-A\supseteq T+T-T$. Hence, for $x\ge L-1$, $T_x=A\setminus[0,x]$ and $q\le|J|$:
  - $|[0,x]\setminus(T_x+T_x-T_x)|\ge\lfloor (x+1)/L\rfloor|J|\ge\frac{\eta}{2(4+\eta)}(x+1)$;
  - each residue class $r\bmod q$ contains at least $\lfloor (x+1)/L\rfloor\lfloor |J|/q\rfloor$ such holes.
- (e) $|E_x|=|A\cap[0,x]|\le2(\lfloor x/L\rfloor+1)$. So the loading is $\lambda(x)=|E_x|n/x\le 2/3+2p/x\le 4/3$ for $x\ge 3p$.
- (f) $Q(A)\ge(p/4-1)(1+\eta)^2p^2/t\sim(1+\eta)^2p/2\to\infty$, where $t=p(p+1)/2$.

Consequently, for every $C_0>3$, no lemma of either of the following forms holds.
- "For Sidon $A$ with $D\le C_0n^2$ and $\gcd(A-A)=1$ (and even with hole counts taken in each residue class mod $q$ for all $q\le \eta n$), $|[0,x]\setminus(T_x+T_x-T_x)|\le K x/n$ at many dyadic scales."
- Any Chebyshev hypothesis of the r1s1/C1 type "$V_x(\mu)\le K^2\mu^2 x/n$ for some $\mu>0$". Here $V_x(\mu)=\sum_{y\le x}(R_x(y)-\mu)^2\ge\mu^2|\{R_x=0\}|\ge\mu^2c_\eta x$. (Caveat: this assumes $H(K)$ has that form; the round-1 text was truncated.)
**Beyond.** r1s1/C2 gave holes only from a global modulus (2 or M) and needed $C_0\ge M$. A gcd or mod-$q$ normalisation removes that example. Here the holes come from a modulus $L\asymp n$. They survive gcd normalisation and every mod-$q$ normalisation with $q\le\eta n$, at bounded $C_0=3+\eta$, and on an unloaded set. This answers the lead's question "do dense families carry residue structure that breaks normalised lemmas?": yes, at $C_0>3$.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Erdős–Turán 1941 (J. London Math. Soc. 16), construction a = 2pk + (k^2 mod p); here with coordinates swapped and spacing L≈(3+η)p", "why": "This is the classical Erdős–Turán two-digit Sidon construction, and the holes in A+A−A modulo L follow at once from bounding the low digit, so no expert would call it new. It usefully kills one internal lemma shape for C_0>3, but it neither touches CORE for C_0≤3 nor bears on #153 directly.", "panel": [{"verdict": "routine", "cite": "Erdős–Turán 1941 (J. London Math. Soc. 16), construction a = 2pk + (k^2 mod p); here with coordinates swapped and spacing L≈(3+η)p", "significance": 1, "why": "This is the classical Erdős–Turán two-digit Sidon construction, and the holes in A+A−A modulo L follow at once f`
**Proof or evidence.**

- (a) Suppose $a_i+a_k=a_{i'}+a_{k'}$.
  - Since $i+k,\,i'+k'\in[0,2p-2]$ and $2p-2<L$, reducing mod $L$ gives $i+k=i'+k'$, and then $j_i+j_k=j_{i'}+j_{k'}$.
  - Mod $p$: $i+k\equiv i'+k'$ and $i^2+k^2\equiv i'^2+k'^2$, hence $ik\equiv i'k'$. So $\{i,k\}$ and $\{i',k'\}$ are the root multisets of the same quadratic over $\mathbb F_p$, so they agree mod $p$.
  - Since all indices lie in $[0,p)$, they agree as integers. The $a_i$ are distinct, because $i$ is recovered as $a_i \bmod L$.
- (b) $a_0=0$, and $a_i\le(p-1)+L(p-1)$. So $D/p^2\le (L+1)/p\le 3+\eta+3/p$.
- (c) $a_1=1+L$ and $a_2=2+4L$ (valid since $4<p$).
  - $\gcd(a_1,a_2)$ divides $a_2-4a_1=-2$.
  - $a_1$ is odd because $L$ is even, so $\gcd=1$, and $\gcd(A-A)$ divides it.
- (d) Any $a_{i_1}+a_{i_2}-a_{i_3}=u+Lk$ has $u=i_1+i_2-i_3\in[-(p-1),2p-2]$.
  - So its residue mod $L$ lies in $[0,2p-2]\cup[L-p+1,L-1]$, which is disjoint from $J$ because $L-p\ge 2p-1$.
  - Each full block $[mL,(m+1)L)\subseteq[0,x]$ contains the run $mL+J$ of $|J|$ consecutive integers. That run contains $\ge\lfloor|J|/q\rfloor$ elements of each class mod $q$.
  - There are $\ge\lfloor (x+1)/L\rfloor\ge (x+1)/(2L)$ full blocks, and $|J|/L\ge \eta p/((3+\eta)p+2)\ge\eta/(4+\eta)$.
- (e) $a_i\le x$ forces $j_i\le x/L$. Each value $j$ has at most 2 square roots mod $p$, and the indices are in $[0,p)$.
- (f) Every sum lies in some block $[mL,mL+2p-2]$, and each block holds $\le 2p-1$ sums.
  - So at least $B\ge t/(2p-1)\ge p/4$ blocks are occupied.
  - Consecutive occupied blocks are separated by a gap $\ge L-(2p-2)\ge(1+\eta)p$.
  - Hence $\sum d_i^2\ge(B-1)(1+\eta)^2p^2$.

Computer check (holes2.py): Sidon, gcd=1 and $D/n^2$ were confirmed for $p=53,101,199$ ($\eta=1$) and $p=101$ ($\eta=0.3$). The hole fraction in $[0,D/2]$ is 0.67–0.86, at least the band prediction of about 0.25. The minimum per-class hole density mod $q\in\{2,3,5,7,11\}$ is 0.67–0.86.

## [unjudged] r2s3/C1 PROVED OTHER
**Statement.** The exact minima are:
- $f(3)=4/3$, attained by (0,1,3);
- $f(4)=9/5$, attained by (0,1,4,6);
- $f(5)=14/5$, attained by (0,1,4,9,11);
- $f(6)=74/21$, attained by (0,1,4,10,15,17);
- $f(7)=9/2$, attained by (0,1,4,10,18,23,25);
- $f(8)=11/2$, attained by (0,2,5,16,22,23,31,35);
- $f(9)=254/45$, attained by (0,1,5,12,25,27,35,41,44) and its mirror image (two minimisers).

Also $f(10)\le 376/55$, attained by (0,1,9,14,24,35,41,53,57,60) and its mirror (0,3,7,19,25,36,46,51,59,60).
**Beyond.** r1s3/C2 had no definitions and no exact values. These are the first exact values of the Lean $f$.
**Referee.** `{"error": "claude -p returned an error result (engine-referee): None: {\"type\":\"system\",\"subtype\":\"init\",\"cwd\":\"/Users/nicolas.kudeba/workspace/erdos-harness\",\"session_id\":\"627c2006-3820-4675-a978-b056f3844ef1\",\""}`
**Adversary.** `{"error": "claude -p returned an error result (engine-adversary): None: {\"type\":\"system\",\"subtype\":\"init\",\"cwd\":\"/Users/nicolas.kudeba/workspace/erdos-harness\",\"session_id\":\"7afcefed-0683-4496-8cda-e6083530cb6d\""}`
**Proof or evidence.**

- A DFS runs over all Sidon sets containing 0, adding elements in increasing order. Sidon-ness is tested through a difference bitmask.
- Pruning 1 (exact_small.py): $D\le\lfloor\sqrt{Q^*t(t-1)/4}\rfloor+1$, which is valid since $\sum g=2D$ over $t-1$ gaps gives $Q\ge4D^2/(t(t-1))$. Ties are kept.
- Pruning 2 (exact_bb.py), the edge bound. If $P=A\cap[0,x]$ with $x=\max P$, then $(A+A)\cap[0,x]=(P+P)\cap[0,x]$, because a sum $\le x$ has both summands $\le x$. So the gaps there are already fixed.
  - Let $c$ be the number of those sums and $s^*$ the largest of them.
  - The remaining $t-c$ gaps sum to $2D-s^*\ge 2x-s^*$.
  - So $Q\ge\big(G_{in}+(2x-s^*)^2/(t-c)\big)/t$, and the search prunes when this exceeds $Q^*$.
- Both runs give identical $f(9)$ and identical minimisers. $f(3..8)$ come from run 1, which completed.

## [broken] r1s3/C2 PROVED OTHER
**Statement.** For 7 <= n <= 12 and D = floor(1.1n^2), the exact maximal two-ended edge mass at x = D/8 is 2.8–3.4 times
the uniform value 2nx/D, and 70–80% of the absolute ceiling 2G(x).
**Beyond.** this answers the TEST, negatively as evidence. At these n, D_min(n)/n^2 ≈ 0.55–0.66, so the constraint
D <= 1.1n^2 has about 70% slack, and loading below delta0·D is trivially attainable. It says nothing about the
asymptotic regime (B8).
**Referee.** `{"valid": false, "first_error": "No proof or computation is supplied for the asserted exact maxima (n=7..12), and the functional ('two-ended edge mass', G(x), uniform value 2nx/D) is undefined, so the 2.8–3.4x and 70–80% figures are unverifiable. Additionally, the side claim D_min(n)/n^2 ≈ 0.55–0.66 is wrong: optimal Golomb ruler lengths 25,34,44,55,72,85 give ratios ≈0.51–0.60.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "Taking A ⊂ [0,D], edge mass = |A∩[0,x]|+|A∩[D−x,D]|, G(x) = largest Sidon set in a window of length x (definitions assumed; the claim does not state them). For n=7: D=53, x=6.625, each window is {0..6}, G=4, 2G=8, uniform value 1.75. Sidon forces C(a,2)+C(b,2) ≤ 6 for the a, b points in the two windows. a+b=6 requires a=b=3 with the differences 1..6 split into two triples {p,q,p+q}, which is impossible. So the max edge mass is ≤5, i.e. 62.5% of 2G (83% under the [1,D] convention). The claimed 70–80% would need 6, which is impossible. The ratio 2.86x uniform fits the claim, but the percentage-of-ceiling claim fails at n=7. Only n=7 was checked.", "severity": "fixable"}`
**Proof or evidence.**

(none)

## [broken] r2s2/C2 PROVED NEGATIVE
**Statement.** Let A = ⊔_{j=1}^K (M·S_j + r_j), where {r_j} is a Sidon set mod M (so A is Sidon iff each S_j is Sidon and the S_j−S_j are pairwise disjoint off 0). Then D(A)/n² ≥ (K+1)L/(2(2L+n)) = (K+1)/4 − o(1), where L = max diam S_j.
**Beyond.** Bounded C forces boundedly many residue-separated pieces, so C1 applies to residue gluing of Singer pieces.
**Referee.** `{"valid": false, "first_error": "Final step '(K+1)L/(2(2L+n)) = (K+1)/4 − o(1)': this needs n = o(L), which is never shown and fails in general. With singleton pieces (K = n, L = 0), e.g. any Sidon set with M > 2 max A, the proved bound is 0 while the claimed asymptotic asserts D/n² ≳ (n+1)/4. The steps up to the inequality D/n² ≥ (K+1)L/(2(2L+n)) are correct; D ≥ ML is unjustified but true, since D ≥ Σgaps = 2·diam A ≥ 2ML.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The inequality D/n^2 >= (K+1)L/(2(2L+n)) is valid, but '= (K+1)/4 - o(1)' needs n = o(L), which fails for unbounded K. Counterexample: a Singer Sidon set {r_j} mod M ~ K^2 with all S_j = {0}. Then n = K, L = 0, D = diam(A+A) <= 2M ~ 2K^2, so D/n^2 = O(1) while (K+1)/4 -> infinity. Any family with L = O(n) (e.g. K >= sqrt(L) pieces of size ~sqrt(L)) also fails. With K bounded, n^2 <= K(2L+n) gives n = O(sqrt(KL)) = o(L), and the asymptotic holds.", "severity": "fixable"}`
**Proof or evidence.**

- The nonzero differences of all the S_j are distinct and lie in [−L,L], so Σn_j(n_j−1) ≤ 2L.
- Cauchy–Schwarz gives n² ≤ KΣn_j² ≤ K(2L+n).
- D ≥ M·L.
- Sidon mod M forces the K(K+1)/2 sums r_i+r_j (i≤j) to be distinct, so M ≥ K(K+1)/2. ∎

## [broken] r2s3/C2 PROVED NEGATIVE
**Statement.** The minimiser of Q among Sidon n-sets need not have minimal diameter. For n=8 the optimal Golomb ruler (0,1,4,9,15,22,32,34) (D=34) has Q=17/3, while f(8)=11/2 is attained only at diameter 35. For n=10 the known optimal ruler (0,1,6,10,23,26,34,41,53,55) has Q=378/55, which is above 376/55, attained at D=60.
**Beyond.** It rules out the heuristic "dense ⇒ small Q" at the level of exact extremals. The boundary arrangement matters more than total density.
**Referee.** `{"valid": false, "first_error": "The headline claim f(8)=11/2, attained only at diameter 35, has no exhibited witness (no Sidon 8-set of diameter 35 with squared-gap sum 198 is given) and no shown exhaustive search for minimality and the 'only' clause (reducible to diameter <= 42, but not stated or shown). It rests solely on unseen script output. The n=10 set with Q=376/55 at D=60 is likewise not exhibited. The explicit values Q=17/3 and Q=378/55 for the optimal rulers are correct.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

direct exact evaluation (exact10.py, exact_bb.py).

## [broken] r2s4/C2 PROVED STRUCTURE
**Statement.** Let $A$ be Sidon, $E\subseteq A$ and $T=A\setminus E$. Put $R_A(y)=\#\{(a_1,a_2,a_3)\in A^3:a_1+a_2-a_3=y\}$. If $y\notin E$ and $y\notin T+T-T$, then $y\notin A$ and $R_A(y)\le 4|E|$; more precisely, $R_A(y)\le\sum_{e\in E}\big(2\cdot1_{y-e\in A-A}+r_{A+A}(y+e)\big)$. Hence
$$[0,x]\setminus(T_x+T_x-T_x)=E_x\ \sqcup\ Z_x,\qquad Z_x\subseteq\{y\in[0,x]\setminus A:\ R_A(y)\le4|E_x|\}.$$
In particular, $Z_x=\emptyset$ whenever $R_A>4|E_x|$ on $[0,x]\setminus A$. Also $E_x\subseteq$ holes always, by Sidon.
**Beyond.** This is the correct normalisation the lead asked for. Holes are measured against $R_A$, i.e. relative to $A+A-A$, not against residues mod $q$. It explains every example:
- for $2\cdot$Singer, $M\cdot S$ and C1, $Z_x$ is the set of zeros of $R_A$;
- for Singer and Ruzsa, $Z_x=\emptyset$ (see Data).

It also shows the limits of the route. The information "$E\cap(T+T-T)=\emptyset$" forces nothing beyond $E$ itself except at points where $R_A$ is already small. So the hole route reduces to bounding $|E_x|$ directly, which is the open edge condition (compare r1s2/C1).
**Referee.** `{"valid": false, "first_error": "The 'Hence' step: applying the lemma to the truncated set A_x=A∩[0,x] (with E_x, T_x) only bounds R_{A_x}(y), not R_A(y). Triples a1+a2-a3=y∈[0,x] can use elements of A larger than x. Counterexample: A={0,1,5,20,22} (Sidon), x=6, E=∅. Then T_x={0,1,5}, and 3∉T_x+T_x-T_x, so 3∈Z_x. But 5+20-22=3 gives R_A(3)≥2>0=4|E_x|. The untruncated lemma itself (R_A(y)≤Σ_e(2·1_{y-e∈A-A}+r_{A+A}(y+e))≤4|E|) is correct.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The core lemma (y∉E, y∉T+T−T ⇒ y∉A and R_A(y)≤Σ_e(2·1_{y−e∈A−A}+r_{A+A}(y+e))≤4|E|) is correct, but the truncated corollary is not: y∉T_x+T_x−T_x does not imply y∉T+T−T, since triples may use elements of A above x. Counterexample: A={0,1,4,6} (Sidon), E=∅, x=3. T_3={0,1}, T_3+T_3−T_3={−1,0,1,2}, so Z_3={3}, yet R_A(3)≥1 via 3=4+0−1, violating R_A(3)≤4|E_3|=0. The 'in particular' also fails: R_A(2)≥1 (2=1+1−0) and R_A(3)≥1, so R_A>0 on [0,3]\\A, but Z_3≠∅. Fix: use R_{A_x} (A_x=A∩[0,x]) in place of R_A, or define holes via the untruncated T+T−T intersected with [0,x].", "severity": "fixable"}`
**Proof or evidence.**

- If $y\in T$, then $y=y+y-y\in T+T-T$. So $y\notin A$.
- Every triple counted by $R_A(y)$ then has a coordinate in $E$. Count by position:
  - $a_1=e$: then $a_2-a_3=y-e\neq0$ (because $y\ne e$). Sidon gives at most one ordered pair with a given nonzero difference: $a_2-a_3=a_2'-a_3'$ gives $a_2+a_3'=a_2'+a_3$, so $\{a_2,a_3'\}=\{a_2',a_3\}$; $a_2=a_3$ would mean difference 0, so $a_2=a_2'$.
  - $a_2=e$: same, at most one.
  - $a_3=e$: $a_1+a_2=y+e$ has $r_{A+A}(y+e)\le2$ ordered solutions.
- Summing over $e$ gives $\le4|E|$.

Checked numerically: no violation at any scale in any family below.

## [not validated] r2s4/C3 CONJECTURED OTHER
**Statement.** Two computational statements.
- (i) For lifted Singer sets ($q=31,47,71$, best rotation, $D/n^2\approx0.86$–$0.92$) and lifted Ruzsa sets ($p=101,199$), the hole set of $T_x+T_x-T_x$ in $[0,x]$ equals $E_x$ exactly, at all dyadic $x\in[n,D/8]$ (Singer) and $x\in[n,0.65D]$ (Ruzsa).
- (ii) For $A=2S\cup\{a_0\}$ ($S$ Singer, $a_0$ the largest odd number $<2D_S$ outside $S+S$), we have $\gcd(A-A)=1$ and $D/n^2\approx1.72$–$1.79$. About half of all odd $y\le x$ are holes for $x\le D/16$, while $\lambda\le1$.
**Beyond.** - (i) answers the lead's question for Singer and Ruzsa: they carry no residue structure that breaks the relative ($R_A$) normalisation. Bose sets are untested.
- (ii) would lower the gcd-normalised failure threshold from $C_0>3$ (C1, proved) to about 1.8, though such sets are defeated by mod-2 local-density normalisation.

PROOF/EVIDENCE: holes.py and holes2.py, with exact FFT triple counts (tables in Data). Mechanism for (i): cyclically, $R_S(y)=q+1$ for $y\notin S$, so C2 gives $Z=\emptyset$ when $|E|<(q+1)/4$. The integer lift loses about half the representations but stays far above $4|E_x|$ at small $x$. Mechanism for (ii): the odd part of $T+T-T$ lies in $(a_0+2(S-S))\cup(2(S+S)-a_0)$, which covers about half the odds. No rigorous density bound has been proved.
**Proof or evidence.**

(none)

## Frontier map

Q$ over Sidon sets of size $n$; the Lean encoding is faithful (the set is nonempty and $Q\ge0$) | standard / blackboard | direct check
- $Q(A)\ge 4D^2/(t(t-1))\ge 16D^2/(n(n+1))^2$; hence $Q\to\infty$ whenever $D/n^2\to\infty$ | Dutta, forum, Feb 2026 | Cauchy–Schwarz on $\sum d_i=2D$
- Lindström: $A\subset[1,N]$ Sidon implies $|A|<N^{1/2}+N^{1/4}+1$. Improved constants: $0.998N^{1/4}$ (Balogh–Füredi–Roy) and $0.99703N^{1/4}$ (O'Bryant), constants as I recall them. Consequence: $D\ge n^2-(2+o(1))n^{3/2}$, so $f(n)\ge16-O(n^{-1/2})$ | literature | counting differences
- Singer ($q+1$ elements in $\mathbb Z_{q^2+q+1}$), Bose ($q$ in $\mathbb Z_{q^2-1}$) and Ruzsa ($p-1$ in $\mathbb Z_{p(p-1)}$) are perfect or relative difference sets. They have flat spectrum: $|\hat S(\xi)|^2=q$ for Singer, $\xi\ne0$. A suitable rotation gives Sidon sets with $D\le n^2$ | Singer 1938, Bose 1942, Ruzsa 1993 | finite fields
- Equidistribution of Singer sets: every interval $I\subset\mathbb Z_m$ satisfies $|S\cap I|=(q+1)|I|/m+O(m^{1/4}\log m)$ | standard | flat spectrum plus the Erdős–Turán discrepancy inequality
- Local energy: $\sum_y|A\cap[y,y+L)|^2\le nL+L^2$ | standard (Erdős–Turán) | each nonzero difference occurs at most once
- Shifted energy: $\sum_x r(x)r(x+k)\le n^2+n$ for $k\ne0$. For Sidon sets the exact identity is $\sum_x r(x)r(x+k)=|(A-A)\cap(A-A+k)|+2n\,1_{A-A}(k)$ | blackboard (unverified) / standard | expanding quadruples
- Maximal Sidon sets ($|A|\sim\sqrt N$) are equidistributed in $[1,N]$ at macroscopic scales | Erdős–Freud, Lindström; Pikhurko (limit form) | second-moment slack goes to 0
- Edge sums are counted exactly: with $\min A=0$, $|(A+A)\cap[0,x]|=A(x)(A(x)+1)/2$ | standard | sums $\le x$ use only elements $\le x$
- Dyadic Cauchy–Schwarz: the window $[x/2,x]$ contributes $\ge (x/2)^2/(N(x)+1)$ to $\sum d_i^2$. Writing $\lambda=nA(x)/x$, this is about $\lambda^{-2}$ per window in $Q$ | blackboard | intersected gaps
- If $D\le(1+\delta)n^2$ and $n\ge8/\delta^2$, then $|A\cap[0,x]|\le8x/n$ for $\delta n^2\le x\le n^2/1000$, and $Q\ge c\log(1/\delta)-C$. Hence $Q\to\infty$ when $D/n^2\to1$ | leon2k2k2k corrected note (May 2026); harness variant 2 | local energy plus dyadic Cauchy–Schwarz
- Combining these, the open case is $D/n^2\in[1+\delta_0,C_0]$ | blackboard | combination
- The mean gap is $2D/(t-1)\approx4D/n^2=O(1)$ in the open range. So divergence of $Q$ must come from an $o(1)$ fraction of gaps | standard | averaging
- A constant gain $Q\ge16+\eta$ (claimed $33/2$) | harness warm-up 1, unverified | shift-4 near-invariance is impossible
- The forum's "short proof" relied on Bloom's bound $|(A+A)\cap(A+A+d)|\le2n^{3/2}$. Bloom has said the bound is false, and the proof was withdrawn | forum, May 2026 | —
- Infinite Sidon sequences: $\liminf A(x)\sqrt{\log x/x}<\infty$ (Erdős); $\limsup A(x)/\sqrt x\ge1/\sqrt2$ (Krückeberg); there exist sequences with $A(x)\ge x^{\sqrt2-1-o(1)}$ (Ruzsa 1998) | literature | multiscale difference counting; construction via discrete logarithms
- The number of Sidon subsets of $[N]$ is $2^{\Theta(\sqrt N)}$ | Kohayakawa–Lee–Rödl–Samotij | hypergraph containers
- Sizes of $B_2[g]$ sets via autoconvolution constants and continuous limit profiles | Cilleruelo–Ruzsa–Vinuesa 2010 | constructions realising profiles
- Structure results for near-extremal Sidon sets | Eberhard–Manners, "apparent structure of dense Sidon sets"; details unverified | Fourier
- Erdős's question whether every finite Sidon set lies in a perfect difference set (#707) has reportedly been answered negatively, e.g. by $\{1,2,4,8,13\}$ (Alexeev–Mixon 2025; verify) | literature | exhaustive or algebraic exclusion
- [ESS94] (Erdős–Sárközy–Sós, sum sets of Sidon sets) is the source of the problem and has related results on the block and gap structure of $A+A$ (#152). Exact statements not verified here | literature | —
- Continuum heuristic: for a random-like profile $h$ (so $\mu=h\,du$ on $[0,1]$ and $D\sim C'n^2$), $Q\approx4\kappa C'^2\int_0^2du/(h*h)(u)$, where $\kappa\in[1,2]$ is the local ratio $E[d^2]/E[d]^2$. A uniform $h$ gives $Q\asymp\log n$ | blackboard plus my check | Riemann sum of windowed Cauchy–Schwarz

=== BARRIERS
- **B1, the counting ceiling.**
  - What it is: $A(x)\le\sqrt x+O(x^{1/4})$ only gives $\lambda_j\le2^{j/2}\sqrt C$, which makes $\sum_j\lambda_j^{-2}$ convergent.
  - What it defeats: every edge argument that uses only $|A\cap[0,x]|$ or Erdős–Turán bounds.
  - What it does not rule out: structural inputs.
- **B2, second-order slack.**
  - What it is: for $D=Cn^2$ the local energy has slack $(1-1/C)L^2$ at every scale. That slack pays for constant-factor end-loading, and for any loading $K_j$ at dyadic scale $j$ with $\sum_j K_j^22^{-j}\lesssim C-1$.
  - What it defeats: Pikhurko-type uniformity, window second moments, shifted energies of sums or differences, and density bounds for sums and differences.
  - What it does not rule out: third- and higher-order constraints, such as $A$ avoiding $T+T-T$ (with $T$ the rest of $A$), or algebraic rigidity.
- **B3, the continuum-profile barrier (my calculation; it should be written up).**
  - What it is: take $h_\alpha(u)=c(u^{-\alpha}+(1-u)^{-\alpha})$ with $0<\alpha<1/2$, or even $h\sim\log^{0.6}(1/u)$ near each end. Then:
    - $\|h\|_2^2<\infty$;
    - $h*h\le\|h\|_2^2$;
    - every pair constraint holds for $C\ge C_h$;
    - yet $\int_0^2du/(h*h)<\infty$, because $h*h\asymp u^{1-2\alpha}$ at the ends.
  - What it defeats: any argument that sees only macroscopic profiles plus pairwise (sum or difference) constraints.
  - What it does not rule out: arguments that exclude unbounded end profiles by higher-order or algebraic structure.
- **B4, Erdős's multiscale argument.**
  - What it is: it gives a contradiction only when $A(x)\ge c\sqrt x$ on more than $1/c^2$ scales. The loading needed for a counterexample, $\lambda\sim(\log D/x)^{1/2+\epsilon}$, is far below $\sqrt x$, and the per-scale sums of self-differences converge geometrically.
  - What it defeats: the G3 route (finite Erdős lim-inf).
  - What it does not rule out: arguments using exact coincidences.
- **B5, short-gap counting.**
  - What it is: for Singer-type sets, $|S\cap(S+k)|\approx t/2$ for every small $k$, and most gaps really are $O(1)$.
  - What it defeats: every "most gaps are long" approach. Bloom's claimed bound is false.
  - What it does not rule out: rare long gaps at the two ends.
- **B6, the cyclic barrier.**
  - What it is: in $\mathbb Z_m$ the Singer sumset has exactly flat pair correlations and density $1/2$, so its cyclic $Q$ is plausibly bounded (about 6).
  - What it defeats: translation-invariant arguments that do not see the boundary.
  - What it does not rule out: edge-based arguments.
- **B7, the construction barrier for FALSE.**
  - What it is:
    - all known dense Sidon sets are algebraic and Fourier-flat, hence uniform at scales $\ge n^{3/2+\epsilon}$, so $Q\gtrsim\log n$;
    - random or greedy constructions reach only $N^{1/3}$, or $x^{\sqrt2-1}$, so $D/n^2\to\infty$;
    - a dense set cannot be augmented, because $A+A-A$ covers the ambient interval;
    - single-element local moves are frozen.
  - What it defeats: counterexample searches built from known families or local moves.
  - What it does not rule out: unknown non-algebraic dense Sidon sets.
- **B8, finite computation.**
  - What it is: growth of order $\log n$ cannot be told apart from bounded growth for $n\le10^4$.
  - What it defeats: deciding the problem by computation.
  - What it does not rule out: computation that guides structure, such as extremal edge loading at small $n$.

=== CORE
**What remains.** For every fixed $C_0>1$,
$$\inf\{Q(A):A\text{ Sidon},\ |A|=n,\ D(A)\le C_0n^2\}\to\infty.$$
The cases $D/n^2\to1$ and $D/n^2\to\infty$ are done. The classes are nested, so there is a threshold $C^*\in[1,\infty]$ with CORE true for $C<C^*$, and CORE is the statement $C^*=\infty$. Nothing better than $C^*\ge1$ is known.

**Why it is hard.**
- The mean gap is bounded, so divergence must come from rare long gaps, essentially at the two ends of $[0,2D]$.
- The edge sum counts are exactly $A(x)(A(x)+1)/2$. So the edge route needs: at one end, at a non-square-summable set of dyadic scales, $A(x)\lesssim x/n$ up to a constant.
- B1, B2 and B3 show this lies beyond every pairwise inequality.
- A proof therefore needs a rigidity theorem for Sidon sets of size $c\sqrt N$ with $c<1$. No stability or inverse theory exists in this regime.
- A disproof needs a Sidon set of a kind nobody knows how to build.

=== TARGET T1
TYPE: QUANT
STATEMENT: $\liminf_{n\to\infty}f(n)\ge18$.
- For $D\ge1.07n^2$ this follows from Cauchy–Schwarz ($16\cdot1.07^2>18.3$).
- For $D\le1.07n^2$ the plan has three steps:
  - prove that $A$ is uniform to within a factor $1\pm\epsilon$ at every scale $x\ge K\delta D$;
  - feed this uniformity into the dyadic windows;
  - finish with the sharp continuum lower bound $4C'^2\int du/\varphi$, where $\varphi$ is the limiting density of sums.
BEYOND: KNOWN gives $16-o(1)$, plus an unverified $33/2$. The idealised ceiling of this method is about $19.1$, at the crossing of $16(1+\delta)^2=8\log(1/\delta)$.
VALUE: It forces explicit constants in the near-maximal uniformity argument. That is the template for T4.
SIGNIFICANCE: 1
TEST: Compute $Q$ for Singer, Bose and Ruzsa sets, their random subsets and lifts for $q\le2000$. Find the exhaustive minimum of $Q$ for $n\le12$.

=== TARGET T2
TYPE: QUANT
STATEMENT:
- (a) If $D\le(1+\delta)n^2$ and $n\ge n_0(\epsilon)\delta^{-2}$, then $Q(A)\ge(8-\epsilon)\log(1/\delta)-O_\epsilon(1)$.
- (b) For Singer sets $A_q$ in an optimal rotation, $(4-\epsilon)\log q\le Q(A_q)\le C_1\log q$.
BEYOND: KNOWN has $c\log(1/\delta)$ with an unspecified crude $c$ (sparsity constant 8). No upper bound on $Q$ is proved for any family.
- In (a), the constant 8 is $4C'^2$ times twice $\int du/u$.
- The lower bound in (b) comes from Weil-range uniformity at scales $\ge m^{3/4}\log m$.
- Second moments give $Q(A_q)\lesssim\log^2q$. The bound $O(\log q)$ needs control of 3- and 4-point correlations.
VALUE: It shows that $\log$ is the true growth rate for extremal sets, which calibrates what a proof of CORE can give.
SIGNIFICANCE: 1
TEST: Compute $Q(A_q)/\log q$ for $q\le3000$ and compare with the heuristic $8\kappa$, $\kappa\in[1,2]$.

=== TARGET T3
TYPE: SPECIAL
STATEMENT: Let $A$ be Sidon with $D\le Cn^2$. Suppose that for some $m\le n^{8/3-\epsilon}$ the reduction $A\to\mathbb Z_m$ is injective with image inside a Singer or Bose set. Then $Q(A)\ge c\log n/C^2$.

Proof sketch.
- After shifting, $A\cap[0,x]$ injects into $S\cap I$ for an interval $I$ of length $x$.
- So $|A\cap[0,x]|\le(q+1)x/m+O(m^{1/4}\log m)$.
- This gives $\lambda\le C(1+o(1))$ for $x\ge m^{3/4}\log^2m$, at both ends.
- That covers about $\frac14\log_2n$ dyadic windows per end, each contributing at least $c/C^2$.

BEYOND: KNOWN lists these families only as heuristic dead ends for counterexamples. This makes them a theorem, for arbitrary subsets and arbitrary lifts.
VALUE: Every known dense construction is excluded as a counterexample. It is also the endgame for A3 and T5.
SIGNIFICANCE: 1
TEST: Run adversarial lifts (choosing representatives to front-load the ends) of Singer sets for $q\le500$ and verify the bound.

=== TARGET T4
TYPE: SPECIAL
STATEMENT: There is an absolute $\delta_0>0$ such that $Q(A)\to\infty$ uniformly over Sidon sets with $D\le(1+\delta_0)|A|^2$. Equivalently, $C^*>1$.
BEYOND: KNOWN needs $D/n^2\to1$. For fixed $\delta_0$ it gives only $Q\ge c\log(1/\delta_0)-C$, which is bounded.
VALUE: It is the first fixed-ratio case of CORE. By nesting it is the easiest case, and it must beat B2 at small slack.
SIGNIFICANCE: 3
TEST: For $n\le40$, solve exactly by ILP the maximal two-ended edge mass at $D=\lfloor1.1n^2\rfloor$. Check whether loading below scale $\delta_0D$ is actually attainable.

=== TARGET T5
TYPE: CONDITIONAL
STATEMENT: Assume the hypothesis SEB (Sidon edge boundedness): there are $\epsilon>0$ and $M=M(C)$ such that every Sidon set $A\subset[0,D]$ with $D\le Cn^2$ satisfies $|A\cap[0,x]|\le Mnx/D$ for all $x\in[Dn^{-\epsilon},D]$, or the mirror statement at $D$. Then $Q(A)\ge c\,\epsilon\log n/(M^2C^2)$, which implies CORE.

No standard named conjecture (GRH, Hardy–Littlewood, abc, ...) is known to bear on CORE; the problem is purely additive-combinatorial. SEB is the natural named structural input:
- it holds for the algebraic class with $\epsilon<1/2$ (see T3);
- it would follow from a robust quantitative form of Erdős's extension question (#707), with $o(n)$ deletions allowed.

The implication is the dyadic Cauchy–Schwarz over $\epsilon\log_2n$ windows.
BEYOND: There is no conditional result of any kind in KNOWN.
VALUE: It isolates exactly the rigidity input needed, with a quantitative conclusion.
SIGNIFICANCE: 1
TEST: Measure $\max_x nA(x)/x$ over $x\ge Dn^{-1/4}$ in best-found search outputs.

=== TARGET T6
TYPE: STRUCTURE
STATEMENT: Let $A_n$ be Sidon with $0,D_n\in A_n$, $Q(A_n)\le K$, $D_n/n^2\to C'\in[1,\infty)$, and normalised counting measures $\mu_n\to\mu$ on $[0,1]$. Then:
- (i) $\mu=h\,du$ with $\|h\|_2^2\le C'$;
- (ii) $h*h\le2C'$;
- (iii) $4C'^2\int_0^2du/(h*h)\le K$;
- (iv) $\sum_j\bigl(2^{-j}/\mu[0,2^{-j}]\bigr)^2\le K/C'^2$. Hence $\mu[0,u]/u\to\infty$ as $u\downarrow0$, and likewise at 1.

So every counterexample has a macroscopically unbounded density at both ends.

Proof outline.
- (i) Local energy with $L=\epsilon D$.
- (ii) Sums are distinct.
- (iii) Windowed Cauchy–Schwarz on a fixed partition, using that $N_I/t\to\nu(I)$, then refining the partition.
- (iv) $\nu([u/2,u])\le\mu[0,u]^2$.

BEYOND: KNOWN has finite-$n$ bounds only, and only near $C=1$. There is no description of hypothetical counterexamples.
VALUE: It reduces CORE to a question about macroscopic profiles (T7) and makes the target of any construction precise (T10).
SIGNIFICANCE: 2
TEST: Run the search of A4 and fit $\mu[0,u]/u$.

=== TARGET T7
TYPE: REDUCTION
STATEMENT: Define PEB (profile endpoint boundedness): every limit $\mu$ as in T6, without the assumption $Q\le K$, has $\liminf_{u\downarrow0}\mu[0,u]/u<\infty$, or the same at 1. Then PEB implies CORE.

Proof.
- Suppose CORE fails. Then there is a sequence with $Q\le K$.
- Pass to a subsequence with $D_n/n^2\to C'$ and $\mu_n\to\mu$.
- T6(iv) forces $\mu[0,u]/u\to\infty$ at both ends, contradicting PEB.

PEB is strictly stronger than CORE, since it ignores the microscopic scales. It is a statement at fixed macroscopic scales, and it is stable under deleting $o(n)$ elements.
BEYOND: G1 on the blackboard needs control at all scales simultaneously. PEB needs only the macroscopic limit and allows robust, structural tools.
VALUE: A robust inverse theorem for dense Sidon sets would now suffice.
SIGNIFICANCE: 2
TEST: none

=== TARGET T8
TYPE: NEGATIVE
STATEMENT: Let $h_\alpha=c(u^{-\alpha}+(1-u)^{-\alpha})$ with $\alpha\in(0,1/2)$. Then:
- $\|h_\alpha\|_2^2<\infty$;
- $h_\alpha*h_\alpha\le\|h_\alpha\|_2^2$;
- $\int_0^2du/(h_\alpha*h_\alpha)<\infty$.

For $C\ge C_\alpha$, the continuum versions of all of the following hold:
- Erdős–Turán counting at every scale;
- the local energy inequality at every scale;
- density at most 1 for sums and for differences;
- the shifted energy bound.

Hence no proof of CORE can use only these inequalities together with dyadic or windowed Cauchy–Schwarz. The same holds for $h\sim\log^{\beta}(1/u)$ with $\beta>1/2$.
BEYOND: It formalises why warm-up variant 3 and G1 stalled. KNOWN records these routes as dead ends without a proof of impossibility.
VALUE: It redirects effort to third-order or algebraic inputs.
SIGNIFICANCE: 1
TEST: Numerical quadrature of the stated integrals.

=== TARGET T9
TYPE: ANALOGUE
STATEMENT: For Singer sets $S_q\subset\mathbb Z_m$, the cyclic mean-square gap of $S_q+S_q$ is $O(1)$, conjecturally $\to6$.
- Second moments, via the exact flat pair correlation, give only $O(\log m)$.
- An $O(1)$ bound needs 3- and 4-point correlations of $S+S$. These reduce, via Sidon identities, to configuration counts in $S-S$, which can be bounded by character sums.
BEYOND: There is no cyclic analogue in KNOWN.
VALUE: Together with T2 it proves that the divergence for integer sets is purely an edge phenomenon. That justifies the edge focus and kills bulk-only routes.
SIGNIFICANCE: 1
TEST: Compute the cyclic $Q$ for $q\le3000$.

=== TARGET T10
TYPE: NEGATIVE
STATEMENT: There exist $C<\infty$ and Sidon sets $A_n\subset[0,D_n]$ with $0,D_n\in A_n$ and $D_n\le Cn^2$, whose limit profile satisfies $\mu[0,u]/u\to\infty$ as $u\downarrow0$. That is, the one-ended form of PEB is false.

Either outcome is valuable:
- A construction shows that any proof must couple the two ends.
- A refutation (one-ended PEB) gives CORE directly by T7.

BEYOND: Every known construction has bounded end density relative to the mean, at most a constant factor, via lifts (see T3).
VALUE: It decides which half of the dichotomy the team should attack.
SIGNIFICANCE: 2
TEST: Run the A4 search with a one-ended objective.

=== ANGLE A1
TECHNIQUE: Third-order hole counting: avoidance of $T+T-T$ plus local sixth moments. KNOWN does not use this.
IDEA: Let $E=A\cap[0,x]$ and $T=A\cap(x,D]$. If $y\in E$ and $y=t_1+t_2-t_3$, then $y+t_3=t_1+t_2$, which is impossible for a Sidon set because $y\notin T$. So $E$ lies in the zero set of $R=r_{T+T-T}$ on $[0,x]$. On $[0,x]$ the function $R$ has mean about $nx/C$, so $E$ must occupy rare holes. Bound the number of holes by Cauchy–Schwarz on the support, and control the variance of $R$ through $\sum|\hat T|^6$ localised to frequencies $\gtrsim D/x$.
BARRIERS: It is a third-order constraint, so B2 and B3 do not apply. It must beat B7-type structure: it needs near-minimal local $E_3(T)$, to relative precision about $1/n$.
FIRST STEP: Prove $|A\cap[0,x]|\le x-\bigl(\sum_{y\le x}R\bigr)^2/\sum_{y\le x}R^2$, and evaluate the right-hand side for Singer lifts. It should come out at $O(nx/D)$ for $x\ge n^{3/2+\epsilon}$.

=== ANGLE A2
TECHNIQUE: A level-3 relaxation hierarchy (Lasserre or Schrijver-type SDP, as for codes) with dual certificates, followed by flag-algebra-style limit inequalities for Sidon profiles. KNOWN does not use this.
IDEA: Pose $\max|A\cap[0,x]|+|A\cap[D-x,D]|$ as a 0/1 program with quadruple constraints. Level-1 (pair) relaxations reproduce B3, so impose the triple constraints $y\notin T+T-T$. Extract dual certificates at small $n$ and guess an analytic family. The goal is a new limit inequality forcing PEB (T7).
BARRIERS: It beats B3 only if level 3 strictly cuts off unbounded profiles, and checking exactly that is the experiment.
FIRST STEP: For $n\le30$ and $C\in\{1.5,2,3\}$, compare the ILP optimum with the level-1 and level-3 relaxation values as functions of $x/D$.

=== ANGLE A3
TECHNIQUE: Algebraic transfer: character sums (Gauss and Weil) plus a Fourier-flatness criterion.
IDEA:
- Prove T3.
- Then find a criterion of the form: if $A\bmod m$ is Sidon for some $m\in[n^2,C'n^2]$ and $\sup_{\xi\ne0}|\hat A(\xi)|\le K\sqrt n$, then $|A\cap I|\le n|I|/m+O(K\sqrt n\log n)$, hence $Q\ge c\log n/K^2$.
- Then try to manufacture such an $m$ from $A$, e.g. as a period that $A+A-A$ nearly respects.
BARRIERS: Flatness is algebraic information that B1–B5 never see. The risk is B7: a general $A$ may have no good modulus.
FIRST STEP: Prove the flatness-to-$Q$ lemma, and test whether Erdős–Turán-type sets $\{2pk+(k^2\bmod p)\}$ fit it for some $m$ (they live naturally on $\mathbb Z_p^2$).

=== ANGLE A4
TECHNIQUE: Counterexample engineering on the FALSE side, in $\mathbb Z_p\times\mathbb Z$.
IDEA: If $S\subset\mathbb Z_p\times[0,L)$ is Sidon in $\mathbb Z_p\times\mathbb Z$, then $\{u+2pv\}$, with $u\in[0,p)$ the representative of the first coordinate, is Sidon in $\mathbb Z$ with the same row profile. So FALSE reduces to Sidon "functions" $f:\mathbb Z_p\to[0,Kp)$, meaning that for every $s$ the values $f(x)+f(s-x)$ are distinct over unordered pairs, with many small and many large values. Search these by ILP or annealing using block moves, since single moves are frozen.
BARRIERS: It must beat B7, so it uses non-modular lifts. Any success refutes T4, T5 or T7 directly.
FIRST STEP: Run an ILP for $p\le60$ maximising the number of $x$ with $f(x)<\epsilon p$ or $f(x)>(K-\epsilon)p$, and compare with the lift ceiling $K$.

=== ANGLE A5
TECHNIQUE: Profile compactness (T6) plus a robust inverse theorem in the style of Eberhard–Manners, aiming at PEB.
IDEA:
- PEB is macroscopic and stable under $o(n)$ deletions.
- So it suffices to show that every Sidon $A\subset[0,Cn^2]$ agrees, up to $o(n)$ elements, with a set whose profile is bounded at one end.
- One candidate: a subset of an affine or Freiman lift of a near-maximal Sidon set in a group of order $O(n^2)$. Near-maximal sets in groups are macroscopically uniform by the cyclic local-energy argument.
BARRIERS: Deletions make the finite-configuration counterexamples to #707 irrelevant. The method must beat B3 through genuinely structural input.
FIRST STEP: Prove that the limit profile of any Sidon sequence with $C\le1+\delta_0$ satisfies $\|h-1\|_2^2\le\delta_0$ (immediate), and then that $h$ is bounded on a positive proportion of each endpoint neighbourhood.

=== ANGLE A6
TECHNIQUE: Exact correlation identities transferring $A+A$ to $A-A$, plus truncated Bonferroni inequalities on the gap generating function $\sum_i d_i^2=\sum_k(2k-1)g_k$, where $g_k$ is the number of gaps $\ge k$.
IDEA: For Sidon sets, the $\ell$-point correlations of $A+A$ reduce exactly to configuration counts in $A-A$; the pair case is the shifted-energy identity in KNOWN. Truncate inclusion–exclusion at order 3–4, localised to windows, to get lower bounds on $g_k$. Use this both for the bulk alternative G2 and for T9.
BARRIERS: Pair-level use is killed by B5. Orders 3 and 4 are new. It cannot by itself see the edges (B6), so pair it with A1 at the ends.
FIRST STEP: Derive the exact 3-point identity $\#\{x:x,x+k,x+l\in A+A\}$ in terms of $A-A$, and verify it numerically on Singer sets.

## Meta-review

=== STATE
Validated results beyond the frontier map. All three are rated routine, with significance 0.
- **r1s1/C1 (valid, routine).** This is the $T+T-T$ reduction.
  - On $E_x=A\cap[0,x]$ the count $R_x=r_{T_x+T_x-T_x}$ vanishes. This is just the Sidon property.
  - Chebyshev then gives $|E_x|\le V_x(\mu)/\min\mu^2$.
  - If the hypothesis $H(K)$ holds at $L$ dyadic scales $x_j\ge n$, then $Q\ge L/(64K^4)$.
  - $H(K)$ is strictly stronger than the open edge condition $|E_x|\lesssim K^2x/n$. It is a reformulation, not progress.
- **r1s1/C2 (valid, routine).** This is the local-obstruction example.
  - For $A=2S$ with $S$ Singer, $D/n^2<2$. Every odd $y$ is a hole of $T_x+T_x-T_x$, so $H(K)$ fails at every scale.
  - So no un-normalised hole lemma holds for $C_0\ge2$. Using $M\cdot S$ gives the same for $C_0\ge M$.
  - Positive by-product: residue separation ($T\subset2\mathbb Z$, $E\subset2\mathbb Z+1$) makes the third-order constraints $(E+T)\cap(T+T)=\emptyset$ and $(E+E-E)\cap T=\emptyset$ hold automatically.
- **r1s2/C1 (valid, routine).** Level-3 constraints collapse to pairwise ones.
  - For any partition $A=\sqcup P_i$, the condition $E\cap(T+T-T)^{\rm nontriv}=\emptyset$ is equivalent to $(E-T)\cap(T-T)\setminus\{0\}=\emptyset$.
  - Taken over all partitions, these conditions say exactly "Sidon".
  - In the continuum limit, every positioned level-3 counting constraint follows from $\|h\|_2^2\le C$. So the B3 profiles $h_\alpha$ satisfy all of them.
  - Consequence: the "third-order constraints" escape hatch listed under B2 is closed at the counting/profile level.

Broken:
- **r1s3/C2.** Exact small-$n$ edge-loading figures ($2.8$–$3.4\times$ uniform, $70$–$80\%$ of $2G(x)$).
  - The functionals were undefined and no computation was given.
  - The side claim about $D_{\min}/n^2$ was disputed.
  - The adversary showed that at $n=7$ the windows are only of length $\approx6$, so the claim is meaningless at these sizes.

Best unvalidated ideas:
- **(i) Residue-class gluing (r1s1/C2 turned positive).**
  - Place pieces $P_j=M\cdot S_j+r_j$ with residues $\{r_j\}$ forming a Sidon set mod $M$.
  - Then $A$ is Sidon if and only if each $S_j$ is Sidon and the sets $S_j-S_j$ are pairwise disjoint away from $0$.
  - This turns end-loading into a clean packing problem for difference sets: one piece bulk-uniform, the others end-loaded.
- **(ii) Where a counterexample's loading must live.**
  - If the end-loading is bounded at all scales $x\ge n^{3/2+\epsilon}$, then $Q\gtrsim\log n$.
  - So any counterexample needs unbounded loading at scales above $n^{3/2}$.
  - That is exactly where algebraic sets are uniform (B7). So a counterexample must be non-algebraic at mesoscopic-to-macroscopic scales.
- **(iii) Small-difference reformulation.**
  - Edge-loading forces $T-T$ to miss at least $|E_x|^2/2$ of the integers in $[1,x]$.
  - Lifted Singer sets miss almost none of them, since $r(d)\approx1-d/m$.
  - So an extremal $T$ must be far from Singer at small differences.
- **(iv) Pushing $C^*$ above 1.**
  - Showing $C^*>1$, i.e. CORE for $C_0=1+\delta$, would already be new.
  - The natural route is an explicit-$\delta$ stability version of the existing $D/n^2\to1$ argument.

=== LESSONS
- **Reformulation, not progress.** All three valid results only restate the problem.
  - C1 encodes the edge condition as a stronger hypothesis.
  - r1s2/C1 proves that partition-based third-order counting equals Sidon.
- **B2 and B3 bit hard, and B3 now reaches further.** It defeats every positioned counting constraint at any level, not just pairwise ones.
  - Lesson: any argument that passes to a weak-limit profile is dead on arrival.
  - A proof must use exact coincidences or arithmetic structure that does not survive the limit.
- **Local (congruence) obstructions are real.**
  - Every hole or density lemma must be normalised: $\gcd(A-A)=1$ at the least, and preferably stated relative to local densities mod small $q$.
  - We should check whether genuine dense families (Bose sets mod $q^2-1$, Ruzsa sets mod $p(p-1)$) carry residue structure that breaks even normalised lemmas.
- **The computational claim failed on rigour, not on idea.**
  - The definitions were never stated.
  - At $n\le12$ the dyadic windows are too small to say anything.
  - B8 says computation should guide structure: extremal configurations at moderate $n$. It should not produce ratio tables at tiny $n$.
- **Most alive angles:**
  - (a) the construction side, via residue gluing and difference-set packing. It is the one place where B3 says there is no pairwise obstruction, and C2 supplies an exact tool for killing cross-coincidences;
  - (b) pushing $C^*>1$ by quantitative stability. It is modest, but it would be the first improvement on the threshold and is expert-significant.

=== NEXT
1. **CORE: push $C^*>1$ by quantitative stability.**
   - Technique: redo the proof of the $D/n^2\to1$ case with every error term written explicitly in $\delta=C-1$.
   - This includes the Erdős–Turán / Lindström interval counting and the slack $(1-1/C)L^2$ from B2.
   - Aim: show that end-loading $K_j$ at the scales $x_j\ge D^{3/4}$ is forced to satisfy $K_j\le1+o_\delta(1)$, which yields $Q\to\infty$ for $C_0=1+\delta_0$.
   - First step: write the existing $C\to1$ argument as a single chain of inequalities, and mark the first line where the hypothesis $D/n^2\to1$ is used non-quantitatively.
2. **CORE (disproof side): combine r1s1/C2 with B3 into a residue-gluing construction.**
   - First step: state and prove the gluing lemma exactly. Pieces $P_j=MS_j+r_j$ with $\{r_j\}$ Sidon mod $M$ form a Sidon set if and only if every $S_j$ is Sidon and the sets $S_j-S_j$ are pairwise disjoint off $0$.
   - Then compute the forced $D/n^2$ as a function of the piece sizes and positions.
   - Then try to realise a two-class version: a bulk Bose/Singer subset plus end pieces of size about $Kx_j/n$ at dyadic scales above $n^{3/2}$, using subsets of a second algebraic Sidon set.
   - Goal: either a family with bounded $C$ and slowly growing loading (toward FALSE), or a packing lemma showing that a bulk-uniform piece with $|S-S|\approx$ (length)$/C$ leaves too few small differences. That lemma would be a non-profile obstruction.
3. **Repair r1s3/C2 as structure-guiding exact computation.**
   - Fix the definitions: edge mass $\Lambda(x)=|A\cap[0,x]|+|A\cap[D-x,D]|$ and loading $K=\Lambda D/(2nx)$.
   - Work with $C\in\{1.2,1.5,2,3\}$ and scales $x=D/2^j$ with $x\ge 2n$. This requires $n$ around 20–40, so use CP-SAT/ILP with symmetry breaking.
   - Compute the exact maximum loading at each scale, the joint maximum of $\sum_j K_j^{-2}$ minimised, and the true $\min Q$.
   - First step: verify the adversary's $n=7$ bound by hand. Then rerun at $n=20$, recording the extremal sets and their residue structure mod small primes.
4. **Push r1s1/C1–C2: the correct normalised hole lemma.**
   - Technique: restate $H(K)$ relative to local densities, with $\mu(y)$ replaced by the expected $R_x(y)$ given $A$'s distribution mod $q$ for $q\le Q_0$.
   - Test it on lifted Singer, Bose and Ruzsa sets and their cuts at all rotations. Then prove it for the Singer family using Fourier flatness, giving an explicit constant in $Q\gtrsim\log n$.
   - First step: compute the distribution mod $q\pm1$ of Bose sets mod $q^2-1$, to see whether a genuine $C\approx1$ family already defeats the normalised lemma, as $2S$ did for the un-normalised one.
