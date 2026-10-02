# NOTEBOOK deep: glitch threshold beyond 2/3

## Result
SUMMARY: unconditional glitch threshold 2/3 → **3/4** (C1). Beyond 3/4: **θ<5/6 ⇒ liminf q_n/n² ≥ 2**, and θ<3/4+5^{1−A}/20 ⇒ liminf ≥ A+1 (C2). Both are proved modulo standard theorems, with ineffective constants via Siegel. Conditionally (C4): the glitch threshold is 1−β whenever Siegel-strength split-prime density holds at k^β (hypothesis BD(β)). So the GOAL θ<1 follows from BD(β) for all β>0, which GRH implies. 3/4 is exactly the unconditional limit of the method (C3, argued). It corresponds to Burgess's exponent 1/4.
**C1 (PROVED modulo standard theorems: Burgess, Siegel, Montgomery's large sieve, Chebyshev).**
The glitch threshold moves from θ<2/3 (r2s2/C1) to **θ<3/4**. If #{i≤n : Δ³q_i≠0} ≤ n^θ for all large n, with θ<3/4, then q_n/n²→∞.
New mechanism: **stays**. The discriminant walk D^{(a)}_i=(g_i−a)²−4a q_i has total variation O(n²) on [n/2,3n/4]. A change of row f→f′ inside one field costs |D₀|·|f′²−f²| ≥ 4|D₀|H. So the number of row changes is ≤ n²/(|D₀|H). A 1-D large sieve is then run per stay (a maximal stretch on one row), not per row and not per run. This removes the r2s2 loss "number of rows × n/H".
**C2 (PROVED, same tools, QUANT beyond 3/4).** If #glitches ≤ n^θ with θ<5/6, then liminf q_n/n² ≥ 2. More generally, if θ < 3/4 + 5^{1−A}/20 then liminf q_n/n² ≥ A+1. The mechanism is that the e=2 discriminant walk D^{(1)} is one-sided: it decreases only at repeated gaps (e_i=0). Those steps lie in AP blocks of length O(log n), so the downward variation is ≤ n^{1+θ+o(1)} instead of n². The bound for e=4,6,… runs comes from a recursion whose fixed point is exactly 3/4.
**C3 (method barrier, NEGATIVE, argued, not a theorem about primes).** These ingredients cannot pass θ=3/4 uniformly in C. As a→∞ the recursion's fixed point x*=1/4 hits the stay condition exactly at θ=3/4. An explicit phantom configuration (a field with |D₀|≈n, rows f≈n^{1−θ}, Burgess-extremal χ) satisfies every constraint used.

## Claims
### C1
STATEMENT: Let q_1<q_2<… be primes with nondecreasing gaps g_i=q_{i+1}−q_i, and let e_i=g_{i+1}−g_i. Fix θ<3/4 and C≥1. For all n≥n_0(θ,C) with q_n≤Cn²: #{i∈[n/2,3n/4] : e_{i+1}≠e_i} > n^θ. Hence if #{i≤n : Δ³q_i≠0} ≤ n^θ for all large n, then q_n/n²→∞. (n_0 is ineffective, through Siegel.)
STATUS: PROVED (all steps checked by hand; standard theorems cited)
TYPE: STRUCTURE / CONDITIONAL
BEYOND: r2s2/C1 (validated) has θ<2/3, and KNOWN has θ<1/2. The new ingredient is the discriminant-walk stay count (Step 5). It defeats the r2s2/C2 barrier configuration: there, n^{1/3} rows each visited ≈ once give S≈n^{1/3} stays, with sieve mass ≪ (n + S·√k)/H = O(n/H).
PROOF: see the section "Proof of C1" below.

## Proof of C1
Notation. Suppose q_n≤Cn², n large. W=[n/2,3n/4]∩Z. Convex tail: for i≤3n/4+2, g_i ≤ (q_n−q_i)/(n−i) ≤ 5Cn. y_i := g_i − a (a is fixed below), which is nondecreasing in i. For i≥2 the e_i are even. K_0:=20C. H:=n^{1−θ}/32. ε>0 is small in terms of θ.

Step 1 (bookkeeping, as in r2s2). A block is a maximal index interval with constant e_i. At most 1+n^θ blocks meet W. Partition W:
 (i) e=0 blocks are APs of primes >n/2 with difference ≤5Cn. Every prime ≤ the length divides the difference, so the length is O(log n), and the total is O(n^θ log n).
 (ii) #{i∈W: e_i ≥ 2K_0+2} ≤ 5Cn/(2K_0+2) < n/8.
 (iii) Blocks with 2≤e≤2K_0 and |B∩W|<2H have total < (1+n^θ)2H ≤ n/16+o(1).
 (iv) The remaining "long blocks" B (e_i=2a, 1≤a≤K_0, |B∩W|≥2H) therefore cover ≥ n/16−o(n) indices of W.
Write B′=B∩W=[u,v].

Step 2 (parabola, local structure; r2s4/C1 / r2s2 Step A, re-proved). D^{(a)}_i := (g_i−a)²−4a q_i satisfies the exact identity
 D^{(a)}_{i+1}−D^{(a)}_i = (e_i−2a)(2g_i+e_i).   (*)
(Expand: e_i(g_{i+1}+g_i−2a) − 4a g_i = (e_i−2a)(2g_i+e_i).) So D^{(a)}_i ≡ D_B for i∈[u,v+1], and 4a q_i = y_i² − D_B with y_{i+1}=y_i+2a there. Let p∤2a be a prime ≤2H. If (D_B/p)≠−1, then y²≡D_B (mod p) is solvable. y_i runs through all classes mod p on p consecutive i, so p | 4a q_i, hence p|q_i, but q_i>p is prime: contradiction. So (D_B/p)=−1. Hence D_B≠0 is a nonsquare (some such p exists), D_B≡(g−a)² (mod 4), D_B=D_0f² with D_0≠1 fundamental. For p≤2H, p∤2a: p∤f and χ_{D_0}(p)=−1. Write f=f_1f_2 with f_1|(2a)^∞ and (f_2,2a)=1. Every prime factor of f_2 is >2H. Row of B := (a,D_0,f). Also |D_B| ≤ max((5Cn)², 4K_0Cn²) =: c_0n² =: X, so k:=|D_0| ≤ X.

Step 3 (Lemma S: Siegel-strength split-prime density). Fix m≥1 and ε∈(0,1/8). For fundamental D_0≠1 with k=|D_0|≥k_0(m,ε) (ineffective), M:=k^{1/4+ε}:
 σ(D_0,m) := Σ_{p≤M, p∤m, χ(p)=1} 1/p ≥ k^{−ε}.
Proof. r′(j)=ψ_0(j)Σ_{d|j}χ(d) ≥ 0, with ψ_0 principal mod m.
Lower bound (hyperbola, parameter U): Σ_{j≤M} r′(j) = (φ(m)/m)M·L(1,χψ_0) + O_m(U + M U^{−1/r}k^{c_r}), with c_r=(r+1)/(4r²)+η. Here we used Burgess |Σ_{x≤y}χ(x)| ≪ y^{1−1/r}k^{c_r} for every r. If 8|k, split into classes mod 8, which reduces to interval sums of the primitive character mod the odd squarefree part; Möbius over d|m handles ψ_0. Also L(1,χψ_0) ≥ (φ(m)/m)L(1,χ) ≥ (φ(m)/m)c(η)k^{−η} (Siegel). Take r ≥ 1/(2ε), η = ε/(10r), U = Mk^{−2η}. Then the errors are ≪ Mk^{−2η}, so Σ_{j≤M} r′(j) ≥ c_1k^{−η}M.
Upper bound: r′(j)>0 forces j=s²wv, with s inert-composed, w|D_0^∞ and v split-composed, all coprime to m, and r′(j)=τ(v). So Σ_{j≤M} r′ ≤ Π_{p|D_0}(1−p^{−1/2})^{−1}·Σ_{v≤M}τ(v)√(M/v) ≤ k^{o(1)}(√M + 4σM(1+log M)). (Each v>1 equals p·v′ with p its least prime factor, so N(t):=Σ_{1<v≤t}τ(v) ≤ 2σ t(1+log t); then partial summation.) Since √M ≤ Mk^{−1/8} and η<1/8, we get σ ≥ k^{−η−o(1)}/log M ≥ k^{−ε}. ∎
Corollaries for a field D_0 carrying a long block with this a (m=2a): (S1) split p∤2a with p≤2H do not exist (Step 2), so σ counts only p∈(2H,M]. (S2) For large n, k≥k_0: for the finitely many D_0 with k<k_0, Dirichlet gives a fixed split prime p∤2a, which is <2H for large n, contradicting Step 2. (S3) σ>0 gives a split p∤2a with 2H<p≤k^{1/4+ε}, so k ≥ (2H)^{4/(1+4ε)} ≥ H^{4−16ε}.

Step 4 (field count, elementary). Let E be the set of all D_0 of long blocks (all a≤K_0). For large n every prime in (H,2H] exceeds 2K_0, so χ_{D_0}(p)=−1 for all p∈(H,2H] and all D_0∈E. Take r=⌈log(X²)/log H⌉ (bounded in terms of θ), N=(2H)^r ≥ X², and a_j=1 on the products of r distinct primes from (H,2H]. Their number is Z ≥ (H/(2r log H))^r, and χ(j)=(−1)^r on them. The large sieve for primitive characters, Σ_{q≤X}Σ*_χ|Σa_jχ(j)|² ≤ (N+X²)Σ|a_j|², gives |E|Z² ≤ 2NZ. So |E| ≤ 2N/Z ≤ 2(4r log H)^r = (log n)^{O(1)}.

Step 5 (stays and the discriminant-walk budget). Fix a≤K_0 and D_0∈E, with k=|D_0|.
 Small rows: f_2=1. There are ≤ (1+log_2 X)^{ω(2a)} = (log n)^{O(1)} of them.
 Big rows: f_2>1, so f≥f_2>2H.
 List the long a-blocks of field D_0 on big rows in index order. A *stay* is a maximal run of consecutive list members with the same row f. Consecutive stays σ_j, σ_{j+1} have rows f≠f′, both >2H. Take i_j = last index of σ_j and i′_{j+1} = first index of σ_{j+1}. By (*):
 k|f′²−f²| = |D^{(a)}_{i′_{j+1}} − D^{(a)}_{i_j}| ≤ Σ_{i_j≤i<i′_{j+1}} |e_i−2a|(2g_i+e_i).
 The intervals [i_j,i′_{j+1}) are disjoint subsets of W, and 2g_i+e_i=g_i+g_{i+1} ≤ 10Cn. Also Σ_{i∈W}|e_i−2a| ≤ Σ_W e_i + 2a|W| ≤ 5Cn+K_0n. So Σ_j k|f′²−f²| ≤ V := 10C(5C+K_0)n². Each term is ≥ k(f+f′) > 4kH. Hence the number of stays is
 S ≤ 1 + V/(4kH).
 y-ranges: J_σ := [y at the first index of σ, y at the last index of σ]. y is nondecreasing and stays are index-disjoint, so the J_σ have disjoint interiors and Σ_σ|J_σ| ≤ 5Cn.

Step 6 (large sieve per stay). Stay σ has row (a,D_0,f) and D=D_0f². For each class y_0 mod 2a put t=(y−y_0)/2a and G(t)=((y_0+2at)²−D)/4a. Every block point i of σ with y_i≡y_0 gives a prime G(t). Call t a *good start* if G(t+i) is prime for all i<H. A block with |B′|≥2H has ≥|B′|+1 points, hence ≥|B′|/2 good starts. Distinct points of the stay have distinct y, since the same y and D give the same q. So mass(σ) := Σ_{B∈σ}|B′| ≤ 2·Σ_{y_0}#{good starts with y∈J_σ}.
 For a split p (χ_{D_0}(p)=1) with p∤2af and p≤Q:=M=k^{1/4+ε}, we have p>2H by (S1), (D/p)=1, and G has a root t_p mod p. A good start avoids the H distinct classes t_p−i (i<H), since all values exceed p (they are ≥n/2>Q). Montgomery's large sieve gives
 #good ≤ (|J_σ|/2a + 1 + Q²)/(H·σ_f),  σ_f := Σ_{split p≤Q, p∤2af} 1/p ≥ k^{−ε} − ω(f)/(2H) ≥ k^{−ε}/2.
 (The last step holds for large n, since ω(f) ≤ 2log n and k^{−ε} ≥ (c_0n²)^{−ε} ≫ log n/H.) So mass(σ) ≤ c_a(|J_σ| + Q² + 1)k^{ε}/H.
 Summing: mass_big(a,D_0) ≤ c_a k^ε(5Cn + S(k^{1/2+2ε}+1))/H ≪ n^{4ε}(n/H + k^{1/2}/H + n²/(H²k^{1/2})).
 Small rows: one sieve over the whole row (t-range ≤ 5Cn/a+1) gives ≪ n^{1+4ε}/H per row.
 By (S3), k^{1/2} ≥ H^{2−8ε}, so mass(a,D_0) ≪ (log n)^{O(1)} n^{4ε}(n/H + n²/H^{4−8ε}) ≪ n^{θ+5ε} + n^{4θ−2+13ε}.

Step 7 (conclusion). Summing over a≤K_0 and D_0∈E ((log n)^{O(1)} pairs), the long-block mass is ≪ n^{θ+6ε} + n^{4θ−2+14ε} = o(n) when θ<3/4 and ε<(3−4θ)/20. This contradicts Step 1(iv). ∎

### C2
STATEMENT: Let q be a convex prime sequence with #{i≤n : Δ³q_i≠0} ≤ n^θ for all large n.
 (a) If θ<5/6, then liminf q_n/n² ≥ 2.
 (b) If A≥1 and θ < 3/4 + 5^{1−A}/20, then liminf q_n/n² ≥ A+1. (For A=1 this gives θ<4/5, superseded by (a). For θ<3/4 it holds for every A, which reproves C1.)
 (c) (Key lemma, e=2 part.) Fix δ∈(0,1/10), θ<5/6, C. For n large with q_n≤Cn², the indices i∈W_δ:=[δn,(1−δ)n] lying in e=2 blocks B with |B∩W_δ| ≥ 2H, H:=n^{1−θ−ε′}, number o(n).
STATUS: PROVED (modulo the same standard theorems as C1)
TYPE: QUANT / CONDITIONAL
BEYOND: KNOWN unconditional liminf is 0.864. Under the glitch hypothesis, r2s2 gives nothing for θ≥2/3, and C1 gives nothing for θ≥3/4. (a) gives liminf ≥ 2 for every θ<5/6. The new ingredient is the one-sidedness of the D^{(1)} walk.
PROOF.
Setup: W_δ as above. For i≤(1−δ)n+2, g_i ≤ (q_n−q_i)/(n−i) ≤ Cn/(δ−o(1)) ≤ Gn with G:=2C/δ. Steps 2–4 and Lemma S of C1 hold verbatim on W_δ, with 5C replaced by G. Every H=n^{η} with η>0 fixed is admissible there: one only needs H→∞ polynomially, and the "long" threshold is 2H. The number of e=0 indices in W_δ is T_0 ≤ (n^θ+1)·2log n, since an e=0 block is an AP of primes > n^{1/2} with difference ≤ Gn, so its length is ≤ (1+o(1))log(Gn).
(c) Fix a=1. D^{(1)}_i=(g_i−1)²−4q_i is odd, so f is odd and the only small row is f=1. Fix a field D_0∈E, k=|D_0|. Big rows have f>2H (Step 2).
 One-sided walk: by (*), D^{(1)}_{i+1}−D^{(1)}_i=(e_i−2)(2g_i+e_i). This is <0 iff e_i=0, and then it equals −4g_i ≥ −4Gn. So D_down := Σ_{i∈W_δ, e_i=0} 4g_i ≤ 8Gn(n^θ+1)log n.
 Dyadic rows: fix F≥2H (a power of 2). Stays = maximal runs of consecutive (in index order) long e=2 blocks of field D_0 with the same row f∈[F,2F). Let d_j=D_0f_j² be the stay values. Then |d_last−d_first| ≤ 3kF². Each d_{j+1}−d_j is the walk increment over a disjoint index interval, so its negative part is ≤ that interval's downward variation. Hence Σ_j|d_{j+1}−d_j| = (d_last−d_first) + 2Σ_j(d_{j+1}−d_j)_− ≤ 3kF² + 2D_down. Each term is ≥ k(f+f′) ≥ 2kF, so S_F ≤ 1 + 3F/2 + D_down/(kF).
 Stay sieve (C1 Step 6): mass_F ≤ c k^ε(Σ|J_σ| + S_F(k^{1/2+2ε}+1))/H. Rows f≥F exist only if kF² ≤ X=c_0n², so F√k ≪ n. Hence
 mass_F ≪ n^{4ε}(n/H + n^{1+θ}log n/(√k F H)).   (i)
 Pair sieve per row (used when k≤n): for a big row f, sieve the whole row (t-range ≤ Gn) by the split p∤2f, p∈(2H,M], M=k^{1/4+ε}, with moduli q=pp′ ≤ Q_2:=M². Then L ≥ Σ_{p<p′}(H/p)(H/p′) = ½[(Hσ_f)² − Σ(H/p)²] ≥ ¼(Hσ_f)², using H/p<½ and Hσ_f≥1. The large sieve gives #good ≤ (Gn+1+Q_2²)/L, with Q_2² = k^{1+4ε} ≤ n^{1+4ε}. So mass(row) ≪ n^{1+8ε}/H². There are ≤ F rows in [F,2F), so
 mass_F ≪ F n^{1+8ε}/H²  (k≤n).   (ii)
 Combine. If k≤n: min((i),(ii)) ≤ n^{8ε}[n/H + √(n^{2+θ}log n/(√k H³))] ≤ n^{9ε}[n/H + n^{1+θ/2}/H^{5/2−4ε}], using k^{1/4} ≥ H^{1−4ε} (Lemma S, S3). If k>n: (i) ≤ n^{5ε}[n/H + n^{1/2+θ}/H²]. With H=n^{1−θ−ε′} both are ≪ n^{θ+ε′+9ε} + n^{3θ−3/2+3ε′+19ε} = o(n) for θ<5/6 and ε,ε′ small. Summing over ≤log n values of F, the row f=1 (≪n^{1+4ε}/H by the C1 per-row sieve), and |E|=(log n)^{O(1)} fields (Step 4) gives (c). ∎
(a) Suppose liminf q_n/n² < 2. Pick C<2 and δ with 2(1−2δ)²>C; there are infinitely many n with q_n≤Cn². In W_δ: the e=0 indices are o(n); e=2 indices in short blocks (|B∩W_δ|<2H) number ≤ (n^θ+1)2H = O(n^{1−ε′}); e=2 indices in long blocks are o(n) by (c). So e_i≥4 for all but o(n) indices i∈W_δ, and g_i ≥ 4(i−δn) − o(n) on W_δ (e_j≥0). Hence q_n ≥ Σ_{i∈W_δ}g_i ≥ 2(1−2δ)²n² − o(n²) > Cn²: contradiction.
(b) Stays-only recursion. For a≥1 let T_a=#{i∈W_δ: e_i=2a}. Downward steps of D^{(a)} are exactly those with e_i<2a, so D^{(a)}_down ≤ 2a(2G+2a)n·Σ_{a′<a}T_{a′} (with a′=0 meaning e=0). The proof of (c), using only (i) and the small rows f|(2a)^∞ ((log n)^{O(1)} of them, each ≪ n^{1+4ε}/H), gives for every admissible H:
 m_a(H) ≪ n^{O(ε)}(n/H + D^{(a)}_down/H⁴),  T_a ≤ (n^θ+1)2H + m_a(H).
 WLOG θ≥3/4. By induction T_a ≤ n^{θ+x_a+o(1)} with x_0=0 and x_a=(1+x_{a−1})/5, taking H=n^{(1+x_{a−1})/5}; the n/H term is smaller since θ≥1/2. So x_a=(1−5^{−a})/4. With H=n^{1−θ−ε′}: m_a = o(n) iff 1+θ+x_{a−1} − 4(1−θ) < 1, i.e. θ < (4−x_{a−1})/5 = 3/4 + 5^{1−a}/20. Given θ<3/4+5^{1−A}/20, this holds for all a≤A, so e_i≥2A+2 for all but o(n) indices of W_δ, and q_n ≥ (A+1)(1−2δ)²n² − o(n²). Conclude as in (a). ∎

### C4
STATEMENT (glitch exponent = 1 − split-density exponent). For β∈(0,1/4] let BD(β) be the hypothesis: for every fixed m≥1 and ε>0, every real primitive character χ of conductor k≥k_0(m,β,ε) satisfies Σ_{p≤k^β, p∤m, χ(p)=1} 1/p ≥ k^{−ε}. If BD(β) holds, then #{i≤n: Δ³q_i≠0} ≤ n^θ (all large n) with θ<1−β implies q_n/n²→∞.
 - BD(β) holds for every β>1/4 (Lemma S: Burgess + Siegel). Since the conclusion only improves as β decreases, this recovers C1 (θ<3/4).
 - GRH implies BD(β) for every β>0. Under GRH, Σ_{p≤x}χ(p)log p ≪ √x log²(kx), so for x=k^β the split primes in (x/2,x] have Σ1/p ≫ 1/log x. Hence **BD(β) for all β>0 implies the GOAL (every θ<1)**, under a hypothesis far weaker than GRH. It only excludes characters that are inert at almost all primes up to k^β, measured in Σ1/p with a k^{−ε} margin.
STATUS: PROVED (conditional on BD(β); the other steps are as in C1)
TYPE: CONDITIONAL / REDUCTION
BEYOND: KNOWN has θ<1 only under GRH (informal), via least split prime ≪ log²D. C4 isolates the exact arithmetic input: the glitch threshold is 1 − (the exponent at which Siegel-strength split-prime density is known). Unconditionally that exponent is 1/4+, which gives θ<3/4.
PROOF. Repeat C1 with Lemma S replaced by BD(β) (m=2a), and set Q:=k^β.
 - (S1) still holds: split p∤2a lie in (2H,Q].
 - (S3) becomes: some split p∤2a with p≤k^β exists and p>2H, so k ≥ (2H)^{1/β}.
 - Step 6 gives mass(σ) ≤ c(|J_σ| + k^{2β} + 1)k^ε/H. With S ≤ 1+V/(4kH): Σ_σ mass ≪ k^ε(n + k^{2β} + V k^{2β−1}/H)/H. Here k^{2β} ≤ (c_0n²)^{2β} ≪ n, since β≤1/4.
 - Since 2β−1<0 and k ≥ (2H)^{1/β}, we have k^{2β−1} ≤ (2H)^{2−1/β}. So the last term is ≪ n²H^{−1/β} = n^{2−(1−θ)/β+o(1)}, which is o(n^{1−c}) iff θ<1−β.
 - Small rows: ≪ n^{1+O(ε)}/H each. Field count: Step 4, unchanged.
 - Summing over (a,D_0) gives o(n) long-block mass, which contradicts Step 1(iv). ∎

### C3
STATEMENT (method barrier): the ingredients of C1/C2 cannot reach any θ>3/4 uniformly in C. Those ingredients are: local structure (Step 2), Lemma S at k^{1/4+ε}, field count, 1-D large sieve per stay or per row at level √(length), the D-walk identity with up/down budgets, and short-block counting by glitches.
STATUS: CONJECTURED (an analysis of the method, not a statement about primes)
TYPE: NEGATIVE
EVIDENCE/MECHANISM:
 (1) In (b) the recursion's fixed point is x*=1/4, and the stay condition 5θ+x*<4 becomes exactly θ<3/4. With the pair sieve added, the k>n regime still gives x*=1/4: there the stays term is n^{1/2+θ+x}/H², the fixed point of x=(1/2+x)/3 is 1/4, and the threshold 3θ+x<5/2 again gives 3/4.
 (2) Phantom at θ=1−h, h<1/4, for large a. The construction: one field with k≈n and χ(p)=−1 for p≤n^{1/4−ε}, with split primes only in (n^{1/4−ε},n^{1/4+ε}] and Σ1/p≈n^{−ε}. This is consistent with Lemma S and is not excluded by any known result.
 - Rows are the primes f∈[2H,4H], each visited by ≈n^{1/2} stays, so S≈n^{1/2+h}.
 - Each stay has y-length ≈n^{1/2−h} and holds ≈n^{1/2−2h} runs of length H≈n^h ≤ k^{1/4}. Total runs n^{1−h}=n^θ.
 - Every per-stay sieve bound (≈√k/H) and per-row bound (≈n/H) is satisfied. The pair sieve is unavailable since M²≈n^{1/2+2ε}>√n.
 - The D-walk needs S·kF≈n^{3/2+2h} ≤ n² of variation, supplied downward by ≈n^{1/2+2h} steps with e=2a−2 grouped into ≤n^θ blocks. This is possible iff h≤1/4.
 (3) 2-D (ideal-lattice) sieving over (y,f) does not help in the phantom. The lattice 𝔭𝔭′ has λ₂≈√(k·M²)≈n^{3/4}, which exceeds the thin width √|D|≈n^{1/2+h} of the visited region.

## Data
- check1.py: greedy convex prime chain from (3,5), 3459 terms, q_n/n²=5.85.
 - Identity (*) verified for a=1..4 at every index (0 violations).
 - Step 2 Legendre condition verified on every block with e>0 and length ≥3 (0 violations).
 - Greedy chains are glitchy: (#blocks−1)/#e = 0.89, the longest block has length 5, and e is spread over 0..16. This is far from the glitch-sparse regime, as expected: the theorem is asymptotic and these checks only validate the algebra.
- exps.py (exact exponent bookkeeping):
 - Recursion thresholds (4−x_{a−1})/5 for a=1..6 are 4/5, 19/25, 94/125, 469/625, 2344/3125, 11719/15625. These match the closed form 3/4+5^{1−a}/20 exactly.
 - a=1 combined bound (stays ∧ pair-sieve geometric mean, over all κ=log k/log n ∈ [4h,2]): the worst exponent is <1 exactly for θ<5/6. Values: 0.9999 at θ=0.8333 and 1.002 at θ=0.834.
 - The phantom constraints of C3(2) all hold for h∈(0,1/4]. At h=0.15 the "runs ≤ n^θ" check is an exact tie (float rounding), not a violation.

## Dead ends
- **Per-row counting (r2s2).** It loses #rows×n/H and is stuck at 2/3. Stays replace #rows by the number of row CHANGES, which the D-walk budget controls.
- **Total variation alone.** V≈n² for a general a gives exactly 3/4 (C1). One-sidedness helps only when downward steps are rare, which holds for a=1 (e=0 rare) but not for a≥2: e=2a−2 steps can come from short blocks.
- **Higher-moment sieves per row.** k-th moments need products of k split primes ≤ the window length. Window classes contribute H^k error, and (HM)^2≈n is already the knife edge.
- **2-D ideal-lattice large sieve.** Knife-edge or worse in the extremal configuration; see C3(3).
- **Deuring–Heilbronn (plan 5a).** The extremal configurations use ONE field, so repulsion between fields gives nothing.
- **Plan's "T≳√|D₀|" diagnosis.** That is only the knife edge for rows with |D|≍n². The true extremal case is small rows f≈H with |D|≈kH² ≪ n². There the stays are short and the per-row sieve is tight simultaneously.
