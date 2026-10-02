# Research engine: problem 455, run 20261002-160957-739019-erdos455

Spend $36.1056; 25 claim(s); 4 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] deep/C1 PROVED STRUCTURE
**Statement.** Let q_1<q_2<… be primes with nondecreasing gaps g_i=q_{i+1}−q_i, and let e_i=g_{i+1}−g_i. Fix θ<3/4 and C≥1. For all n≥n_0(θ,C) with q_n≤Cn²: #{i∈[n/2,3n/4] : e_{i+1}≠e_i} > n^θ. Hence if #{i≤n : Δ³q_i≠0} ≤ n^θ for all large n, then q_n/n²→∞. (n_0 is ineffective, through Siegel.)
**Beyond.** r2s2/C1 (validated) has θ<2/3, and KNOWN has θ<1/2. The new ingredient is the discriminant-walk stay count (Step 5). It defeats the r2s2/C2 barrier configuration: there, n^{1/3} rows each visited ≈ once give S≈n^{1/3} stays, with sieve mass ≪ (n + S·√k)/H = O(n/H).
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No published result restricts convex prime sequences by third-difference glitch counts; going from θ<1/2 to θ<3/4 needs a genuinely joint multi-discriminant argument beyond the single-run Linnik–Vinogradov barrier. But it is a conditional structural statement that leaves the core (sequences with linearly many glitches) and the unconditional liminf bound untouched.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published result restricts convex prime sequences by third-difference glitch counts; going from θ<1/2 to θ<3/4 needs a genuinely joint multi-discriminant argument beyond the single-run Linnik–Vinogradov barrier. But it is a conditional structural statement that leaves the core (sequences with line`
**Proof or evidence.**

see the section "Proof of C1" below.

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

## [validated-new] r1s2/C1 PROVED QUANT
**Statement.** Let q_1<q_2<… be primes with q_{n+1}−q_n ≥ q_n−q_{n−1}. Then liminf q_n/n² ≥ 255255/(295318+E0_17) = 0.864289…,
where E0_17 = Σ_{p>17}(p−2)(1−1/p)∏_{17<ℓ<p}ℓ^{−1} = 17.224430. Equivalently d_n ≥ (2·0.864289 − o(1)) n.
**Beyond.** improves the blackboard's 0.80024 (S={3..13}) and Richter's 0.352.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No published bound beyond Richter's 0.352 is known, so 0.8643 is new. But it is a mechanical extension of the team's own congruence-game method to S={3..17}, and that method is provably capped at liminf 1 by Euler/Rabinowitsch quadratics, so it does not bear on whether q_n/n^2 tends to infinity.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published bound beyond Richter's 0.352 is known, so 0.8643 is new. But it is a mechanical extension of the team's own congruence-game method to S={3..17}, and that method is provably capped at liminf 1 by Euler/Rabinowitsch quadratics, so it does not bear on whether q_n/n^2 tends to infinity."}, {"verdict": "new", "cite": null, "significance": 1, "why": "No publishe`
**Proof or evidence.**

- The game. S={3,5,7,11,13,17}, M=∏S. The state is q mod M, restricted to q ≢ 0 mod every p∈S. At step k (gap value d=2k), the player chooses
  a multiplicity m with 0 ≤ m ≤ cap(k), where cap(k) = (least p∈S with p∤k) − 2, and cap = 0 if M|k. Every visited q+jd (1≤j≤m) must stay
  nonzero mod each p∈S. The payoff is Σm.
- Reduction. In the real sequence, gap value d=2k occurs m_k times. Then q, q+d, …, q+m_k d are all primes > 17 once past a finite
  transient. If p∤d, these m_k+1 terms are distinct mod p, so none of them can be 0 mod p. That makes the real choices a legal play.
  When M|k the residue mod M does not move. The real multiplicity is then ≤ p(d)−2, where p(d) is the least prime not dividing d, and this
  prime is > 17. By CRT, the average of p(d)−2 over k ≡ 0 mod M is E0_17.
- Bound. Max-plus value iteration starting from v=0 on valid states. After the M steps k=1..M, max_q T(v)[q] = 295318. This is the largest
  total payoff over one full period, maximised over every start state and every play. Hence any n consecutive periods give ≤ n·295318,
  and an arbitrary starting phase changes this by only O(M).
- Conclusion. So #{i : d_i ≤ 2K} ≤ (K/M)(295318 + E0_17) + o(K), which gives d_n ≥ (2M/(295318+E0) − o(1))n. Summing gives the claim.
- Validation. The same code reproduces ρ = 20, 156, 1596, 18748 for S={3,5}, {3,5,7}, {3..11}, {3..13}. With E0_13 it gives exactly the
  blackboard's 0.800240.
- The min one-period growth is 295209. So the exact game value ρ_17 lies in [295209, 295318], i.e. ρ_17/M ∈ [1.15653, 1.15696].
  The exact bound 1/κ' therefore lies in [0.864289, 0.864608].

## [validated-new] r1s3/C1 PROVED QUANT
**Statement.** Let q_1 < q_2 < ... be primes with q_{n+1}-q_n >= q_n-q_{n-1}. Then liminf q_n/n^2 >= 1/rho_17 >= 0.86429.
Here rho_17 = G_17/M + tau_17 with M = 3·5·7·11·13·17 = 255255, G_17 = 295318 and
tau_z = sum_{p>z} (p-2)(1-1/p)/prod_{3<=l<p} l, so tau_17 = 0.0000675 and rho_17 = 1.157020.
Equivalently d_n >= (2/rho_17 - o(1)) n.
**Beyond.** the blackboard bound 0.80024 (z = 13, informally refereed). Richter has 0.352 and AP-multiplicity 0.543.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No published bound beyond Richter's 0.352 is known to me. The z=17 congruence-game value 0.86429 is a modest new numerical improvement, but it is a routine extension of the team's z=13 method, which is provably capped at liminf ≤ 1 by the Rabinowitsch-quadratic barrier, so it does not advance the core question.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published bound beyond Richter's 0.352 is known to me. The z=17 congruence-game value 0.86429 is a modest new numerical improvement, but it is a routine extension of the team's z=13 method, which is provably capped at liminf ≤ 1 by the Rabinowitsch-quadratic barrier, so it does not advance the core question."}, {"verdict": "new", "cite": null, "signi`
**Proof or evidence.**

Game. S = odd primes <= z, M = prod S. State s in (Z/M)^*. A period is v = 0, 1, ..., M-1 (v read mod M).
At step v with M ∤ v, choose m >= 0 such that s + 2vj is a unit mod M for j = 1..m; gain m; then s <- s + 2vm.
At v ≡ 0 (mod M) set m := 0 (s is unchanged anyway). T is the one-period Bellman operator on functions of s:
(T h)(s) = max over one period of (gain + h(end state)).
(a) Reduction. Discard the finitely many terms <= max(z, ...). Gaps are even, d = 2v, and by monotonicity each value v
is used in one consecutive block of m_v >= 0 gaps. The terms are primes > z, hence units mod M, so a block with M ∤ v
is a legal game move from s = (current term mod M). A block with M | v leaves s mod M unchanged. For it, m_v <= p(d)-2,
where p(d) is the least odd prime not dividing d (necessarily > z): the m_v + 1 terms form an AP with difference prime
to p, so if m_v + 1 >= p one term is ≡ 0 (mod p) and so equals p. That is impossible for large terms, since
p(d) = O(log d) = O(log q).
(b) Game bound. If T h = h + G (an eigenvector), then by induction any path over j periods gains
<= jG + max h - min h. Extending a path by m = 0 moves only increases the window, so any window of v-values of length
V gains <= G·V/M + O_z(1).
(c) Tail. Sum_{w<=W} (p(2Mw)-2) = W·M·tau_z + o(W). Here p(2Mw) is the least prime > z not dividing w, its law
(density (1-1/p)/prod_{z<l<p} l) is periodic, and p(2Mw) = O(log w).
(d) So N(V) := #{k : d_k <= 2V} <= rho_z V + o(V). Since n <= N(d_n/2), we get d_n >= (2/rho_z - o(1)) n and
q_n >= sum_{k<n} d_k >= (1/rho_z - o(1)) n^2.
(e) Computation for z = 17. Value iteration on the full residue array, with nonunits set to -inf (float32; all values
are integers < 2^24, so the arithmetic is exact). The step at v takes p(v)-2 Jacobi sweeps of
C(x) = max(W(x), 1 + C(x+2v)), restricted to units, where p(v) is the least prime of S not dividing v. This covers all
chains, because m+1 consecutive units along step 2v force m <= p(v)-2. The first period gives max T(0) = 295318, so
already G <= 295318: T is monotone and commutes with constants, hence T^j 0 <= j·max T0. The second period, with
V = T0 - max, gives T V - V = 295318 on EVERY unit state. So V is an exact eigenvector and G_17 = 295318 exactly
(runtime 88 s).
Check: the same code gives G = 2, 20, 156, 1596, 18748 for z = 3, 5, 7, 11, 13, which are exactly the blackboard
values (and 1/rho = 0.54345 = 1/kappa at z = 3).

## [validated-new] r2s2/C1 PROVED CONDITIONAL
**Statement.** Let q_1<q_2<… be primes with d_i=q_{i+1}−q_i nondecreasing and e_i=d_{i+1}−d_i. Fix θ<2/3 and C≥1. For all n≥n_0(θ,C) with q_n≤Cn², #{i∈[n/2,3n/4] : e_{i+1}≠e_i} > n^θ. (Note Δ³q_i=e_{i+1}−e_i.) Hence, if #{i≤n:Δ³q_i≠0}≤n^θ for all large n, then q_n/n²→∞. The constants are ineffective, via Siegel.
**Beyond.** KNOWN has the threshold θ<1/2 (per-run LV). This raises it to 2/3 unconditionally.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": "No counterexample or fatal gap found. Minor slips only: (1) Lemma S claims real primitive characters have cube-free conductor, which is false when 8 divides the conductor; fix by factoring out chi_8 and applying Burgess to the cube-free part on residue classes mod 8. (2) Step C exponent should be n^{1+8eps}/H rather than n^{1+6eps}/H (Q^2 ~ n^{1+4eps} times k^{2eps} <= n^{4eps}), which only changes the final epsilon condition to theta+8eps<1. Neither affects the theta<2/3 threshold, which enters only in (d) via 6h>2.", "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "Raising the threshold for the conditional 'few Δ³q changes ⇒ q_n/n²→∞' from 1/2 to 2/3 is not in the literature, but it is a modest step using standard tools (Siegel/Landau–Page or a Linnik-type large sieve over many run discriminants). It concerns a strong structural special case, not the problem's core, and a large-sieve argument may push θ further almost routinely.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "Raising the threshold for the conditional 'few Δ³q changes ⇒ q_n/n²→∞' from 1/2 to 2/3 is not in the literature, but it is a modest step using standard tools (Siegel/Landau–Page or a Linnik-type large sieve over many run discriminants). It concerns a strong structural special case, not the proble`
**Proof or evidence.**

Setup. Suppose q_n≤Cn², and put W=[n/2,3n/4]∩Z, so |W|≈n/4. Convex tail: for i≤3n/4+1, d_i≤(q_n−q_i)/(n−i)≤5Cn. Hence Σ_{i∈W}e_i≤5Cn. For i≥2 the gaps are even, so the e_i are even. A *block* is a maximal set of consecutive indices with constant e_i. At most 1+n^θ blocks meet W. On a block [u,v] with e=2a: d_{u+j}=d_u+2aj, so q_{u+j}=q_u+jd_u+aj(j−1) for 0≤j≤v−u+2, and
 4a·q_{u+j} = y_j² − D,  y_j = 2aj+d_u−a,  D = (d_u−a)² − 4a q_u   (D is constant on the block).
With y_0∈[0,2a), y≡y_0 (mod 2a), t=(y−y_0)/2a≥0, these values are G(t)=at²+y_0t+(y_0²−D)/4a. G is the *parabola* (a,D,y_0), and it is strictly increasing for t≥0. |D|≤X:=max((5Cn)²,4K_0Cn²)=c_0n². The relevant t lie in an interval of length ≤√C·n+1.
Partition W. Put K_0=20C, H=n^{1−θ}/32, h=1−θ>1/3.
 (i) Blocks with e=0 are APs of primes >n/2 with difference ≤5Cn. Every prime ≤ length divides the difference, so the length is O(log n), and the total is O(n^θ log n)=o(n).
 (ii) #{i∈W : e_i≥2K_0+2} ≤ 5Cn/(2K_0+2) < n/8.
 (iii) Blocks with 2≤e≤2K_0 and |block∩W|<2H have total < (1+n^θ)2H ≤ n/16+o(1).
 (iv) The rest, "long blocks", therefore cover ≥ n/16−o(n) indices of W.
Starting points. For a parabola G put T_H(G)={t : n/2≤G(t), G(t+H−1)≤Cn², G(t+i) prime ∀ i<H}. A long block on G gives m≥2H consecutive t; at least m−H+1≥m/2 of them lie in T_H(G). Distinct blocks on the same G have disjoint t-ranges, since G is injective. Hence n/16−o(n) ≤ 2Σ_{G∈𝒢}|T_H(G)|, where 𝒢 is the set of parabolas carrying a long block.
Step A (local structure). Let G=(a,D,y_0) carry a long block (≥2H consecutive prime values >n/2), and let p∤2a be a prime ≤2H. Then 4aG(t)=(2at+y_0)²−D. If D is a square mod p (including 0), G has a root mod p, so p divides some value in the block, which is a contradiction. Hence (D/p)=−1, and in particular p∤D. Write D=D_0f² with D_0 fundamental. Then (a) χ_{D_0}(p)=−1 for all p≤2H with p∤2a. This also excludes D_0=1 and D=0, because 2H>2K_0 means there are such p. (b) f=f_1f_2, where f_1 is composed of primes dividing 2a and every prime factor of f_2 is >2H (roughness).
Lemma S (split primes; Linnik–Vinogradov method with Siegel). Fix a≥1 and ε>0. For a fundamental D_0≠1 with k=|D_0| large and M=k^{1/4+ε}: σ*(M):=Σ_{p≤M, p∤2a, χ_{D_0}(p)=1} 1/p ≥ c(a,ε)k^{−2ε}.
 Proof. Let ψ_0 be the principal character mod 2a and r'(m)=ψ_0(m)Σ_{d|m}χ(d)≥0. Hyperbola method with parameter U: Σ_{m≤M}r'(m) = (φ(2a)/2a)·L(1,χψ_0)·M + O_{a,r}(U + k^{c_r}MU^{−1/r}). Here c_r=(r+1)/4r²+η_1. The error uses Burgess, |Σ_{x≤y}χ(x)|≪y^{1−1/r}k^{c_r}, which is valid for all r because real primitive characters have cube-free conductor. The tail is Σ_{d>U}χψ_0(d)/d≪k^{c_r}U^{−1/r}. Also L(1,χψ_0)=L(1,χ)∏_{p|2a}(1−χ(p)/p) ≥ (φ(2a)/2a)L(1,χ), and Siegel gives L(1,χ)≥c(η)k^{−η}. Take U=Mk^{−3η}, choose r≥1/(2ε), then choose η and η_1 small. Then Σ_{m≤M}r'(m) ≥ c(a)k^{−η}M.
 Upper bound: r'(m)≠0 forces m=s²wv, where s is inert-composed, w is ramified-composed (p|D_0) and v is split-composed (p∤2a), and r'(m)=τ(v). Every v>1 is p·v' with p the least prime factor, and τ(v)≤2τ(v'). This gives N(t):=Σ_{v≤t}τ(v)≤1+2σ*(M)t(1+log M) for t≤M. Partial summation gives Σ_{v≤T}τ(v)√(T/v) ≤ 1+√T+4σ*T(1+log M). Summing over w≤M with T=M/w gives Σ_{m≤M} r'(m) ≤ 2√M·k^{o(1)} + 4σ*M(1+log M)·O(loglog k), using ∏_{p|D_0}(1−p^{−1/2})^{−1}=k^{o(1)}. Since M^{−1/2}≤k^{−1/8}, σ*≥c k^{−2η}. ∎
 Consequences. (c) Applying Lemma S with M=2H and (a): k=|D_0| > (2H)^{4/(1+4ε)}. (d) If f_2>1 then f_2>2H, so (2H)²·(2H)^{4/(1+4ε)} < f²k ≤ X = c_0n². With 2H≍n^h and 6h>2, this is false for small ε and large n. So f_2=1 (this is the only place θ<2/3 is used). f_1≤√X has ≤(1+log X)^{ω(2a)} choices.
Step B (bounded field set). Let E_a be the set of fundamental D_0 with |D_0|≤X and χ_{D_0}(p)=−1 for all p≤y:=2H, p∤2a. Then |E_a| ≤ 2M'/Ψ_a(M',y)=O_{θ,a}(1), with M'=X^{1/2+ε'}.
 Proof. Put w_m=λ(m)·1[m≤M', m y-smooth, (m,2a)=1], where λ is Liouville. For every χ∈E_a we have χ=λ on supp w, so Σw_mχ(m)=Ψ_a:=Ψ_a(M',y). For distinct D_0,D_0'∈E_a the product χχ' is χ_{D_1} restricted to (m,D_0D_0')=1, with χ_{D_1} primitive and nonprincipal and |D_1|≤X². By Möbius over rad(D_0D_0') and Burgess (r>1/ε'): |Σ_{m≤M'}χχ'(m)| ≤ M'X^{−δ}. By Cauchy–Schwarz, for any F⊂E_a: |F|Ψ_a ≤ Ψ_a^{1/2}(|F|M'+|F|²M'X^{−δ})^{1/2}. So |F|(Ψ_a−M'X^{−δ}) ≤ M'. Here u=log M'/log y→(1+2ε')/h is bounded, so Ψ_a≫_{a,u}M' (Dickman with a fixed coprimality condition). ∎
 Hence |𝒢| ≤ Σ_{a≤K_0} 2a·|E_a|·(1+log X)^{ω(2a)} = O((log n)^{c}).
Step C (large sieve in t, per parabola). Take G∈𝒢 and Q=X^{1/4+ε}. For p≤Q with p∤2a and (D/p)≠−1, G has a root t_p mod p. Every value is >n/2>Q≥p. If p≤H then T_H(G)=∅. If p>H then T_H(G) avoids the ≥H classes t_p−i (i<H) mod p. Montgomery's large sieve: |T_H(G)| ≤ (√C n+1+Q²)/L with L ≥ Σ_{H<p≤Q,…} H/p. By (a), no p≤H with p∤2a has (D/p)≠−1. Every p with χ_{D_0}(p)=1 and p∤2a has (D/p)∈{1,0}. So L ≥ H·σ*(D_0,a,Q) ≥ H·c·k^{−2ε} (Lemma S; σ* is monotone in Q, and Q≥k^{1/4+ε}). So |T_H(G)| ≪ n^{1+6ε}/H.
Conclusion: n/16−o(n) ≤ 2|𝒢|·max|T_H| ≪ (log n)^c·n^{1+6ε}/H ≍ (log n)^c·n^{θ+6ε} = o(n) for ε<(1−θ)/12. Contradiction. ∎

## [valid-routine] r1s1/C1 PROVED STRUCTURE
**Statement.** Let P(x)=x²+Bx+c ∈ Z[x] with P(j) an odd prime > ℓ for j=0..ℓ−1. Write D=B²−4c and D=D₀f² with D₀ a fundamental discriminant. For Q→∞ and fixed α∈(0,1), let E be the set of D₀ arising from such polynomials with ℓ ≥ Q^α and |D| ≤ Q. Then |E| ≤ 2/ρ(2/α)+o(1), and every D₀∈E has |D₀| ≫_ε Q^{4α/(1+4ε)}. Consequently the number of distinct D is ≤ |E|·(Q^{1/2−2α+ε}+1).
**Beyond.** KNOWN uses Linnik–Vinogradov pointwise, which allows run length up to n^{1/2+ε}. C1 bounds jointly the whole set of long-run discriminants at one scale, and here that set has O_α(1) square classes.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Linnik's large-sieve bound on characters with large least non-residue (Elliott/Montgomery Gram-matrix form with Dickman rho), plus Linnik–Vinogradov (least split prime << |D|^{1/4+eps}) and trivial square-class counting", "why": "P(j) prime for j<ℓ forces χ_{D0}(p)=-1 for all odd p≤ℓ, so E is a set of real characters equal to Liouville on Q^α-smooth numbers; the classical large-sieve/Gram-matrix argument bounds it by O(1/ρ), and the |D0| and f bounds are direct Linnik–Vinogradov and counting. It refines run-by-run analysis but does not address the core o(√X) chain-length statement.", "panel": [{"verdict": "routine", "cite": "Linnik's large-sieve bound on characters with large least non-residue (Elliott/Montgomery Gram-matrix form with Dick`
**Proof or evidence.**

(a) Parity. P(j) is odd for all j, so j(j+B) is even for all j, so B is odd and c is odd. Hence D ≡ 1−4c ≡ 5 (mod 8). Then f is odd, D₀ ≡ 5 (mod 8), and χ_{D₀}(2) = −1.
(b) Odd primes. Let p ≤ ℓ be an odd prime. If (D/p) ≠ −1 (this includes p | D), then P has a root mod p. Among the ℓ ≥ p consecutive j some j has p | P(j). But P(j) is a prime > ℓ ≥ p, a contradiction. So (D/p) = −1. In particular p ∤ f, so χ_{D₀}(p) = (D/p) = −1.
(c) Hence χ_{D₀}(n) = λ(n) (Liouville) for every ℓ-smooth n.
(d) Distinct fundamental D₀ give distinct primitive real characters of conductor |D₀| ≤ Q. Apply the large sieve Σ_{q≤Q} Σ*_{χ mod q} |Σ_{n≤N} a_n χ(n)|² ≤ (N+Q²) Σ|a_n|² with a_n = λ(n)·1[n ≤ N, n is Q^α-smooth] and N = Q². Each D₀∈E contributes |Σ a_n χ_{D₀}(n)|² = Ψ(N,Q^α)², so |E|·Ψ² ≤ 2Q²·Ψ. Hence |E| ≤ 2Q²/Ψ(Q²,Q^α) = 2/ρ(2/α)+o(1) (de Bruijn, fixed u).
(e) Lower bound on |D₀|. χ_{D₀}(p) ≠ 1 for all p ≤ ℓ. By Linnik–Vinogradov (least split prime ≪ |D₀|^{1/4+ε}) we get |D₀| ≫ ℓ^{4/(1+4ε)}.
(f) Counting. The D are of the form D₀f² with D₀∈E and f ≤ (Q/|D₀|)^{1/2}.
Remark (general e=2A). The same argument works with a_n supported on n whose prime factors lie in (ℓ^{1/2}, ℓ] and that are coprime to 2A. Because A varies, one bounds the error from p | A by 2ω(A)N/ℓ^{1/2}. This gives |E| ≪_α log Q. I have not written this version out in full.

## [valid-routine] r1s2/C3 PROVED NEGATIVE
**Statement.** (Growing-modulus cap.) Fix ε>0 and let z = (2−ε)log n with n large. Then there is an integer c ∈ [1, n²] for which
x_k := k² + k + c (n ≤ k ≤ 2n) has three properties:
(i) every x_k ∈ [n², 7n²] has no prime factor ≤ z;
(ii) the gaps x_{k+1} − x_k = 2k+2 are strictly increasing, each with multiplicity 1, so every AP-multiplicity cap holds;
(iii) the sequence is therefore a legal play of the congruence game with S = {primes ≤ z} on the index window [n,2n], scoring 1 per step.
Consequence. The growing-modulus congruence game cannot certify average gap multiplicity < 1 on [n,2n] unless z ≥ (2−o(1))log n.
It cannot certify d_k ≥ (2+δ)k either, so on its own it cannot get past liminf q_n/n² ≥ 1 or prove → ∞. The period-averaging regime
of the game needs M_z = e^{θ(z)} ≤ n, i.e. z ≤ (1+o(1))log n, and that regime lies strictly inside this dead zone.
So the assignment's plan to push z up to log n provably gives no more than the congruence cap 1. Least-split-prime input is needed for
z ≥ 2 log n: GRH gives ≪ (log n)², and Linnik–Vinogradov gives n^{1/2+ε}. Neither falls inside the averaging regime.
**Beyond.** the frontier's "congruence cap 1" covers only bounded S and explicitly leaves open "moduli growing with n (p ≍ log n and beyond)".
C3 closes p ≤ (2−ε)log n for every congruence-only argument.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Euler/Rabinowitsch prime-producing quadratics plus CRT (the frontier's 'congruence cap 1' barrier, made uniform in z via primorial e^{θ(z)} ≤ n²)", "why": "Choosing c by CRT so that 1−4c is a non-residue mod every odd p ≤ z, with c odd, is possible in [1,n²] precisely because the primorial e^{θ(z)} ≈ n^{2−ε} < n²; this is a one-step uniform version of the known bounded-S Euler-quadratic barrier. It usefully rules out a congruence-only plan up to z ≈ 2 log n but gives no progress on the problem.", "panel": [{"verdict": "routine", "cite": "Euler/Rabinowitsch prime-producing quadratics plus CRT (the frontier's 'congruence cap 1' barrier, made uniform in z via primorial e^{θ(z)} ≤ n²)", "significance": 1, "why": "Choosing c by CRT so that 1−4c`
**Proof or evidence.**

The construction is CRT. For each odd p ≤ z pick a quadratic non-residue u_p mod p and set c ≡ (1−u_p)/4 mod p; also take c odd.
Let c be the least positive solution mod 2∏_{3≤p≤z}p. Then c ≤ 2e^{θ(z)} = e^{(2−ε+o(1))log n} ≤ n². For odd p ≤ z, x_k ≡ 0 mod p would
force (2k+1)² ≡ 1−4c ≡ u_p, which is impossible. Also x_k = k(k+1)+c is odd. The range: n² ≤ x_k ≤ 4n²+2n+n² ≤ 7n².
The gaps are x_{k+1}−x_k = 2k+2. A play with multiplicity 1 at every step meets every cap, since cap ≥ 1 always.

## [valid-routine] r1s3/C2 PROVED STRUCTURE
**Statement.** rho_z is nonincreasing in z. Hence rho_inf := lim rho_z exists, and 1 <= rho_inf <= rho_17 = 1.157020.
**Beyond.** Not on the blackboard. It makes "rho_z -> 1" a statement about one limit.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Monotonicity of the congruence-game value in z follows because adding primes adds constraints, and a bounded monotone sequence converges; the bound rho_inf >= 1 is the known Euler/Rabinowitsch congruence cap. It gives no new bound on liminf q_n/n^2 and does not touch the growing-moduli core.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Monotonicity of the congruence-game value in z follows because adding primes adds constraints, and a bounded monotone sequence converges; the bound rho_inf >= 1 is the known Euler/Rabinowitsch congruence cap. It gives no new bound on liminf q_n/n^2 and does not touch the growing-moduli core."}, {"verdict": "routine", "cite": null, "significance": 0, "why": "Monoton`
**Proof or evidence.**

Let z < z', S ⊂ S', R = M'/M. Take a z'-game path over j periods of length M' and reduce its states mod M.
Steps with M ∤ v are legal z-moves. Steps with M | v, M' ∤ v leave s mod M unchanged and satisfy m_v <= p(2v)-2,
because m+1 consecutive units along step 2v mod p(v) ∈ S' are impossible once m+1 >= p(v). So
jG_{z'} <= (jR·G_z + O(1)) + j·sum_{w mod R, w≢0} (p(2Mw)-2).
In that last sum, p(2Mw) depends only on w mod R (the least prime of S'\S not dividing w). Averaging over all w gives
M·tau_z = (1/R)·[sum_{w≢0} + M'·tau_{z'}], so sum_{w≢0} = M'(tau_z - tau_{z'}). Divide by jM' and let j -> ∞:
G_{z'}/M' <= G_z/M + tau_z - tau_{z'}, i.e. rho_{z'} <= rho_z.
Lower bound: the Euler/Rabinowitsch quadratic path (m = 1 at every step, discriminant a nonresidue mod every p in S)
gives G_z >= M-1, so rho_z >= 1 - 1/M + tau_z > 1.

## [valid-routine] r1s4/C3 PROVED CONDITIONAL
**Statement.** Assume UHL_conv. Fix A > 3/2. For all large X, put m = L+1 with L = ⌈A log X/loglog X⌉, take D ≤ X, and take s_j = Σ_{t<j}(j−t)e_t with e_t ≥ 0 and Σe_t ≤ X. Then #{(x,d) ∈ [X]×[D] : x+jd+s_j prime for all j ≤ L} ≤ C₀^m 𝔖₂(s) XD/(log X)^m. Conclusion: q_n/n² → ∞. More precisely, q_n ≥ n²(log n)^δ for large n, for every δ < 1 − 3/(2A).
**Beyond.** This is the corrected form of T4. It shows exactly which uniformity is needed: restriction to convex patterns at length ≥ (3/2+ε)log X/loglog X.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "At L ≈ A log X/loglog X with A > 3/2 and gaps ≍ √X, the assumed bound C₀^m 𝔖 XD/(log X)^m is below 1, so UHL_conv simply asserts that the relevant convex prime windows do not exist. That is a nonexistence hypothesis stronger than the frozen core, and q_n/n² → ∞ then follows by a standard union bound. The value lies only in pinpointing the 3/2 log X/loglog X threshold, not in any real conditional progress.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "At L ≈ A log X/loglog X with A > 3/2 and gaps ≍ √X, the assumed bound C₀^m 𝔖 XD/(log X)^m is below 1, so UHL_conv simply asserts that the relevant convex prime windows do not exist. That is a nonexistence hypothesis stronger than the frozen core, and `
**Proof or evidence.**

- **Setup.** Suppose q_n ≤ Cn² with C = (log n)^δ for infinitely many n. Put X = Cn².
- **Gap bound.** By the [Lean] convex tail, for i ≤ 3n/4 we have d_i ≤ q_n/(n−i) ≤ 4Cn =: D.
- **A cheap window.** The increments e_i = d_{i+1} − d_i ≥ 0 over [n/2, 3n/4] sum to ≤ 4Cn. There are ≥ n/(8L) disjoint windows of length L, so one window has Σe ≤ 32CL. That window is (x, d, s) = (q_i, d_i, s(e)) with x ≤ X and d ≤ D, and s is convex.
- **Counting patterns.** The number of patterns is ≤ C(32CL+L, L) ≤ (e(32C+1))^L.
- **Union bound.** By UHL_conv and C2(i), the number of windows is ≤ X·D·(e(32C+1))^L·(C₀·5 e^{0.23} log m/log X)^m. Here log m ≤ loglog X and C = (log X)^{δ+o(1)}. So the total is ≤ exp((3/2)log X − m((1−δ)loglog X − logloglog X − O(1))) = X^{3/2 − A(1−δ) + o(1)} → 0.
- **Contradiction.** For large X the total is < 1, contradicting the existence of the window. ∎

## [valid-routine] r2s1/C3 PROVED STRUCTURE
**Statement.** Let q be a convex prime sequence, and let i..i+ℓ−1 be a stretch on which the gaps increase by exactly 2 at each step (e = 2). Put d = q_{i+1} − q_i, D = (d−1)² − 4q_i and Q ≥ |D|. Assume ℓ ≥ Q^{1/6+2ε}, Q is large and q_i > ℓ.

Then D is fundamental, D ≡ 5 (mod 8), and χ_D(p) = −1 for all p ≤ ℓ. Moreover q_{i+j} = F_D(x₀ + j) for j < ℓ, where F_D(x) = x² + x + (1−D)/4 and x₀ = (d−2)/2 is an integer.

Distinct e = 2 runs on the same F_D use disjoint x-intervals. Hence the e = 2 runs of the sequence with q ∈ [Y, Z] that lie on one F_D have total length ≤ √Z + 1.
**Beyond.** It turns "same polynomial" (the KNOWN discriminant invariant) into "one of |E| explicit Rabinowitsch–Euler polynomials". So long e = 2 runs are forced onto exactly the polynomials behind the congruence-cap barrier.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Follows from the KNOWN discriminant invariant / split-prime run argument plus Linnik–Vinogradov (least split prime ≪ |D|^{1/4+ε}); Rabinowitsch–Euler polynomial form is completing the square", "why": "Completing the square gives F_D; a root mod any p ≤ ℓ kills the run; applying Linnik–Vinogradov to D/f² with f > ℓ forces fundamentality (hence the 1/6 exponent); disjointness is monotonicity. It is a clean structural normalization but does not get past the Linnik–Vinogradov or congruence-cap barriers.", "panel": [{"verdict": "routine", "cite": "Follows from the KNOWN discriminant invariant / split-prime run argument plus Linnik–Vinogradov (least split prime ≪ |D|^{1/4+ε}); Rabinowitsch–Euler polynomial form is completing the square", "signif`
**Proof or evidence.**

- On the stretch, q_{i+j} = P(j) = j² + (d−1)j + q_i. This is monic with D = (d−1)² − 4q_i, and C2 applies.
- b = d − 1 is odd. With t = (b−1)/2 = x₀: (j+t)² + (j+t) + (1−D)/4 = j² + (2t+1)j + t² + t + (1−D)/4. Here t² + t + (1−D)/4 = (b² − 1 + 1 − D)/4 = q_i, so this equals P(j).
- Disjointness: F_D(x+1) − F_D(x) = 2x + 2 is strictly increasing for x ≥ 0. Terms of q are distinct, so distinct terms correspond to distinct x. WLOG x ≥ 0, using the symmetry x ↦ −1−x.

## [valid-routine] r2s1/C5 PROVED STRUCTURE
**Statement.** Let P = ax² + bx + c, I an interval of N integers, and W ⊆ I a union of m intervals with |W| ≥ cN, such that P(x) is a prime > N for all x ∈ W. Then for every prime p ∤ 2a with p < cN/(m+2), the symbol (D/p) = −1.
**Beyond.** C1 needs the minimum run length. C5 needs only the average length |W|/m, so short runs on the same parabola need not be discarded.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard root-mod-p / pigeonhole argument (cf. Rabinowitsch-type prime-producing quadratics; the team's own 'run has a root mod any split prime ≤ run/2' item)", "why": "If (D/p)≠−1 and p∤2a, P has a root class mod p which W must avoid, so each of the m intervals has length < p and |W| < mp < cN — a one-line pigeonhole replacing minimum run length by average run length. It does not touch the Linnik–Vinogradov 1/4 barrier or the multi-discriminant core.", "panel": [{"verdict": "routine", "cite": "Standard root-mod-p / pigeonhole argument (cf. Rabinowitsch-type prime-producing quadratics; the team's own 'run has a root mod any split prime ≤ run/2' item)", "significance": 0, "why": "If (D/p)≠−1 and p∤2a, P has a root class mod p which W must a`
**Proof or evidence.**

- If (D/p) ≠ −1, then as in C1 there is a class r mod p with p | P(x) for all x ≡ r.
- This progression has ≥ N/p − 1 points in I, and none lies in W (P(x) > N ≥ p).
- I∖W is a union of ≤ m+1 intervals J_k with Σ|J_k| ≤ (1−c)N, and each J_k holds ≤ |J_k|/p + 1 points of the progression.
- So N/p − 1 ≤ (1−c)N/p + m + 1, i.e. p ≥ cN/(m+2).

## [broken] deep/C2 PROVED QUANT
**Statement.** Let q be a convex prime sequence with #{i≤n : Δ³q_i≠0} ≤ n^θ for all large n.
 (a) If θ<5/6, then liminf q_n/n² ≥ 2.
 (b) If A≥1 and θ < 3/4 + 5^{1−A}/20, then liminf q_n/n² ≥ A+1. (For A=1 this gives θ<4/5, superseded by (a). For θ<3/4 it holds for every A, which reproves C1.)
 (c) (Key lemma, e=2 part.) Fix δ∈(0,1/10), θ<5/6, C. For n large with q_n≤Cn², the indices i∈W_δ:=[δn,(1−δ)n] lying in e=2 blocks B with |B∩W_δ| ≥ 2H, H:=n^{1−θ−ε′}, number o(n).
**Beyond.** KNOWN unconditional liminf is 0.864. Under the glitch hypothesis, r2s2 gives nothing for θ≥2/3, and C1 gives nothing for θ≥3/4. (a) gives liminf ≥ 2 for every θ<5/6. The new ingredient is the one-sidedness of the D^{(1)} walk.
**Referee.** `{"valid": false, "first_error": "Proof of (c), pair sieve per row (bound (ii)): L ≥ ¼(Hσ_f)² needs Hσ_f ≥ 1, and the claimed mass(row) ≪ n^{1+8ε}/H² needs σ_f ≫ n^{-2ε}, where σ_f sums 1/p over split primes p∤2f in (2H, k^{1/4+ε}]. Neither is proved. S3 gives only M = k^{1/4+ε} ≥ H^{1-16ε²}, so the range may be empty. Burgess/Linnik–Vinogradov give at most one split prime there, which leaves no pairs p<p' and L = 0. Without (ii), (i) alone gives n^{1+θ}/H^4, i.e. only θ < 4/5, so (a) for 4/5 ≤ θ < 5/6 is unsupported.", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

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

## [broken] deep/C4 PROVED CONDITIONAL
**Statement.** For β∈(0,1/4] let BD(β) be the hypothesis: for every fixed m≥1 and ε>0, every real primitive character χ of conductor k≥k_0(m,β,ε) satisfies Σ_{p≤k^β, p∤m, χ(p)=1} 1/p ≥ k^{−ε}. If BD(β) holds, then #{i≤n: Δ³q_i≠0} ≤ n^θ (all large n) with θ<1−β implies q_n/n²→∞.
 - BD(β) holds for every β>1/4 (Lemma S: Burgess + Siegel). Since the conclusion only improves as β decreases, this recovers C1 (θ<3/4).
 - GRH implies BD(β) for every β>0. Under GRH, Σ_{p≤x}χ(p)log p ≪ √x log²(kx), so for x=k^β the split primes in (x/2,x] have Σ1/p ≫ 1/log x. Hence **BD(β) for all β>0 implies the GOAL (every θ<1)**, under a hypothesis far weaker than GRH. It only excludes characters that are inert at almost all primes up to k^β, measured in Σ1/p with a k^{−ε} margin.
**Beyond.** KNOWN has θ<1 only under GRH (informal), via least split prime ≪ log²D. C4 isolates the exact arithmetic input: the glitch threshold is 1 − (the exponent at which Siegel-strength split-prime density is known). Unconditionally that exponent is 1/4+, which gives θ<3/4.
**Referee.** `{"valid": false, "first_error": "BD(β) is assumed only for each fixed m, with threshold k_0(m,β,ε). The proof applies it with m=2a and sums over (a,D_0), but in the q_n ≤ Cn² regime a ranges up to about n/H = n^{θ+o(1)}, which grows with n. Nothing guarantees k ≥ k_0(2a) uniformly, and split primes dividing 2a cannot be ignored, so (S3) and the Step 6 mass bound are not justified for the summed family.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

Repeat C1 with Lemma S replaced by BD(β) (m=2a), and set Q:=k^β.
 - (S1) still holds: split p∤2a lie in (2H,Q].
 - (S3) becomes: some split p∤2a with p≤k^β exists and p>2H, so k ≥ (2H)^{1/β}.
 - Step 6 gives mass(σ) ≤ c(|J_σ| + k^{2β} + 1)k^ε/H. With S ≤ 1+V/(4kH): Σ_σ mass ≪ k^ε(n + k^{2β} + V k^{2β−1}/H)/H. Here k^{2β} ≤ (c_0n²)^{2β} ≪ n, since β≤1/4.
 - Since 2β−1<0 and k ≥ (2H)^{1/β}, we have k^{2β−1} ≤ (2H)^{2−1/β}. So the last term is ≪ n²H^{−1/β} = n^{2−(1−θ)/β+o(1)}, which is o(n^{1−c}) iff θ<1−β.
 - Small rows: ≪ n^{1+O(ε)}/H each. Field count: Step 4, unchanged.
 - Summing over (a,D_0) gives o(n) long-block mass, which contradicts Step 1(iv). ∎

## [broken] r1s1/C2 PROVED STRUCTURE
**Statement.** Fix α>0 and 0<δ<2α−ε. Let D, D' = D+h be discriminants of runs as in C1, with |D|, |D'| ≤ Q, both runs of length ≥ Q^α, and 0 < |h| ≤ Q^{1/2+δ}. Then D₀ ≠ D₀'. In other words, the joint FIRST STEP can fail only for pairs of distinct members of the bounded set E_α(Q).
**Referee.** `{"valid": false, "first_error": "The step 'With |D₀| ≫ Q^{4α−ε}' is unjustified: the run-length bound ℓ ≪ |D|^{1/4+ε} only gives a lower bound on |D|, not on the fundamental part D₀ (D = D₀f² may have large conductor f and small D₀). Independently, the small-|D| case fails: with only |D| ≥ Q^{4α−ε} one gets |h| ≫ Q^{4α−ε}, which contradicts |h| ≤ Q^{1/2+δ} only if roughly α > 1/4. The authors' caveat that |D| ≍ Q is needed is not among the hypotheses, which give only |D| ≤ Q.", "fixable": false}`
**Adversary.** `{"broken": true, "how": "The proof only works when |D| ≍ Q, but the claim allows any |D| ≤ Q. In the small-|D| branch, the bound gives only |h| ≫ |D0|^{1/2}|D|^{1/2} ≥ Q^{4α−ε} (extreme case f=1, |D|≈|D0|≈Q^{4α−ε}). That contradicts |h| ≤ Q^{1/2+δ} for all δ<2α−ε only if α ≥ 1/4. For α < 1/4−ε/2, take D=D0, D'=4D0 (f=1, f'=2), h=3D0 with |D0|≈Q^{4α} and δ in (4α−1/2, 2α−ε): all size constraints hold and D0=D0', so the proof does not exclude this. Also, the needed lower bound is on |D0|, but the cited run-length bound ℓ ≪ |D|^{1/4+ε} constrains |D|, not D0. The E_α(Q) conclusion is never argued.", "severity": "fixable"}`
**Proof or evidence.**

Suppose D₀ = D₀'. Then |h| = |D₀|·|f'²−f²| ≥ |D₀|·(f+f') ≥ |D₀|^{1/2}·|D|^{1/2}. With |D₀| ≫ Q^{4α−ε} this gives |h| ≫ Q^{2α−ε/2}·|D|^{1/2}. This contradicts |h| ≤ Q^{1/2+δ} when |D| ≫ Q^{1−o(1)}. For smaller |D| the condition ℓ ≥ Q^α with ℓ ≪ |D|^{1/4+ε} already forces |D| ≥ Q^{4α−ε}. (Caveat: this route needs |D| ≍ Q, which holds at scale n since D ≍ n².)

## [broken] r1s1/C3 PROVED NEGATIVE
**Statement.** Suppose that among any R consecutive long runs at scale n, at least one has length ≤ n^{β}. This includes the FIRST STEP for consecutive pairs (R=2, β=1/4). Then the glitch counting still only gives #glitches ≥ n^{1/2−ε}, i.e. no improvement over KNOWN θ<1/2.
**Referee.** `{"valid": false, "first_error": "Paragraph 1, the step 'the hypothesis is consistent with alternating run lengths n^{1/2+ε} (allowed by Linnik–Vinogradov)': Linnik–Vinogradov only says that a single run of length about n^{1/2+ε} is not excluded. The scenario needs about n^{1/2-ε} such runs, each with a discriminant whose least split prime is at least about n^{1/2+ε}. Joint consistency with the constraints used by glitch counting is never checked: distinct D of this kind are very rare by large sieve, and the same-D route via repair glitches rests on an undefined set E_α and an unproved bound of '≤ n^θ runs per D'. The identity and the 0,4,4,0 computation are correct, but they do not establish the barrier.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

The hypothesis is consistent with alternating run lengths n^{1/2+ε} (allowed by Linnik–Vinogradov) and n^{β}. Total length n then needs only ≍ n^{1/2−ε} runs. To gain, one needs a bound on the number of long runs, not on tuples.
Moreover the discriminant walk Δ_i := (d_i−1)²−4q_i satisfies the exact identity Δ_{i+1}−Δ_i = (e_i−2)(2d_i+e_i), checked by expansion. So "repair" glitches such as e = 0,4,4,0 have zero net jump (−4d+(4d+8)+(4d+24)−4(d+8) = 0). They return to the SAME polynomial. Runs per discriminant are therefore not bounded by any split-prime statement. The residual problem is to count the runs of ONE quadratic P_D(x)=x²+x+(1−D)/4, for D₀ in the O(1)-element set E_α. Under the glitch hypothesis this costs ≤ n^θ runs per D.

## [broken] r2s1/C1 PROVED STRUCTURE
**Statement.** Let P(x) = ax² + bx + c ∈ ℤ[x] with a ≥ 1, D = b² − 4ac and ℓ ≥ 2. Suppose P(j) is a prime > ℓ for every j = 0, …, ℓ−1. Then:
- (i) for every odd prime p ≤ ℓ with p∤a, the Legendre symbol (D/p) = −1;
- (ii) if a is odd, then D ≡ 5 (mod 8).

Consequently D is not a square. Write D = D₀f² with D₀ fundamental. Then every prime factor of f either divides a or is > ℓ, and χ_{D₀}(p) = χ_D(p) = −1 for all p ≤ ℓ with p∤a (p∤2a when a is even).
**Beyond.** This is the lemma the lead sketched but did not check. The KNOWN "split prime" remark only covers (D/p) = 1. Here the ramified case and the 2-adic case are included, and the conclusion about the conductor is stated.
**Referee.** `{"valid": false, "first_error": "The step 'Consequently D is not a square' (and its proof) for even a: it applies (i) at p=3 or at the least prime not dividing a, but (i) requires that odd prime to be <= ℓ, which the hypothesis ℓ >= 2 does not guarantee (the proof itself admits 'this works once ℓ ≥ that prime'). Counterexample: P(x)=(2x-1)(8x-3)=16x^2-14x+3, ℓ=2: P(0)=3 and P(1)=5 are primes >2, but D=4 is a square, so D0, f and χ_{D0} are not even well-defined as claimed.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The corollary 'Consequently D is not a square' is false without an extra hypothesis. P(x)=12x^2-12x+3=3(2x-1)^2 with l=2 has P(0)=P(1)=3, primes > 2, and a=12>=1. (i) is vacuous (no odd prime <= 2) and (ii) does not apply (a even), yet D=144-144=0 is a square, so D=D0 f^2 and the conductor/character statements are meaningless. More generally p(2x-1)^2 for any odd prime p works. The proof itself concedes the even-a case only 'works once l >= that prime', which is not a hypothesis of the claim. Parts (i) and (ii) are correct.", "severity": "fixable"}`
**Proof or evidence.**

- (i) Suppose (D/p) ∈ {0, 1}. Pick s with s² ≡ D (mod p). Since p∤2a, put r ≡ (s − b)(2a)^{−1} (mod p). Then 4aP(r) = (2ar + b)² − D ≡ s² − D ≡ 0, so p | P(r) because p∤4a. Every residue class mod p meets {0, …, ℓ−1}, since p ≤ ℓ. So p | P(j) for some j < ℓ. As P(j) is prime, P(j) = p ≤ ℓ, a contradiction.
- (ii) P(0) = c and P(1) = a + b + c are odd, so c is odd and a + b is even, hence b is odd. Then b² ≡ 1 and 4ac ≡ 4 (mod 8), so D ≡ 5 (mod 8).
- D is not a square: a square would give (D/3) ∈ {0, 1} if 3∤a. If 3 | a, use (ii) when a is odd, or the least prime p∤a; this works once ℓ ≥ that prime. For a = 1 it suffices that ℓ ≥ 2.
- Conductor: if an odd prime p ≤ ℓ with p∤a divides f, then p | D, contradicting (i). If a is odd, 2∤D by (ii), so 2∤f.
- χ_D(p) = χ_{D₀}(p) for p∤f. Every p ≤ ℓ with p∤a has p∤f, so it gets the value from (i) or (ii). For p = 2, D₀ ≡ D·f^{−2} ≡ 5 (mod 8), since f is odd.

Numerical check (rough.py): over 13,289 quadratics with a ∈ {1, 2, 3, 4, 6}, |b| ≤ 60, c < 4000, prime runs of length 3 to 40 and all values > ℓ, there were 0 violations.

## [broken] r2s1/C2 PROVED STRUCTURE
**Statement.** Fix ε > 0. If Q > Q₀(ε), P(x) = x² + bx + c is prime > ℓ at j = 0..ℓ−1, |D| ≤ Q and ℓ ≥ Q^{1/6+2ε}, then D is a fundamental discriminant, D ≡ 5 (mod 8).

For general a ≥ 1, the same holds with "D = D₀g², where every prime of g divides a". This assumes the Linnik–Vinogradov variant "least prime p∤a with χ_{D₀}(p) = 1 is ≪_{a,ε} |D₀|^{1/4+ε}". That variant is standard: run the same proof with Burgess applied to χ·1_{(n,a)=1}, which reduces to plain Burgess sums by Möbius over d | a.
**Beyond.** This repairs r1s1/C2. That claim broke because LV bounds |D₀|, not |D|. Roughness closes the gap; no separate small-|D| branch is needed, because f² = |D|/|D₀| ≤ Q/|D₀| holds whatever |D| is. It also sharpens r1s1/C1's count of D's, from |E|·Q^{1/2−2α+ε} down to |E| (a = 1), for every α > 1/6.
PROOF (a = 1):
- By C1, χ_{D₀}(p) = −1 for every prime p ≤ ℓ, including p = 2.
- LV gives a prime p₁ ≪_ε |D₀|^{1/4+ε} with χ_{D₀}(p₁) = 1. So ℓ < p₁, and |D₀| ≫ ℓ^{4/(1+4ε)}.
- Suppose f > 1. By C1, f has a prime factor > ℓ, so f > ℓ. Then ℓ² < f² = |D|/|D₀| ≪ Q·ℓ^{−4/(1+4ε)}. Hence ℓ ≪ Q^{(1+4ε)/(6+8ε)} ≤ Q^{1/6+ε}, which contradicts ℓ ≥ Q^{1/6+2ε} for large Q.
- So f = 1, and D = D₀ is squarefree with D ≡ 5 (mod 8).
- For a > 1 the argument is identical, applied to the part of f made of primes ∤ a.
**Referee.** `{"valid": false, "first_error": "The a=1 argument is correct. The general-a claim ('the same holds' with D = D0 g^2) still asserts D ≡ 5 (mod 8). That rests on the 'no root mod 2' step, which fails when 2 | a. For a even, P(0)=c and P(1)=a+b+c odd force b odd, so D = b^2 - 4ac ≡ 1 (mod 8). The mod-8 conclusion is therefore unproved for even a and contradicts what the hypotheses force (it could hold only if no such P exists). Q0 must also depend on a.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [broken] r2s1/C4 PROVED REDUCTION
**Statement.** Fix θ < 2/3, ε > 0 small and C ≥ 1. Let q be a convex prime sequence with #{i ≤ n : Δ³q_i ≠ 0} ≤ n^θ for all large n. Let n be large with q_n ≤ Cn², and let T₂(n) be the number of indices in [n/4, n/2] lying in e = 2 runs.

Then T₂(n) ≤ o(n) + Σ_{D∈E_n} T_{2,D}(n), where E_n is the set E of r1s1/C1 (at Q = 8C²n², α = (1−θ−ε)/2), so |E_n| ≤ 2/ρ(2/α) + o(1) = O_θ(1). Here T_{2,D} counts e = 2 run indices lying on F_D. Every D ∈ E_n is fundamental, with:
- χ_D(p) = −1 for all p ≤ n^{1−θ−ε};
- n^{4(1−θ)−5ε} ≪ |D| ≤ 8C²n².

In particular, if T₂(n) ≥ βn, then some F_{D_n} is prime at ≥ (β/|E_n| − o(1))n integers x ∈ [0, √C·n + 1]. These x form at most n^θ intervals, each of length ≥ n^{1−θ−ε}.
**Beyond.** The KNOWN result stops at θ < 1/2. For θ ∈ [1/2, 2/3), this reduces the e = 2 part of the glitch problem to excluding a positive density of primes for one exceptional Euler polynomial. That is the "joint statement about many discriminants" the barriers leave open.
**Referee.** `{"valid": false, "first_error": "Step placing D in E_n via r1s1/C1: E is taken at Q = 8C^2 n^2, alpha = (1-theta-eps)/2, so (assuming C1 requires inertness up to Q^alpha) membership needs chi_D(p) = -1 for all p <= Q^alpha = (8C^2)^alpha n^{1-theta-eps}. The kept runs only have length >= n^{1-theta-eps}, so inertness is proved only up to n^{1-theta-eps}, a constant factor short; the primes in between are unaccounted for. Second, concrete error: the counting step's x-range [0, sqrt(C) n + 1] assumes F_D(x) >= x^2, i.e. D < 0, but the proof's own bound |D| <= max((d-1)^2, 4q) allows D > 0 up to (d-1)^2, giving x up to about C n rather than sqrt(C) n.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The x-range [0, sqrt(C) n + 1] relies on F_D(x) >= x^2, which only holds for D<0. Convexity allows q_i to be small (~n^{1+o(1)}) while d_i ~ Cn, so D=(d-1)^2-4q can be positive (up to ~4C^2 n^2). Then F_D(x) = (x+1/2)^2 - D/4 <= Cn^2 only gives x <= sqrt(C+2C^2) n + 1. Minor gaps: E is defined at Q^alpha = (8C^2)^alpha n^{1-theta-eps}, which exceeds the guaranteed inert range n^{1-theta-eps} (shrink alpha slightly); run pieces cut at n/4 or n/2 can be shorter than n^{1-theta-eps} (at most two, total o(n), drop them). The rest checks out: d_i <= 2Cn, |D| <= 8C^2 n^2, the short-run o(n) bound, the Q^{1/6+2eps} threshold for theta < 2/3 - 5eps, inertness, |E| = O(1/rho(2/alpha)) via Polya-Vinogradov on chi_D chi_D', the least-split-prime lower bound on |D|, and the pi`
**Proof or evidence.**

- For i ∈ [n/4, n/2], the convex tail gives d_i ≤ Cn²/(n/2) = 2Cn. Then |D| ≤ max((d−1)², 4q) ≤ 8C²n² = Q.
- e = 2 runs shorter than n^{1−θ−ε} have total length ≤ (n^θ+1)·n^{1−θ−ε} = o(n), so drop them.
- The rest have ℓ ≥ n^{1−θ−ε} ≥ Q^{1/6+2ε}, because (1−θ−ε)/2 > 1/6 + 2ε for small ε. C3 applies, so D is fundamental and the run lies on F_D.
- r1s1/C1 then puts D₀ = D in E_n. The bound on |D| from below is LV, as in C2.
- Counting: the C3 disjointness bounds the x-range by √(Cn²) + 1, and pigeonhole over E_n gives one D carrying the stated share.
- The run structure gives ≤ n^θ intervals.

REMARK: Unconditionally the sieve cannot finish this off. All p ≤ n^{1−θ−ε} ≥ n^{1/3} are inert, so the upper-sieve density ∏_{p≤z}(1 − ω(p)/p)(1 − 1/p)^{−1} is ≍ log n for every admissible z ≤ n^{1/2}. A positive proportion of primes is then sieve-consistent. Killing it needs L(1, χ_{D_n})-type input: Siegel territory, i.e. r2s3's dichotomy.

## [broken] r2s3/C1 PROVED STRUCTURE
**Statement.** Fix ε>0, K, G and an even E. Let X ≥ X₀(ε,K,G,E). Let q_u<…<q_v be primes in [X/K, X], convex (g_i = q_{i+1}−q_i nondecreasing), with all gaps ≤ G√X.
- A *run* is a maximal index interval on which e_i = g_{i+1}−g_i takes a constant value e. Its *length* ℓ is its number of points.
- On a run starting at q_u with first gap g we have q_{u+j} = P(j) := a j² + b j + c, where a = e/2, b = g−a, c = q_u. Its discriminant is D = b²−4ac. Write D = D₀f² with D₀ a fundamental discriminant, and χ = χ_{D₀}.

Then for every run R of length ℓ ≥ X^{1/6+ε} with 2 ≤ e ≤ E:
- (i) D is not a square. Every prime p ≤ ℓ with p ∤ 2a has χ(p) = −1. And f | (2a)^∞, i.e. every prime factor of f divides 2a.
- (ii) If a is squarefree, then f ∈ {1,2}. If a is odd (e ≡ 2 mod 4), then f = 1.
- (iii) Fix a field K = Q(√D₀) and a squarefree a ≤ E/2. Consider the chain indices lying on runs R as above with second difference 2a and field K. Their number is ≤ C(E,G,K)·√X / L(X^{1/5}), where L(z) = 1 + Σ_{3≤p≤z, p∤2a·D₀} (1+χ(p))/p.
- (iv) Fix e = 2. All runs as above in a given field K lie on the single parabola Π_K = {(y²−D₀)/4 : y odd}. Two such runs therefore lie on the same parabola, and the chain between them satisfies the re-entry identity Σ_i (e_i−2)(2g_i+e_i) = 0 (see C2).
**Beyond.** - The frontier map says LV/Siegel barriers "do not rule out joint statements about many discriminants along the walk", and large-sieve sparsity "does not rule out sieving in the index variable run by run". C1 is such a joint statement.
- Round 1 (r1s1/C1) bounded the number of fields of long runs. C1 adds two things: all long runs in a field collapse onto O(1) parabolas (exactly one for e = 2), and that field's carrying capacity is ≪ √X/L_K.
- It makes the Siegel half of the dichotomy precise: a counterexample whose long runs carry a positive proportion must use a character χ with Σ_{p≤X^{1/5}} (1+χ(p))/p = O(1).
- (r2s1 is repairing r1s1/C2 with the roughness idea. Part (i) is a self-contained version of that roughness step and uses only LV. It does not use the r1s1 bound on f.)
**Referee.** `{"valid": false, "first_error": "Step (c) / claim (ii), second sentence: 'f = 1 for odd a' is only proved for odd p with p || a, i.e. squarefree a. For odd non-squarefree a (e.g. a=9, e=18 ≡ 2 mod 4), (c) forces 3|b, so D = 9(b'^2-4c) and 3 | f necessarily; the claim would then assert that no such long runs exist, which is unproved. (Secondary: in the corollary, L_K omits p | D_0, so L_K = O(1) does not give Σ_p(1+χ(p))/p = O(1), and (H_pret) as stated does not imply L_K → ∞ since Σ_{p|D_0} 1/p can be ~ log log log X.)", "fixable": true}`
**Adversary.** `{"broken": true, "how": "Assertion (ii), second sentence ('If a is odd (e ≡ 2 mod 4), then f = 1') is stated without a squarefree hypothesis, but the proof (c) only treats odd p with p ∥ a. For odd non-squarefree a it is false whenever a long run exists: e.g. e = 18, a = 9. The kill-lemma step forces 3 | b, b = 3b', so D = 9(b'^2 − 4c), and since v_3(D_0) ≤ 1 for a fundamental discriminant, 3 | f, so f ≠ 1. Same for any a with p^2 | a, p odd. The rest checks out: kill lemma, LV/Burgess conductor step (exponent (1/4)/(3/2) = 1/6), the 2-adic analysis for squarefree a, the large sieve count, and the re-entry identity D_{i+1} − D_i = (e_i − 2)(2g_i + e_i) with D_i = (g_i − 1)^2 − 4q_i. Fix: require a odd AND squarefree in (ii). Minor: the corollary's 'i.e. Σ_{p≤X^{1/5}}(1+χ(p))/p = O(1)' igno`
**Proof or evidence.**

(a) *Kill lemma.* Let p ≤ ℓ be prime with p ∤ 2a, and suppose (D/p) ≠ −1 (Legendre symbol, value 0 allowed).
- Since 4aP(j) = (2aj+b)² − D and 2a is invertible mod p, some residue j₀ mod p satisfies p | P(j₀).
- Take j₀ ∈ [0, p−1] ⊆ [0, ℓ−1]. Then P(j₀) is a chain prime divisible by p, so P(j₀) = p.
- That is impossible, because P(j₀) ≥ X/K > X^{1/6+ε} ≥ ℓ ≥ p for X large. Hence (D/p) = −1 for all such p.
- If D were a square, then (D/p) ∈ {0,1} for every p. Taking p = the least prime ∤ 2a (≤ 3 + log E·O(1) < ℓ) gives a contradiction.
- (D/p) = −1 implies p ∤ D, so p ∤ f. For p ∤ f we have (D/p) = (D₀/p)(f/p)² = χ(p). This proves the first two assertions of (i).

(b) *Conductor.* Write f = f′f″, where f″ collects the primes dividing 2a. By (a), every prime factor of f′ exceeds ℓ. Suppose f′ > 1. Then f′ > ℓ.
- From |b| ≤ g ≤ G√X and 4a·c ≤ 2E·X we get |D| ≤ (G²+2E)X =: C₁X. Hence |D₀| ≤ C₁X/ℓ².
- By (a), χ(p) = −1 for all p ≤ ℓ with p ∤ 2a. Apply LV with m = E!.
  - If |D₀| is large: ℓ < |D₀|^{1/4+ε'} ≤ (C₁X/ℓ²)^{1/4+ε'}. So ℓ^{3/2+2ε'} < (C₁X)^{1/4+ε'}, i.e. ℓ < (C₁X)^{(1/4+ε')/(3/2+2ε')} < X^{1/6+ε} once ε' is small and X is large.
  - If |D₀| is bounded: ℓ < max over the finitely many small D₀ of the least such p.
- Either way this contradicts ℓ ≥ X^{1/6+ε}. So f′ = 1. Also χ ≠ principal, since D is not a square.

(c) *p-adic part.* Let p | 2a. The goal is to bound v_p(D) ≤ v_p(4a)+1 in the cases below.
- If p | a and p ∤ b, then P(j) ≡ bj + c (mod p) has a root. That gives p | P(j₀) with j₀ < p ≤ ℓ, contradicting (a)'s argument. So p | a ⇒ p | b.
- **Odd p with p ∥ a.** v_p(4ac) = 1 since p ∤ c (c is a prime > p). Also v_p(b²) ≥ 2. So v_p(D) = 1 and p ∤ f.
- **p = 2, a odd.** b = g − a is odd because g is even. So D is odd and 2 ∤ f.
- **p = 2, 2 ∥ a.** v₂(4ac) = 3 and v₂(b²) is even ≥ 2. So v₂(D) ∈ {2,3} and v₂(f) ≤ 1.
- Hence f ∈ {1,2} for squarefree a, and f = 1 for odd a. This is (ii).

(d) *Parabolas.* For fixed (a, D), the run values are P(j) = (y²−D)/(4a) with y = 2aj+b ≡ b mod 2a, and y² ≡ D mod 4a.
- So the runs with given (a, D) lie on at most 2a ≤ E polynomial families P_β(j) = (( 2aj+β)² − D)/(4a), β mod 2a.
- For e = 2 (a = 1): D is odd, b is odd, and Π = {(y²−D)/4 : y odd}. This is one parabola and D = D₀.

(e) *Large sieve.* Fix one family P_β with discriminant D = D₀f², f ∈ {1,2}.
- If P_β(j) ∈ [X/K, X] is prime and p ≤ z = X^{1/5} < X/K, then P_β(j) ≢ 0 mod p. So j avoids the root set Ω_p of P_β mod p.
- For odd p ∤ 2aD we have ω(p) = 1 + χ(p) ≤ 2 < p.
- The admissible j form ≤ 2 intervals (y > 0 and y < 0), each of length ≤ √(X/a) + 1.
- By LS with 𝒫 = {odd p ∤ 2aD₀}, Q = z, keeping only the q = 1 and q = p terms of L:
  #{prime values} ≤ 2(√X + 1 + X^{2/5}) / (1 + Σ_{p≤z, p∤2aD₀} (1+χ(p))/(p−1−χ(p))) ≤ 6√X / L(z).
- A chain index on a run R lies on R's family. Distinct chain indices give distinct primes. So the number of indices in (iii) is ≤ (#families)·6√X/L(z) ≤ 2·E·6√X/L(X^{1/5}): at most 2 choices of f, ≤ E choices of β. ∎

COROLLARY (dichotomy, conditional form).
- Suppose a chain in [X/K, X] of length N ≥ c√X has ≥ δN indices on runs of length ≥ X^{1/6+ε}, with e ≤ E and squarefree e/2, and these runs come from ≤ F fields.
- Then some field K among them has L_K(X^{1/5}) ≤ 12E²F/(cδ), i.e. Σ_{p≤X^{1/5}} (1+χ_K(p))/p = O(1).
- By r1s1/C1 (validated), F = O(1) for monic runs.
- Hence under (H_pret): "for real primitive χ of conductor ≤ C₁X, Σ_{p≤X^{1/5}} (1+χ(p))/p → ∞". (H_pret) is implied by GRH and is much weaker than the least-split-prime bound.
  - Under (H_pret), long monic runs carry o(N) points.
  - This holds even when the glitch count is as large as n^{2/3−ε} (run length n^{1/3+ε}). The known unconditional glitch theorem needs θ < 1/2, and the GRH glitch theorem needs least split prime ≪ log²D.
  - CAVEAT: this corollary alone does NOT give CORE. Chain points on short runs (< X^{1/6+ε}) are untouched.

## [broken] r2s3/C2 PROVED STRUCTURE
**Statement.** For any convex chain and any even e*, put D^{(e*)}_i := (g_i − e*/2)² − 2e*·q_i, the discriminant of the local quadratic of second difference e* through q_i, q_{i+1}. Then
D^{(e*)}_{i+1} − D^{(e*)}_i = (e_i − e*)(2g_i + e_i).
- D^{(e*)} is constant exactly on runs of second difference e*. Each glitch moves it by ≥ 4g_i ≍ √X.
- If two runs of second difference e* have equal D (by C1(iv), this is automatic for two long e = 2 runs in one field), then Σ_{between} (e_i − e*)(2g_i + e_i) = 0.
- So the chain between them contains a step with e_i < e* and one with e_i > e*. For e* = 2, the step with e_i < e* is a repeated gap (e_i = 0).
- Adjacent runs (e, e′), e ≠ e′, sharing the gap g after q_m satisfy D^{(e)} − D^{(e′)} = (e′ − e)(2q_m + g − (e+e′)/4) ≠ 0. So adjacent runs never share a discriminant.
**Referee.** `{"valid": false, "first_error": "Last bullet: the formula D^{(e)}-D^{(e')} = (e'-e)(2q_m+g-(e+e')/4) is correct, but '≠ 0' is unproved and false, since convexity does not bound e'. Counterexample: primes 17,19,23,29,241,659 (gaps 2,4,6,212,418; second differences 2,2,206,206) form an e=2 run adjacent to an e'=206 run sharing g=6 after q_m=23, with e+e'=208=8·23+4·6, and D^{(2)} = D^{(206)} = -67.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The last bullet ('adjacent runs never share a discriminant', i.e. (e'-e)(2q_m+g-(e+e')/4) ≠ 0) is false: nothing bounds e' relative to q_m. The factor vanishes when q_{m+2} = 9q_m + 6g - e. Explicit convex prime chain 3, 5, 17, 107 (gaps 2, 12, 90; second differences 10, 78): the adjacent runs e=10 and e'=78 share the gap 12 after q_m=5, and D^{(10)} = (12-5)^2 - 100 = -51 = (12-39)^2 - 780 = D^{(78)}. The identity D_{i+1}-D_i = (e_i-e*)(2g_i+e_i) and the other bullets are correct; the nonvanishing needs an extra hypothesis such as e+e' < 8q_m+4g (true when gaps are much smaller than q_m).", "severity": "fixable"}`
**Proof or evidence.**

(none)

## [not validated] deep/C3 CONJECTURED NEGATIVE
**Statement.** the ingredients of C1/C2 cannot reach any θ>3/4 uniformly in C. Those ingredients are: local structure (Step 2), Lemma S at k^{1/4+ε}, field count, 1-D large sieve per stay or per row at level √(length), the D-walk identity with up/down budgets, and short-block counting by glitches.
**Proof or evidence.**

(1) In (b) the recursion's fixed point is x*=1/4, and the stay condition 5θ+x*<4 becomes exactly θ<3/4. With the pair sieve added, the k>n regime still gives x*=1/4: there the stays term is n^{1/2+θ+x}/H², the fixed point of x=(1/2+x)/3 is 1/4, and the threshold 3θ+x<5/2 again gives 3/4.
 (2) Phantom at θ=1−h, h<1/4, for large a. The construction: one field with k≈n and χ(p)=−1 for p≤n^{1/4−ε}, with split primes only in (n^{1/4−ε},n^{1/4+ε}] and Σ1/p≈n^{−ε}. This is consistent with Lemma S and is not excluded by any known result.
 - Rows are the primes f∈[2H,4H], each visited by ≈n^{1/2} stays, so S≈n^{1/2+h}.
 - Each stay has y-length ≈n^{1/2−h} and holds ≈n^{1/2−2h} runs of length H≈n^h ≤ k^{1/4}. Total runs n^{1−h}=n^θ.
 - Every per-stay sieve bound (≈√k/H) and per-row bound (≈n/H) is satisfied. The pair sieve is unavailable since M²≈n^{1/2+2ε}>√n.
 - The D-walk needs S·kF≈n^{3/2+2h} ≤ n² of variation, supplied downward by ≈n^{1/2+2h} steps with e=2a−2 grouped into ≤n^θ blocks. This is possible iff h≤1/4.
 (3) 2-D (ideal-lattice) sieving over (y,f) does not help in the phantom. The lattice 𝔭𝔭′ has λ₂≈√(k·M²)≈n^{3/4}, which exceeds the thin width √|D|≈n^{1/2+h} of the visited region.

## [not validated] r1s2/C2 CONJECTURED OTHER
**Statement.** The game excess ε_z := ρ_S/M − 1 (S = odd primes ≤ z) decays faster than 1/log z. The data:
ε_7=0.4857, ε_11=0.3818, ε_13=0.2486, ε_17≈0.1569 (±0.0004). Successive ratios are 0.79, 0.65, 0.63.
**Proof or evidence.**

(none)

## [not validated] r1s4/C1 PROVED NEGATIVE
**Statement.** Fix any C₀ ≥ 1 and ε > 0. For all large X and every integer k with (1+ε)·log X/loglog X ≤ k ≤ 2 log X, there is an admissible H ⊂ [0, 5 log²X] with |H| = k and an x ∈ [X/2, X] such that x+h is prime for all h ∈ H, yet C₀^k·𝔖(H)·X/(log X)^k < 1. So UHL is false. It stays false when restricted to admissible H, to x ≥ X/2, or to H of diameter O(log²X).
**Beyond.** This refutes T4's hypothesis. KNOWN has only the GT/GTZ abundance barrier, which is for fixed L.
**Proof or evidence.**

- **Primes in [X/2, X].** Let k ≤ 2 log X. Chebyshev/PNT (Rosser–Schoenfeld: π(x) > x/log x for x ≥ 17, π(x) < 1.25506x/log x) gives π(X) − π(X/2) ≥ X/(3 log X) for large X. Cut the increasing list of these primes into N ≥ X/(4k log X) disjoint blocks of k consecutive primes. The blocks are disjoint and lie in an interval of length X/2, so their spans add up to at most X/2. Hence some block p_1 < … < p_k has span y ≤ X/(2N) ≤ 2k log X ≤ 5 log²X.
- **The tuple.** Put x = p_1 and H = {p_j − p_1}. Then x + h is prime for every h ∈ H, so the count is ≥ 1. H is admissible: for a prime ℓ ≤ k we have x+H ⊂ primes > ℓ, so −x mod ℓ is missed and ν_ℓ ≤ ℓ − 1. For ℓ > k, ν_ℓ ≤ k < ℓ.
- **Bounding 𝔖(H).** For ℓ ≤ y we have ν_ℓ ≥ 1, so the local factor (1−ν/ℓ)(1−1/ℓ)^{−k} ≤ (1−1/ℓ)^{−(k−1)}. For ℓ > y, the elements of H are distinct mod ℓ, so ν_ℓ = k. The factor (1−k/ℓ)(1−1/ℓ)^{−k} is then ≤ 1 by Bernoulli, since (1−1/ℓ)^k ≥ 1−k/ℓ. Hence 𝔖(H) ≤ ∏_{ℓ≤y}(1−1/ℓ)^{−(k−1)} ≤ (1.01·e^γ log y)^{k} (Mertens–Rosser–Schoenfeld, y large). Here log y ≤ 2 loglog X + 2, so 𝔖(H) ≤ (4 loglog X)^k for large X.
- **The bound is < 1.** C₀^k 𝔖 X/(log X)^k ≤ exp(log X − k(loglog X − logloglog X − log 4C₀)). For k ≥ (1+ε)log X/loglog X this is exp(−(ε−o(1)) log X) → 0, so it is < 1 for large X. This contradicts count ≥ 1. ∎
- **Literal-statement remark.** The literal UHL also fails trivially: take H = {2,3} and x = 0, so 𝔖 = 0 but the count is ≥ 1. C1 is the robust failure.

## [not validated] r1s4/C2 PROVED NEGATIVE
**Statement.** (i) **2D version.** Let m = L+1 and 𝔖₂(s) = ∏_p ρ_p(s)p^{−2}(1−1/p)^{−m}, where ρ_p(s) = #{(x,d) ∈ F_p² : x + jd + s_j ≢ 0 for all j ≤ L}. For every shift vector s ∈ Z^m, 𝔖₂(s) ≤ e^{0.23m+1}·(1.01 e^γ log m)^{m} for m ≥ m₀. (ii) Consequently the 2-parameter analogue of UHL is false for every C₀ whenever X·D·(C₀·1.01e^γ e^{0.23} log m/log X)^m < e^{−1}. The analogue reads: for all s with |s_j| ≤ X, #{(x,d) ∈ [X]×[D] : x+jd+s_j all prime} ≤ C₀^m 𝔖₂(s) XD/(log X)^m. In particular it is false at D = X^{1/2}, L = ⌈2 log X⌉. (iii) **Step 4 needs a false range.** Step 4 of the T4 sketch needs X^{3/2}e^{O_C(k)}(C′ loglog X/log X)^k < 1. That forces k ≥ (3/2 − o(1))·log X/loglog X, which by C1 lies inside the refuted range k ≥ (1+ε)log X/loglog X.
**Beyond.** It refines the Sieve-dimension barrier note "does not rule out Hardy–Littlewood-quality upper bounds". Such bounds, if uniform over patterns, are false exactly where the union bound needs them, in 1D and in 2D.
**Proof or evidence.**

- **(i), primes p ≤ m.** The j=0 line removes p points, so ρ_p ≤ p² − p and the local factor β_p ≤ (1−1/p)^{−(m−1)}. The product over p ≤ m is ≤ (1.01e^γ log m)^m (Rosser–Schoenfeld).
- **(i), primes p > m.** The m lines x + jd + s_j = 0 have pairwise distinct slopes, so any two meet in exactly one point. Bonferroni gives ρ_p ≤ p² − mp + m(m−1)/2, so ρ_p/p² ≤ 1 − t + t²/2 with t = m/p < 1. For t ∈ [0,1] we have 1 − t + t²/2 ≤ e^{−t} + t³/6 (alternating series). Also (1−1/p)^{−m} ≤ e^{m/p + m/p²}, since −log(1−u) ≤ u+u² for u ≤ 1/2. So β_p ≤ (1 + e t³/6)e^{m/p²} ≤ exp(0.46 m³/p³ + m/p²). Summing over p > m with Σ_{n>m} n^{−3} ≤ 1/(2m²) and Σ_{n>m} n^{−2} ≤ 1/m gives ∏_{p>m} β_p ≤ e^{0.23m+1}.
- **(ii).** Take any m primes P_0 < … < P_L in [X/2, X] and d₀ = 1 ≤ D. Put s_j = P_j − P_0 − j. Then (x,d) = (P_0, 1) is a solution, so the count is ≥ 1, while the bound is < 1 by (i). At L = ⌈2 log X⌉ and D = √X the bound is X^{3/2 − (2−o(1))(loglog X − logloglog X)} → 0.
- **(iii).** Taking logs, X^{3/2}(C′ loglog X/log X)^k < 1 iff k(loglog X − logloglog X − log C′) > (3/2) log X. That needs k ≥ (3/2)(1−o(1)) log X/loglog X > (1+ε) log X/loglog X. ∎
- **Remark.** In 2D the "realizable" threshold log(XD)/(loglog X − logloglog X − O(1)) and the union-bound threshold agree to second order. So a pattern-uniform 2D bound could at best win a battle of constants, which pattern-realization will likely also defeat. A working hypothesis must use the convexity of s.

## [not validated] r2s4/C1 PROVED STRUCTURE
**Statement.** Let P(j) = aj²+bj+c with a ≥ 1, and let P(j) be prime with P(j) > ℓ for 0 ≤ j < ℓ, where ℓ ≥ 2. Let D = b²−4ac = D₀f², with D₀ a fundamental discriminant or 1. For every prime p ≤ ℓ:
- (i) If p ∤ a and p is odd, then p ∤ D and (D/p) = (D₀/p) = −1. If a is odd, then b is odd and D ≡ 5 (mod 8), so χ_{D₀}(2) = −1.
- (ii) If p | a, then p | b, p ∤ c and p | D. If v_p(a) = 1, then p ∤ f and p | D₀ (ramified).
- (iii) Hence every prime p ≤ ℓ dividing f satisfies p² | a. In particular, if a has no square factor p² with p ≤ ℓ, then f is ℓ-rough. The monic case is the roughness lemma from the lead's notes.
**Beyond.** extends the monic roughness lemma and r1s1/C1's hypotheses to every second difference e.
**Proof or evidence.**

Any ℓ ≥ p consecutive j cover every residue class mod p. So if P has a root mod p, then p | P(j) for some j < ℓ. Since P(j) > ℓ ≥ p, P(j) is not prime, a contradiction. So P has no root mod p, for every p ≤ ℓ.
- (i) For odd p ∤ a, the number of roots of P mod p is 1+(D/p). So (D/p) = −1, and in particular p ∤ D. Then p ∤ f, so (D₀/p) = (D/p).
  - For p = 2 with a odd: P(0) = c is odd, and P(1) ≡ a+b+c ≡ b (mod 2) is odd, so b is odd. Then b² ≡ 1 and 4ac ≡ 4 (mod 8), so D ≡ 5 (mod 8). Hence f is odd, D₀ ≡ D·f⁻² ≡ 5 (mod 8), and the Kronecker symbol (D₀/2) = −1.
- (ii) Suppose p | a. Then P ≡ bj+c (mod p). If p ∤ b this has a root, so p | b. Also p ∤ c, since p | P(0) = c would force c = p ≤ ℓ. Then p | b² − 4ac = D.
  - If v_p(a) = 1 and p is odd: v_p(b²) ≥ 2 and v_p(4ac) = 1, so v_p(D) = 1. Hence p ∤ f and p ∥ D₀.
  - If p = 2 and v_2(a) = 1: v_2(4ac) = 3.
    - If v_2(b) ≥ 2, then v_2(D) = 3, so D = 8·odd.
    - If v_2(b) = 1, then D/4 = (b/2)² − (a/2)·2c ≡ 1 − 2 ≡ 3 (mod 4).
    - In both cases f is odd and 2 | D₀.
- (iii) Let p | f with p ≤ ℓ. If p ∤ a, then p | D, contradicting (i) (or D odd when p = 2). So p | a, and by (ii) v_p(a) ≥ 2. ∎

Check: s1.py enumerated 1205 runs with a ≤ 30, 0 ≤ b < 2a, c < 6000 and ℓ ≥ 7. Every flagged case had P(0) = c = p = ℓ, which violates the hypothesis P(j) > ℓ. There were 0 violations under the hypothesis. This also shows the hypothesis is needed.

## [not validated] r2s4/C2 PROVED QUANT
**Statement.** Fix α ∈ (0, 1/4], ε > 0 and an integer M ≥ 1. There is Q₀(α, ε, M) such that the following holds for Q ≥ Q₀. Let 𝓡 be any family of runs P_i = a_i j² + b_i j + c_i as in C1, satisfying:
- ℓ_i ≥ y := Q^α;
- 0 < |D_i| ≤ Q;
- every prime p ≤ y with p | a_i divides M (the a_i may differ; e_i = 2a_i is arbitrary otherwise).

Let E be the set of distinct fundamental parts D₀,ᵢ. Then |E| ≤ (M/φ(M))/ρ(1/(2α)) + ε, where ρ is Dickman's function. (D_i is never a square: by Gauss's lemma, a square D makes P a product of two integer linear factors, which is prime for at most 4 values of j. So we also need ℓ ≥ 5, which holds for large Q.)

Moreover, when M = 1, LV(Linnik–Vinogradov) gives:
- (a) for α > 1/4, 𝓡 = ∅;
- (b) for α > 1/6, f_i = 1, so D_i = D₀,ᵢ, and the number of distinct D_i is ≤ 1/ρ(1/(2α)) + ε.
**Beyond.** r1s1/C1 gives |E| ≤ 2/ρ(2/α), monic only. This result:
- replaces u = 2/α by u = 1/(2α), a factor 4 in u;
- removes the factor 2;
- extends to every e, jointly across e when M = 1.

Numbers (s1.py):

| α | 1/4 | 0.22 | 1/5 | 0.18 | 1/6 | 0.15 | 1/8 | 1/10 |
|---|---|---|---|---|---|---|---|---|
| new bound 1/ρ(1/(2α)) | 3.26 | 5.14 | 7.67 | 13.0 | 20.6 | 42.3 | 204 | 2819 |
| r1s1 bound 2/ρ(2/α) | 6.3e7 | 4.7e9 | ≈7e10 | — | — | — | — | — |
**Proof or evidence.**

- **Characters.** Let χ_i be the Kronecker character of D₀,ᵢ, one run per element of E. These are distinct primitive real characters of conductor |D₀,ᵢ| ≤ Q.
- **Agreement with Liouville.** Let p ≤ y with p ∤ M. Then p ∤ a_i, so C1(i) gives χ_i(p) = −1; this includes p = 2 when 2 ∤ M, since then a_i is odd. So χ_i(n) = λ(n) on T := {n ≤ N : n is y-smooth, (n, M) = 1}.
- **Choice of N.** Fix δ > 0 and take N = Q^{1/2+δ}.
- **Lower bound.** Σ_{n≤N} |Σ_i χ_i(n)|² ≥ k²|T|, where k = |E|.
- **Upper bound.** The diagonal terms give ≤ kN. The off-diagonal terms give ≤ k(k−1)B, where B = max_{i≠j} |Σ_{n≤N} χ_iχ_j(n)|. So k(|T| − B) ≤ N.
- **Bounding B.**
  - Write χ_iχ_j(n) = ψ(n)·1[(n,g)=1]. Here ψ is the primitive character of the fundamental discriminant D* with Q(√D*) = Q(√(D_iD_j)), so ψ is nonprincipal, D* ≠ 1 and m := |D*| ≤ Q². Also g = rad(D_iD_j).
  - Then Σ = Σ_{d|g} μ(d)ψ(d)S(N/d), where S(t) = Σ_{n≤t} ψ(n).
  - Burgess gives |S(t)| ≪_{r,ε} t^{1−1/r} m^{(r+1)/(4r²)+ε}.
    - m is cube-free except possibly for 8 ∥ m. In that case split n by residue mod 8: each class is an interval sum of the primitive character ψ′ of squarefree modulus m/8, and Burgess applies to it.
    - If m ≤ 8, then |S| ≤ 8.
  - For d ≤ Q^{δ/2}: (N/d)^{1−1/r} Q^{(r+1)/(2r²)+2ε} ≤ N·Q^{−(1/2+δ)/r+(r+1)/(2r²)+2ε+o(1)} = N·Q^{−δ/r+1/(2r²)+2ε+o(1)}. Take r > 1/δ and ε small, so the exponent is ≤ −δ/(2r) + 2ε < 0.
  - For d > Q^{δ/2}: Σ_{d|g, d>Z} N/d ≤ N Z^{−1/2} ∏_{p|g}(1+p^{−1/2}). Since ω(g) ≤ 2 log Q, the product is exp(O(√log Q)) = Q^{o(1)}.
  - Also τ(g) = Q^{o(1)}. Hence B ≤ N·Q^{−c(δ)} = o(N).
- **Size of T.** Since rad(M) is fixed and y-smooth for large Q, |T| = Σ_{d|rad M} μ(d)Ψ(N/d, y) ~ (φ(M)/M)ρ(u_δ)N, where u_δ = (1/2+δ)/α is fixed.
- **Conclusion.** k ≤ N/(|T| − B) = (M/φ(M))/ρ(u_δ) + o(1). Let δ → 0 and use the continuity of ρ.
- **(a) and (b), M = 1.**
  - Every prime ≤ y is inert for χ_i, so LV gives y ≪ |D₀,ᵢ|^{1/4+ε}. Since |D₀,ᵢ| ≤ Q, this is impossible for α > 1/4.
  - Otherwise |D₀,ᵢ| ≥ Q^{4α−ε}, so f_i ≤ Q^{1/2−2α+ε}.
  - By C1(iii) with M = 1 (a has no prime factor ≤ y), f_i is y-rough, so f_i = 1 or f_i > Q^α.
  - For α > 1/6 we have Q^α > Q^{1/2−2α+ε}, so f_i = 1. ∎

Application to chains: on a run with second difference e, starting at q with gap d, set P(j) = (e/2)j² + (d − e/2)j + q. Then |D| ≤ 2eq + d² ≍ e·n² in the CORE regime. With e bounded, ℓ ≥ n^θ means α ≈ θ/2, which gives the 1/ρ(1/θ) form in the Result.

## Frontier map

=== DIRECTION
**TRUE**, confidence 0.9.

Strongest evidence:

1. **Random-model heuristic.** Suppose q_n ≤ Cn² for some n. Then over the indices i ∈ [n/2, 3n/4]:
   - the gaps satisfy d_i ≍ n;
   - the increments e_i = d_{i+1} − d_i ∈ 2ℤ_{≥0} average O(C).
   
   Take a window of length L at scale X = Cn². It has about X^{3/2} starting states and about e^{L·log(e(A+1))} increment patterns, where A is the average increment. Each pattern is all-prime with "probability" about (c·loglog X/log X)^L. The product tends to 0 once L ≥ 2 log X. So the expected number of counterexamples is 0, and heuristically min q_n ≍ n² log n. The greedy rule "next prime ≥ 2q_n − q_{n−1}" achieves n² log n heuristically.
2. **The margin.** The per-element cost of being prime is loglog X (the Mertens divergence). The entropy of bounded increments is O(1). So the conjecture is a "density → 0" phenomenon. It is TRUE heuristically but by an unbounded margin that grows only like loglog X.
3. **Consistency of rigorous partial results.** Every rigorous partial result (Richter, AP-multiplicity, the game bounds) points the same way. No construction comes close to O(n²). The best unconditional construction I can derive is about n^{4.2}.

=== KNOWN
- liminf q_n/n² > 0.352… | Richter [Ri76], quoted on erdosproblems #455 | elementary counting of repeated gaps.
- liminf q_n/n² ≥ 1/κ = 0.54345, with κ = Σ_{p odd prime} (p−2)(1−1/p)/∏_{3≤ℓ<p} ℓ = 1.840102. Equivalently d_n ≥ (2/κ − o(1))n. This already beats Richter | standard (an AP of primes with difference d has at most p(d)−1 terms beyond p(d), where p(d) is the least odd prime not dividing d; so the even gap value d occurs at most p(d)−2 times; sum the n smallest gaps) | AP-multiplicity plus greedy rearrangement.
- [Lean] Convex tail: (n−k)(q_{k+1} − q_k) ≤ q_n − q_k for k ≤ n | blackboard, machine-checked | telescoping.
- [Lean] In any convex prime chain p_0..p_L: i ≤ 6(p_{i+1} − p_i) | blackboard, machine-checked | mod-3/5 multiplicity bound.
- [Lean] The frozen target follows from the open piece erdos_455_hyp_no_short_convex_chain (∀C ∃N … C n² < p(n/2)). The judge noted this piece is the target restated | blackboard | reduction.
- liminf ≥ 0.80024 (S = {3,…,13}); ≥ 0.63555 (S = {3,5,7}); ≥ 0.71859 (S = {3,…,11}) | blackboard, informally refereed, NOT Lean | "congruence game": an optimal residue-strategy value ρ_S plus a phase term E0_S.
- If #{i ≤ n : Δ³q_i ≠ 0} ≤ n^θ with θ < 1/2, then q_n/n² → ∞ | blackboard, informal | a run with constant e is a quadratic; it has a root mod any split prime p ≤ run/2, and Linnik–Vinogradov gives a least split prime ≪ D^{1/4+ε}.
- Under GRH for quadratic L-functions: if #{i ≤ n : Δ³q_i ≠ 0} ≤ n/(log n)^5, then q_n/n² → ∞ | blackboard, informal | least split prime ≪ log² D.
- Discriminant invariant: on a run with e ≡ 2, Δ_i = (d_i + d_{i+1})² − 16q_i is constant; equal Δ means the same polynomial | blackboard | algebra.
- A periodic gap pattern with one repeated gap per period P is never Ẑ-good (it fails mod some prime ≤ max(7, P)) | blackboard, informal | CRT/Legendre symbols.
- For every k there are k-term APs of primes, i.e. arbitrarily long finite convex chains | Green–Tao 2008 | transference.
- For every fixed k and fixed admissible pattern, #{(x,d) ∈ [X]×[√X] : x + jd + s_j prime for all j < k} ~ 𝔖·X^{3/2}/(log X)^k | Green–Tao "Linear equations in primes" plus Green–Tao–Ziegler GI(s) | higher-order Fourier analysis (the complexity of the quadratic pattern is ≤ k−3).
- The least prime p with χ_D(p) = 1 is ≪ |D|^{1/4+ε} | Linnik–Vinogradov | Burgess plus 1∗χ ≥ 0.
- The same least split prime is ≪ (log|D|)² under GRH | standard (Ankeny/Bach-type) | explicit formula.
- n² + n + c is prime for 0 ≤ n ≤ c−2 iff 1 − 4c is a Heegner discriminant | Rabinowitsch | class number one.
- Landau–Page: at most one real primitive χ of conductor ≤ Y has a zero > 1 − c₀/log Y. Also L(1,χ) ≫ 1/log q otherwise | standard | zero-repulsion via a biquadratic ζ_K.
- Sieve limit: the β-sieve of dimension κ has sieving limit β_κ ~ 2.44κ, so a dimension-k upper bound loses about (ck)^k against Hardy–Littlewood | Diamond–Halberstam–Richert | sieve theory.
- Constructions (derived, standard):
  - Greedy with Baker–Harman–Pintz (gaps ≤ x^{0.525}) gives a convex prime sequence with q_n ≪ n^{2/0.475+ε} ≈ n^{4.21}.
  - Under RH: about n⁴.
  - Under Cramér: ≪ n²(log n)².

=== BARRIERS
- **Abundance of finite windows** (rigorous, by GT/GTZ). For fixed L, prime windows with gaps ≍ √X and bounded increments occur ≫ X^{3/2}/(log X)^{L+1} times in [X, 2X] | Defeats any argument looking at windows of bounded or slowly growing length; it forces L(X) ≥ (1.5 − o(1))·log X/loglog X | Does not rule out window arguments with L ≫ log X/loglog X.
- **Congruence cap 1** (Euler/Rabinowitsch quadratics). For any finite prime set S, n² + n + c with 1 − 4c a non-residue mod every p ∈ S avoids S forever and has q_n ~ n² | Defeats every argument using congruences modulo a bounded set of primes: Richter, AP-multiplicity, the game values ρ_z, and stationary/compactness limits of residue processes. All of them cap at liminf ≥ 1 | Does not rule out moduli growing with n (p ≍ log n and beyond), where least-split-prime theory enters.
- **Sieve dimension.** A union bound over (x, d, pattern) needs a per-element saving of ≪ 1/loglog X. Any upper-bound sieve (Selberg, β-sieve, large sieve in 1D or 2D) in dimension L at level X^θ saves only (eL/θ log X) per element, and sup_t t·log(1/t) = 1/e < 3/2. So NO choice of L works | Defeats all unconditional counting/union-bound proofs, including GPY/Maynard weights, whose λ-support ∏d_i ≤ R gives the same G(R) ~ (log R)^L/L! | Does not rule out Hardy–Littlewood-quality upper bounds (hence T4), or structural arguments.
- **Linnik–Vinogradov exponent 1/4.** A single pure run is only killed at length ≫ n^{1/2+ε}, so the adversary survives with n^{1/2−ε} glitches | Defeats pure-run analysis | Does not rule out joint statements about many discriminants along the walk.
- **Large-sieve sparsity.** The sequence has about √X terms in [X, 2X]; structure-blind sieves bound sets of size about X/log X | Defeats Gallagher/large-sieve on the value set | Does not rule out sieving in the index variable run by run.
- **Pointwise short intervals.** In tree/path counting from a fixed root, branching is controlled only by Brun–Titchmarsh in intervals of length O(A), which saves log A, not log X | Defeats transfer-operator/ℓ^∞ path counting | Does not rule out ℓ² arguments that exploit averaging over states.
- **Siegel zeros/ineffectivity.** Small L(1,χ_D) cannot be excluded pointwise | Defeats per-discriminant arguments | Does not rule out Landau–Page/Deuring–Heilbronn, which allow at most O(1) exceptional discriminants per scale.
- **Parity is NOT a barrier.** Only upper bounds on primes are needed.

=== CORE
For every C, for all large n, there is no chain of primes p_0 < … < p_{n/2} with nondecreasing gaps, all gaps ≤ 2Cn, and p_{n/2} ≤ Cn². This is the frozen erdos_455_hyp_no_short_convex_chain.

Equivalently: in [X/K, X], a convex prime chain with gaps ≍ √X and average increment ≤ A has length o(√X).

Why it is hard:
- The adversary is a single, adaptive, sparse (√X elements) sequence.
- Counting fails because upper-bound sieves lose L^L in dimension L.
- Local congruences cap at liminf 1.
- Pure-polynomial arithmetic only kills runs longer than n^{1/2}.
- A proof must exploit prime density across all multiplicative scales up to √X: the loglog X divergence against bounded entropy.

=== TARGET T1
TYPE: QUANT
STATEMENT: liminf q_n/n² ≥ 1/ρ' = 0.80024, with ρ' = (18748 + 15.13085)/15015 for S = {3,5,7,11,13}. The proof must be complete, including the phases with 15015 | d (where repeats are forced to come in AP runs of length ≤ p(d) − 2) and the tail τ_13.
BEYOND: Richter 0.352 and the elementary 1/κ = 0.5434. The blackboard version is informal.
VALUE: It certifies the game-to-sequence reduction needed for T2.
SIGNIFICANCE: 1
TEST: Exact dynamic programming over states (q mod 15015, d mod 15015, multiplicity). Compare with the longest convex chains found by beam search in [10⁸, 10⁹].

=== TARGET T2
TYPE: QUANT
STATEMENT: Two parts.
- ρ_z → 1 as z → ∞, uniformly enough to run the game with z = z(n) → ∞.
- Hence liminf q_n/n² ≥ 1: every convex prime sequence has d_n ≥ (2 − o(1))n, i.e. average gap multiplicity ≤ 1 + o(1).

BEYOND: The best congruence bound is 0.80 at z = 13. This reaches exactly the congruence cap from T3.
VALUE: It is optimal for local methods and isolates the global input needed beyond 1.
SIGNIFICANCE: 2
TEST: Compute ρ_z for z ≤ 23 via CRT transfer matrices. Fit ρ_z − 1 against 1/log z, as conjectured on the blackboard.

=== TARGET T3
TYPE: NEGATIVE
STATEMENT: Two parts.
- (a) For every finite set S of primes there is c with q_n = n² + n + c convex, coprime to every p ∈ S, and q_n/n² → 1. So arguments using congruences modulo a fixed finite set of primes cannot prove liminf > 1.
- (b) For every ε > 0 and large N there is a convex chain of length N with all terms ≤ 2N² and coprime to every prime ≤ (2 − ε)·log N. (Choose c ≤ ∏_{p≤z} p by CRT.) Extend (b) to z = (log N)^{1+δ} using piecewise-quadratic chains with glitches.

BEYOND: Not recorded anywhere. It quantifies the barrier.
VALUE: It tells the team which moduli a proof must use.
SIGNIFICANCE: 1
TEST: Search for c that maximise the least split prime of 1 − 4c, and for glitched chains.

=== TARGET T4
TYPE: CONDITIONAL
STATEMENT: Assume UHL, the uniform Hardy–Littlewood upper bound: there is an absolute C₀ such that for all large X, all k ≤ 2 log X and all H ⊂ [0, X] with |H| = k,

#{x ≤ X : x + h prime for all h ∈ H} ≤ C₀^k · 𝔖(H) · X/(log X)^k.

Then q_n/n² → ∞. Quantitatively, q_n ≫ n² log n/loglog n.

Proof sketch:
1. If q_n ≤ Cn², then for i ∈ [n/2, 3n/4] the gaps are d_i ∈ [n/12, 4Cn] (by [Lean]).
2. Some window of length L = ⌈2 log X⌉ has increment sum ≤ 32CL.
3. Use 𝔖(H) ≤ (c·loglog X)^k. This follows from (1 − ν/p)(1 − 1/p)^{−k} ≤ (1 − 1/p)^{−(k−ν)} and Σ_{p | m} 1/p ≤ logloglog m.
4. Union bound: X^{3/2} · e^{L·O_C(1)} · (C' loglog X/log X)^L < 1.

BEYOND: No conditional proof of the full statement is recorded. The GRH result needs few glitches.
VALUE: It makes the "density → 0" mechanism rigorous and pins down exactly what unconditional methods lack.
SIGNIFICANCE: 2
TEST: Check UHL numerically for convex patterns with k ≤ 12 and X ≤ 10¹⁰.

=== TARGET T5
TYPE: REDUCTION
STATEMENT: CORE follows from W(L), with L(X) = ⌈(log X)²⌉: for every A, for large X, there is no chain of L(X) primes in [X/A, X] with nondecreasing gaps in [√X/A, A√X] and total increment ≤ A·L(X). The implication follows by averaging increments over [n/2, 3n/4] (as in T4).

W(L) is a finite, start-free statement. It is strictly stronger than CORE, and it fails for L ≤ (1.5 − ε) log X/loglog X by GT/GTZ.
BEYOND: It replaces the infinite adversary with a scale-local window and locates the threshold length.
VALUE: Window statements are what counting, sieve or character methods can attack.
SIGNIFICANCE: 1
TEST: Exhaustive search for the longest bounded-increment convex prime windows near X = 10^6 to 10^9. Fit against log X/loglog X.

=== TARGET T6
TYPE: SPECIAL
STATEMENT: limsup q_n/n² = ∞. That is, no sequence of primes with nondecreasing gaps has q_n ≤ Cn² for all n.
BEYOND: Not known. It is weaker than CORE, but it constrains every scale at once.
VALUE: A uniform-in-scale adversary must use long runs at every scale. This is where Landau–Page (at most one exceptional discriminant per scale) can bite.
SIGNIFICANCE: 2
TEST: Run beam search for chains that stay below Cn² for C = 1, 2, 4. Record the depth at which they die as a function of C.

=== TARGET T7
TYPE: SPECIAL
STATEMENT: Unconditionally: if #{i ≤ n : Δ³q_i ≠ 0} ≤ n^{1−δ} for all large n (some δ > 0), then q_n/n² → ∞.
BEYOND: The blackboard (informal) has θ < 1/2 via Linnik–Vinogradov. Going past 1/2 needs joint control of many run discriminants D_r. Linnik–Vinogradov caps each run at n^{1/2+ε}, so there are ≥ n^{1/2−ε} long runs per scale.
VALUE: It forces counterexamples to glitch almost everywhere.
SIGNIFICANCE: 2
TEST: Compute D_r for consecutive runs in near-extremal chains and record their least split primes.

=== TARGET T8
TYPE: STRUCTURE
STATEMENT: For the local discriminant Δ_i = (d_{i−1} + d_i)² − 8e_i·q_i, with e = e_{i−1} and e' = e_i:
- (i) if e = e' = 2 then Δ_{i+1} − Δ_i = 4d_i(e + e' − 4) + e'² − e²;
- (ii) in any counterexample, along the subsequence with q_n ≤ Cn², a (1 − o(1)) fraction of indices lie in runs whose discriminant satisfies Δ/n² = 16α(α − 1) + o(1), where α is the local ratio; so a counterexample with α < 1 runs on imaginary quadratic discriminants;
- (iii) every maximal constant-e run of length ℓ has χ_Δ(p) ≠ 1 for all p ≤ ℓ/2 with p ∤ 2eΔ;
- (iv) there are ≥ n^{1/2−ε} runs in [n/2, n].

BEYOND: It assembles the blackboard fragments into a rigid profile of any counterexample, with the sign dichotomy.
VALUE: It supplies the input objects for A1 and A3.
SIGNIFICANCE: 1
TEST: Verify the identity symbolically. Check the profile on beam-search chains.

=== TARGET T9
TYPE: NEGATIVE
STATEMENT: Let R_δ ⊂ ℕ contain each m independently with probability δ (fixed). Almost surely R_δ contains an infinite convex sequence with q_n ≤ C(δ)n², with C(δ) ≍ 1/δ (supercritical Galton–Watson). Consequently, no argument exploiting only a bounded-factor density deficit can prove CORE. This covers sieving by primes in [y, y^K], or by p ≤ z with z fixed.
BEYOND: It formalises the multi-scale barrier, which is currently only heuristic.
VALUE: It forces the team toward arguments that use all scales up to √X.
SIGNIFICANCE: 1
TEST: Simulate branching search in R_δ.

=== TARGET T10
TYPE: ANALOGUE
STATEMENT: Let P(m ∈ R) = 1/log m independently (the Cramér model). Almost surely every convex sequence in R has q_n/n² → ∞. Moreover 0 < liminf over sequences of q_n/(n² log n) ≤ limsup < ∞ almost surely; the lower bound comes from a first moment over windows of length 2 log X, the upper from greedy or beam search. Determine the constant.
BEYOND: There is no rigorous model result. Its true order n² log n refines the conjecture.
VALUE: It predicts the truth and calibrates T4.
SIGNIFICANCE: 1
TEST: Monte Carlo up to 10⁹, compared with actual primes.

=== ANGLE A1
TECHNIQUE: Discriminant walk plus a multi-character Linnik–Vinogradov/Burgess argument, and Heath-Brown's quadratic large sieve.
IDEA: Long runs r carry discriminants D_r = D_1 + H_r, with jumps ≍ n by T8(i). Each long run needs χ_{D_r}(p) ≠ 1 for p ≤ ℓ_r/2. Prove a joint split-prime bound: among R discriminants D + H_j (H_j ≍ n, distinct mod most p), one has a split prime ≤ n^{2^{1−R}+ε}. Use 1∗χ_j ≥ 0 together with the products χ_iχ_j, which are +1 on all small primes. Summing over the ≥ n^{1/2} long runs gives T7.
BARRIERS: It beats the Linnik–Vinogradov exponent by exploiting many characters at once. It avoids the sieve-dimension barrier because it never counts tuples.
FIRST STEP: For nonsquare D and 1 ≤ |h| ≤ |D|^{1/2+o(1)}, prove that D or D + h has a split prime ≤ |D|^{1/8+ε}. Test it numerically first.

=== ANGLE A2
TECHNIQUE: Growing-modulus congruence game, using CRT transfer matrices and Weil bounds for Paley-graph shifts.
IDEA: Encode states (q, d, run multiplicity) mod P_z, and compute ρ_z by Perron–Frobenius. Prove ρ_z = 1 + O(1/log z), using the fact that each repeat in an AP run of length m costs a factor of about 2^{−m} in surviving residues mod each p ≤ m. Then push z up to log n, where T3(b) shows quadratics fail and the D-constraints become non-local.
BARRIERS: It must pass the congruence cap 1. That needs z growing with n plus least-split-prime input; T3 quantifies exactly where.
FIRST STEP: Prove ρ_z ≤ 1 + C/log z for the mod-3·5·7 subgame with geometric-mean bookkeeping, and compute ρ_17, ρ_19.

=== ANGLE A3
TECHNIQUE: Per-run one-variable sieve, plus pretentious distance and Landau–Page/Deuring–Heilbronn repulsion.
IDEA: Sieve each run in its own index variable. It is a single quadratic, so the dimension is ≤ 2 and the high-dimension loss does not arise. All terms being prime forces Σ_{p≤√ℓ, χ_D(p)=1} 1/p ≤ 1/2 + o(1). That makes χ_D "pretend to be λ" up to √ℓ, so L(1,χ_D) ≪ 1/log ℓ. Runs with ℓ ≥ n^δ then need Siegel-type discriminants. Repulsion allows O_δ(1) of them per dyadic scale, which contradicts the ≥ n^{1/2−ε} runs from T8(iv).
BARRIERS: Siegel ineffectivity is irrelevant because the argument counts exceptional characters; it does not bound them pointwise. The open issue is the constant in "L(1,χ) ≤ K/log D implies an exceptional zero".
FIRST STEP: Show that two real primitive characters of conductor ≤ Y cannot both satisfy Σ_{p≤Y^δ} (1 + χ(p))/p ≤ 1. Use ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂), whose coefficients on Y^δ-smooth integers are supported on squares.

=== ANGLE A4
TECHNIQUE: Cross-scale rigidity for T6, via self-similarity of the normalised walk Δ_i/i² across dyadic scales.
IDEA: If q_n ≤ Cn² for all n, then α_i stays in [1/κ, C] at every scale, and the drift identity forces Δ_i/i² to move slowly. The sequence must supply long runs at every scale, but A3 permits only O(1) exceptional discriminants per scale. Show that the walk cannot re-enter exceptional discriminants at the next scale, because the jumps are ≍ i and the exceptional set is sparse.
BARRIERS: It uses Landau–Page multiplicatively across scales. Its target, T6, is weaker than CORE.
FIRST STEP: Prove that Δ_i/i² has bounded total variation along any sequence with q_n ≤ Cn² for all n.

=== ANGLE A5
TECHNIQUE: Furstenberg-type compactness that keeps an arithmetic coordinate.
IDEA: Take weak limits of windows along the bad subsequence. The data are stationary processes on (Ẑ-residues, increments, Δ/n², and least-split-prime profile). T3 says the residue part alone admits Euler-type limits. So prove rigidity: a limit with mean increment < ∞ must have e ≡ 2 almost surely on a set of positive measure, i.e. long pure runs. That reduces CORE to the long-run case handled by A1/A3.
BARRIERS: It sidesteps the dimension barrier by never counting. It must beat the cap by retaining the Δ/n² coordinate.
FIRST STEP: Classify stationary Ẑ-good increment processes with E[e] < 2. The blackboard's periodic NEGATIVE result is the first instance.

=== ANGLE A6
TECHNIQUE: Weaken the hypothesis in T4 using averaged Hardy–Littlewood inputs (GRH with Montgomery–Soundararajan-type moments of 𝔖 over convex pattern families), validated in Granville's model.
IDEA: The union bound needs only Σ_{d, patterns} π_H(X), summed over the convex 2-parameter family, not UHL for every H. Gallagher-type averaging of 𝔖 over patterns with bounded increments is e^{O(L)}. So try to prove the summed bound from GRH plus pair-correlation-type hypotheses for L ~ log X. Use the Granville model, sieved to ε·log X, to check that structured (Euler-type) chains do not break the averaged bound.
BARRIERS: It must avoid the sieve limit, so it takes analytic hypotheses rather than sieve weights. T3 shows structured chains contribute only z ≲ log X worth of gain.
FIRST STEP: Prove T4 with UHL replaced by the same bound averaged over d ≤ √X, and verify that the averaged bound holds in Granville's model.

## Meta-review

=== STATE

**Validated new results (beyond the frontier map)**
- **liminf q_n/n² ≥ 1/ρ₁₇ = 255255/(295318 + E0₁₇) = 0.864289…**, equivalently d_n ≥ (1.72857 − o(1))n. This is the congruence game at S = {3,…,17}; r1s2/C1 and r1s3/C1 reached the same value independently. It is new against Richter's 0.352, but the Euler/Rabinowitsch barrier caps it below 1.
- **(valid-routine) Bounded field set for long runs (r1s1/C1).** Take monic runs x²+Bx+c that are prime at j = 0..ℓ−1, with ℓ ≥ Q^α and |D| ≤ Q, and write D = D₀f².
  - The fundamental parts D₀ form a set E with |E| ≤ 2/ρ(2/α) + o(1). These are real characters that equal Liouville on Q^α-smooth numbers.
  - Each D₀ ∈ E has |D₀| ≫ Q^{4α−ε}.
  - The number of distinct D is ≤ |E|·(Q^{1/2−2α+ε} + 1).
- **(valid-routine) Growing-modulus dead zone (r1s2/C3).** For z ≤ (2−ε)log n, a CRT-chosen x_k = k²+k+c is a legal score-1 play on [n, 2n]. So no congruence game with moduli up to about 2 log n beats liminf 1. The averaging regime z ≤ (1+o(1))log n lies inside this dead zone.
- **(valid-routine)** ρ_z is nonincreasing in z, and 1 ≤ ρ_∞ ≤ 1.157020.
- **(valid-routine, but vacuous)** UHL_conv implies q_n ≥ n²(log n)^δ for every δ < 1 − 3/(2A). At L ≈ A·log X/loglog X the assumed bound is below 1, so UHL_conv is a nonexistence statement stronger than CORE.

**Best unvalidated ideas**
- **r1s4/C1: UHL is false for k ≥ (1+ε)·log X/loglog X.** Almost certainly true by the trivial witness: take H to be the actual pattern of k consecutive primes near X. Combined with r1s4/C2(iii), the T4 union bound needs exactly the refuted range. This should be recorded as a barrier, not a result.
- **r1s2/C2:** the game excess ε_z decays faster than 1/log z. The numerics are fine, but it is irrelevant to CORE because of the cap.
- **Not yet checked by anyone: conductor roughness, observed while planning this round.**
  - Lemma: if p is odd, p ∤ a, p | f and p ≤ ℓ, then P ≡ a(x−r)² mod p. So p | P(j) for some j < ℓ, which contradicts primality. Hence f = 1 or f > ℓ ≥ Q^α.
  - Combined with r1s1/C1's bound f ≤ Q^{1/2−2α+ε}: for α > 1/6, i.e. every run of length ≥ n^{1/3+ε}, we get f = 1.
  - So D = D₀ ∈ E. All such runs have discriminants in a set of absolutely bounded size.
  - By the discriminant invariant, they lie on O(1) parabolas per value of e.

=== LESSONS

**What failed, and why**
- **The congruence game is exhausted.**
  - Two sessions spent effort pushing z to 17. The result is new but has significance 1, and ρ_∞ ≥ 1 means it can never reach CORE.
  - r1s2/C3 extends the cap to z ≈ 2 log n, so "grow z to log n" is dead too.
  - No more z-pushes.
- **Counting is dead even with Hardy–Littlewood-quality bounds.**
  - Uniform HL fails exactly in the range k ≥ (1+ε)·log X/loglog X.
  - The union bound needs k ≥ (1.5 − o(1))·log X/loglog X.
  - The only surviving version, UHL_conv, is CORE restated.
  - Lesson: any "upper bound for structured windows" must use the convex/quadratic structure itself.
- **r1s1/C2 broke on the conductor.**
  - Linnik–Vinogradov lower-bounds |D|, not |D₀|.
  - The small-|D| branch only works for α ≥ 1/4.
  - The fix looks available: the roughness lemma forces f = 1 or f > ℓ. The case |D| ≪ Q^{1−η} must be handled separately, or excluded because LV makes such runs short.
- **r1s1/C3 overreached.** It treated "LV does not forbid one long run" as "LV permits n^{1/2} long runs with distinct D₀". C1 shows exactly that this is false.
- **Barriers that bit:** congruence cap (game sessions), sieve dimension and abundance of windows (T4/UHL), LV exponent 1/4 (single runs).

**Most alive angle: field collapse**
- r1s1/C1 plus roughness says that runs of length ≥ n^{1/3+ε} use O(1) discriminants, i.e. O(1) quadratic fields with trivial conductor.
- This is the first "joint statement about many discriminants along the walk", which is precisely the loophole that the LV and Siegel barriers leave open.
- The adversary's remaining strategy is to re-use one exceptional field Q(√D₀) across many runs, switching e and re-entering parabolas.
- That points straight at Siegel-zero territory. Values of a·P are norms from Q(√D), so their prime factors split. An exceptional D₀ makes P prime-rich.
- The decisive dichotomy is therefore:
  - either convexity forbids exploiting one field for √X steps, which beats θ = 1/2 and maybe reaches CORE modulo Siegel zeros;
  - or Siegel zeros yield a counterexample, which would be a major barrier result.

=== NEXT

1. **Repair r1s1/C2 via conductor roughness.**
   - First step: prove the lemma "p odd, p ∤ a, p | f, p ≤ ℓ ⇒ p | P(j) for some j < ℓ", including the case p | a (where P ≡ c mod p).
   - Then restate the joint first step for |D|, |D'| ∈ [Q^{1−η}, Q] and |h| ≤ Q^{1/2+δ}. Prove D₀ ≠ D₀' by splitting into f = f' = 1 versus f > Q^α.
   - Separately show that runs with |D| < Q^{1−η} have length ≤ Q^{(1−η)/4+ε}, so they can be discarded.
2. **CORE, field-collapse counting.** Goal: beat the glitch threshold θ < 1/2 unconditionally, e.g. show that ≤ n^{θ} glitches with some θ > 1/2 already forces q_n/n² → ∞.
   - Technique: r1s1/C1 at α > 1/6, roughness (f = 1), the e-budget Σ e·len ≤ 2Cn, and the invariant Φ_e(i) = d_i² − 2e·q_i, which is constant on a run of second difference e and must lie in the O(1) set E.
   - First step: bound how many times the walk can return to a fixed level set {Φ_e = D}, for D ∈ E and fixed e (re-entry to one parabola), using the monotonicity of d and q. Then sum over e ≤ 2C·n^{1/3}.
3. **CORE dichotomy, Siegel zeros versus convexity.** Decide whether one exceptional field can carry a convex chain of length ≍ √X with q ≤ CX.
   - Technique: the norm identity 4aP(x) = (2ax+B)² − D, so odd prime factors of P(x) coprime to 2a split or ramify in Q(√D₀). Add parabola switching (changing e and translate) at each glitch, constrained by convexity.
   - First step: take a model where Σ_{split p ≤ X} 1/p ≤ η. Compute the composite density along a fixed parabola and test whether glitch re-routing through other forms of discriminant D₀ can respect convexity.
   - Output, either way, is significant:
     - a conditional "No" (Siegel zeros at infinitely many scales give a counterexample, so an unconditional proof must defeat Siegel zeros); or
     - a rigidity lemma, which would feed session 2 and give "Yes unless there are infinitely many exceptional characters with χ(p) = −1 for all p ≤ D^{c}".
4. **Push r1s1/C1 to all second differences e and sharpen |E|.**
   - Generalize from monic P to a·x² + Bx + c with a = e/2, controlling primes dividing a.
   - Replace 2/ρ(2/α) with an explicit small constant (ideally 1 for α near 1/4) using Landau–Page and an explicit L(1,χ) ≤ C/log Q bound from χ(p) = −1 on p ≤ Q^α plus Pólya–Vinogradov.
   - First step: compute C and compare it with the Landau–Page constant c₀.
   - In parallel, formalize the roughness/root lemma in Lean, since it is short and purely algebraic.

## Deep dive

GOAL: **Theorem to prove (unconditional, constants ineffective via Siegel).** Fix θ < 1. Let q_1 < q_2 < … be primes with nondecreasing gaps, and suppose #{i ≤ n : Δ³q_i ≠ 0} ≤ n^θ for all large n. Then q_n/n² → ∞.

Equivalently, using the core reduction: for every C, every large n, and every chain in [n/4, n/2] with q ≤ Cn², gaps ≤ 2Cn and at most n^θ changes of e_i = Δ²q_i, a contradiction follows.

**Why an expert would rate it 2.**
- The team has this statement only for θ < 2/3 (r2s2/C1, validated, rated 1). The full range θ < 1 is known only under GRH, and only informally.
- Getting every θ < 1 unconditionally kills every "polynomial-type" adversary: any sequence that is quadratic on runs of length n^{δ}, however many fields and conductors it uses.
- It turns the problem into a sharp dichotomy. Any counterexample must have n^{1−o(1)} glitches, so its runs have length n^{o(1)}. That is exactly the regime of the finite-window abundance and sieve-dimension barriers, and nothing else is left.
- It needs a joint use of Siegel/Landau–Page across the walk of run discriminants that goes past the Linnik–Vinogradov 1/4 barrier. An analytic number theorist would see that as a genuinely new mechanism, not a constant pushed inside a method's ceiling.

**Fallback deliverable (still new).** The theorem for some explicit θ₁ > 2/3. Alternatively, the three lemmas of Steps 3–5 as standalone results.
