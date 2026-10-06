# The engine's proof (deep/C1, run runs/20261006-021530-371610-discover-erdos77933)

**Statement.** If f: R→R satisfies 2f(x) ≤ f(x+h)+f(x+2h) for all x∈R and all h>0, then f is nondecreasing.

**Proof.**

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

**Referee.** `{"valid": true, "first_error": null, "fixable": true}`

**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
