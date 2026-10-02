## Result
NEW (C1, PROVED modulo a finite certified computation): every convex prime sequence has
liminf q_n/n² ≥ 15015/(18748 + E0) = 0.80024… (E0 = 15.1308…), improving Richter's 0.352… (and the
cap-(P(v)−2) bound 1/κ = 0.5434). Method: a max-plus "value-period game" mod M = 3·5·7·11·13 that couples the
run-length caps of consecutive gap values through the residues q_i mod p. It is purely local, so by the profinite barrier
it can never exceed 1; data (C3) suggest it may tend to 1 as S grows.
Assigned angle A1: T5 proved (C2, the elementary part fully; the analytic input is the cited Linnik–Vinogradov bound),
but data (D1) show that extremal finite chains have constant-second-difference pieces of length ≤ 9, so the
piecewise route eliminates nothing that actually occurs (obstruction C4).

## Claims
### C1
STATEMENT: Let q_1<q_2<… be primes with q_{n+1}−q_n ≥ q_n−q_{n−1}. Then liminf q_n/n² ≥ 1/κ'_S for
S={3,5,7,11,13}, where κ'_S = (ρ_S+E0_S)/M, M=15015, ρ_S=18748, E0_S=15.13085 (defined below); numerically
liminf q_n/n² ≥ 0.80024. Also (same method) S={3,5,7}: ρ=156, ≥0.63555; S={3,…,11}: ρ=1596, ≥0.71859.
STATUS: PROVED (the integer ρ_S is certified by an exact integer computation, check.py; see below). Referee should re-run check.py.
TYPE: QUANT
BEYOND: KNOWN has liminf > 0.352 (Richter); the obvious cap P(v)−2 version gives 1/κ = 0.5434. 0.8002 beats both.
PROOF:
Notation. d_i = q_{i+1}−q_i (nondecreasing), M = ∏_{p∈S} p, S = {3,5,7,11,13}. Fix i0 with q_{i0} > 13; from then on all
gaps are even and every q_i is ≢ 0 mod p for p ∈ S. For an even value v let m(v) = #{i ≥ i0 : d_i = v}. Because the gaps
are nondecreasing, the indices with d_i = v are consecutive. So the chain passes through the values in increasing
order: from a prime q it adds v exactly m(v) times, giving the primes q+v, …, q+m(v)v.
(1) Values v with M ∤ v. Track only r = q mod M, an element of R = {r : r ≢ 0 mod p for all p ∈ S}. Going through value v
with multiplicity m moves r → r+mv and requires r+tv ∈ R for t = 1..m. Write v = 2j. The residue of v mod M depends only
on j mod M. Let A be the R×R max-plus matrix: A[r,r'] is the largest total number of steps over one period
j = 1..M−1 (skipping j ≡ 0 mod M) that moves r to r'. Steps at values with M | v do not change r, because then p | v for
every p ∈ S. The chain's steps at values v ≢ 0 mod M with v ≤ V form a path in this max-plus system through at most
V/(2M)+2 periods, the partial first and last periods costing ≤ 13M steps. Certificate: let U_k = (0-vector) ⊗ A^k
(forward max-plus). check.py verifies that U_k is finite on all of R (for k=k0=2), and that
δ := max_t (U_{k+K}(t) − U_k(t))/K = 18748 with K=2. (The min is also 18748, so ρ_S = 18748 exactly.) For any s,t we
have A^K[s,t] ≤ U_{k+K}(t) − U_k(s) = (U_{k+K}(t) − U_k(t)) + U_k(t) − U_k(s) ≤ Kδ + U_k(t) − U_k(s). Summing along a
path of P blocks of K periods, the telescoping gives weight ≤ PKδ + (max U_k − min U_k), and check.py reports
max U_k − min U_k = 50. Hence #{steps at values v ≤ V, M∤v} ≤ (V/(2M))·ρ_S + O_S(1).
(2) Values v with M | v. Then P(v) (the least odd prime not dividing v) is ≥ 17. The block at v is an AP of m(v)+1
primes with difference v not divisible by p = P(v). If its first term exceeds p, the AP lemma gives m(v)+1 ≤ p−1,
i.e. m(v) ≤ P(v)−2. If its first term q_s is ≤ p, then s ≤ q_s ≤ P(v) ≤ P(V) ≪ log V. Some term ≡ 0 mod p appears
among any p consecutive terms, and only one term can equal p, so m(v) ≤ 2p. So these exceptional blocks contribute
O(log² V) in total. Write v = 2Mk. Then P(2Mk) is the least prime p ≥ 17 with p ∤ k. So
Σ_{k ≤ K}(P(2Mk)−2) = K·E0_S + o(K), where E0_S = Σ_{p≥17} (p−2)(1−1/p)∏_{17≤p'<p}(1/p') = 15.130849…
(The tail beyond 200 has mass < 4e−78. The o(K) uses P(2Mk) ≪ log k and a slowly growing truncation.)
(3) Combining, with V = d_{n−1}: n − i0 ≤ (V/(2M))(ρ_S + E0_S) + o(V) + O(log² V). Hence V → ∞ and
d_{n−1} ≥ (2/κ'_S − o(1)) n. Then q_n ≥ Σ_{k<n} d_k ≥ (1/κ'_S − o(1)) n². ∎
Sanity: S={3} reproduces κ'=κ=1.84010 (ρ=2). The DP minima Xmin(L)/L² (D1) are ≥ 0.59 and rise above 1, consistent.
Code: game3.py (value iteration), check.py (certificate); S={3,5,7} was also checked by exact Karp min-mean-cycle (game2.py: ρ=156).

### C2 (assigned first step, T5)
STATEMENT: Let f(x)=ax²+bx+c with a ≥ 1, D=b²−4ac, and suppose f(0),…,f(N−1) are all primes > N.
(a) If D is a perfect square (including 0), then N ≤ 10.
(b) Otherwise every prime p ≤ N with p ∤ 2a has (D/p) = −1. So N < n_a(D) := the least prime p ∤ 2a with (D/p) ≠ −1.
(c) Consequently, if (LV_a) holds (the least prime p ∤ 2a with χ_D(p)=1 is ≪_{ε,a} |D|^{1/4+ε}), then N ≪_{ε,a} |D|^{1/4+ε}.
In a convex chain, a stretch of N+1 consecutive terms with constant second difference e=2a lies on such an f, with
D = (d−a)² − 4a·q (d any gap of the stretch, q its left endpoint). In CORE (gaps ≤ 4CL, X=4CL²) this gives |D| ≪_C X.
Hence every constant-e stretch with e ≥ 2 has length ≪ L^{1/2+ε}. Since e=0 stretches have length ≤ P(v)−2 ≪ log L,
a CORE counterexample has ≫ L^{1/2−ε} changes of e.
STATUS: (a), (b) PROVED. (c) CONDITIONAL on (LV_a). This is the Linnik–Vinogradov theorem with finitely many excluded
primes; I did not check that extension in detail.
TYPE: STRUCTURE / CONDITIONAL
BEYOND: This is the T5 step requested; it is close to KNOWN (AP lemma + Linnik–Vinogradov) and of low novelty.
PROOF: We have 4a f(x) = (2ax+b)² − D. (b) Let p ≤ N with p ∤ 2a and D ≡ s² mod p (allowing s ≡ 0). Then
x0 ≡ (−b+s)(2a)^{−1} mod p is a root of f. Among the N ≥ p consecutive x some x ≡ x0, so p | f(x). Since f(x) is prime,
f(x) = p ≤ N, a contradiction. (a) If D = s², then 4a f(x) = u·w with u = 2ax+b−s and w = u+2s. If f(x) = p0 is prime,
then p0 divides u or w. If p0 | u, write u = p0·u'. Then u'·w = 4a, so w is a nonzero divisor of 4a and |w| ≤ 4a. So w ∈ [−4a,4a]. Since w = 2ax + const, at
most 5 values of x qualify; the same holds for u. So N ≤ 10. (c) is immediate from (b). D ≡ b² mod 4, so χ_D is a
Kronecker character, nonprincipal when D is not a square.

### C3
STATEMENT (conjecture): κ'_S → 1 as S runs over the initial segments of the odd primes. Equivalently, the local
value-period game proves liminf q_n/n² ≥ 1−ε for every ε. That is exactly the profinite-barrier ceiling: κ'_S ≥ (M−1+E0)/M > 1
always, via the quadratic chain with e ≡ 2.
STATUS: CONJECTURED. Evidence: κ'_S = 1.8401, 1.7068, 1.5734, 1.3916, 1.2496 for S up to 3, 5, 7, 11, 13. The decrease is
steady (~0.13–0.18 per prime). It is only 5 points, and the next case (M = 255255) was too big for this method.
Mechanism: repeating a gap needs a highly divisible gap value. The joint residue walk mod 3, …, 13 penalises the long
repeats that Richter's per-value count allows.
TYPE: QUANT (conjectural)

### C4 (obstruction to angle A1)
STATEMENT: Exact DP over all convex prime chains with terms ≤ 10^6 finds that the length-minimal chains (L ≤ 676) have
maximal constant-second-difference stretches of length ≤ 9 (484 stretches for L=676). So "long pieces die by
Linnik–Vinogradov" (C2) applies to no extremal chain in range. Any successful A1-type proof must get its contradiction
entirely from the glitch structure, i.e. from a family-level input on the walk of discriminants Δ_i. One-piece Burgess bounds
contribute nothing at observable scales.
STATUS: computational observation (D1), NEGATIVE.

## Data
D1 (dp.py). Exact DP over all convex prime chains with all terms ≤ 10^6. Gap cap 3600, never binding (max gap used 3354).
Xmin(L) is the least possible largest term of a convex chain with L gaps. All optimal chains start at 2.
L: 100→10589 (X/L²=1.059); 200→57751 (1.444); 300→154073 (1.712); 400→301057 (1.882); 500→503621 (2.014);
600→760913 (2.114); 676→997427 (2.183). L=40→1213 (0.758). X/L² rises ~0.4 per doubling of L, consistent with ~c·L² log L.
e-distribution of the L=676 optimal chain: e=0:151, 2:212, 4:71, 6:69, 8:55, 10:37, 12:14, 14:18, …. Longest constant-e run: 9.
D2 (game2/game3/check). ρ_S (max steps per value-period, exact): S={3}:2, {3,5}:20, {3,5,7}:156, {3..11}:1596, {3..13}:18748.
E0_S: 3.5203, 5.6015, 9.2107, 11.3178, 15.1308. Bounds 1/κ'_S: 0.5434, 0.5859, 0.6356, 0.7186, 0.8002.
D3 (indep.py). Independent pure-Python check of the whole local relaxation for S={3,5,7}. It works directly over values
v = 2..12600, with the true caps P(v)−2 at 105 | v. The maximal N(V)/(V/2) is 1.57143, 1.57238, …, 1.57302 at
V = 2100·k, converging up to the predicted κ' = 1.57344. This agrees with the certificate.

## Dead ends
- Naive mean-payoff game with cost e over finite S (game.py): its value is 0, because a constant gap ≡ 0 mod M is locally
  free. One must count steps per gap VALUE and use the true cap P(v)−2 at values with M | v. That is what C1 does.
- Angle A1 as stated: the "glitch budget" does not bind. The average e allowed in CORE is ~4C ≥ 2, so no e=2 dominance
  is forced, and extremal chains glitch every ≤ 9 steps (C4).
