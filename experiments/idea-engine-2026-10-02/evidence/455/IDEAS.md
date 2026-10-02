# Research engine: problem 455, run 20261002-041515-654114-erdos455

Spend $15.4223; 17 claim(s); 2 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] r1s1/C1 PROVED QUANT
**Statement.** Let q_1<q_2<… be primes with q_{n+1}−q_n ≥ q_n−q_{n−1}. Then liminf q_n/n² ≥ 1/κ'_S for
S={3,5,7,11,13}, where κ'_S = (ρ_S+E0_S)/M, M=15015, ρ_S=18748, E0_S=15.13085 (defined below); numerically
liminf q_n/n² ≥ 0.80024. Also (same method) S={3,5,7}: ρ=156, ≥0.63555; S={3,…,11}: ρ=1596, ≥0.71859.
**Beyond.** KNOWN has liminf > 0.352 (Richter); the obvious cap P(v)−2 version gives 1/κ = 0.5434. 0.8002 beats both.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "cite": null, "significance": 1, "why": "No published improvement on Richter's liminf q_n/n^2 > 0.352 is known, and 0.80024 via joint residue run-counting mod 15015 appears new. But it is a congruence-only refinement provably capped at 1 by the local barrier, so it is a modest constant improvement with no bearing on the limit being infinity."}`
**Proof or evidence.**

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

## [validated-new] r2s1/C3 PROVED NEGATIVE
**Statement.** Let P ≥ 1 and r* ∈ Z/P, and let m(r*) = 2 and m(r) = 1 for r ≠ r* (one repeated gap per period, average
multiplicity 1 + 1/P). This pattern is never Ẑ-good: it fails mod some prime ≤ max(7, P).
**Beyond.** This is the first proof that the simplest "beat the quadratic" local strategies are killed by the profinite
constraints alone. Previously only the cap ρ_z ≥ 1 and numerical ρ_z were known.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "cite": null, "significance": 1, "why": "No published classification of Ẑ-good gap-multiplicity patterns is known to me; the claim is a likely elementary finite residue check that confirms local obstructions for the simplest 'one repeat per period' family. By the team's own profinite barrier it can at best feed toward a local liminf ≥ 1 (improving Richter's 0.352), not toward the q_n/n² → ∞ question."}`
**Proof or evidence.**

- **Setup.** Here Mt = P + 1 and d = 1. The cyclic increments are all 1 except one 0 per period, so there are
  P − 1 = Mt − 2 consecutive unit increments.
- **Applying C2.** Any odd prime p ≤ P with p ∤ P(P+1) satisfies p − 2 ≤ P − 1 and p ≤ Mt, so C2 applies.
- **P ≥ 17.** By Ramanujan (R_3 = 17) there are at least 3 primes in (P/2, P].
  - If such a p divides P then p = P.
  - If p | P+1, then (P+1)/p < 2(P+1)/P ≤ 2.12, so p = (P+1)/2.
  - Hence at least one of the three is a valid p. Independently, a direct check found no exception for
    17 ≤ P ≤ 20000.
- **P ≤ 16.** I checked every dip position computationally (pat4.py): full brute force for P ≤ 6, and the C1
  criterion plus brute force at the primes dividing 2P·Mt for 7 ≤ P ≤ 16.
  - Every case fails at some p ∈ {3, 5, 7}.
  - Failure at 3 happens exactly when 3 ∤ P, since then the repeated value hits 3 ∤ k in some block (AP lemma).

## [valid-routine] r1s2/C2 PROVED CONDITIONAL
**Statement.** Assume GRH for quadratic Dirichlet L-functions. Then Φ_f(K,P) ≪ K·P·log⁴(KP) for K ≤ P^{O(1)}. In particular the FIRST STEP holds for non-square m_k, for every ε > 0.
**Beyond.** Together with C2 this pins the repaired step strictly between "Burgess-ε removal" and GRH.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": "Standard GRH explicit-formula bound Σ_{p≤P} χ(p)log p ≪ √P log²(qP) (Ankeny 1952; Montgomery–Vaughan, Multiplicative Number Theory I, §13; Bach 1990), squared and summed over k ≤ K", "significance": 1, "why": "Under GRH each quadratic character sum over primes up to P is ≪ √P log²(|m|P), and squaring and summing over K discriminants gives K·P·log⁴(KP) directly, with no cross-discriminant input. It only confirms that a step of the team's programme is consistent under GRH and makes no progress on the unconditional CORE or the glitch barrier."}`
**Proof or evidence.**

1. Write m = g²m₀ with m₀ squarefree, m₀ ≠ 1 since m is non-square. For p ∤ 2m, (m/p) = χ(p), where χ is the primitive real character of Q(√m₀), of conductor ≤ 4|m₀|.
2. GRH gives Σ_{p≤x}χ(p)log p ≪ √x·log²(|m|x). Partial summation gives |Σ_{p∈Π_P}χ(p)| ≪ √P·log²(|m|P).
3. The primes p | 2m change S by ≤ ω(2m) ≪ log|m|.
4. Here |m_k| ≪ K² ≤ P^{O(1)}. Sum over k ≤ K.

## [valid-routine] r1s2/C3 PROVED STRUCTURE
**Statement.** (a) Let f be quadratic with a ≥ 1 and disc(f) = b² − 4ac ≠ 0. Let β = #{p ∈ Π_P : p | a·disc(f)}. Then
Σ_{k≤K}|S(f(k))|² ≤ Kπ_P(1+2β) + π_P²K/P² + 8Pπ_P²(1 + log 4P²).
Hence #{k ≤ K : S(f(k)) ≤ −π_P/2} ≪ (1+β)K log P/P + P log P. For K = P² this is ≪ K^{1/2} log K.
(b) For every x and H ≥ 1: Σ_{x<m≤x+H}|S(m)|² ≤ Hπ_P + 4Pπ_P²(1 + log 4P²).
(c) If |r_k| ≤ R, then Σ_k max_{|r|≤R}|S(f(k)+r)|² ≤ Σ_{|r|≤R} [bound (a) for f+r]. Exactly one shift r can make disc(f+r) = 0; when that happens the family f + r consists of a·(linear)², so bound (a) is not available for it.
**Beyond.** Not listed in KNOWN. It is standard technology, so this is low novelty. Its role is to show that the gain over Heath-Brown exists only when perturbations are o(π_P), as in (c), whereas C4 shows that real glitches are of size ≍ k.
PROOF of (a):
1. Expand |S|² = Σ_{p,p'∈Π_P} Σ_k (f(k)/p)(f(k)/p').
2. Diagonal p = p': each term is ≤ 1, giving ≤ Kπ_P.
3. Pairs involving a bad prime (one dividing a·disc): there are ≤ 2βπ_P such pairs, each ≤ K.
4. Good p ≠ p', with n = pp' ≤ 4P². Let ψ(x) = (f(x)/n), the Jacobi symbol, which is n-periodic. Completion gives |Σ_{k≤K}ψ(k)| ≤ (K/n)|ψ̂(0)| + max_{h≢0}|ψ̂(h)|·(1/n)Σ_{h=1}^{n−1}1/(2‖h/n‖), and the last factor is ≤ 1 + log n.
5. By CRT, ψ̂(h) factors as a product over p and p' of the sums Σ_{x mod p}(f(x)/p)e(h_p x/p).
6. For a good p, the untwisted sum equals −(a/p), of absolute value 1. Each twisted sum is ≤ 2√p by Weil: f has 2 distinct roots mod p and the twist is linear, so the bound is (2 + 1 − 1)√p.
7. Hence |ψ̂(0)| = 1 and |ψ̂(h)| ≤ 4√n ≤ 8P.
8. Summing over ≤ π_P² pairs gives π_P²(K/P² + 8P(1 + log 4P²)).
9. The counting consequence follows from Chebyshev's inequality: each such k contributes ≥ π_P²/4.
PROOF of (b): The same argument with f(m) = m. The complete sums Σ_{x mod n}(x/n) vanish for p ≠ p'. The twisted sums are Gauss sums of modulus √n ≤ 2P.
NUMERICS (s2.py):
- (a): lhs/(Kπ_P) ≈ 0.95–1.10 and lhs/rhs ≈ 0.04–0.06, for f ∈ {k²+k+41, 2k²−3, 3k²+5k−7, k²+1} and P ∈ {30, 100, 300}.
- (b): lhs/(Hπ_P) ≈ 0.84–1.07.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": "Standard completion + Weil bound for character sums at polynomial values (e.g. Iwaniec–Kowalski, Analytic Number Theory, Ch. 11–12; Pólya–Vinogradov completion method)", "significance": 0, "why": "A textbook second-moment computation for sums of Legendre symbols along a quadratic: expand the square, complete sums, and apply CRT factorisation with Weil/Gauss-sum bounds. By the team's own remark it gives no traction once glitch perturbations are of size ≍ k, so it does not advance CORE."}`
**Proof or evidence.**

(none)

## [valid-routine] r1s2/C4 PROVED STRUCTURE
**Statement.** Let d_j = q_j − q_{j−1}. For a stretch with constant second difference 2, set Δ_i := (d_i + d_{i+1})² − 16q_i. This is constant on the stretch. Indeed Δ_i = 4·disc of the local interpolating quadratic x² + x(d_i+d_{i+1})/2 + q_i. Now suppose the gaps are d_j = g + 2j up to j = i₀, and d_j = g + 2j + 2 for j > i₀ (one extra bump of 2). Then Δ is constant on both sides, and Δ_after − Δ_before = 16(g + 2(i₀+1)), i.e. 16 times the unbumped gap d_{i₀+1}.
**Beyond.** This quantifies the "glitch" drift in the frontier map.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": null, "significance": 0, "why": "The invariance of (d_i+d_{i+1})^2-16q_i under constant second difference 2, and its jump of 16·d' at a single bump, follow from a direct two-line expansion of the local interpolating quadratic's discriminant. It is correct but gives no new constraint on convex prime chains."}`
**Proof or evidence.**

1. Invariance. Δ_{i+1} − Δ_i = (2d_{i+1}+2)² − (2d_{i+1}−2)² − 16d_{i+1} = 0.
2. After the bump, q'_i = q_i + 2(i − i₀) and d'_i = d_i + 2. So Δ' = (d_i + d_{i+1} + 4)² − 16q_i − 32(i − i₀) = Δ + 8(d_i + d_{i+1}) + 16 − 32(i − i₀).
3. Substituting d_i + d_{i+1} = 2g + 4i + 2 gives Δ' − Δ = 16g + 32i₀ + 32.
REMARK (heuristic, not claimed): If q_k ≈ λk² with λ > 1, then Δ ≈ 16λ(λ−1)k², so consecutive squares near Δ are ≈ 8√(λ(λ−1))·k apart. One bump moves Δ by ≈ 32λk, which is larger. Real chains thus realise perturbations of size ≍ k per glitch, the regime where C1 and C2 show the family structure is useless, rather than the regime |r| = o(π_P) where C3(c) helps.

## [valid-routine] r1s4/C1 PROVED SPECIAL
**Statement.** Fix θ < 1/2. Let q_0<q_1<… be primes with nondecreasing gaps g_i = q_{i+1}−q_i. Suppose that for all large n,
#{i ≤ n : Δ³q_i ≠ 0} ≤ n^θ, where Δ³q_i = q_{i+3}−3q_{i+2}+3q_{i+1}−q_i. Then q_n/n² → ∞.
(Stronger structural form: for every C, and for every large n with q_n ≤ Cn², the window W=[n/2,3n/4] contains ≥ n^{1/2−o(1)} glitches.)
**Beyond.** KNOWN kills only a single exact quadratic piece (Euler-type, via least split prime). This handles n^{1/2−ε} pieces
with any second differences, beating the assignment's n^{1/3−ε}.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": null, "significance": 1, "why": "Splitting the window into at most n^θ exact quadratic pieces, applying the AP lemma or Linnik–Vinogradov to each piece's discriminant (|D| ≪ a n²), and combining with Σ a_j m_j ≪ n via Hölder gives a contradiction exactly for θ < 1/2, so the claim is a short consequence of tools already listed as known. It does not address the glitch-dense regime that constitutes the real core."}`
**Proof or evidence.**

Suppose not. Then there are C and infinitely many n with q_n ≤ Cn². Fix such an n, large.
(1) Gap bound. By the Lean convex tail inequality (n−i)g_i ≤ q_n − q_i, for i ≤ 3n/4+1 we get g_i ≤ Cn²/(n/4−1) ≤ 5Cn.
(2) Pieces. Let W = [⌈n/2⌉, ⌊3n/4⌋]. Call i ∈ W a glitch if Δ³q_i ≠ 0; there are at most g := n^θ of them. The
non-glitch indices (at least n/4−1−g of them) form at most g+1 maximal runs J=[s,s+ℓ−1]. On J, Δ²q_i = D_J (constant)
for i ∈ [s,s+ℓ], so q_{s+j} = f(j) := q_s + d j + D j(j−1)/2 for 0 ≤ j ≤ ℓ+2, with d = g_s ≤ 5Cn and D = D_J ≥ 0.
(3) Averaging. The ranges [s,s+ℓ] of distinct runs are disjoint subsets of W, and Δ²q_i = g_{i+1}−g_i ≥ 0. Hence
Σ_J ℓ_J D_J ≤ Σ_{i∈W} Δ²q_i ≤ g_{⌊3n/4⌋+1} ≤ 5Cn.
(4) Choosing a piece. Put θ = 1/2−3η and L = n^{1/2+η}. Runs with ℓ < L have total length ≤ (g+1)L = o(n). By (3),
runs with D_J ≥ 40C have total length ≤ n/8. So for large n there is a run with ℓ ≥ L and D ≤ 40C. Note also
q_s ≥ s ≥ n/2 > ℓ+1.
(5) Case D = 0. Then f(0..ℓ) is an AP of primes > ℓ+1. For each prime p ≤ ℓ+1, p | d: otherwise f(0),…,f(p−1)
covers every residue mod p, so p | some f(j) > p, which is impossible. So d ≥ 2^{π(ℓ+1)} > 5Cn, a contradiction.
(6) Case D ≥ 1. The identity 8D f(j) = (2Dj+2d−D)² − Δ holds with Δ := (2d−D)² − 8D q_s (checked by expanding).
Let p ≤ ℓ+1 be an odd prime with p ∤ D. Then u_j = 2Dj+2d−D, j=0..p−1, runs over all residues mod p. If Δ ≡ t² mod p
for some t (t=0 allowed), choose u_j ≡ t; then p | 8Df(j), and p ∤ 8D, so p | f(j) with f(j) prime > p. This is
impossible. Hence (Δ/p) = −1. Consequently Δ is not a square: ω(D) is O(1) < #{odd p ≤ ℓ+1}. Also Δ ≡ 0,1 mod 4.
So Δ = Δ0 f0² with Δ0 ≠ 1 a fundamental discriminant, and χ = χ_{Δ0} is a primitive real character mod k = |Δ0| ≥ 3.
For odd p ≤ ℓ+1 with p ∤ D: p ∤ Δ, so p ∤ f0, and χ(p) = (Δ/p) = −1.
Also k ≤ |Δ| ≤ max((2d−D)², 8Dq_s) ≤ max((11Cn)², 320C²n²) ≤ 400C²n².
So χ(p) ≠ 1 for all primes p ≤ y := ℓ+1 outside E := {2} ∪ {p | D}, where |E| ≤ 1+ω(D) = O_C(1),
y ≥ n^{1/2+η} ≥ k^{1/4+η/3} for large n. This contradicts Lemma C below. ∎

LEMMA C. For ε>0 and B ≥ 1 there is Y0 such that: if χ is a primitive real character mod k ≥ 3, E is a set of ≤ B
primes, and y ≥ max(Y0, k^{1/4+ε}), then some prime p ≤ y, p ∉ E, has χ(p) = 1.
(This is a Linnik–Vinogradov variant with an excluded set of primes. The proof follows their hyperbola argument.)
Proof. Let r = 1*χ ≥ 0. r is multiplicative, with r(p^a) = a+1 if χ(p)=1, 1 if χ(p)=0, and [a even] if χ(p)=−1.
Upper bound: suppose no such p exists. Every n ≤ y factors as n = a·b·c, where c is built from primes in E, b from
primes dividing k but not in E, and a from the remaining primes ≤ y, all of which have χ = −1. Then
r(n) ≤ [a = □]·τ(c), so
Σ_{n≤y} r(n) ≤ √y · Π_{p∈E}(1−p^{−1/2})^{−2} · Π_{p|k}(1−p^{−1/2})^{−1} ≤ √y · 11.7^B · 3.42^{ω(k)} = √y · k^{o(1)}.
Lower bound: Let S(t) = Σ_{d≤t} χ(d), take 1 ≤ z ≤ y, and put β = sup_{t≥z}|S(t)|/t. By the hyperbola method,
Σ_{n≤y} r(n) = Σ_{d≤z}χ(d)⌊y/d⌋ + Σ_{e≤y/z}(S(y/e)−S(z)).
Partial summation, together with periodicity (S(t+k) = S(t)), gives |Σ_{d>z}χ(d)/d| ≤ 2β(2+log⁺(k/z)). Hence
Σ_{n≤y} r(n) ≥ yL(1,χ) − z − 2βy(3+log(yk)).
Case k ≤ y^{1/3}: take z = √y. Pólya–Vinogradov gives β ≪ √k log k/√y. The class number formula gives the effective
bound L(1,χ) ≥ 0.96/√k. The main term ≥ 0.96 y^{5/6} beats the errors y^{2/3+o(1)} and the upper bound y^{1/2+o(1)}.
Case k > y^{1/3} (so k is large and y^{o(1)} = k^{o(1)}): take z = k^{1/4+ε/2} ≤ y k^{−ε/2}. Burgess (IK Thm 12.6)
gives |S(N+H)−S(N)| ≪_{r,δ} H^{1−1/r} k^{(r+1)/(4r²)+δ}, valid for all r when k is cube-free. A real primitive k that is
not cube-free is 8k′ with k′ odd squarefree; split into classes mod 8 and apply Burgess mod k′ on shifted intervals.
With r ≥ 1/ε and δ = ε/(8r) this gives β ≪ k^{−η}, η = ε/(8r). Siegel gives L(1,χ) ≫_{η} k^{−η/2}. Then
yk^{−η/2} ≫ z + βy log(yk) + √y k^{o(1)}, using √y ≤ y k^{−1/8}. This is a contradiction for large k. ∎

## [valid-routine] r1s4/C2 PROVED CONDITIONAL
**Statement.** Assume GRH for quadratic Dirichlet L-functions. If #{i≤n: Δ³q_i≠0} ≤ n/(log n)^5 for all large n, then q_n/n² → ∞.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": "Ankeny (1952)/Bach (1990) GRH least-split-prime bound; cf. the team's own 'glitch barrier' (pieces shorter than log²|Δ| evade GRH)", "significance": 0, "why": "The hypothesis forces quadratic pieces of length about (log n)^5. The GRH least split/ramified prime bound (log|D|)^{2+ε} plus the AP lemma rules out pieces longer than polylog, so the implication is a short standard argument and is nearly vacuous. It says nothing about the actual obstruction, chains that glitch frequently."}`
**Proof or evidence.**

As in C1, with L = K0 (log n)^4: short runs have total length ≤ K0 n/log n = o(n). We obtain a piece with
D ≤ 40C, length ℓ ≥ K0 log^4 n, k ≤ 400C²n², and χ(p) ≠ 1 for all p ≤ x = ℓ+1 outside the bounded set E. Then
Σ_{p≤x}(1+χ(p))log p ≤ 2Σ_{E} log p + log k = O(log n). Under GRH, ψ(x,χ) ≪ √x log²(kx) (Davenport ch. 20).
Chebyshev gives ψ(x) ≥ x/2, and prime powers contribute ≪ √x log x. So
x/2 − c√x log²(kx) ≤ O(log n), which is false for x = K0 log^4 n with K0 large. ∎

## [valid-routine] r2s1/C1 PROVED STRUCTURE
**Statement.** Put R = Σ_s r_s and R_s = Σ_{s'<s} r_{s'}. Then T_{j,s} = a j² + b_s j + c_s with a = P·Mt,
b_s = 2R − P·Mt + 2Ps and c_s = q0 + 2R_s. Put D_s = b_s² − 4a·c_s.
- (i) For an odd prime p ∤ P·Mt, the pattern is p-good iff some D ∈ F_p makes D + δ_s a quadratic nonresidue mod p
  for every s, where δ_s = D_s − D_0 does not depend on q0.
- (ii) For every s, D_{s+2} − 2D_{s+1} + D_s = 8P² − 8P·Mt·(r_{s+1} − r_s).
**Beyond.** The KNOWN Δ-invariant (r1s2/C4) is per-step. This is the exact local admissibility criterion for an entire
periodic gap strategy, and it reduces p-goodness at every prime p ∤ P·Mt to a finite pattern of shifted
discriminants.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "cite": null, "significance": 0, "why": "Part (i) is the standard discriminant/nonresidue criterion for a quadratic to avoid 0 mod p, plus the observation that shifting q0 translates all D_s uniformly through F_p; part (ii) is a direct algebraic second-difference computation. Both are purely local (congruence) statements, so the team's profinite barrier caps them, and they do not touch the CORE size–residue coupling."}`
**Proof or evidence.**

- **Formula.** Q_{j+1} − Q_j = Σ_s 2(Pj + r_s) = 2P·Mt·j + 2R. Hence Q_j = P·Mt·j² + (2R − P·Mt)j + q0, and adding
  Σ_{s'<s} 2(Pj + r_{s'}) = 2Ps·j + 2R_s gives the formula.
- **Criterion (i).** Fix s. As j runs over j ≥ j0, j covers every residue mod p, so T_{j,s} mod p runs over all
  values of the quadratic polynomial a j² + b_s j + c_s on F_p. Since p is odd and a is invertible mod p, the
  polynomial has a root iff D_s is a square or 0 mod p. So a start is good iff every D_s is a nonresidue.
- **Free parameters.** D_0 = b_0² − 4a·q0 runs over all of F_p as q0 does, and δ_s = b_s² − b_0² − 8a·R_s does not
  involve q0. The block-origin residue k0 mod p is free when p ∤ P. Replacing j by j + j0 does not change the
  discriminant, so k0 drops out.
- **(ii).** b_s is linear in s with slope 2P, so b_s² has second difference 8P². Also
  R_{s+2} − 2R_{s+1} + R_s = r_{s+1} − r_s.
- **Rotation.** If the block origin is moved to k ≡ c mod P, every gap gains 2c. This adds 2c·s to c_s and changes
  b_s only by a constant, so (ii) still holds. Any stretch of at most Mt consecutive steps of the cyclic step
  sequence (r_{s+Mt} = r_s + P) therefore lies inside one block after rotation.
- **Check.** Brute-force simulation (enumerating all starts over a full period lcm(P,p)·p) agreed with the
  criterion on 202 of 202 random (pattern, p) pairs with p ∈ {5,7,11,13}. Script: pat3.py.

## [broken] r1s2/C2 PROVED REDUCTION
**Statement.** Define Φ_f(K,P) = sup Σ_{k≤K}|S(m_k)|², the sup taken over integer sequences with m_k non-square and |m_k − f(k)| ≤ kK.
(i) Let K ≥ max(|b|, 8a). Let J_K be the interval of integers m with |m − f(K)| ≤ K²/4. Then every non-square m ∈ J_K satisfies Φ_f(K,P) ≥ ⌊K/(8a)⌋·|S(m)|².
(ii) Trivially, Φ_f(K,P) ≤ K·max{|S(m)|² : m non-square, |m| ≤ |f(K)| + K²}.
(iii) Corollary. Suppose the repaired FIRST STEP holds for some f, some ε < 1/2 and all large P, i.e. Φ_f(P²,P) ≤ A P^{2+4ε}·P/log P. Then there is m₀ such that every non-square integer m ≥ m₀ has a prime p ∤ m, p ≤ C_a m^{1/4}, with (m/p) = 1.
**Beyond.** Linnik–Vinogradov in KNOWN gives ≪ |D|^{1/4+ε}. Part (iii) would remove the ε, and 1/4 is the Burgess barrier. So any proof of the A2 first step, even after the square fix, must beat Burgess/LV for individual characters. Part (i) shows the reason: the "near-quadratic structure" with |r_k| ≤ kK carries no information, because for k ≍ K the windows have length ≍ K² ≍ the whole range.
**Referee.** `{"valid": false, "first_error": "(iii) step 1: the corollary's hypothesis is Φ_f(P²,P) ≤ A P^{2+4ε}·P/log P with ε<1/2, but the proof substitutes the stronger A(K+P)^{1+ε}P/log P ≈ A P^{2+2ε}·P/log P. Under the stated hypothesis, (i) only gives |S(m)|² ≪ P^{1+4ε}/log P, which contradicts |S(m)|² ≫ P²/log²P only for ε<1/4; for 1/4 ≤ ε < 1/2 there is no contradiction. (Minor, harmless earlier slip: (i) step 5's claim that at most one of f(k), f(k)+1, f(k)+2 is a square is false when f(k)=0 or −1, since 0 and 1 are both squares; a non-square still exists.)", "fixable": true}`
**Adversary.** `{"broken": true, "how": "Part (iii) states the hypothesis Φ_f(P²,P) ≤ A P^{2+4ε}·P/log P (= A K^{1+2ε}P/log P with K=P²) for ε<1/2, but the proof substitutes the stronger A(K+P)^{1+ε}P/log P ≈ A P^{2+2ε}P/log P. Under the stated hypothesis, (i) gives only |S(m)|² ≤ 8aA P^{1+4ε}/log P, which contradicts |S(m)|² ≫ P²/log²P only when ε<1/4. For 1/4 ≤ ε < 1/2 no contradiction arises and the m^{1/4} conclusion is not established. Fix: restrict to ε<1/4 or state the hypothesis with P^{2+2ε}. Minor: step 5 of (i) wrongly says at most one of f(k),f(k)+1,f(k)+2 is a square (0 and 1 are both squares), but a non-square still always exists.", "severity": "fixable"}`
**Proof or evidence.**

(i)
1. Let k be an integer in [(1−δ)K, K] with δ = 1/(8a).
2. Then 0 ≤ f(K) − f(k) = (K−k)(a(K+k) + b) ≤ δK(2aK + |b|) ≤ K²/4 + |b|K/(8a).
3. So |m − f(k)| ≤ K²/4 + K²/4 + |b|K/(8a) ≤ K²/2 + 3K²/8 = 7K²/8 ≤ (1−δ)K² ≤ kK. This uses |b| ≤ 3aK, which holds since K ≥ |b|, and δ ≤ 1/8.
4. Hence m_k := m is admissible for all ≥ ⌊K/(8a)⌋ such k.
5. For each remaining k, choose m_k ∈ {f(k), f(k)+1, f(k)+2} non-square. At most one of these can be zero, and two nonzero squares never differ by 1 or 2, so at most one of the three is a square. All three are admissible since kK ≥ 2. These terms contribute ≥ 0.
(ii) Each term is ≤ the max, and |m_k| ≤ |f(k)| + kK ≤ |f(K)| + K² for large K.
(iii)
(Read the hypothesis literally, as Φ_f(P²,P) ≤ A(K+P)^{1+ε}P/log P with K = P².)
1. By (i), every non-square m ∈ J_{P²} has |S(m)|² ≤ A(2K)^{1+ε}P/(log P·⌊K/(8a)⌋) ≤ 17a·2^{ε}A·P^{1+2ε}/log P for large P.
2. Take m ∈ J_{P²}. Then m ≍ aP⁴, so ω_P(m) := #{p ∈ Π_P : p | m} ≤ log m / log P ≤ 5 for large P.
3. Suppose (m/p) = −1 for every p ∈ Π_P with p ∤ m. Then |S(m)| ≥ π_P − 5 ≫ P/log P, so |S(m)|² ≫ P²/log²P.
4. This exceeds the bound in step 1 for large P, because 1 + 2ε < 2. Contradiction.
5. So some p ∈ Π_P with p ∤ m has (m/p) = 1, and p < 2P ≤ C_a m^{1/4}, since m ≥ aP⁴ − P⁴/4 − O(P²) ≥ (3/4)P⁴ for large P.
7. Covering all large m. The intervals J_{P²} = [aP⁴ + O(P²) − P⁴/4, aP⁴ + O(P²) + P⁴/4] for consecutive integers P overlap for large P, because a(P+1)⁴ − aP⁴ ≈ 4aP³ < P⁴/2. So every large m lies in some J_{P²}. For non-square m with p ∤ 2m, (m/p) = 1 means p splits in Q(√m).

## [broken] r1s3/C1 PROVED QUANT
**Statement.** Let q_1 < q_2 < ... be primes with nondecreasing gaps d_n = q_{n+1} − q_n. Then
d_n >= (2/ρ − o(1)) n and liminf q_n/n^2 >= 1/ρ, where ρ = 18748/15015 + τ_13 and
τ_13 = Σ_{p prime, p >= 17} (p−2)(1−1/p)/∏_{3<=ℓ<p, ℓ prime} ℓ = 0.0010078....
So ρ = 1.2496258... and 1/ρ = 0.8002396... > 0.8002.
**Beyond.** Richter's 0.352 (KNOWN) and the T1 target 0.5434.
PROOF.
Setup. Let S = {3,5,7,11,13} and M = 15015. Call r ∈ Z/M a unit if gcd(r, M) = 1.
Fix n0 with q_{n0} > 13 and q_{n0} odd. For n >= n0 every q_n is a prime > 13, so it is odd and a unit mod M, and every d_n is even.
Since the d_n are nondecreasing, for each even v the set I_v = {n >= n0 : d_n = v} is an interval of indices. Write m_v = |I_v|.
If I_v = {a, ..., a+m_v−1}, then the run is q_a, q_a+v, ..., q_a+m_v·v = q_{a+m_v}, and all of these are terms of the sequence.

(1) Game. A state is a unit r mod M. The phases are k = 1, ..., M, with phase k having step s_k = 2k mod M. At phase k the player
picks m >= 0 such that r + j·s_k is a unit for j = 1..m, and moves to r + m·s_k with gain m. When s_k = 0 (M | 2k) the player must
take m = 0. One period is phases 1..M. Let F act on vectors x ∈ (Z ∪ {−∞})^{units} by
F(x)(r') = max over one-period paths r -> r' of x(r) + gain.
F is monotone and commutes with adding constants.
cert13.py computes F by the vectorised DP (k = 1..M; at each phase y(r') = max_m x(r' − m s) + m along unit chains). It finds an
integer vector x* that is finite on all 5760 units with F(x*) = x* + λ, λ = 18748, exactly. Value iteration from 0 reaches it after
1 period, and the second period confirms it.
Consequence: for every path of K periods with gain G from r0 to rK, x*(r0) + G <= F^K(x*)(rK) = x*(rK) + Kλ. Hence
G <= Kλ + B, where B = max x* − min x* is a finite constant.

(2) The sequence is a game pa
**Referee.** `{"valid": false, "first_error": "Step (2) onward is missing: the text breaks off at '(2) The sequence is a game pa)' and no proof is given. Nothing proves the reduction of the sequence to a game path, the separate bound for phases with 15015 | v (where the game forces m=0 but real runs can have length up to p-2 for the least prime p>=17 not dividing v; this is the source of tau_13 and its averaging), or the counting that turns G <= K*lambda + B into d_n >= (2/rho - o(1))n and liminf q_n/n^2 >= 1/rho. Also, the identity F(x*) = x* + 18748 depends on an unprovided cert13.py and cannot be verified.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [broken] r2s1/C2 PROVED NEGATIVE
**Statement.** (glitch forcing) Let a periodic pattern have d = Mt − P ≠ 0. Let p be an odd prime with p ∤ P·Mt·d and
p ≤ Mt. If the cyclic step sequence contains p−2 consecutive unit increments (r_{s+1} − r_s = 1), then the pattern
is not p-good. Consequently every Ẑ-good periodic pattern with d ≠ 0 has, for every such prime p, a dip or bump
(r_{s+1} − r_s ≠ 1) among every p−2 consecutive increments.
**Beyond.** This is a profinite analogue of the glitch barrier. In the local model, any periodic strategy denser than
the quadratic must glitch at a rate controlled by the least prime not dividing P·Mt·d.
**Referee.** `{"valid": false, "first_error": "Step 1/2: the hypothesis gives only p−2 consecutive unit increments, i.e. p−1 consecutive indices (s0..s0+p−2), but the proof applies C1(ii) on p consecutive indices s0..s0+p−1 without justification. On p−1 consecutive s the s-values miss one residue class mod p; if it is the vertex −B/(2A), the quadratic takes only (p−1)/2 values, all of which can be nonresidues (e.g. p=3), so the pigeonhole contradiction fails. Rotation (p ≤ Mt) only places the stretch in one block; it does not supply the missing index.", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

- Rotate (C1) so that the p consecutive step indices s0, …, s0+p−1 lie in one block; this is possible since p ≤ Mt.
- On that stretch, C1(ii) gives a constant second difference D_{s+2} − 2D_{s+1} + D_s = 8P(P − Mt) = −8Pd.
  This is nonzero mod p.
- So D_s ≡ A s² + B s + C mod p with A = −4Pd invertible.
- The s-values form a complete residue system mod p. By completing the square, D_s therefore takes exactly (p+1)/2
  distinct residues.
- By C1(i), all of them must be nonresidues, but only (p−1)/2 nonresidues exist. Contradiction.
- Check: 1052 random (pattern, p) instances satisfying the hypotheses all failed in brute force, with 0 violations
  (pat4.py).

## [not validated] r1s1/C2 OTHER STRUCTURE
**Statement.** Let f(x)=ax²+bx+c with a ≥ 1, D=b²−4ac, and suppose f(0),…,f(N−1) are all primes > N.
(a) If D is a perfect square (including 0), then N ≤ 10.
(b) Otherwise every prime p ≤ N with p ∤ 2a has (D/p) = −1. So N < n_a(D) := the least prime p ∤ 2a with (D/p) ≠ −1.
(c) Consequently, if (LV_a) holds (the least prime p ∤ 2a with χ_D(p)=1 is ≪_{ε,a} |D|^{1/4+ε}), then N ≪_{ε,a} |D|^{1/4+ε}.
In a convex chain, a stretch of N+1 consecutive terms with constant second difference e=2a lies on such an f, with
D = (d−a)² − 4a·q (d any gap of the stretch, q its left endpoint). In CORE (gaps ≤ 4CL, X=4CL²) this gives |D| ≪_C X.
Hence every constant-e stretch with e ≥ 2 has length ≪ L^{1/2+ε}. Since e=0 stretches have length ≤ P(v)−2 ≪ log L,
a CORE counterexample has ≫ L^{1/2−ε} changes of e.
**Beyond.** This is the T5 step requested; it is close to KNOWN (AP lemma + Linnik–Vinogradov) and of low novelty.
**Proof or evidence.**

We have 4a f(x) = (2ax+b)² − D. (b) Let p ≤ N with p ∤ 2a and D ≡ s² mod p (allowing s ≡ 0). Then
x0 ≡ (−b+s)(2a)^{−1} mod p is a root of f. Among the N ≥ p consecutive x some x ≡ x0, so p | f(x). Since f(x) is prime,
f(x) = p ≤ N, a contradiction. (a) If D = s², then 4a f(x) = u·w with u = 2ax+b−s and w = u+2s. If f(x) = p0 is prime,
then p0 divides u or w. If p0 | u, write u = p0·u'. Then u'·w = 4a, so w is a nonzero divisor of 4a and |w| ≤ 4a. So w ∈ [−4a,4a]. Since w = 2ax + const, at
most 5 values of x qualify; the same holds for u. So N ≤ 10. (c) is immediate from (b). D ≡ b² mod 4, so χ_D is a
Kronecker character, nonprincipal when D is not a square.

## [not validated] r1s1/C4 OTHER OTHER
**Statement.** Exact DP over all convex prime chains with terms ≤ 10^6 finds that the length-minimal chains (L ≤ 676) have
maximal constant-second-difference stretches of length ≤ 9 (484 stretches for L=676). So "long pieces die by
Linnik–Vinogradov" (C2) applies to no extremal chain in range. Any successful A1-type proof must get its contradiction
entirely from the glitch structure, i.e. from a family-level input on the walk of discriminants Δ_i. One-piece Burgess bounds
contribute nothing at observable scales.
**Proof or evidence.**

(none)

## [not validated] r1s2/C1 REFUTED NEGATIVE
**Statement.** Fix any f with a ≥ 1, any A > 0 and any ε < 1/2. For all sufficiently large P there are integers r_k with |r_k| ≤ kK (where K = P²) such that Σ_{k≤K}|S(f(k)+r_k)|² > A(K+P)^{1+ε}P/log P. So the FIRST STEP of the assignment is false. For ε ≥ 1/2 it holds trivially, since K π_P² ≤ K^{3/2}P/log P·O(1).
**Beyond.** This disproves the proposed lemma outright. It is not one of the KNOWN items.
**Proof or evidence.**

1. Construction. For k ≥ k₀(f) we have f(k) > 0. Let j_k = ⌊√f(k)⌋ and m_k = j_k². Then |r_k| = f(k) − j_k² ≤ 2j_k ≤ 2√f(k) ≤ 2√(a+|b|+|c|)·k ≤ kK once K ≥ 2√(a+|b|+|c|). For the finitely many k < k₀, put r_k = 0; those terms are ≥ 0.
2. Few primes of Π_P divide j_k. We have j_k ≤ √f(K) ≤ √(a+|b|+|c|)·P² < P³ for large P. A product of three primes ≥ P is at least P³, so at most 2 primes of Π_P divide j_k.
3. Lower bound for each term. For every other p ∈ Π_P, (m_k/p) = (j_k/p)² = 1. Hence S(m_k) ≥ π_P − 2.
4. Comparison. LHS ≥ (K − k₀)(π_P − 2)². The RHS is ≤ A(2K)^{1+ε}P/log P. By PNT, π_P ~ P/log P, so LHS/RHS ≳ P^{1−2ε}/(2^{1+ε}A log P) → ∞.
5. Numerical check (s1.py, f = k² + k + 41, K = P², m_k = nearest square below): Σ|S|²/(Kπ_P) = 9.7, 20.7, 31.8, 60.8 for P = 50, 100, 200, 400. That is ≈ π_P, as predicted. The unperturbed f gives ≈ 1.00.

## [not validated] r1s3/C2 PROVED QUANT
**Statement.** Every convex prime sequence has d_n >= (2/κ − o(1)) n and liminf q_n/n^2 >= 1/κ = 0.5434481483390644517...,
where κ = Σ_{p odd prime} (p−2)(1−1/p)/∏_{3<=ℓ<p} ℓ = 1.8401019546322694241851258342...
**Beyond.** Richter's 0.352... = 1/(1+κ) (it matches to 10 digits: 0.3521000358). This is consistent with a run cap of P(v)−1;
we use P(v)−2. C2 is superseded numerically by C1, but its proof is computer-free.
**Proof or evidence.**

This is step (3) of C1 applied to every even v, with no game. For n >= n0 (q_{n0} > 3), the run of gap value v has
m_v <= P(v) − 2, except for O(log V) exceptional runs with one extra each.
Write v = 2w. Then #{w <= W : P(2w) = p} = W(1−1/p)/∏_{3<=ℓ<p} ℓ + O(1), and only O(log W) primes p occur, each of size O(log W).
So N(V) <= κ V/2 + O(log^2 V). Conclude as in step (4). ∎

## [not validated] r1s3/C3 CONJECTURED STRUCTURE
**Statement.** The game bound ρ_z (primes <= z) takes these values:
- z=3: 1.840102 (= κ; 1/ρ = 0.543448)
- z=5: 20/15 + τ_5 = 1.706769 (1/ρ = 0.585902)
- z=7: 156/105 + τ_7 = 1.573435 (1/ρ = 0.635552)
- z=11: 1596/1155 + τ_11 = 1.391617 (1/ρ = 0.718588)
- z=13: 18748/15015 + τ_13 = 1.249626 (1/ρ = 0.800240)
Every ρ_z is >= 1 (the profinite quadratic achieves density 1), so the method is capped at 1.
**Proof or evidence.**

(none)

## [not validated] r2s1/C4 CONJECTURED STRUCTURE
**Statement.** (conjecture) There is no Ẑ-good convex gap strategy, periodic or not, with lim inf of the running average
multiplicity > 1. Equivalently, the profinite cap for congruence-only arguments is exactly 1. Quantitatively,
I expect ρ_z − 1 ≍ 1/log z.
**Beyond.** It sharpens the profinite barrier. The barrier shows the cap is ≤ 1; this asserts it is attained in the limit.
**Proof or evidence.**

Evidence and mechanism:
- **(a) Exhaustive search.** Every periodic pattern with P ≤ 9, m ∈ {0,1,2,3} and average > 1 fails at some prime
  ≤ 11 (pat.py).
- **(b) Few-change patterns.** All patterns with P ∈ {105, 210, 315} that are all-ones except 1–2 changed entries
  fail by 11 (pat3.py). Random dense-glitch patterns with P = 30 fail by 7.
- **(c) Mechanism.** By C1 and C2, a strategy denser than the quadratic must glitch within every p − 2 steps, and the
  set of discriminant shifts {δ_s} must fit inside a translate of the nonresidues at every generic p. That requires
  t := #{δ_s} ≤ (p−1)/2 and has probability about p·2^{−t} for p < 4^t.
- **(d) Heuristic rate.** A random line misses Σ_p with probability about e^{−T} (T = spacing between glitches).
  This predicts survival only up to primes p ≈ e^{T/2}, which gives the 1/log z rate.

## Frontier map

=== DIRECTION
TRUE, confidence 0.93.

Evidence:
- **Cramér first moment.** Fix L. Convex chains of length L ending below X number about X^{L+1}/(L!)², and each is all-prime with probability about (2/log X)^L. With X = λL² log L the expected count is about (e²λ/2)^L, which tends to 0 when λ < 2/e². So heuristically q_n ≫ n² log n. Greedy construction suggests q_n ≍ n² log n is attainable.
- **Structured candidates die.** The most dangerous structured candidates are Euler-type quadratic chains x² + x + A. These are prime for long runs only when the class number is 1 (Rabinowitsch), and Heegner–Baker–Stark gives A ≤ 41.
- **Richter's bound and its likely sharpening.** Richter's 0.352… is unconditional. A recount of what is probably his run-length argument gives 0.5434… (T1).
- **Bounded gaps impossible.** Bounded gaps would force an eventually constant gap, hence an infinite arithmetic progression of primes, which is impossible.

A counterexample would need about n primes in [1, Cn²] arranged convexly. That means beating the random model by a factor e^{Θ(n log log n)}.

=== KNOWN
- liminf q_n/n² > 0.352… | [Ri76], via erdosproblems #455 | Probably the run-length argument with cap P(v)−1. Here P(v) is the least odd prime not dividing the gap v. Numerically 0.352… = 1/(1+κ), with κ ≈ 1.84010 defined in T1.
- AP lemma: if q, q+d, …, q+(k−1)d are all primes greater than k, then every prime p ≤ k divides d | standard | pigeonhole on residues mod p.
- Gaps d_n → ∞, and every run of equal gaps v has length at most P(v)−2 once the terms exceed P(v) | standard (AP lemma) | P(v) ≤ (1+o(1)) log v.
- [Lean] Convex tail inequality (n−k)(q_{k+1}−q_k) ≤ q_n − q_k | blackboard | telescoping.
- [Lean] For every convex prime chain, i ≤ 6(p_{i+1} − p_i) | blackboard | run counting.
- [Lean] The target follows from the finite statement erdos_455_hyp_no_short_convex_chain | blackboard | window [n/2, n].
- Rabinowitsch: x² + x + A is prime for all 0 ≤ x ≤ A−2 iff h(1−4A) = 1 | Rabinowitsch 1913 | reduction theory of binary quadratic forms.
- Class number one: the largest such A is 41, so the longest Euler chain has 40 terms | Heegner, Baker, Stark | modular functions / linear forms in logarithms.
- Least split prime: the least p with χ_D(p) = 1 is ≪_ε |D|^{1/4+ε} | Linnik–Vinogradov 1966 | Burgess bound plus a Siegel-type input (likely ineffective).
- Under GRH, the least split prime is ≪ (log|D|)² | Ankeny/Bach type | explicit formula.
- Some discriminants have no split prime up to c·log|D|·log log|D| | Graham–Ringrose type / CRT constructions | character constructions.
- For a fixed quadratic f, #{i ≤ x : f(i) prime} ≪ x·S(f)/log x | Selberg/Brun upper-bound sieve | uniformity in the discriminant enters only through S(f).
- Quadratic large sieve: Σ_{m≤M} |Σ_{n≤N} a_n (n/m)|² ≪ (MN)^ε (M+N) Σ|a_n|² | Heath-Brown 1995 | Poisson summation plus recursion.
- For each fixed k, the asymptotic count of k-term prime blocks with constant second difference c ≥ 0 (differences of size about x) | Green–Tao 2010 plus Green–Tao–Ziegler (GI(s) for all s) | higher-order Fourier analysis. Finite convex blocks are therefore abundant.
- There is a convex prime sequence with q_n ≪ n^{2/(1−0.525)+ε} ≈ n^{4.21} | standard, from Baker–Harman–Pintz | greedy construction. Under Cramér's gap conjecture one gets q_n ≪ n² log² n.
- No conditional proof of the full statement is known, including under GRH or Hardy–Littlewood.

=== BARRIERS
- **Profinite (local) barrier.** Take q_i = i² + bi + c with discriminant a non-residue mod every odd p ≤ z, fixed by CRT. This is convex, has q_n ~ n², and avoids every prime ≤ z. In Ẑ, the same construction avoids 0 at every prime.
  - Defeats: every argument using only congruence information. This includes Richter-type run counting, finite-automaton or mean-payoff games, Furstenberg-type limits on Ẑ, and sieving only to level O(log n). Such arguments can never give more than liminf ≥ 1.
  - Does not rule out: arguments coupling size (the discriminant is at most n²) with residues, as least-split-prime bounds do.
- **Sparsity barrier.** The chain has about √X elements in [1, X].
  - Defeats: the large sieve, Selberg/Brun applied to the chain, and Brun–Titchmarsh. These detect only sets of size ≳ X/log X, and the large sieve RHS (X + Q²)|A| swamps the main term n²/log Q.
  - Defeats: the Selberg sieve on the chain itself, which needs a level of distribution that an adversarial chain does not have.
  - Does not rule out: arguments that transfer to dense auxiliary objects such as the gap multiset or discriminant families.
- **Entropy (union-bound) barrier.** There are e^{Θ(L)} candidate chains.
  - Defeats: any per-pattern bound weaker than e^{−cL}. That would need Hardy–Littlewood upper bounds uniform in k ≈ √X, which are false beyond the log scale. Window arguments with windows of length polylog L fail; I checked that n³(8Ch/log X)^h is not small.
  - Does not rule out: deterministic arguments applied to each chain individually.
- **Euler-polynomial / Siegel barrier.**
  - The finite-chain statement (blackboard conjecture, C ≥ 1) implies Heilbronn–Linfoot finiteness of class-number-1 fields of the form 1−4A. Infinitely many such A would give chains of length A−1, below about A², with gaps at most 2A.
  - In a Siegel-zero world, Euler polynomials are prime with density close to 1.
  - Defeats: purely sieve-theoretic or elementary proofs of the finite statement. Some Deuring–Heilbronn or Siegel-strength input is required.
  - Does not rule out: proofs that use Linnik–Vinogradov, or proofs that exploit the infinite tail.
- **Glitch barrier.** A non-quadratic step changes the invariant Δ_i (see T10). Piecewise-quadratic chains whose pieces are shorter than |Δ|^{1/4} evade Linnik–Vinogradov, and pieces shorter than log²|Δ| evade even GRH.
  - Defeats: one-discriminant-at-a-time character-sum methods.
  - Does not rule out: family averages over the walk of discriminants.
- **Non-barrier: parity.** CORE needs only upper-bound or nonexistence information about rough numbers (T9), so the parity problem does not block it.

=== CORE
Prove the following. For every C there is L₀ such that no convex chain p_0 < … < p_L of primes with L ≥ L₀, gaps at most 2C·2L, and p_L ≤ C(2L)² exists. A parity-free sufficient version is stated in T9.

Why it is hard:
- The chain is a √X-sparse, adversarially chosen set.
- Congruence information alone is provably capped at constant 1 by the profinite barrier.
- The only known tool coupling size with residues, least-split-prime bounds, handles one quadratic piece at a time. It needs pieces of length at least X^{1/3+ε}.
- A counterexample can glitch between discriminants as often as every few steps.
- Even the purely quadratic special case already contains Heilbronn's theorem.

=== TARGET T1
TYPE: QUANT
STATEMENT: Let P(v) be the least odd prime not dividing v, and define κ = Σ_{p odd prime} (p−2)(1−1/p)∏_{3≤ℓ<p} ℓ^{−1} ≈ 1.84010. Then every convex prime sequence satisfies liminf q_n/n² ≥ 1/κ ≈ 0.54345. In finite form, every convex prime chain with p_0 > log L has gaps d_i ≥ (2/κ − o(1))·i.
BEYOND: Richter's 0.352… equals 1/(1+κ) to five digits. This strongly suggests his run cap was P(v)−1. The correct cap is P(v)−2: m+1 ≥ P(v) terms of an AP with step v cover every residue mod P(v). This also beats the Lean bound i ≤ 6d_i.
VALUE: This is an immediate, publishable improvement. It is also a Lean-certifiable lemma that feeds every window argument.
TEST: Compute κ to 10 digits. Search for convex prime sequences by beam search up to 10⁹ and compare their empirical q_n/n² with 0.543.

=== TARGET T2
TYPE: QUANT
STATEMENT: Define the mean-payoff game G₇. Its state is (q mod 105, d mod 210·11·13). It tracks the residue walk exactly mod 3, 5 and 7, and imposes run caps P(v)−2 for primes 11 ≤ p ≤ 13. The goal is to maximise steps per unit increase of the gap. Claim: the game value c₇ = (1/2)·(minimum mean increment) satisfies c₇ > 1/κ, and every convex prime sequence has liminf q_n/n² ≥ c₇.
BEYOND: T1 ignores how consecutive runs interact. A maximal run of gap v with P(v) = p forces the start residue q ≡ v (mod p), which forbids the all-maximal schedule. I checked that the schedule using gap 6k twice and 6k±2 once covers every class mod 5.
VALUE: This gives the best constant reachable by local methods, and shows how far below 1 (the profinite ceiling) they stop.
TEST: Run Karp's or Howard's algorithm on the finite graph, then certify c₇ with an LP-dual potential function. Lean can verify the potential.

=== TARGET T3
TYPE: SPECIAL
STATEMENT: Let q be a convex prime sequence with #{i ≤ n : Δ³q_i ≠ 0} ≤ n^{1/3−ε} for all large n. Then q_n/n² → ∞.
BEYOND: KNOWN only kills exact Euler-type polynomials, that is, a single quadratic piece. This statement handles piecewise-quadratic sequences with polynomially many pieces of any leading coefficient.
VALUE: It disposes of the structured regime in a structure-versus-randomness split of CORE.
TEST: Generate piecewise-quadratic prime chains with few pieces and check that their maximal piece lengths stay below X^{1/3}.

=== TARGET T4
TYPE: CONDITIONAL
STATEMENT: Assume H_θ: every fundamental discriminant D has a split prime p ≤ |D|^θ not dividing a given integer of size |D|^{O(1)}. Then CORE holds for every convex prime sequence whose third-difference support up to n is at most n^{1−4θ/(1+2θ)−ε}. Under GRH the conclusion holds with support up to n/(log n)³.
BEYOND: No conditional result of any kind is known. H_θ for θ < 1/4 is strictly weaker than GRH.
VALUE: This measures exactly how much least-split-prime strength buys. It shows that GRH reduces CORE to chains that glitch at density ≥ (log n)^{−3}.
TEST: Compute least split primes of the discriminants Δ_i (defined in T10) along beam-searched chains.

=== TARGET T5
TYPE: STRUCTURE
STATEMENT: In any convex chain of primes up to X, every stretch of consecutive indices with constant second difference 2a has length ℓ ≪_ε X^{1/3+ε}. If a = 1, the bound improves to ℓ ≪_ε X^{1/4+ε}.
Proof route:
- On the stretch, q = f(i) with f of discriminant Δ, where |Δ| ≤ 4X²/ℓ² and a ≤ X/ℓ².
- Linnik–Vinogradov supplies a split prime p ≪ (X/ℓ)^{1/2+ε} with p ∤ 2a.
- If p < ℓ, some index in the stretch has p | q_j with q_j > p, a contradiction.
- Remaining work: obtaining several split primes, and the square-discriminant case.
BEYOND: KNOWN controls only x² + x + A on the full range 0..A−2.
VALUE: This is the engine behind T3 and T4, and it quantifies the glitch barrier.
TEST: Find the longest constant-second-difference prime stretches below 10¹² and compare them with X^{1/4}.

=== TARGET T6
TYPE: ANALOGUE
STATEMENT: Let 𝒫 contain each odd m independently with probability 2/log m (the Cramér model). Almost surely, every infinite convex sequence in 𝒫 satisfies liminf q_n/(n² log n) = λ*, a deterministic constant. Determine λ*; the first moment suggests λ* ≥ 2/e² and greedy gives λ* ≤ 1.
BEYOND: Only heuristics exist. Neither the order n² log n nor the constant has been proved in any model.
VALUE: This calibrates the truth: it predicts the growth rate that a proof of CORE should eventually match.
TEST: Simulate random sets up to 10⁸. Use dynamic programming over (q, d) to find the minimal convex chains.

=== TARGET T7
TYPE: ANALOGUE
STATEMENT: In Granville's model (sieve by primes ≤ (log x)^{1−ε}, then select at random with the compensating density), decide whether there are a.s. convex sequences with q_n = o(n² log n). The concrete guess is order n² log n/log log n, achieved by glitchy quadratic chains with inert discriminants.
BEYOND: This tests whether local structure lowers the heuristic growth below Cramér's. Nothing is known.
VALUE: If yes, the truth may be q_n ≍ n² log n/log log n. That would show the structured, discriminant-walk chains are where a proof must be sharp.
TEST: Run a Monte-Carlo beam search in the Granville model, comparing the best chains among generic and quadratic-glitch families.

=== TARGET T8
TYPE: NEGATIVE
STATEMENT: There is an infinite convex sequence of integers with q_n = (1+o(1))n² such that no prime factor of q_n is at most c·log q_n. In particular, each prime divides only finitely many q_n.
Construction:
- Use quadratic pieces whose discriminants are inert at all primes ≤ 2c log n. Such discriminants exist, of size n^{2c+o(1)}, by CRT.
- Join consecutive pieces by a bounded number of glitches, using the T10 recursion. Choose the glitch times so that every intermediate discriminant stays inert.
BEYOND: The profinite barrier is currently known only for fixed z.
VALUE: This proves that Richter-type arguments, T1, T2, and any method sieving below c log q cannot prove CORE or exceed ratio 1. It forces the team toward size–residue coupling.
TEST: Build the sequence explicitly up to 10⁷ and verify roughness.

=== TARGET T9
TYPE: REDUCTION
STATEMENT: Suppose that for every C and all large L, no convex chain of L integers in [L, CL²] has all its terms free of prime factors ≤ L. Then CORE holds.
Proof:
- If liminf q_n/n² < C, then infinitely many n have q_n ≤ Cn².
- For those n, the block q_{n/2}, …, q_n has length L = n/2 and lies in [0.54·L², 4CL²] by T1.
- Its terms are primes larger than L, hence L-rough.
BEYOND: The certified reduction still involves primes. This hypothesis is parity-free, and every sieve-style proof would automatically prove it.
VALUE: It frees the team to use any upper-bound tool, and it removes P2-type parity worries.
TEST: Search for long convex L-rough chains with ratio C; these exist more often than prime chains, so this stress-tests the reduction.

=== TARGET T10
TYPE: STRUCTURE
STATEMENT: Let e_i = d_{i+1} − d_i and Δ_i := (d_i − 1)² − 4q_i. Then:
- Δ_{i+1} − Δ_i = (e_i − 2)(2d_i + e_i), and 4q_i = (d_i − 1)² − Δ_i.
- Each q_i is the norm of ((d_i − 1) + √Δ_i)/2.
- A chain is prime iff Δ_i ≢ (d_i − 1)² mod p for all p ≤ √q_i (and size conditions hold).
- On every e = 2 stretch that sweeps a full residue system mod p, χ_{Δ}(p) = −1.
- If q_i ~ λi², then Δ_i ~ 4λ(λ−1)i². So a counterexample with λ < 1 lives in imaginary quadratic orders.
BEYOND: This is a new exact reformulation of the problem as a walk on discriminants.
VALUE: It is the canonical object for T3, T4, T5 and T8 and for angles A1–A3, and it turns glitches into explicit discriminant jumps.
TEST: Symbolic verification, plus Lean.

=== ANGLE A1
TECHNIQUE: Burgess / Linnik–Vinogradov character sums on the discriminant walk.
IDEA:
- Decompose a counterexample window into e = 2 stretches, i.e. constant-Δ pieces (T10).
- Long pieces (≥ X^{1/4+ε}) die by T5.
- Short pieces carry glitches. Each glitch costs |e − 2| in increment budget, and the total budget is at most 4Cn.
- Count how many glitches the budget allows. A ratio C forces either long pieces or many glitches with e ≠ 2.
- Bound the number of discriminants with no split prime below a piece's length by Burgess applied to each piece.
BARRIERS: Beats the profinite barrier through the size bound |Δ| ≤ X. The glitch barrier remains, and A2 is designed for it.
FIRST STEP: Prove T5 in full, with p ∤ 2a and the square-discriminant case.

=== ANGLE A2
TECHNIQUE: Quadratic large sieve along sparse quadratic-type families (Heath-Brown; Baier–Zhao-type large sieves for sparse moduli).
IDEA:
- The piece discriminants Δ_k drift like 4λ(λ−1)k² with structured jumps. Each piece of length ℓ_k needs χ_{Δ_k}(p) = −1 for every p in [ℓ_k/2, ℓ_k].
- Average Σ_k |Σ_{p∼ℓ} χ_{Δ_k}(p)|² over this near-quadratic family.
- A large sieve exploiting the family's quadratic structure, gaining over the generic (M+N), would kill pieces of medium length [polylog, X^{1/3}].
BARRIERS: The sparsity barrier defeats generic Heath-Brown (one loses a factor n). The angle must exploit the near-polynomial structure of {Δ_k}, as sparse large sieves for squares do.
FIRST STEP: Prove Σ_{k≤K} |Σ_{p∼P} χ_{f(k)+r_k}(p)|² ≪ (K + P)^{1+ε}·P/log P for f quadratic and |r_k| ≤ k·K, with K ≈ P².

=== ANGLE A3
TECHNIQUE: Mean-payoff games with LP-duality certificates, extended by a size coupling.
IDEA:
- Model the local problem as a game on (q mod M, d mod M′, current Δ-class).
- Let the prime set grow with the scale, and add the archimedean constraint |Δ| ≤ 4CX by tracking how many "inert classes" remain available.
- The dual potentials give rigorous constants (T2) and expose which strategies can keep ratio < 1.
BARRIERS: Cannot pass the profinite barrier by itself. Its purpose is to locate exactly where size–residue coupling must enter, and to supply the explicit constructions for T8.
FIRST STEP: Compute c₃,₅ and c₃,₅,₇ exactly with Lean-checkable potentials.

=== ANGLE A4
TECHNIQUE: Inverse sieve theorem for convex sequences, a structure-versus-randomness dichotomy in pattern space.
IDEA:
- Show that a convex h-pattern missing a residue class mod every prime in [h^{1/2}, h] must be near-quadratic, i.e. have few e ≠ 2 steps.
- Non-quadratic patterns cover all residues mod some such p, so they die directly.
- Near-quadratic patterns go to A1 and A2.
BARRIERS: Avoids the entropy barrier, since the argument is deterministic and per chain. Avoids the sparsity barrier, since it uses moduli up to h, which are visible.
FIRST STEP: For a prime p and a walk q_{i+1} = q_i + d_i with nondecreasing d_i, show: if no q_i ≡ 0 mod p for p consecutive steps with d_i covering all classes mod p, then Δ_i mod p takes at most O(1) values outside a set of size O(#glitches).

=== ANGLE A5
TECHNIQUE: Deuring–Heilbronn dichotomy applied to the discriminant family.
IDEA:
- Split into cases according to whether some Δ in [−X, X] has an exceptional character.
- If none, log-free zero-density estimates give, for all but X^{o(1)} discriminants, a split prime ≤ (log X)^A. Then pieces must glitch at density (log)^{−A}, which feeds A4.
- If one exists, Deuring–Heilbronn repulsion makes every other character well-behaved. The single exceptional discriminant can occupy at most one piece-class, which T5 handles.
BARRIERS: This directly confronts the Siegel barrier. Ineffective dependence is acceptable because the conclusion is qualitative.
FIRST STEP: Prove #{D ∈ [−X, X] : χ_D(p) ≠ 1 for all p ≤ (log X)^A} ≪ X^{1/2−δ} for some A and δ > 0, unconditionally apart from at most one exceptional modulus.

=== ANGLE A6
TECHNIQUE: Exploit the infinite tail by renormalising across scales (not a single-window argument).
IDEA:
- liminf ≤ C gives infinitely many windows, and the sequence is the same in all of them.
- The walk Δ_i must be inert, along its long pieces, at the primes p ≤ ℓ at every scale.
- Δ changes only by (e−2)(2d+e). So the residues of Δ mod a fixed small prime set evolve by a deterministic rule tied to d_i, and must remain compatible forever.
- Combine with the T8 analysis: maintaining inertness at a slowly growing set of primes requires glitches whose total cost diverges relative to n.
BARRIERS: Single-window arguments run into the Heilbronn-strength Siegel barrier. A6 instead exploits the infinite tail, where T8 suggests the cost of staying inert accumulates.
FIRST STEP: Show that any infinite convex integer sequence with q_n = O(n²) and no prime factor ≤ (log q_n)^{1+ε} has Σ_{i≤n} |e_i − 2| ≫ n/(log n)^{O(1)}. Under GRH this follows from T4; the goal is an unconditional proof via A5.

## Meta-review

=== STATE
**Validated new**
- **[r1s1/C1] liminf q_n/n² ≥ 0.80024 for every convex prime sequence.** The method is joint-residue run counting mod M = 15015 (S = {3,5,7,11,13}), with κ'_S = (18748 + 15.13085)/15015 and an explicit E0 term for phases in which every p ∈ S divides the gap. The same method gives 0.63555 for S = {3,5,7} and 0.71859 for S = {3,…,11}. This more than doubles Richter's 0.352. It is congruence-only, so the profinite barrier caps it at 1.

**Validated routine (now usable as tools)**
- Under GRH, Φ_f(K,P) ≪ K·P·log⁴(KP) for non-square shifts (r1s2/C2-cond).
- Second-moment bound for Legendre sums along a fixed quadratic family (r1s2/C3): exceptional k number ≪ (1+β)K log P/P + P log P, and the degenerate shift is isolated.
- Δ-invariant (r1s2/C4). Δ_i = (d_i+d_{i+1})² − 16q_i is constant on e=2 stretches, and one +2 bump changes it by 16·(the unbumped gap).
- Few-glitch theorem (r1s4/C1). If #{i ≤ n : Δ³q_i ≠ 0} ≤ n^θ with θ < 1/2, then q_n/n² → ∞. Structurally, whenever q_n ≤ Cn², the window [n/2, 3n/4] contains ≥ n^{1/2−o(1)} glitches.
- Under GRH, the same conclusion holds with ≤ n/(log n)⁵ glitches (r1s4/C2).

**Best unvalidated ideas**
- **r1s3/C3: game values ρ_z.** The values are 1.840, 1.707, 1.573, 1.392, 1.250 for z = 3, 5, 7, 11, 13, all ≥ 1. They fall by about 0.13–0.18 per prime, so they must flatten soon. Is lim ρ_z = 1, i.e. is the profinite cap attained?
- **r1s1/C2: piece lemma.** If D is a perfect square then N ≤ 10. Otherwise (D/p) = −1 for every p ≤ N with p ∤ 2a. Under LV_a this gives N ≪ |D|^{1/4+ε}. Consequently every e ≥ 2 piece in CORE has length ≪ L^{1/2+ε}. The a ≥ 2 case is not yet refereed.
- **r1s1/C4: DP data.** Length-minimal convex chains below 10⁶ (L ≤ 676) have constant-e stretches of length ≤ 9. So single-piece methods are irrelevant at observable scales.
- **r1s2/C1: refutation.** The sup-over-shifts FIRST STEP (|r_k| ≤ kK, ε < 1/2) is false, because arbitrary shifts let the adversary park on discriminants that are non-residues at every small prime.
- **r1s2/C2(iii), salvageable.** For ε < 1/4 the hypothesis Φ_f(P²,P) ≤ A P^{3+4ε}/log P does force a split prime ≤ C_a m^{1/4} for all large non-square m. That is Linnik–Vinogradov with no ε.
- **r1s3/C2: 1/κ = 0.54345.** Superseded by r1s1/C1 and no longer worth validating separately.
- **Observation, unchecked.** A monic integer quadratic is determined up to integer translation by its discriminant. So all e=2 pieces with the same Δ are segments of one polynomial g_D(y) = y² − D/4. Also Δ ≈ 16q(d̄²/(4q) − 1), so the local discriminant is positive (real quadratic) exactly when the local constant d̄²/(4q) exceeds 1.

=== LESSONS
**What failed and why**
- **r1s3/C1 broke on a missing case.** It omitted the phases where 15015 | v. There the game forces m = 0, but real runs can have length up to P(v) − 2. r1s1/C1 survived because its E0_S term handles exactly this. Lesson: any game-to-sequence reduction must treat the "all small primes divide the gap" phase explicitly, with the tail τ_z.
- **r1s2/C2(iii) broke on an exponent swap.** It used P^{2+2ε} where the hypothesis gives P^{2+4ε}. The surviving range is ε < 1/4.
- **The sup-family FIRST STEP fails.** r1s2/C1 refutes it, and (iii) shows that even a correct version is at least Linnik–Vinogradov-hard. Family averages over arbitrary perturbations are useless. Any family input must use the rigidity of the actual discriminant walk: increments are tied to the gaps (16d per bump), and the steps are sign-constrained by e_i ≥ 0.

**Which barriers bit**
- **Glitch barrier.** It bit everything one-discriminant: the GRH results (routine), LV per piece, and the few-glitch theorem. C4's data says extremal chains glitch every ≤ 9 steps, so these tools never engage in range.
- **Sparsity barrier.** It killed the second-moment approach (r1s2/C3) once the shifts are of size ≍ k.
- **Profinite barrier.** It bounds the r1s1 line at 1 but has not stopped it yet.

**Most alive angles**
- **Near term: drive the congruence constant to its proven cap.** Showing liminf ≥ 1 exactly would make the local barrier sharp. That is a clean theorem, and the ρ_z data suggests it is reachable.
- **For CORE: the discriminant walk.** It is the only object seen so far that couples size (|D| ≪ L², jumps ≍ L) with residues across glitches. The translate lemma turns "same Δ" into "same polynomial", and the step formula appears to make the walk monotone when there are no e=0 dips. Both structures are new and untested.

=== NEXT
1. **Push r1s1/C1 to the profinite cap (liminf q_n/n² ≥ 1).**
   - Technique: exact mean-payoff analysis of the full second-order congruence game. The state is (q, d) mod M_z, the adversary picks even e ≥ 0 at cost e, it must keep q ≢ 0 mod every p ≤ z, and the r1s1 E0/τ_z tail covers phases where M_z divides the gap.
   - Goal: prove that the value tends to 2 (equivalently ρ_z → 1), or find the first z at which the full game strictly beats run counting.
   - First step: quotient by the scaling symmetry (q, d) ↦ (λq, λd) and use CRT. Compute V_z for z = 3, 5, 7 exactly by policy iteration and check against ρ_z. Then fit ρ_z − 1 = Σ_{p>z} c_p to the five known values to guess an explicit c_p to prove.
2. **Repair r1s2/C2(iii) and turn it into a barrier lemma.**
   - Technique: redo (i) ⇒ (iii) with the stated exponent. A non-square m with no split prime ≤ P has |S(m)| ≈ π_P. So Φ ≥ (K/8a)π_P² ≫ P⁴/log²P, which contradicts A P^{3+4ε}/log P exactly when ε < 1/4. Prove (iii) in that range and validate the r1s2/C1 refutation alongside it.
   - Deliverable: a "shift-rigidity" barrier for the map. Any second-moment bound uniform over arbitrary shifts |r_k| ≤ kK is LV-hard, and is false at ε < 1/2.
   - Then restate the FIRST STEP with shifts restricted to discriminant walks generated by convex gap sequences.
   - First step: write the corrected (iii) with explicit ε-dependence and constants, then check whether the r1s2/C1 counterexample shifts are realisable by a convex walk.
3. **Combine r1s4/C1, r1s2/C4 and r1s1/C2 into a "distinct discriminants" theorem.**
   - Technique: use the translate lemma (equal Δ ⇒ pieces lie on one g_D(y) = y² − D/4, and the a-scaled analogue for e = 2a). Combine it with the Selberg upper bound #{y ≤ Y : g_D(y) prime} ≪ Y·S(g_D)/log Y, with S(g_D) ≪ log log L since |D| ≪ L². This caps the total mass any one discriminant can carry.
   - Goal: prove that a CORE counterexample uses ≫ log L/log log L distinct discriminants unconditionally. Aim for ≫ L^{1/2−ε} distinct discriminants when returns of the walk are limited.
   - First step: referee r1s1/C2 (a) and (b) for a ≥ 2. Then verify the general jump identity Δ_{i+1} − Δ_i = 4d_{i+1}(e_i + e_{i+1} − 4) + (e_{i+1}² − e_i²) symbolically.
4. **Attack CORE in the no-dip subclass (all e_i ≥ 2) via the monotone discriminant walk.**
   - Technique: by the identity in item 3, with no dips the walk Δ_i is nondecreasing and rises by ≳ 8d ≍ L at each glitch. So the pieces' discriminants are distinct, L-separated, and confined to |D| ≪ L². Couple this with the local condition (D_j/p) = −1 for p ≤ m_j (from r1s1/C2(b)). Count admissible separated walks using Heath-Brown's quadratic large sieve restricted to the short D-intervals the walk is forced through, together with Granville–Soundararajan large-deviation counts for small L(1, χ_D).
   - First step: rerun the r1s1/C4 DP independently up to 10⁷ and dump the D-walks of length-minimal chains. Record how often e = 0 occurs (if rarely, this subclass is the main case), whether D_j ever repeats, and how n(D_j) compares with m_j. Use the data to fix the exact counting statement to prove.
