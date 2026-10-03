# Research engine: problem 727285, run 20261002-235647-826042-hardstep-erdos727285

Spend $7.9966; 11 claim(s); 1 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] r1s3/C1 PROVED REDUCTION
**Statement.** Let n ≥ 2 not be a prime power, n = Π p^{a_p}, C_{p,d} := C(n,p^d). For r ∈ Z/n and p | n let (e_{p,d}(r))_{1≤d≤a_p} ∈ {0..p−1}^{a_p} be the unique digits with r ≡ Σ_d e_{p,d} C_{p,d} (mod p^{a_p}); φ(r) := Σ_p Σ_d e_{p,d}(r) C_{p,d}.
(a) If φ(r+C(n,i)) ≤ φ(r)+C(n,i) for all r and all 1 ≤ i < n, then ¬Rep(n, X−n).
(b) For i ∈ {p^j, n−p^j : 1 ≤ j ≤ a_p} the inequality holds unconditionally.
(c) For every other i, the inequality follows from (E): C(n,i) ≥ B(i) := Σ_p (p−1) Σ_{d=1}^{J_p(i)} C_{p,d}, J_p(i) = max(0, a_p − v_p(C(n,i))).
**Beyond.** KNOWN gives only the upper bound g(S) ≤ X−n (Brauer on the tower T). This gives the matching lower bound from (E) alone, and it handles all the non-tower generators C(n,i). It also proves the carry lemma outright.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "A natural but apparently unpublished dual-certificate (Apéry potential) reduction of the lower bound to the binomial inequality (E), assembled from standard tools (Brauer–Shockley digits, Gomory potentials, Kummer). It leaves the real analytic core, (E), unproved, so it is a minor though useful step.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "A natural but apparently unpublished dual-certificate (Apéry potential) reduction of the lower bound to the binomial inequality (E), assembled from standard tools (Brauer–Shockley digits, Gomory potentials, Kummer). It leaves the real analytic core, (E), unproved, so it is a minor though useful step."}, {"verdict": "new", "cite": null, "significance": 2, "why": "P`
**Proof or evidence.**

L0 (valuations). For q | n and i with q ∤ i: v_q(C(n,i)) ≥ v_q(n) − v_q(i) = a_q, from i·C(n,i) = n·C(n−1,i−1). For 1 ≤ j ≤ a = a_p: v_p(C_{p,j}) = a−j by Kummer. Base-p, n−p^j has digits 0 at positions < j, p−1 at positions j..a−1, and n_a−1 at position a, where n_a ≥ 1 is the a-th digit of n. Adding p^j gives carries exactly at positions j..a−1, so a−j carries.
L1 (digits well defined). The map {0..p−1}^a → Z/p^a, e ↦ Σ e_d C_{p,d} is injective. Take e ≠ e' and D = max{d : e_d ≠ e'_d}. Then Σ_{d≤D}(e_d−e'_d)C_{p,d} has v_p exactly a−D < a: the term at D has valuation a−D because 0<|e_D−e'_D|<p, and the terms d<D have valuation ≥ a−D+1. So the sum is nonzero mod p^a. Both sides have size p^a, so the map is a bijection. φ is well defined on Z/n because p^{a_p} | n.
L2 (frozen digits). If r ≡ r' (mod p^{a−J}) then e_{p,d}(r) = e_{p,d}(r') for all d > J. Same argument: if D > J were the top differing index, the difference would have valuation exactly a−D < a−J.
(a) φ(0) = 0. Mod p^{a_p} the q-terms of X (q ≠ p) vanish by L0, so X ≡ Σ_d (p−1)C_{p,d}. Hence every digit of X mod n is p−1, and φ(X mod n) = X. Suppose X−n = Σ c_i C(n,i). Add the generators one at a time starting from 0 and apply the hypothesis at each step: φ((X−n) mod n) ≤ Σ c_i C(n,i) = X−n. But (X−n) ≡ X (mod n), so the left side is X > X−n. Contradiction.
Per-prime increment. Let g = C(n,i). Then v_p(g) ≥ a_p − J_p(i), so g ≡ 0 mod p^{a_p−J_p}. By L2 only the digits d ≤ J_p(i) can change, each by at most p−1. Hence φ_p(r+g) − φ_p(r) ≤ (p−1)Σ_{d≤J_p(i)} C_{p,d}. Summing over p gives φ(r+g)−φ(r) ≤ B(i), and (c) follows.
(b) Here g = C_{p,j} by symmetry. For q ≠ p, J_q = 0 by L0, so the q-digits do not change. For p, J_p = j, so the digits d > j are frozen.
 - Case e_j ≤ p−2: the vector e + (unit vector at j) is a valid digit vector of r+g, so by L1 it is the digit vector of r+g. The increment is exactly g.
 - Case e_j = p−1: let e' be the digits of r+g. Mod p^{a−j+1} the terms d<j vanish, so (e_j+1−e'_j)C_{p,j} ≡ 0 (mod p^{a−j+1}). Hence p | p−e'_j, so e'_j = 0. The increment is Σ_{d<j}(e'_d−e_d)C_{p,d} − (p−1)C_{p,j} ≤ (p−1)(Σ_{d<j}C_{p,d} − C_{p,j}) < 0 ≤ g by L3.
L3 (carry lemma, strong form). Since n has a second prime factor, p^a ≤ n/2. Claim: C(n,pk) ≥ 2C(n,k) for k ≥ 2 and pk ≤ n/2. We have C(n,pk)/C(n,k) = Π_{t=k+1}^{pk} (n+1−t)/t. Every factor is ≥ 1 because t ≤ n/2. The first factor is (n−k)/(k+1) ≥ (2pk−k)/(k+1) ≥ 3k/(k+1) ≥ 2. Apply this with k = p^d, d ≥ 1: C_{p,d} ≤ 2^{−(j−d)}C_{p,j}, so Σ_{d<j} C_{p,d} < C_{p,j}. This is stronger than the required bound Σ ≤ C_{p,j}·p/(p−1).
Mirrors i = n−p^j give the same g, and the analysis uses only g. ∎

## [valid-restatement] deep/C2 PROVED QUANT
**Statement.** n as in C1, 1 ≤ i < n, i ∉ E. Then C(n,i) ≥ B(i).
**Beyond.** this is CORE's open inequality.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 2, "cite": null, "why": "The claim is literally the team's stated remaining core inequality (E), which together with the carry lemma and the potential certificate yields the lower-bound half of the Erdős–Graham binomial Frobenius problem, so a proof needs full scrutiny of the reduction. The inequality itself appears to be an exponential binomial-ratio estimate plus a finite check rather than a deep new idea.", "panel": [{"verdict": "restatement", "cite": null, "significance": 2, "why": "The claim is literally the team's stated remaining core inequality (E), which together with the carry lemma and the potential certificate yields the lower-bound half of the Erdős–Graham binomial Frobenius problem, so a proof needs full scrutiny of the reduction. Th`
**Proof or evidence.**

Let P = {p : J_p ≥ 1}. If P = ∅, then B = 0. Otherwise let K_p = p^{J_p} (p ∈ P), K = max K_p, L = Π_{p∈P} K_p.
E1. By V1, for p ∈ P: J_p = a_p − v_p(C(n,i)) ≤ v_p(i) and ≤ v_p(n−i). So L | i and L | n−i.
E2. 2K ≤ i ≤ n − 2K.
- If |P| ≥ 2: i and n−i are positive multiples of L ≥ 2K. L is a product of ≥ 2 factors each ≥ 2, one of which is K.
- If P = {p}: i and n−i are positive multiples of K = p^J with 1 ≤ J ≤ a_p (J ≤ a_p since v_p ≥ 0). Neither equals K, because i ∉ E. So both are ≥ 2K.
- Hence 4K ≤ n, and C(n,i) ≥ C(n,2K) by unimodality and symmetry.
E3. If 1 ≤ m < M ≤ n/4, then C(n,M) ≥ 3^{M−m}·C(n,m). Each factor (n+1−t)/t with t ≤ M is ≥ (n+1−M)/M > 3.
E4 (needs only K_p ≤ K ≤ n/4). For each p ∈ P: Σ_{d=1}^{J_p} C(n,p^d) ≤ (7/6)·C(n,K_p).
- If J_p = 1, this is trivial.
- If J_p ≥ 2: for d < J_p, the exponent K_p − p^d ≥ p^{J_p−1}(p−1) ≥ 2, and these exponents are distinct.
- By E3 the d < J_p terms sum to ≤ Σ_{k≥2} 3^{−k}·C(n,K_p) = C(n,K_p)/6.
E5. Σ_{p∈P}(p−1)·C(n,K_p) ≤ (3/2)(K−1)·C(n,K).
- The K_p are powers of distinct primes, hence distinct. Exactly one p0 has K_{p0} = K, and p0 − 1 ≤ K − 1.
- Every other p has p − 1 ≤ K_p − 1 < K − 1, and by E3 C(n,K_p) ≤ 3^{−(K−K_p)}·C(n,K), with distinct shifts K − K_p ≥ 1.
- So the others contribute ≤ (K−1)·(1/2)·C(n,K).
E6. C(n,2K)/C(n,K) = Π_{t=K+1}^{2K} (n+1−t)/t. Each factor increases in n, and n ≥ 4K, so the ratio is ≥ its value at n = 4K, which is R(K) := C(3K,K)/C(2K,K).
- Check: at n = 4K the product is [(3K)!/(2K)!]/[(2K)!/K!] = C(3K,K)/C(2K,K).
E7. R(K) ≥ (7/4)(K−1) for K ≥ 2.
- Base cases: R(2) = 15/6, R(3) = 84/20 = 4.2 ≥ 3.5.
- R(K+1)/R(K) = 3(3K+1)(3K+2)/(4(2K+1)²) ≥ 3/2, since this is equivalent to 27K² + 27K + 6 ≥ 24K² + 24K + 6.
- For K ≥ 3: (3/2)·(7/4)(K−1) ≥ (7/4)K.
E8. Chain:
B ≤ (E4) (7/6)·Σ(p−1)C(n,K_p) ≤ (E5) (7/4)(K−1)·C(n,K) ≤ (E7) R(K)·C(n,K) ≤ (E6) C(n,2K) ≤ (E2) C(n,i). ∎

## [valid-restatement] deep/C1r PROVED OTHER
**Statement.** Let n ≥ 1 with n ≠ p^k for every prime p and every k ≥ 0. Write a_p = v_p(n) and

X = Σ_{p|n} (p−1) Σ_{d=1}^{a_p} C(n,p^d) ∈ ℤ.

Then there is no c : ℕ → ℕ with X − n = Σ_{i=1}^{n−1} c_i·C(n,i), with equality taken in ℤ. This is unchanged and is `erdos_27285_hyp_top`.
**Beyond.** KNOWN has only the upper bound (Brauer), with (E) and the carry lemma left open in CORE. This is the matching lower bound, complete.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "Brauer's gcd-tower bound already shows every integer above X−n is representable, so non-representability of X−n is exactly the missing half and yields the full answer g = X−n. A proof is a complete solution and needs maximal scrutiny, especially the uniform bound (E) for indices outside the gcd tower.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "Brauer's gcd-tower bound already shows every integer above X−n is representable, so non-representability of X−n is exactly the missing half and yields the full answer g = X−n. A proof is a complete solution and needs maximal scrutiny, especially the uniform bound (E) for indices outside the gcd tower."}, {"verdict": "restatement", "cite": null, "s`
**Proof or evidence.**

**Notation.** For p | n, write a = a_p and C_{p,d} = C(n,p^d) for 1 ≤ d ≤ a. The case n = 1 = p^0 is excluded, so n has at least two distinct prime factors.

**F0.** If p^d | n with d ≤ a, then n = p^d·m' with m' ≥ 2. Hence p^d ≤ n/2.

**V1.** Let 1 ≤ i < n.
- From i·C(n,i) = n·C(n−1,i−1) we get v_p(i) + v_p(C(n,i)) ≥ a_p.
- Since C(n,i) = C(n,n−i), likewise v_p(n−i) + v_p(C(n,i)) ≥ a_p.

**V2.** v_p(C_{p,d}) = a − d.
- We have p^d·C_{p,d} = n·Π_{t=1}^{p^d−1}(n−t)/t.
- For 1 ≤ t < p^d we have v_p(t) < d ≤ a, so v_p(n−t) = v_p(t). The product therefore has valuation 0.

**V3.** For primes q ≠ p with q | n, q^{a_q} divides C_{p,d}. This holds because q^{a_q} | p^d·C_{p,d} and gcd(p,q) = 1.

**D1.** Fix J ∈ {0..a}. The map e ↦ Σ_{d≤J} e_d·C_{p,d} mod p^a, on {0..p−1}^J, is injective. Its image is the set of residues divisible by p^{a−J}.
- Injectivity: let e ≠ e' and let D be the top index with e_D ≠ e'_D. By V2, the D-term of the difference has valuation exactly a−D. The lower terms have valuation ≥ a−D+1. So the difference has valuation a−D < a and is nonzero mod p^a.
- Image: every value is divisible by p^{a−J}, and there are exactly p^J such residues. Counting gives equality.
- For J = a, every residue s mod p^a has a unique digit vector e^p(s).

**D2.** If s ≡ s' (mod p^{a−J}), then e^p_d(s) = e^p_d(s') for all d > J.
- Otherwise let D > J be the top differing index. As in D1, v_p(s−s') = a−D < a−J, a contradiction.

**Potential.** Set φ_p(s) = Σ_d e^p_d(s)·C_{p,d} and φ = Σ_{p|n} φ_p.
- φ(0) = 0.
- φ is n-periodic.

**A.** Suppose φ(s+g) ≤ φ(s)+g for all s ∈ ℤ and every generator g = C(n,i) with 1 ≤ i < n. Then φ(m) ≤ m for every representable m.
- Proof by induction on Σc_i: write m = m' + g, so φ(m) ≤ φ(m') + g ≤ m' + g = m.

**X.** Fix p.
- By V3, X ≡ (p−1)Σ_d C_{p,d} (mod p^a). The all-(p−1) vector is a legal digit vector, so φ_p(X) = (p−1)Σ_d C_{p,d}. Hence φ(X) = X.
- Since p^{a_p} | n for each p, φ(X−n) = φ(X) = X > X−n.
- So, once the generator inequality is shown, A gives that X−n is not representable.

**CL.** For 1 ≤ j ≤ a: (p−1)Σ_{d<j} C_{p,d} ≤ C_{p,j}.
- Let 2 ≤ d ≤ a, m₀ = p^{d−1} ≥ 2 and M = p·m₀ ≤ n/2 (by F0).
- Then C(n,M)/C(n,m₀) = Π_{t=m₀+1}^{M} (n+1−t)/t. Every factor is ≥ 1 because t ≤ n/2.
- The first factor is (n−m₀)/(m₀+1) ≥ (2p−1)m₀/(m₀+1) ≥ (2p−1)·2/3 ≥ p.
- So C_{p,d} ≥ p·C_{p,d−1}. Summing the geometric bound gives Σ_{d<j} C_{p,d} ≤ C_{p,j}/(p−1).
- Consequence (CL′): (p−1)Σ_{d=1}^{J} C_{p,d} ≤ p·C_{p,J} for 1 ≤ J ≤ a.

**G1.** Let g = C(n,i) and J_p = max(0, a_p − v_p(g)) ≤ a_p.
- Then p^{a_p−J_p} | g. By D2, only the digits d ≤ J_p of φ_p change, each by at most p−1.
- Hence φ(s+g) − φ(s) ≤ B(i) := Σ_p (p−1)Σ_{d=1}^{J_p} C_{p,d}.

**C2 (proof of (E)).** Let E = {p^j, n−p^j : p | n, 1 ≤ j ≤ a_p}. If 1 ≤ i < n and i ∉ E, then C(n,i) ≥ B(i).
1. Let m = min(i, n−i) ≤ n/2, so C(n,i) = C(n,m). Also C(n,s) ≤ C(n,m) for 0 ≤ s ≤ m.
2. By V1, a_p − v_p(g) ≤ v_p(i) and a_p − v_p(g) ≤ v_p(n−i). Hence J_p ≤ min(v_p(i), v_p(n−i)), and r_p := p^{J_p} divides m.
3. Let P = {p : J_p ≥ 1}. If P = ∅, then B(i) = 0 and we are done.
4. For p ∈ P we have 1 ≤ J_p ≤ a_p. Since i ∉ E, m ≠ r_p, so m ≥ 2r_p, i.e. r_p ≤ m/2 ≤ n/4.
5. The r_p are distinct, being powers of distinct primes, and each r_p ≥ 2. By CL′ and p ≤ r_p, the p-contribution to B(i) is ≤ p·C(n,r_p) ≤ f(r_p), where f(r) := r·C(n,r).
6. Key ratio. For 4r ≤ n, C(n,2r)/C(n,r) = C(n−r,r)/C(2r,r) = Π_{t=1}^{r} (n−2r+t)/(r+t). Each factor is ≥ (2r+t)/(r+t). So C(n,2r) ≥ c_r·C(n,r), where c_r := C(3r,r)/C(2r,r).
7. Values of c_r: c_2 = 5/2 and c_3 = 21/5. Also c_{r+1}/c_r = 3(3r+1)(3r+2)/(4(2r+1)²) ≥ 3/2. Since c_4 = 99/14 > 6, induction gives c_r ≥ (3/2)r for r ≥ 4. In all cases c_r ≥ r for r ≥ 2.
8. Case |P| = 1, with r = r_p:
   - B(i) ≤ r·C(n,r) ≤ c_r·C(n,r) ≤ C(n,2r) ≤ C(n,m).
9. Case |P| ≥ 2, with r* = max r_p and r* ≥ 4:
   - For r < r* ≤ n/4, f(r+1)/f(r) = (n−r)/r ≥ 3. So for the distinct r_p < r*, Σ f(r_p) ≤ f(r*)·Σ_{s≥1} 3^{−s} = f(r*)/2.
   - Hence B(i) ≤ (3/2)·r*·C(n,r*) ≤ c_{r*}·C(n,r*) ≤ C(n,2r*) ≤ C(n,m).
10. Case |P| ≥ 2 with r* ≤ 3:
    - The only distinct prime powers in {2,3} are 2 and 3, so P = {2,3} and J_2 = J_3 = 1.
    - Then 6 | m, so 6 ≤ m ≤ n/2 and n ≥ 12. Here B(i) = C(n,2) + 2C(n,3).
    - For n ≥ 12, C(n,2) ≤ C(n,3), and C(n,6)/C(n,3) = (n−3)(n−4)(n−5)/120 ≥ 504/120 > 3.
    - So B(i) ≤ 3C(n,3) ≤ C(n,6) ≤ C(n,m).

Therefore, for i ∉ E, φ(s+g) − φ(s) ≤ B(i) ≤ g.

**G2.** Let i ∈ {p^j, n−p^j} with 1 ≤ j ≤ a, so g = C_{p,j}.
- For q ≠ p, φ_q is unchanged by V3.
- For p, the digits d > j are unchanged by D2 and V2. Let e = e^p(s) and e' = e^p(s+g).
- If e_j ≤ p−2: by uniqueness, e' = e + (unit vector at j), so the increment is exactly g.
- If e_j = p−1: reducing C_{p,j} ≡ Σ_{d≤j}(e'_d − e_d)·C_{p,d} mod p^{a−j+1} gives p | (p − e'_j), so e'_j = 0.
  - The increment is then ≤ (p−1)(Σ_{d<j} C_{p,d}) − (p−1)·C_{p,j} ≤ 0 < g, by CL.

**Conclusion.** Every generator satisfies φ(s+g) ≤ φ(s)+g: by G2 for i ∈ E, and by G1 + C2 for i ∉ E. By A, every representable m has φ(m) ≤ m. By X, φ(X−n) = X > X−n. Hence X−n is not representable. ∎

## [valid-restatement] r1s1/C1 PROVED QUANT
**Statement.** Let n ≥ 1 be such that n ≠ p^k for every prime p and every k ≥ 0. Put X = Σ_{p|n} (p−1) Σ_{d=1}^{v_p(n)} C(n,p^d). Then X − n ∉ S := {Σ_{1≤i<n} c_i C(n,i) : c_i ∈ ℕ}. Moreover S = T := ⟨n, C(n,p^d) : p | n, 1 ≤ d ≤ v_p(n)⟩.
**Beyond.** KNOWN gives only the upper bound (all integers > X−n lie in T ⊆ S) and states (E) as an unproved reduction. Here (E) and the carry lemma are proved, and so are the digit-potential lemmas. This gives the lower bound, the full step, and the identity S = T.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "Combined with the known Brauer upper bound, showing X−n ∉ S is exactly the statement that the Frobenius number equals X(n)−n, i.e. the full resolution of the problem; since the problem was reportedly resolved recently, the value itself is likely already known, so any proof needs maximal scrutiny (especially (E) for mixed indices and the small-K finite check).", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "Combined with the known Brauer upper bound, showing X−n ∉ S is exactly the statement that the Frobenius number equals X(n)−n, i.e. the full resolution of the problem; since the problem was reportedly resolved recently, the value itself is likely already known, so any proof needs maximal sc`
**Proof or evidence.**

Notation: n is fixed and not a prime power, so n ≥ 6. For p | n write a = a_p = v_p(n) and g_d = g_d^{(p)} = C(n,p^d) for 1 ≤ d ≤ a.
Facts used from KNOWN:
(K1) v_p(g_d) = a − d, and v_q(C(n,p^d)) ≥ v_q(n) for primes q ≠ p.
(K2) v_p(C(n,i)) ≥ v_p(n) − v_p(i).
(K3) C(n,k) is increasing on 0 ≤ k ≤ n/2 and symmetric.
(F0) If p^d | n then n ≥ 2p^d, because n = p^d·m with m ≥ 2 (m = 1 would make n a prime power).

L1 (digits). The map D: {0..p−1}^a → Z/p^a, e ↦ Σ e_d g_d, is a bijection. For 0 ≤ j ≤ a it maps the vectors supported on {d ≤ j} bijectively onto the residues divisible by p^{a−j}.
Proof. Write g_d = p^{a−d}u_d with p ∤ u_d (K1). Suppose D(e) = D(e') with e ≠ e', and let d0 be the largest d with e_d ≠ e'_d. In Σ (e_d − e'_d) p^{a−d} u_d, the d0 term has valuation exactly a − d0 < a, because 0 < |e_{d0} − e'_{d0}| < p. Every other nonzero term has d < d0 and so valuation > a − d0. Hence the sum has valuation a − d0 < a, so it is not 0 mod p^a. This is a contradiction, so D is injective, and since both sides have p^a elements it is a bijection. For the second part: if e is supported on d ≤ j, every term has valuation ≥ a − j. There are p^j such vectors with distinct images, and there are exactly p^j residues mod p^a divisible by p^{a−j}. ∎
Define φ_p(x) = Σ e_d g_d with e = D^{-1}(x), and φ(r) = Σ_{p|n} φ_p(r mod p^{a_p}) for r ∈ Z/n.
L2. φ(r) ≡ r (mod n), φ(0) = 0, and φ(X mod n) = X.
Proof. Fix p. Mod p^a, the terms of φ(r) coming from primes q ≠ p vanish by (K1), and the p-part is ≡ r. CRT then gives φ(r) ≡ r mod n. The same vanishing gives X ≡ (p−1)Σ_d g_d (mod p^a). The all-(p−1) vector is a legal digit vector, so φ_p(X) = (p−1)Σ_d g_d, and summing over p gives φ(X) = X. ∎
L3 (support). If p^{a−j} | x (mod p^a), then φ_p(x) ≤ (p−1)Σ_{d≤j} g_d. This follows from L1.
L4 (carry lemma, sharp form). If p^d | n and 1 ≤ d' < d, then C(n,p^{d'}) ≤ 2^{−(d−d')} C(n,p^d). Hence Σ_{d'<d} g_{d'} < g_d.
Proof. It suffices to show C(n,K) ≥ 2C(n,k) for k = p^j ≥ 2 and K = pk ≤ p^d ≤ n/2 (F0). Since 2k ≤ K ≤ n/2, (K3) gives C(n,K) ≥ C(n,2k). The ratio C(n,2k)/C(n,k) = Π_{t=k+1}^{2k}(n+1−t)/t increases in n, and n ≥ 2K ≥ 4k, so the ratio is ≥ Π_{t=k+1}^{2k}(4k+1−t)/t. Every factor is ≥ 1, and the t = k+1 factor is 3k/(k+1) ≥ 2 because k ≥ 2. ∎
L5 (tower generators). For all r: φ(r+n) = φ(r), and φ(r + g_d^{(p)}) ≤ φ(r) + g_d^{(p)}.
Proof. Adding g_d^{(p)} changes r mod q^{a_q} only for q = p (K1), so only φ_p changes. Let x = r mod p^a with digits e.
- If e_d < p−1: raising e_d by one gives a legal vector representing x + g_d, so φ_p increases by exactly g_d.
- If e_d = p−1: write x + g_d = Σ_{d'>d} e_{d'}g_{d'} + y with y = Σ_{d'<d} e_{d'}g_{d'} + p g_d. Here v_p(p g_d) = a−d+1, so p^{a−d+1} | y, and by L1 y has digits supported on d' < d. The vector (e_{d'} for d' > d, 0 at d, digits of y below) is legal, so it is the digit vector of x + g_d. Comparing gives φ_p(x+g_d) − φ_p(x) ≤ (p−1)Σ_{d'<d}g_{d'} − (p−1)g_d, which is < 0 ≤ g_d by L4. ∎
Corollary L6. Every t ∈ T satisfies t ≥ φ(t mod n). Proof: induction on the number of generators, using φ(0) = 0 and L5.
L7 (E, proved). Let 1 ≤ i < n with i ∉ E := {p^j, n−p^j : p | n, 1 ≤ j ≤ v_p(n)}. For each q | n let J_q = max(0, v_q(n) − v_q(C(n,i))). Then C(n,i) ≥ R := Σ_q (q−1)Σ_{d=1}^{J_q} C(n,q^d).
Proof. C(n,i) = C(n,n−i), and both J and E are invariant under i ↦ n−i, so we may assume i ≤ n/2. Let P = {q : J_q ≥ 1}. If P = ∅ then R = 0. Otherwise:
- By (K2), J_q ≤ v_q(i), so L := Π_{q∈P} q^{J_q} divides i.
- Let M = max_{q∈P} q^{J_q}. Then i ≥ 2M. If |P| ≥ 2 this holds because L ≥ 2M. If P = {p}, then p^{J_p} | i and i ≠ p^{J_p}, since 1 ≤ J_p ≤ v_p(n) would put i in E. So i ≥ 2p^{J_p}.
- Hence every q^d appearing in R satisfies q^d ≤ M ≤ i/2 ≤ n/4 < i.
- For k < i and n ≥ 2i, the ratio C(n,i)/C(n,k) = Π_{t=k+1}^{i}(n+1−t)/t increases in n, so (#) C(n,k)/C(n,i) ≤ C(2i,k)/C(2i,i).
(i) Case i ≥ 35.
- By (K3), R ≤ s·C(n,M) with s = Σ_{q∈P}(q−1)J_q.
- Since (q−1)J ≤ q^J − 1, and Σ(x_k − 1) ≤ Πx_k − 1 for integers x_k ≥ 2 (the step is (A−1)(x−1) ≥ 0), we get s ≤ L − 1 ≤ i − 1.
- By (#) and C(2i,M) ≤ C(2i,⌊i/2⌋), C(n,i)/C(n,M) ≥ F(i) := C(2i,i)/C(2i,⌊i/2⌋) = Π_{t=⌊i/2⌋+1}^{i}(2i+1−t)/t.
- Every factor of F(i) is ≥ 1. Each factor with t ≤ 3i/4 is ≥ (2i+1)/(3i/4) − 1 > 5/3, and there are ≥ (i−3)/4 such t. So F(i) ≥ (5/3)^{(i−3)/4}.
- This is ≥ i − 1 for i ≥ 35: at i = 35, (5/3)^8 ≈ 59.5 ≥ 34. Going from i to i+1 multiplies the left side by (5/3)^{1/4} ≈ 1.136 and the right side by i/(i−1) ≤ 35/34.
- So C(n,i) ≥ (i−1)C(n,M) ≥ R.
(ii) Case 4 ≤ i ≤ 34 (i ≥ 2M ≥ 4).
- By (#), R/C(n,i) ≤ Σ_{q∈P}(q−1)Σ_{d≤J_q} C(2i,q^d)/C(2i,i). The right side is increasing in P and in the J_q.
- Its maximum over admissible (P,J) is: all q | i with J_q = v_q(i) if i is not a prime power; and J = v−1 if i = p^v.
- s2.py checks C(2i,i) ≥ this maximum for all 2 ≤ i < 200. The minimum ratio is 1.826 at i = 6, then 2.5 at i = 4 and 2.97 at i = 10. ∎
Main argument.
- Let g = C(n,i).
- If i ∈ E, then g = C(n,p^j) is a generator of T, and i = 1 gives g = n.
- If i ∉ E: by L3 applied to each q (v_q(g mod q^{a_q}) ≥ a_q − J_q) and L7, φ(g mod n) ≤ R ≤ g. By L2, g = φ(g mod n) + kn with k ≥ 0, so g ∈ T (φ(·) is by definition in T).
- Hence S ⊆ T. Also T ⊆ S, because n = C(n,1). So S = T.
- If X − n = Σ c_i C(n,i) with c_i ∈ ℕ, then X − n ∈ T. By L6 and L2, X − n ≥ φ((X−n) mod n) = φ(X mod n) = X, a contradiction.
- If X − n < 0 the claim is trivial anyway; the argument above also covers that case. ∎
Remark on the Lean form: Rep(n,m) means exactly m ∈ S with c_i ∈ ℕ over Ico 1 n. X matches erdos_27285_X. The hypotheses force n ≥ 2 and exclude p^0 = 1.

## [valid-restatement] r1s2/C1 PROVED QUANT
**Statement.** Let n ≥ 2 not be a prime power. For p | n let a_p = v_p(n). Let 1 ≤ i < n with i ∉ E := {p^j, n−p^j : p | n, 1 ≤ j ≤ a_p}. Put J_p = max(0, a_p − v_p(C(n,i))). Then
C(n,i) ≥ Σ_{p|n} (p−1) Σ_{d=1}^{J_p} C(n,p^d).
More precisely, if P = {p : J_p ≥ 1} ≠ ∅ and K = max_{p∈P} p^{J_p}, then 4K ≤ n and C(n,i) ≥ C(n,2K) ≥ R(K)·C(n,K) ≥ (7/4)(K−1)·C(n,K) ≥ RHS, where R(K) = C(3K,K)/C(2K,K).
**Beyond.** This is exactly the open inequality (E) of the CORE. It is proved for all n, with no finite verification.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "The claim is exactly inequality (E), which the team identifies as the sole remaining core; with the routine carry lemma and the standard Apéry-potential and Brauer machinery, it yields the lower bound X(n)−n and so resolves the problem. The final inequality (7/4)(K−1)·C(n,K) ≥ RHS needs scrutiny when several primes have J_p ≥ 1, since the naive term count can exceed (7/4)(K−1).", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "The claim is exactly inequality (E), which the team identifies as the sole remaining core; with the routine carry lemma and the standard Apéry-potential and Brauer machinery, it yields the lower bound X(n)−n and so resolves the problem. The final inequality (7/4)(K−1)·C(`
**Proof or evidence.**

L1 (first step of the assignment). If J_p ≥ 1, then p^{J_p} | i and p^{J_p} | n−i.
Proof: i·C(n,i) = n·C(n−1,i−1) gives v_p(i) + v_p(C(n,i)) ≥ a_p, so v_p(i) ≥ a_p − v_p(C(n,i)) = J_p. Since C(n,i) = C(n,n−i), the same argument gives v_p(n−i) ≥ J_p.
(Kummer form of the same fact: if t = v_p(i) < a_p, then n has digit 0 in positions 0..a_p−1, so adding i and n−i carries in each of the positions t..a_p−1. Hence v_p(C(n,i)) ≥ a_p − t.)

L2. If P ≠ ∅, then 2K ≤ i ≤ n − 2K, and so 4K ≤ n.
Proof: By L1, L := Π_{p∈P} p^{J_p} divides both i and n−i, and K | L.
- Case |P| ≥ 2: L ≥ 2K, and i, n−i are positive multiples of L, so both are ≥ 2K.
- Case P = {p}: K = p^{J} with 1 ≤ J ≤ a_p, and i, n−i are positive multiples of K. Since i ∉ E, i ≠ p^J and n−i ≠ p^J. So both are ≥ 2K.

L3. If 1 ≤ m < M ≤ n/4, then C(n,M) > 3^{M−m}·C(n,m).
Proof: C(n,M)/C(n,m) = Π_{t=m+1}^{M} (n−t+1)/t. Each factor is ≥ (n−M+1)/M ≥ (3M+1)/M > 3.

L4. For p ∈ P, let K_p = p^{J_p}. Then Σ_{d=1}^{J_p} C(n,p^d) ≤ (7/6)·C(n,K_p).
Proof: K_p ≤ K ≤ n/4 by L2. By L3, C(n,p^d) ≤ 3^{−(K_p−p^d)}·C(n,K_p) for d < J_p. For J_p ≥ 2, the exponents K_p − p^d (d = 1..J_p−1) are distinct integers, each ≥ p^{J_p−1}(p−1) ≥ 2. So the sum over d < J_p is ≤ Σ_{k≥2} 3^{−k}·C(n,K_p) = C(n,K_p)/6. For J_p = 1 this sum is empty.

L5. Σ_{p∈P} (p−1)·C(n,K_p) ≤ (3/2)(K−1)·C(n,K).
Proof: The K_p are powers of distinct primes, so they are pairwise distinct. Exactly one prime p0 has K_{p0} = K, and p0 − 1 ≤ K − 1.
For every other p: p − 1 ≤ K_p − 1 < K − 1, and by L3, C(n,K_p) ≤ 3^{−(K−K_p)}·C(n,K). The shifts t = K − K_p are distinct positive integers. So these terms sum to ≤ (K−1)·Σ_{t≥1} 3^{−t}·C(n,K) = ((K−1)/2)·C(n,K).

L6. C(n,2K) ≥ R(K)·C(n,K).
Proof: C(n,2K)/C(n,K) = Π_{t=K+1}^{2K} (n−t+1)/t. Each factor increases with n, and n ≥ 4K. At n = 4K the product is [(3K)!/(2K)!]/[(2K)!/K!] = C(3K,K)/C(2K,K).

L7. R(K) ≥ (7/4)(K−1) for all K ≥ 2.
Proof: R(2) = 15/6 = 2.5 ≥ 1.75 and R(3) = 84/20 = 4.2 ≥ 3.5.
R(K+1)/R(K) = 3(3K+1)(3K+2)/(4(2K+1)^2) ≥ 3/2, because 27K²+27K+6 ≥ 24K²+24K+6.
For K ≥ 3: R(K+1) ≥ (3/2)(7/4)(K−1) ≥ (7/4)K, since (3/2)(K−1) ≥ K.

Conclusion. If P = ∅, the RHS is 0. Otherwise, by L2 and unimodality/symmetry of C(n,·), C(n,i) ≥ C(n,2K). Then
C(n,2K) ≥ (L6) R(K)·C(n,K) ≥ (L7) (7/4)(K−1)·C(n,K) ≥ (L5) (7/6)·Σ_{p∈P}(p−1)·C(n,K_p) ≥ (L4) Σ_p (p−1)·Σ_{d≤J_p} C(n,p^d). ∎
(Note that K ≥ 2 automatically. Also 7/6 · 3/2 = 7/4.)

## [valid-restatement] r1s3/C3 PROVED QUANT
**Statement.** (E) holds for every n ≥ 2 that is not a prime power and every non-exceptional i, unconditionally. Consequently (C1 + C3) erdos_27285_hyp_top is TRUE, and by C2, Ap(S,n) = φ and g(S) = X−n.
**Beyond.** proves CORE (E) outright; there is no small-K case split by hand, because the n-uniform reduction to n' = 2m turns the small cases into a finite check.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 2, "cite": null, "why": "By the team's own reduction, (E) plus the carry lemma is exactly the remaining core: it makes the digit potential a valid Apéry lower bound, giving non-representability of X(n)−n and so solving the problem. It needs maximal scrutiny, especially the n′=2m reduction, the finite small-K check and the multi-prime cases.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "By the team's own reduction, (E) plus the carry lemma is exactly the remaining core: it makes the digit potential a valid Apéry lower bound, giving non-representability of X(n)−n and so solving the problem. It needs maximal scrutiny, especially the n′=2m reduction, the finite small-K check and the multi-prime cases."}, {"verdict": "`
**Proof or evidence.**

Fix a non-exceptional i, let P = {p : J_p(i) > 0} (if P = ∅ then B = 0 and we are done), and let K_p = p^{J_p}, K = max K_p, L = Π_{p∈P} K_p, m = min(i, n−i) ≤ n/2, so C(n,i) = C(n,m).
S1. J_p ≤ v_p(i), because a_p − v_p(C(n,i)) ≤ v_p(i) by L0's identity i·C(n,i) = n·C(n−1,i−1). By symmetry J_p ≤ v_p(n−i). Hence L | i and L | n−i, so L | m.
S2. m ≥ 2K. If |P| = 1, then m is a multiple of K = p^J (1 ≤ J ≤ a_p), and m = K would mean i = p^J or n−i = p^J, which is exceptional. So m ≥ 2K. If |P| ≥ 2, then m ≥ L ≥ 2K.
S3 (reduction to n' = 2m). For k ≤ m ≤ n/2, C(n,k)/C(n,m) = Π_{t=k+1}^{m} t/(n+1−t) is non-increasing in n, so it is ≤ C(2m,k)/C(2m,m). Every p^d with d ≤ J_p satisfies p^d ≤ K ≤ m/2. Hence B(i)/C(n,m) ≤ Σ_{p∈P}(p−1)Σ_{d≤J_p} C(2m,p^d) / C(2m,m) ≤ S(m)/C(2m,m), where S(m) is the same sum with every prime p | m and J_p maximal subject to p^{J_p} | m and 2p^{J_p} ≤ m. All terms are ≥ 0, and by S1–S2 the actual configuration is dominated.
S4 (m ≤ 60). Computer check e_check.py, exact integers: S(m) ≤ C(2m,m) for all m ≤ 60. The worst ratio is 0.548, at m = 6.
S5 (m ≥ 44, analytic). By L3, Σ_{d≤J_p} C(n,p^d) < 2C(n,K_p). Since K_p ≤ ⌊m/2⌋ ≤ n/2, monotonicity gives C(n,K_p) ≤ C(n,⌊m/2⌋). Every p ∈ P divides m, so Σ_{p∈P}(p−1) ≤ Π_{p|m} p ≤ m. Hence B < 2m·C(n,⌊m/2⌋) ≤ C(n,m)·2m·C(2m,⌊m/2⌋)/C(2m,m) (by S3). Write C(2m,m)/C(2m,⌊m/2⌋) = Π_{t=⌊m/2⌋+1}^{m}(2m+1−t)/t. Every factor is ≥ 1, and the factors with t ≤ ⌊2m/3⌋ are ≥ 2. There are ⌊2m/3⌋−⌊m/2⌋ ≥ m/6−2/3 of them, so the ratio is ≥ 2^{m/6−2/3}. Then 2^{m/6−2/3} ≥ 2m ⟺ m/6 − 5/3 ≥ log2 m. This holds at m = 44 (5.667 ≥ 5.459), and m/6 − log2 m is increasing for m > 6/ln 2. So B < C(n,m). (Exact check: 2m·C(2m,⌊m/2⌋) ≤ C(2m,m) already for all 13 ≤ m ≤ 3000.)
S4 and S5 overlap and cover every m ≥ 1, so B(i) ≤ C(n,i). ∎
Full step: C1(b) handles the exceptional i, C1(c) + C3 handle all other i, and C1(a) then gives ¬Rep(n, X−n). Since n is not a prime power, n ≥ 6 has ≥ 2 prime factors, as used in L3 (p^a ≤ n/2).

## [valid-routine] r1s2/C2 PROVED QUANT
**Statement.** Let p be prime, j ≥ 1 and p^j ≤ n/2. Then Σ_{d=1}^{j−1} C(n,p^d) ≤ C(n,p^j)/(p−1), and n + Σ_{d=1}^{j−1} C(n,p^d) ≤ C(n,p^j)·p/(p−1). So the CORE's carry lemma holds whether the sum starts at d = 1 or at d = 0.
**Beyond.** This is the carry lemma of the CORE, which was stated there without proof.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Elementary consequence of the growth of C(n,k) for k ≤ n/2: consecutive ratios C(n,p^{d+1})/C(n,p^d) are at least p, giving a geometric-series bound, and n ≤ C(n,p^j) handles the d=0 term. It is a minor helper lemma; the real difficulty lies in inequality (E).", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Elementary consequence of the growth of C(n,k) for k ≤ n/2: consecutive ratios C(n,p^{d+1})/C(n,p^d) are at least p, giving a geometric-series bound, and n ≤ C(n,p^j) handles the d=0 term. It is a minor helper lemma; the real difficulty lies in inequality (E)."}, {"verdict": "routine", "cite": null, "significance": 0, "why": "The carry lemma follows in a few lines from monotonicity of C(n,k) on k`
**Proof or evidence.**

Ratio step: for d ≥ 2 with p^d ≤ n/2, C(n,p^d) ≥ p·C(n,p^{d−1}).
Write m = p^{d−1} ≥ 2 and M = pm ≤ n/2. Then C(n,M)/C(n,m) = Π_{t=m+1}^{M} (n−t+1)/t.
- Every factor is > 1, since t ≤ n/2.
- The factor t = m+1 is (n−m)/(m+1) ≥ (2p−1)m/(m+1) ≥ (2p−1)·(2/3) ≥ p, using m ≥ 2 and p ≥ 2.
Hence C(n,p^d) ≤ p^{−(j−d)}·C(n,p^j) for 1 ≤ d ≤ j, and so Σ_{d=1}^{j−1} C(n,p^d) ≤ C(n,p^j)·Σ_{k≥1} p^{−k} = C(n,p^j)/(p−1).
For the d = 0 term n = C(n,1):
- If j = 1: n ≤ C(n,p) because 1 ≤ p ≤ n/2.
- If j ≥ 2: n ≤ C(n,p) ≤ p^{−(j−1)}·C(n,p^j) ≤ C(n,p^j)/p. The total is then ≤ C(n,p^j)·(1/(p−1) + 1/p) ≤ C(n,p^j)·p/(p−1), because 2p − 1 ≤ p².
∎
(For n not a prime power and j ≤ v_p(n), the hypothesis p^j ≤ n/2 holds automatically: p^j is a proper divisor of n.)

## [valid-routine] r1s2/C3r PROVED SPECIAL
**Statement.** Let n ≥ 6 be an integer that is not a prime power. Let S = { Σ_{1≤i<n} c_i·C(n,i) : c_i ∈ ℤ_{≥0} }.

For each residue r ∈ ℤ/n, define w(r) = min{ s ∈ S : s ≡ r (mod n) }. Define X(n) = max_{r ∈ ℤ/n} w(r). Then:

(a) gcd{ C(n,i) : 1 ≤ i < n } = 1, and every residue class mod n meets S, so w and X(n) are well defined.
(b) For every integer s: s ∈ S ⟺ s ≥ w(s mod n).
(c) X(n) − n ∉ S, and every integer x > X(n) − n lies in S. So the Frobenius number is g(S) = X(n) − n.
(d) w(r) is the shortest-path distance from 0 to r in the weighted digraph on ℤ/n with edges r → r + C(n,i) (mod n) of weight C(n,i), for 1 ≤ i < n. So Dijkstra over ℤ/n computes w, and hence X(n) and g(S), exactly.

Worked instances (by hand):
- n = 6: S = ⟨6, 15, 20⟩. w = (0, 55, 20, 15, 40, 35). X = 55, g = 49.
- n = 10: the only generators not divisible by 10 are 45 and 252. w(r) = min{252k + 45m : 2k + 5m ≡ r (mod 10)}. X = 4·252 + 45 = 1053, g = 1043.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Ram (1909) for gcd of binomial coefficients; Brauer–Shockley (1962), Selmer (1977), Nijenhuis (1979); Rosales–García-Sánchez, Numerical Semigroups (2009), Prop. 2.12", "why": "The claim is the generic Apéry-set/shortest-path description of the Frobenius number of a numerical semigroup containing n, plus Ram's classical gcd fact; it says nothing about the actual value of X(n), which is the hard core (E).", "panel": [{"verdict": "routine", "cite": "Ram (1909) for gcd of binomial coefficients; Brauer–Shockley (1962), Selmer (1977), Nijenhuis (1979); Rosales–García-Sánchez, Numerical Semigroups (2009), Prop. 2.12", "significance": 0, "why": "The claim is the generic Apéry-set/shortest-path description of the Frobenius number of a numerical sem`
**Proof or evidence.**

**(a) gcd = 1.**
1. Suppose a prime p divides every C(n,i) with 1 ≤ i < n.
2. Since C(n,1) = n, we get p | n. Write n = p^k·m with k ≥ 1 and p ∤ m.
3. Because n is not a prime power, m > 1, so 1 ≤ p^k < n.
4. In 𝔽_p[x], the Frobenius map gives (1+x)^{p^k} = 1 + x^{p^k}.
5. Hence (1+x)^n = (1 + x^{p^k})^m. Its coefficient of x^{p^k} is m.
6. So C(n, p^k) ≡ m ≢ 0 (mod p), which contradicts step 1. Therefore the gcd is 1.

**Every residue class mod n meets S.**
1. By Bézout, 1 = Σ a_i·C(n,i) for some integers a_i.
2. For a residue r, pick an integer K ≥ max_i |r·a_i| / n.
3. Set s_r = Σ_i (r·a_i + K·n)·C(n,i). All coefficients are ≥ 0, so s_r ∈ S.
4. Also s_r ≡ r·1 + K·n·Σ_i C(n,i) ≡ r (mod n).
5. So each set {s ∈ S : s ≡ r} is a nonempty set of nonnegative integers, and w(r) exists.
6. w(0) = 0 because 0 ∈ S (all c_i = 0).

**(b) Membership criterion.**
- (⇒) If s ∈ S, then s is in its own residue class, so w(s mod n) ≤ s by minimality.
- (⇐) Suppose s ≥ w(r), where r = s mod n. Then s = w(r) + t·n with t ∈ ℤ_{≥0}. Since n = C(n,1) is a generator and S is closed under addition, s ∈ S.

**(c) Frobenius number.**
1. Fix r with w(r) = X(n).
2. The integer X(n) − n is ≡ r (mod n) and is < w(r). By (b), X(n) − n ∉ S.
3. Now let x > X(n) − n and set r' = x mod n.
4. Then x > X(n) − n ≥ w(r') − n.
5. Since x ≡ w(r') (mod n), x − w(r') is a multiple of n that is > −n, so it is ≥ 0.
6. Hence x ≥ w(r'), and x ∈ S by (b).
7. So X(n) − n is the largest integer not in S.
8. It is positive: for r ≠ 0, w(r) is a sum of generators other than n, each ≥ C(n,2) > n, so X(n) > n.

**(d) Dijkstra correctness.**
1. Any s = Σ c_i·C(n,i) ∈ S gives a walk from 0 in the digraph. Use c_i edges of type i, in any order. The walk has total weight s and ends at s mod n.
2. Conversely, a walk from 0 to r with c_i edges of type i has weight Σ c_i·C(n,i) ∈ S, and that weight is ≡ r.
3. Therefore w(r) is the minimum walk weight from 0 to r, which is the shortest-path distance.
4. Edge weights are nonnegative, so Dijkstra returns exactly these distances.
5. Edges of weight C(n,i) ≡ 0 (mod n) are self-loops and do not affect the distances.

**Instance n = 6.**
- Generators: 6, 15, 20. Residues mod 6: 15 ≡ 3, 20 ≡ 2.
- w(r) = min{15a + 20b : 3a + 2b ≡ r (mod 6)}.
- This gives w = 0, 55 (a = 1, b = 2), 20, 15, 40, 35.
- So X = 55 and g = 49.

**Instance n = 10.**
- C(10,1), C(10,3) = 120, and C(10,4) = 210 (and their mirror images) are ≡ 0 (mod 10). C(10,2) = 45 ≡ 5 and C(10,5) = 252 ≡ 2.
- So w(r) = min{252k + 45m : 2k + 5m ≡ r (mod 10)}.
- The maximum is at r = 3: m must be odd and k ≡ 4 (mod 5), so w(3) = 4·252 + 45 = 1053.
- So g = 1043.

## [broken] deep/C1 PROVED OTHER
**Statement.** Let n ≥ 1 with n ≠ p^k for every prime p and every k ≥ 0. Write a_p = v_p(n), and let
X = Σ_{p|n} (p−1) Σ_{d=1}^{a_p} C(n,p^d) ∈ ℤ.
Then there is no c : ℕ → ℕ with X − n = Σ_{i=1}^{n−1} c_i C(n,i) (equality in ℤ). This is literally `erdos_27285_hyp_top`. Rep and X are in ℤ, so there is no truncated subtraction. n = 1 = p^0 is excluded by hypothesis, so n has ≥ 2 distinct prime factors and n ≥ 6.
**Beyond.** KNOWN has only the upper bound (Brauer), with (E) and the carry lemma left open in CORE. This is the matching lower bound, complete.
**Referee.** `{"valid": false, "first_error": "G1: the generator inequality C(n,i) >= B(i) for i outside E (statement (E)) is asserted as 'proved in C2', but no C2 is supplied; this is exactly the open ingredient, so step A cannot be applied to non-exceptional generators. All other steps (V1-V3, D1, D2, A, X, G2, CL) check out.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

Notation: for p | n, a = a_p, C_{p,d} = C(n,p^d) for 1 ≤ d ≤ a.
(F0) If p^d | n with d ≤ a, then n = p^d·m with m ≥ 2, since n has another prime factor. Hence p^d ≤ n/2.

V1. Let 1 ≤ i < n. Then i·C(n,i) = n·C(n−1,i−1), so v_p(i) + v_p(C(n,i)) ≥ a_p. Applying this to n − i (C(n,i) = C(n,n−i)) gives v_p(n−i) + v_p(C(n,i)) ≥ a_p.
V2. For 1 ≤ d ≤ a: v_p(C_{p,d}) = a − d exactly.
- We have p^d·C_{p,d} = n·C(n−1,p^d−1), and C(n−1,p^d−1) = Π_{t=1}^{p^d−1} (n−t)/t.
- For 1 ≤ t < p^d we have v_p(t) < d ≤ a = v_p(n), so v_p(n−t) = v_p(t).
- So the product has valuation 0, and v_p(C_{p,d}) = a − d.
V3. For primes q ≠ p with q | n: q^{a_q} divides C_{p,d}, since q^{a_q} | n·C(n−1,p^d−1) = p^d·C_{p,d} and gcd(q,p) = 1.

D1 (digits). For J ∈ {0..a}, the map e ↦ Σ_{d≤J} e_d C_{p,d} mod p^a, from {0..p−1}^J, is injective, and its image is exactly the set of residues divisible by p^{a−J}.
- Injectivity: suppose e ≠ e', and let D be the largest index with e_D ≠ e'_D. In Σ_{d≤D}(e_d − e'_d)C_{p,d}, the D term has valuation exactly a − D, by V2 and 0 < |e_D − e'_D| < p. The other terms have valuation ≥ a − D + 1. So the sum has valuation a − D < a and is nonzero mod p^a.
- Image: every term is divisible by p^{a−J}, and there are p^J residues mod p^a divisible by p^{a−J}. Counting gives equality.
- With J = a, every residue mod p^a has a unique digit vector e^p(s).
D2 (frozen digits). If s ≡ s' (mod p^{a−J}), then e^p_d(s) = e^p_d(s') for all d > J.
- Suppose not, and let D > J be the top differing index. As in D1, s − s' ≡ (a sum of valuation a − D) mod p^a.
- So v_p(s − s') = a − D < a − J. This contradicts p^{a−J} | s − s'.

Potential: φ_p(s) = Σ_d e^p_d(s)·C_{p,d}, and φ(s) = Σ_{p|n} φ_p(s), for s ∈ ℤ.
- φ(0) = 0.
- φ is n-periodic.

A (ascent). Suppose φ(s+g) ≤ φ(s) + g for all s ∈ ℤ and every g = C(n,i) with 1 ≤ i < n. Then φ(m) ≤ m for every m = Σ c_i C(n,i).
- Proof: induction on Σ c_i. Remove one generator g from the representation, so m = m' + g. Then φ(m) ≤ φ(m') + g ≤ m' + g = m.

X. Fix p. By V3, X ≡ Σ_d (p−1)C_{p,d} (mod p^a). The all-(p−1) vector is a legal digit vector, so by D1 φ_p(X) = (p−1)Σ_d C_{p,d}.
- Hence φ(X) = X.
- Since p^a | n for every p, X − n ≡ X mod p^{a_p}, so φ(X − n) = X > X − n.
- By A, X − n is not representable, PROVIDED the generator inequality holds. That inequality is proved next.

G1 (general generator). Let g = C(n,i), and for each p let J_p = max(0, a_p − v_p(g)). Then g ≡ 0 mod p^{a−J_p}.
- By D2, only the digits d ≤ J_p change, each by at most p − 1.
- So φ_p(s+g) − φ_p(s) ≤ (p−1)Σ_{d≤J_p} C_{p,d}.
- Summing over p: φ(s+g) − φ(s) ≤ B(i) := Σ_p (p−1)Σ_{d=1}^{J_p} C_{p,d}.
- So the generator inequality holds whenever C(n,i) ≥ B(i). This is (E), proved in C2 for all i outside E := {p^j, n−p^j : p | n, 1 ≤ j ≤ a_p}.

G2 (exceptional generator). Let i ∈ {p^j, n − p^j} with 1 ≤ j ≤ a, so g = C_{p,j}.
- For q ≠ p, g ≡ 0 mod q^{a_q} (V3), so φ_q is unchanged.
- For p, v_p(g) = a − j (V2). By D2 the digits d > j of s+g equal those of s. Let e = e^p(s) and e' = e^p(s+g).
- Case e_j ≤ p−2: e + (unit vector at j) is legal and represents s+g, so by uniqueness it equals e'. The increment is exactly g.
- Case e_j = p−1: subtracting the two representations gives C_{p,j} ≡ Σ_{d≤j}(e'_d − e_d)C_{p,d} (mod p^a).
  - Reduce mod p^{a−j+1}. The terms d < j vanish there by V2, so (p − e'_j)·C_{p,j} ≡ 0 mod p^{a−j+1}.
  - Since v_p(C_{p,j}) = a − j, p divides p − e'_j ∈ [1,p], so e'_j = 0.
  - Increment = Σ_{d<j}(e'_d − e_d)C_{p,d} − (p−1)C_{p,j} ≤ (p−1)(Σ_{d<j}C_{p,d} − C_{p,j}) ≤ 0 < g by CL.
CL (carry lemma). For 1 ≤ j ≤ a: (p−1)Σ_{d=1}^{j−1} C_{p,d} ≤ C_{p,j}.
- Ratio step: for 2 ≤ d ≤ a, put m = p^{d−1} ≥ 2 and M = pm ≤ n/2 (F0).
  - C(n,M)/C(n,m) = Π_{t=m+1}^{M} (n+1−t)/t. Every factor is ≥ 1 because t ≤ n/2.
  - The first factor is (n−m)/(m+1) ≥ (2p−1)m/(m+1) ≥ (2p−1)·2/3 ≥ p.
  - So C_{p,d} ≥ p·C_{p,d−1}, hence C_{p,d} ≤ p^{−(j−d)}·C_{p,j}.
- Summing: Σ_{d<j} C_{p,d} ≤ C_{p,j}·Σ_{k≥1} p^{−k} = C_{p,j}/(p−1).

Hence every generator satisfies φ(s+g) ≤ φ(s) + g:
- G2 for i ∈ E;
- G1 + C2 for i ∉ E. If such an i happens to have C(n,i) equal to some C_{p,j}, G1 still applies, because it uses only i ∉ E through C2.

So by A and X, X − n is not representable. ∎

## [broken] r1s2/C3 PROVED SPECIAL
**Statement.** For all non-prime-powers n with 6 ≤ n ≤ 160: X(n) − n ∉ S = ⟨C(n,i) : 1 ≤ i < n⟩, and the Frobenius number g(S) equals X(n) − n.
**Referee.** `{"valid": false, "first_error": "The proof consists solely of an appeal to check.py, whose code and output are not provided, and X(n) is never defined; the precise Lean statement is also missing. So 'g(S) = X(n) - n' is not checkable even though the Apéry/Dijkstra method is correct (e.g. n=6 gives g=49). Moreover, a finite check for 6 <= n <= 160 does not establish the step if the Lean statement is general.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

check.py computes the Apéry set of S modulo n with Dijkstra over Z/n, using every C(n,i) as a generator. It checks Ap[(X−n) mod n] > X−n and max Ap − n = X − n.

## [broken] r1s3/C2 PROVED STRUCTURE
**Statement.** Under the hypothesis of C1(a), and in particular if (E) holds, Ap(S,n)(r) = φ(r) for every r. Hence F(S) = max φ − n = X − n.
**Referee.** `{"valid": false, "first_error": "The reverse inequality Ap(S,n)(r) >= phi(r) (minimality of phi(r) among elements of S in residue class r mod n) is not proved: it is merely attributed to 'the induction in C1(a)', with no induction shown, and C1(a) is simultaneously invoked as a hypothesis, so the key step is assumed or deferred rather than established. (The upper bound Ap <= phi via L0 + CRT is fine modulo C_{p,d} in S and phi(0)=0.)", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

φ(r) = Σ_p Σ_d e_{p,d}C_{p,d} lies in S, and it is ≡ r mod every p^{a_p} by L0, so it is ≡ r mod n. Hence Ap ≤ φ. The reverse inequality Ap ≥ φ is the induction in C1(a). ∎

## Frontier map

=== DIRECTION
**Verdict: TRUE, confidence 0.95.**

The evidence comes in three parts.

(a) Hand checks confirm that X(n) − n is not representable for n = 6, 10, 12, 15:
- n = 6: X − n = 49, generators {6, 15, 20}.
- n = 10: X − n = 1043. The gcd tower gives exactly 4·252 + 5·(2·9 − 2 − 9) = 1043.
- n = 12: X − n = 989. It is odd, so it needs an odd number of 495s. The remainder 494 is not in ⟨12, 66, 220⟩.
- n = 15: X − n = 12907. It needs four copies of 3003 (mod 5). The remainder 895 = 5·179 is not in ⟨15, 105, 455⟩.

(b) The value X − n is exactly the Brauer telescopic Frobenius value of the sub-semigroup T = ⟨n, C(n,p^d)⟩. The gcd tower is n → n/p → … → 1, and gcd(n, C(n,p^d)) = n/p^d.

(c) A proof sketch follows; it is detailed under CORE and T1. Its only gap is an elementary binomial inequality, (E), which has not been fully verified.
- Define a digit potential φ on Z/n. For each prime p | n with a = v_p(n), every residue mod p^a is uniquely Σ_{d=1}^a e_d·C(n,p^d) with 0 ≤ e_d < p. This holds because v_p(C(n,p^d)) = a − d exactly: C(n,p^d) = (n/p^d)·C(n−1, p^d − 1), and by Lucas the second factor is ≢ 0 (mod p).
- Set φ_p(r) = Σ_d e_d·C(n,p^d) and φ(r) = Σ_p φ_p(r mod p^a).
- Then φ(0) = 0 and φ(X mod n) = X, since all digits of X equal p−1.
- If φ(r + g) ≤ φ(r) + g holds for every generator g and every r, then induction on representations gives: s ∈ S implies s ≥ φ(s mod n). Since X − n ≡ X (mod n) and X − n < X, it follows that X − n ∉ S.

**Caveat.** The inference "(E) ⇒ step" in (c) and in T1 was derived only in sketch form in this analysis and has not been machine-checked.

=== KNOWN
- If a₁, …, a_k have gcd tower d_j = gcd(a₁..a_j) with d_k = 1, then g(A) ≤ Σ_{j≥2} a_j(d_{j−1}/d_j − 1) − a₁ | Brauer (1942) | gcd-tower reduction.
- Equality holds in the Brauer bound iff a_j/d_j ∈ ⟨a₁/d_{j−1}, …, a_{j−1}/d_{j−1}⟩ (telescopic sequences) | Brauer–Shockley (1962); Kirfel–Pellikaan (1995) | normal form with digits c_j < d_{j−1}/d_j.
- Applied to T = ⟨n, C(n,p^d) : p | n, 1 ≤ d ≤ v_p(n)⟩, the Brauer bound gives exactly X(n) − n. Hence every integer > X − n is in S = ⟨C(n,i)⟩ | standard consequence (presumably the already-formalized half) | gcd tower.
- Kummer: v_p(C(n,i)) = number of carries when adding i and n − i in base p | standard | carries.
- v_p(C(n,i)) ≥ v_p(n) − v_p(i) | standard (i·C(n,i) = n·C(n−1, i−1)) | divisibility.
- Lucas: C(n,i) ≡ Π C(n_k, i_k) (mod p) | standard | digit product.
- v_p(C(n,p^d)) = v_p(n) − d, and v_q(C(n,p^d)) ≥ v_q(n) for primes q ≠ p | standard (Kummer/Lucas) | exact valuations.
- For any finite generating set and modulus m, g(S) = max Ap(S,m) − m, and s ∉ S iff s < min of its class in Ap(S,m) | standard (Apéry; Rosales–García-Sánchez) | Apéry sets.
- Every potential φ: Z/m → ℝ with φ(0) = 0 and φ(r+g) ≤ φ(r)+g for all generators g is a lower bound for the Apéry function | standard (Gomory group relaxation / LP duality) | dual certificate.
- C(n,k) is increasing on k ≤ n/2 and symmetric | standard | monotonicity.
- The full answer to the problem is X(n) − n | the problem as posed (resolution not shown to us) | unknown.

=== BARRIERS
- **Extra generators.** The Brauer/telescopic method sees only T, while S contains every C(n,i). The method proves the upper bound for S, but non-representability needs control of non-tower generators. It does not rule out that those generators are simply too large or too p-divisible to help.
- **Non-tower generators need not be multiples of n.** For example, C(18,6) = 18564 ≡ 6 (mod 18). This defeats the trivial argument "all other C(n,i) ∈ nℤ ⊂ T". It does not rule out a cost argument.
- **The units u_d = C(n,p^d)/p^{a−d} are only controlled mod p.** Since u_d ≡ n/p^a (mod p), p·C(n,p^d) is not a fixed multiple of C(n,p^{d−1}) mod p^a. This defeats closed-form carry bookkeeping. It does not defeat the uniqueness of the triangular digit expansion, which is all the potential needs.
- **A crude per-prime increment bound fails at prime-power indices and their mirrors.** For n = 12, i = 8: 495 < C(12,2) + C(12,4) = 561. This defeats a uniform "C(n,i) ≥ worst digit cost" argument. It does not defeat an exact treatment of i ∈ {p^j, n − p^j}, whose residues are tower digits.
- **Mixed indices (p^α q^β | i) could feed several primes at once.** This defeats prime-by-prime separation without a size estimate. Such i are ≥ lcm ≥ 2·max p^J, so C(n,i) is exponentially larger.

=== CORE
**What remains.** Given KNOWN, the step reduces to the following inequality.

(E) For n not a prime power and 1 ≤ i < n with i ∉ {p^j, n − p^j : p | n, 1 ≤ j ≤ v_p(n)}, write J_p(i) = max(0, v_p(n) − v_p(C(n,i))). Then

  C(n,i) ≥ Σ_{p | n} (p − 1)·Σ_{d=1}^{J_p(i)} C(n, p^d),

together with the carry lemma

  Σ_{d<j} C(n,p^d) ≤ C(n,p^j)·p/(p−1)  for p^j ≤ n/2,

which handles the prime-power generators.

**Why (E) plus the carry lemma suffices.**
- Adding g = C(n,i) changes only the digits e_d with d ≤ J_p(i). So the potential increment is at most (p−1)·Σ_{d≤J} C(n,p^d).
- If J_p(i) > 0, then p^{J_p} divides both i and n − i. In the non-excluded case this gives 2K ≤ i ≤ n − 2K, where K = max_p p^{J_p} ≤ n/4.
- For g = C(n,p^j): if e_j < p − 1, the increment is exactly g. Otherwise the increment is ≤ (p−1)(Σ_{d<j} C(n,p^d) − C(n,p^j)) ≤ g.

**Why it is hard.** Conceptually it is not. It is hard in practice for three reasons:
- the dual certificate had to be found, past the barrier that extra generators are invisible to the gcd tower;
- (E) needs uniform binomial ratio estimates (C(n,2K)/C(n,K) ≥ C(3K,K)/C(2K,K) ≈ (27/16)^K) plus a finite check at small K;
- in Lean, the digit expansion mod p^a, CRT gluing over primeFactors, and Kummer valuations are all heavy.

=== TARGET T1
TYPE: REDUCTION
STATEMENT: Define φ as in DIRECTION. If φ(r + C(n,i)) ≤ φ(r) + C(n,i) for all r ∈ Z/n and all 1 ≤ i < n, then ¬Rep(n, X − n). Moreover, the hypothesis follows from (E) plus the carry lemma.
BEYOND: Brauer–Shockley handle only telescopic generators. This certificate handles the arbitrary extra generators C(n,i).
VALUE: It reduces CORE to explicit binomial inequalities.
SIGNIFICANCE: 2
TEST: For n ≤ 200, compute Ap(S,n) by Dijkstra on Z/n and compare with φ pointwise.

=== TARGET T2
TYPE: SPECIAL
STATEMENT: The step holds for squarefree non-prime n. Here every a_p = 1, each φ_p has a single digit, and (E) becomes C(n,i) ≥ Σ_{p | gcd(i,n), p ∤ C(n,i)} (p−1)·C(n,p) for i ∉ {p, n − p}.
BEYOND: No case is covered beyond hand checks.
VALUE: It handles the base case with no carries and serves as a template for the Lean CRT plumbing.
SIGNIFICANCE: 1
TEST: Brute-force the Frobenius number for squarefree n ≤ 100.

=== TARGET T3
TYPE: SPECIAL
STATEMENT: The step holds for n = p^a·q^b with two primes.
BEYOND: This adds carry structure at two primes. It is not covered by T2.
VALUE: The general case is the same argument with more primes.
SIGNIFICANCE: 1
TEST: Brute-force for n ≤ 300 of this form.

=== TARGET T4
TYPE: STRUCTURE
STATEMENT: Ap(S,n) = {Σ_{p,d} e_{p,d}·C(n,p^d) : 0 ≤ e_{p,d} < p}. Equivalently, the Apéry function equals φ.
BEYOND: This is the exact Apéry set, not just its maximum.
VALUE: It implies CORE, and also gives the genus formula of S.
SIGNIFICANCE: 2
TEST: Dijkstra mod n for n ≤ 500.

=== TARGET T5
TYPE: QUANT
STATEMENT: For K ≥ 2 and n ≥ 4K, C(n,2K) ≥ (2K)·C(n,K). Also C(n,p^{d+1}) ≥ 2·C(n,p^d) whenever p^{d+1} ≤ n/2.
BEYOND: This makes the ratio C(3K,K)/C(2K,K) explicit, with no constants found in the literature.
VALUE: It is the analytic input to (E). Note Σ(p−1) over primes dividing K' is ≤ lcm.
SIGNIFICANCE: 1
TEST: Check all n ≤ 10⁴ numerically.

=== TARGET T6
TYPE: CONDITIONAL
STATEMENT: No standard named conjecture is relevant. Instead: the full step holds conditional on (E) for all n ≤ N₀ (a finite computation), given T5 for n > N₀.
BEYOND: This replaces infinitely many cases with a decidable finite check.
VALUE: It gives a Lean route of `decide`/`native_decide` for small n plus an analytic tail.
SIGNIFICANCE: 1
TEST: Run (E) over n ≤ 2000.

=== TARGET T7
TYPE: NEGATIVE
STATEMENT: Two naive routes provably fail. First, the trivial route "C(n,i) ∈ nℤ for non-prime-power i" fails at n = 18, i = 6. Second, the uniform increment bound fails at n = 12, i = 8.
BEYOND: It documents exactly why the exceptional set in (E) is needed.
VALUE: It prevents the team from wasting effort on these routes.
SIGNIFICANCE: 1
TEST: Direct arithmetic.

=== TARGET T8
TYPE: ANALOGUE
STATEMENT: For any finite A ⊂ ℕ containing a tower a₁ = m, a_{p,d} with v_p(a_{p,d}) = v_p(m) − d, let J_p(x) = max(0, v_p(m) − v_p(x)). Suppose every other x ∈ A satisfies x ≥ Σ_p (p−1)·Σ_{d≤J_p(x)} a_{p,d}. Then g(A) = Brauer value.
BEYOND: This is a new sufficient condition for Brauer-bound sharpness with non-telescopic extras.
VALUE: It packages the proof abstractly, which simplifies the Lean work.
SIGNIFICANCE: 2
TEST: Run random instances.

=== TARGET T9
TYPE: STRUCTURE
STATEMENT: Every s ∈ S with s ≡ X (mod n) and s < X + min_{i non-tower} C(n,i) has all of its representations supported only on prime-power and mirrored indices.
BEYOND: This describes near-extremal representations.
VALUE: It gives a contrapositive form usable in an induction proof.
SIGNIFICANCE: 1
TEST: Enumerate for n ≤ 60.

=== TARGET T10
TYPE: QUANT
STATEMENT: The genus of S equals Σ_{r ∈ Z/n} φ(r)/n − (n−1)/2 (Selmer's formula combined with T4).
BEYOND: No genus formula for the binomial semigroup is known.
VALUE: It is a corollary-level strengthening that checks T4.
SIGNIFICANCE: 2
TEST: Count gaps for n ≤ 100.

=== ANGLE A1
TECHNIQUE: Gomory group-relaxation dual certificate (digit potential).
IDEA: Use φ = Σ_p φ_p from the triangular base {C(n,p^d)} mod p^a. Verify the subadditivity φ(r+g) − φ(r) ≤ g for each generator class: n, prime-power indices and their mirrors, and the rest.
BARRIERS: It beats the extra-generators barrier because it bounds the cost of all generators, not just the tower. The unit mismatch is irrelevant because only uniqueness of digits is used.
FIRST STEP: Prove the lemma that for p^a ‖ n, the map {0..p−1}^a → Z/p^a, e ↦ Σ e_d·C(n,p^d), is a bijection.

=== ANGLE A2
TECHNIQUE: Kummer carry counting.
IDEA: Bound J_p(i) = v_p(n) − (#carries of i + (n−i) in base p). Then J_p(i) ≤ min(v_p(i), v_p(n−i)), which forces 2p^J ≤ i ≤ n − 2p^J outside the exceptional set.
BARRIERS: This is what defeats the mixed-index barrier.
FIRST STEP: Prove that if J_p(i) ≥ 1 then p^{J_p(i)} | i and p^{J_p(i)} | n − i.

=== ANGLE A3
TECHNIQUE: Binomial ratio analysis.
IDEA: Show C(n,2K)/C(n,K) is increasing in n and at least C(3K,K)/C(2K,K) ≥ 2.5 for K ≥ 2, growing exponentially. Combine with Σ(p−1) ≤ K to get (E).
BARRIERS: This is pure size; it is unaffected by the arithmetic barriers.
FIRST STEP: Prove C(n,2K) = C(n,K)·C(n−K,K)/C(2K,K) and C(n−K,K) ≥ C(3K,K) for n ≥ 4K.

=== ANGLE A4
TECHNIQUE: Gluing of numerical semigroups (Rosales–Delorme).
IDEA: Write T as an iterated gluing along the gcd tower. Show each extra C(n,i) lies in T and is "absorbed" by Apéry minimality in each gluing step.
BARRIERS: It must beat the non-multiple-of-n barrier. Membership C(n,i) ∈ T is plausible because the extras are large.
FIRST STEP: Prove C(n,i) ∈ T for every non-tower index i when n ≤ 100.

=== ANGLE A5
TECHNIQUE: Hilbert series evaluated at roots of unity.
IDEA: Compare Σ_{s∈S} x^s with Π(1 − x^{C(n,p^d)})-based telescopic series. Show the difference vanishes in the residue class of X below X.
BARRIERS: There is no clean product formula with extras, so this is risky.
FIRST STEP: Compute the Hilbert series of T for n = 12 and check that it equals that of S.

=== ANGLE A6
TECHNIQUE: Lean engineering via a finite check plus a tail.
IDEA: Prove the abstract T8 theorem once. Discharge (E) for small n with `decide` over explicit bounds, and use A3 for large K.
BARRIERS: The barrier is formalization cost, not mathematics. Retrieve Mathlib's Kummer and Lucas lemmas by search rather than guessing their names.
FIRST STEP: State the T8 lemma in Lean with A, the tower and φ as parameters, and prove the induction "s ∈ S ⇒ s ≥ φ(s mod n)".

## Deep dive

GOAL: **Statement to prove.** Let n ≥ 2 with n not a prime power, let a_p = v_p(n), and let

  X(n) = Σ_{p | n} (p−1) Σ_{d=1}^{a_p} C(n, p^d).

Then X(n) − n is not of the form Σ_{1≤i<n} c_i C(n,i) with c_i ∈ ℕ.

First action: read the exact Lean statement (presumably `erdos_27285_hyp_top` or the non-representability lemma it feeds) and match it literally. It may be phrased as this non-membership, as the potential hypothesis of r1s3/C1(a), or as (E) itself. The plan below proves all three in sequence, so it covers every phrasing.

**Why 2–3.** Together with the already-formalized Brauer upper bound, this step gives g(S) = X(n) − n, which answers the whole problem.

- The answer itself was reportedly found recently, so the value is not new.
- A complete, machine-checked proof by an explicit dual certificate is still new. That certificate is the digit potential plus the inequality (E).
- An expert would rate this 2 as an independent verified proof of a just-resolved problem, and possibly 3 if the certificate argument is new.
