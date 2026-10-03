# Research engine: problem 156, run 20261002-214504-015603-erdos156

Spend $28.3948; 35 claim(s); 2 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] deep/C1 PROVED ANALOGUE
**Statement.** Let q ≥ 160 be a prime power and 1 ≤ m ≤ q/2. Then Z_{m(q²+q+1)} contains a maximal Sidon set of size q+m. More generally, for any fixed c < (√17−3)/2 = 0.5616, the same holds for m ≤ cq once q ≥ q₀(c). With m = ⌊q/2⌋, |A|/n^{1/3} → 1.5/2^{−1/3} = 1.890. This is the optimum of (1+c)/c^{1/3} over the whole family.
**Beyond.** improves C1's constant from 1.942 to 1.890. The method shows that the pair constraint x_i + x_{−i} ∉ Y+Y, which costs h/2 in C1, costs nothing when the pair is chosen jointly. What remains is the load from 3- and 4-term relations, ≈ (1.5c + 0.5c²)h. This isolates exactly what a proof of C2 (c = 1) must beat.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "I know of no published explicit-constant construction of small maximal Sidon sets in cyclic groups Z_{m(q^2+q+1)}; the closest work (Redman–Rose–Walker, Nagy) is in F_2^n, and Nagy's saturation papers should be checked for a cyclic version. But O(n^{1/3}) for this family was already the team's C1, so this only improves a constant (1.942→1.890) in an analogue that the wrap-around barrier keeps from transferring to [N].", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "I know of no published explicit-constant construction of small maximal Sidon sets in cyclic groups Z_{m(q^2+q+1)}; the closest work (Redman–Rose–Walker, Nagy) is in F_2^n, and Nagy's saturation papers should be checked for a cyclic version. But O`
**Proof or evidence.**

The notation, Y, Lemmas 1–2 and the half-sum fact are as in C1. The fact is that each coset of H contains at most one root of 2z = s, because h is odd.
Order:
- If m is even, first choose x_{m/2}. The only constraint is 2z ∉ Y+Y, which excludes ≤ (q+1)(q+2)/2 < h values.
- Then process the pairs {i, −i} (i ≠ −i) one at a time.
Pair step. C is the set of chosen cosets, closed under negation, with t = |C| ≤ m−3. A = Y ∪ X_C is Sidon.
Single-element bounds. Let G₁ (resp. G₂) be the set of z in coset i (resp. −i) addable to A. Repeat C1's count, but drop the |Y+Y| term:
- the (Y,Y; c ∈ X) term needs x_{−i}, which is not chosen;
- the (Y,Y) half-sum term needs 2i = 0, which is false.
Hence |G₁|, |G₂| ≥ g := h − (q+1)(3t+4)/2 − (t+1)(t+2)/2.
Joint relations. A nontrivial relation in A ∪ {u,v} that uses both u ∈ coset i and v ∈ coset −i has one of the following forms. The list is complete by counting occurrences (#u, #v) ∈ {(1,1), (2,1), (1,2), (2,2)}; the others force u = v or u, v ∈ A.
- (c1) u + v ∈ A+A. Here π(u+v) = 0, so u+v ∈ (Y+Y) ∪ E, where E = {x_j + x_{−j} : j ∈ C} and |E| ≤ t/2 + 1.
- (c2) u − v ∈ (A−A) ∩ π^{−1}(2i). This set is {x_j − x_k : j−k = 2i} ∪ (x_{2i} − Y) ∪ (Y − x_{−2i}), of size ≤ t + 2(q+1).
- (c3) 2u − v ∈ A ∩ π^{−1}(3i), of size ≤ q+1.
- (c4) 2v − u ∈ A ∩ π^{−1}(−3i), of size ≤ q+1.
- (c5) 2u = 2v.
Counting bad pairs (u, v) ∈ G₁×G₂:
- (c1) with E, (c2), (c3) and (c5): for fixed u, each excludes a bounded number of v.
- (c4): for fixed v, it excludes ≤ q+1 values of u.
- Total ≤ K(|G₁| + |G₂|) with K = 1.5t + 3q + 5.
The (c1) part with Y+Y, by Fourier analysis:
- Parametrise u = u₀ + ma and v = v₀ + mb (a, b ∈ Z_h), and write u₀ + v₀ = mc₀.
- Then u + v ∈ Y+Y ⇔ a + b ∈ T := (S+S) − c₀.
- Let P, Q ⊂ Z_h be the parameter sets of G₁, G₂. Then #{(a,b) ∈ P×Q : a+b ∈ T} ≤ |P||Q||T|/h + M√(|P||Q|), where M = max_{ξ≠0} |1̂_T(ξ)|. This is the standard bound via Fourier inversion, Cauchy–Schwarz and Parseval.
- Since S is Sidon, 1_{S+S} = (1_S∗1_S + 1_{2·S})/2. For a planar difference set |Ŝ(ξ)|² = q for ξ ≠ 0, and 2ξ ≠ 0 because h is odd. So M ≤ (q+√q)/2.
Combining. Put α := 1 − |T|/h = (q²−q)/(2h) ≥ (q−2)/(2q). Then
#good pairs ≥ α|G₁||G₂| − M√(|G₁||G₂|) − K(|G₁|+|G₂|) ≥ max(|G₁|,|G₂|)·(αg − M − 2K).
This is positive if αg > (q+√q)/2 + 3t + 6q + 10. A good pair keeps A Sidon, and after all steps Lemma 2 gives maximality.
Verification of the inequality for m ≤ q/2 (so t ≤ q/2):
- g ≥ q²+q+1 − (q+1)(1.5q+4)/2 − (q/2+1)(q/2+2)/2 = 0.125q² − 2.5q − 2.
- RHS ≤ 8q + 0.5√q + 10.
- At q = 160: LHS ≥ 2798·(158/320) = 1381.5 > 1296.3 ≥ RHS.
- For q ≥ 160 the difference LHS − RHS is increasing: d/dq LHS ≥ 0.125q − 1.5 > 8.1 ≥ d/dq RHS.
- So every m ≤ q/2 works for all q ≥ 160.
For general c the leading-order condition is 1 − 1.5c − 0.5c² > 0, i.e. c < 0.5616. t5.py evaluates the exact inequality: m_max/q = 0.54 (q = 300), 0.555 (q = 1000), 0.5615 (q = 10⁵).

## [validated-new] r2s3/C1 PROVED QUANT
**Statement.** Let m(N) = minMaximalSidonSet(N). Then liminf_{N→∞} m(N)³/N ≥ 2/0.981, so m(N) ≥ (1.2679 − o(1)) N^{1/3}.
**Beyond.** improves KNOWN "(1−o(1))(2N)^{1/3}" (constant 1.2599) to 1.2679. It also identifies the exact continuum constant (2/c*)^{1/3}
of the triple-counting method, which no linear (single test function) argument can improve; see Dead ends.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No published improvement of the (2N)^{1/3} counting lower bound for minimal maximal Sidon sets is known to me, so raising the constant to ~1.2679 appears new. But it only sharpens the easy lower bound and does not touch the open upper-bound question of whether O(N^{1/3}) is achievable.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published improvement of the (2N)^{1/3} counting lower bound for minimal maximal Sidon sets is known to me, so raising the constant to ~1.2679 appears new. But it only sharpens the easy lower bound and does not touch the open upper-bound question of whether O(N^{1/3}) is achievable."}, {"verdict": "new", "cite": null, "significance": 1, "why": "No published improvement of the`
**Proof or evidence.**

Step 0 (blocking). Let A ⊆ [N] be maximal Sidon with |A| = k, and let x ∈ [N]∖A. Then A∪{x} has a nontrivial
relation involving x. Either x+a = b+c, giving x = b+c−a (an ordered triple in A³), or 2x = b+c with b ≠ c.
(The cases x+x = x+a and x+a = x+b are trivial or force x ∈ A.)
Step 1 (discrete inequality). Put μ_N = (1/k)Σ_{a∈A} δ_{a/N}, and let ν_N be the law of (a+b−c)/N with (a,b,c) uniform in A³,
so ν_N = μ_N*μ_N*μ̃_N. Fix a closed interval J = [s,t] ⊆ [0,1]. The integers x ∈ [1,N] with x/N ∈ J number at least N|J| − 2.
Each such x lies in A (at most k of them), or is a midpoint (at most k² of them), or equals b+c−a. The number of distinct
values b+c−a is at most the number of triples ({b,c} unordered, a), which is ≤ (k³ν_N(J) + k²)/2.
Hence ν_N(J) ≥ (2N|J| − 4 − 2k − 3k²)/k³.
Step 2 (compactness). Suppose L := liminf m(N)³/N < 2/0.981. L ≥ 2 by KNOWN, so k → ∞. Take N_i with k_i³/N_i → L,
where A_i is a minimum maximal set. Then ν_i(J) ≥ (2/L)|J| − o(1) for each fixed closed J. Pass to a further subsequence
with μ_i → μ weakly (Prokhorov; everything is supported on [0,1]). Characteristic functions converge pointwise, so
ν_i → ν := μ*μ*μ̃ weakly (Lévy). Portmanteau for closed J gives ν(J) ≥ limsup ν_i(J) ≥ α|J| with α = 2/L > 0.981.
This holds for every closed interval J ⊆ [0,1]. By inner approximation it also holds for open intervals, hence (countable
disjoint unions) for open sets U ⊆ (0,1), hence by outer regularity for every Borel E ⊆ [0,1]. Indeed ν(E) = inf ν(U) ≥ λ(E).
So ρ := ν − α·λ|_[0,1] is a nonnegative measure of mass ε := 1−α < 0.019. Here λ is Lebesgue measure.
Step 3 (Fourier zero). Let X,Y,Z be iid with law μ, S = X+Y−Z ~ ν, and φ(ξ) = E e^{iξX}. Then E e^{iξS} = φ(ξ)² conj(φ(ξ)),
so |ν̂(ξ)| = |φ(ξ)|³. The transform of λ|_[0,1] is (e^{iξ}−1)/(iξ), which vanishes at ξ = 2π. Hence |φ(2π)|³ = |ρ̂(2π)| ≤ ε.
Step 4 (variance). S ∈ [−1,2], so |S−½| ≤ 3/2. We have E(S−½)² = α/12 + ∫(t−½)²dρ ≤ α/12 + 9ε/4 =: B, and
|τ| := |ES − ½| = |∫(t−½)dρ| ≤ 3ε/2. Put σ² = Var X and W = X − ½ ∈ [−½,½]. Then E(S−½)² = 3σ² + τ² (ES = EX), so
EW² = σ² + τ² ≤ (B−τ²)/3 + τ² ≤ α/36 + 3ε/4 + 1.5ε² =: s(ε). This is increasing in ε on [0, 0.019], so s(ε) ≤ s0 := s(0.019) = 0.0420415.
Step 5 (convexity). g(u) = cos(2π√u) is convex on [0,¼]. Proof: g''(u) = −(2π/(4u^{3/2}))·(t cos t − sin t) with t = 2π√u ∈ [0,π],
and t cos t − sin t ≤ 0 there. g is also decreasing there. Since W² ∈ [0,¼], Jensen gives
|φ(2π)| ≥ Re(e^{−iπ}φ(2π)) = E cos(2πW) = E g(W²) ≥ g(EW²) ≥ g(s0) = cos(2π·0.205040) = 0.2787.
Step 6. Then 0.2787 ≤ |φ(2π)| ≤ ε^{1/3} < 0.019^{1/3} = 0.2668, a contradiction. Hence L ≥ 2/0.981, i.e. m(N) ≥ ((2/0.981)^{1/3} − o(1))N^{1/3}
and (2/0.981)^{1/3} = 1.26800. ∎
(The threshold of this exact argument is ε* ≈ 0.01974. We use 0.019 for margin.)

## [valid-routine] deep/C1 PROVED ANALOGUE
**Statement.** Let q be a prime power, h = q²+q+1, and m ≥ 1 an integer with m² + 3mq + 2m < q² + q + 2. For instance any m ≤ 3q/10 qualifies. Then Z_n, n = mh, contains a maximal Sidon set A with |A| = m + q. (Sidon in the group sense: a+b = c+d implies {a,b} = {c,d}, including 2a = c+d. Maximal means A ∪ {z} is not Sidon for every z ∉ A.) In particular, for m = ⌊3q/10⌋ we get |A|/n^{1/3} → 1.3/0.3^{1/3} = 1.942.
**Beyond.** KNOWN lists "Cyclic analogue: maximal Sidon sets of size O(n^{1/3}) in Z_n for n = m(q²+q+1)" as blackboard (unverified). This is a complete proof with explicit constants, and the hypotheses are checked. Novelty against the external literature could NOT be checked: there is no internet in the sandbox. I do not recall a published cyclic O(n^{1/3}) construction, but it may be folklore.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "Take a Singer difference set in the index-m subgroup Z_h of Z_{mh}, which blocks its own coset and, via its differences, every coset that A meets; then add a greedily chosen Sidon transversal of the other cosets. This is a short standard counting argument that experts would treat as folklore. It uses the cyclic subgroup structure that the integer problem lacks, so it does not touch the wrap-around barrier.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "Take a Singer difference set in the index-m subgroup Z_h of Z_{mh}, which blocks its own coset and, via its differences, every coset that A meets; then add a greedily chosen Sidon transversal of the other cosets. This is a short standard counting arg`
**Proof or evidence.**

Setup. π: Z_n → Z_m, π(z) = z mod m. Its kernel is H = mZ_n, cyclic of order h, and s ↦ ms is an isomorphism Z_h → H. Let S ⊂ Z_h be a Singer perfect difference set: |S| = q+1, and every nonzero residue mod h is s−s′ for exactly one pair (s, s′) ∈ S². Put Y = mS ⊂ H. Then:
- Y is Sidon in Z_n, because ms₁+ms₂ = ms₃+ms₄ in Z_n ⇔ s₁+s₂ ≡ s₃+s₄ (mod h), and a perfect difference set is Sidon.
- Y − Y = H, with every element of H∖{0} represented.
- |Y+Y| = (q+1)(q+2)/2.

Lemma 1 (addability). Let A be Sidon and z ∉ A. Then A∪{z} is Sidon iff z ∉ A+A−A and 2z ∉ A+A.
Proof. Consider a nontrivial relation in A∪{z} that uses z. If z occurs once, it reads z+c = a+b, so z = a+b−c. If z occurs twice on one side, it reads 2z = a+b. If z occurs on both sides, then z+c = z+d forces c = d, which is trivial. Three occurrences give z ∈ A. Conversely, z = a+b−c gives z+c = a+b, and this is nontrivial because z ∉ {a,b} ⊂ A. Likewise 2z = a+b is nontrivial because z ∉ A. ∎

Lemma 2 (certificate). Suppose A = Y ⊔ X is Sidon, where X contains exactly one element x_i of each coset π^{-1}(i), i ≠ 0. Then A is maximal.
Proof. Let z ∉ A.
- If π(z) = 0, pick any y ∈ Y. Then z−y ∈ H∖{0} = Y−Y, so z−y = y′−y″ with y′ ≠ y″, i.e. z + y″ = y + y′. This relation is nontrivial because z ∉ Y.
- If π(z) = i ≠ 0, then z ≠ x_i, so z − x_i ∈ H∖{0} and z − x_i = y′−y″. Hence z + y″ = x_i + y′, which is nontrivial because z ∉ {x_i, y′}.
In both cases A∪{z} is not Sidon. ∎

Greedy step. Process the cosets i = 1, …, m−1 in any order. Let C be the set of already-processed cosets, so t = |C| ≤ m−2, and let A = Y ∪ {x_j : j ∈ C}, which is Sidon. We bound the number of z ∈ π^{-1}(i) that are not addable, i.e. z ∈ A+A−A or 2z ∈ A+A (Lemma 1). Classify the triples (a, b, c), with {a,b} unordered, satisfying π(a)+π(b)−π(c) = i:
- a, b, c ∈ Y: then π-sum = 0 ≠ i. No values.
- a, b ∈ Y, c ∈ X: then c = x_{−i}. At most |Y+Y| = (q+1)(q+2)/2 values. (If −i = i, then c = x_i is not yet chosen, so there are 0 values.)
- exactly one of a, b in X, the other in Y, and c ∈ Y: then π(a) = i, which is not yet chosen. 0 values.
- one of a, b in X, the other in Y, and c ∈ X: then j − k = i with j, k ∈ C. There are at most t such ordered pairs, since k determines j. Each gives the q+1 values x_j − x_k + Y. Total ≤ t(q+1).
- a, b ∈ X, c ∈ Y: then j + l = i with j, l ∈ C, {j,l} unordered. At most (t+2)/2 pairs: the involution j ↦ i−j has at most 2 fixed points. Each gives q+1 values. Total ≤ (t+2)(q+1)/2.
- a, b, c ∈ X: for each k ∈ C there are at most (t+2)/2 pairs {j,l} with j+l = i+k. Total ≤ t(t+2)/2.
Half-sums 2z = a+b with π(z) = i. Since h is odd, each coset contains at most one solution of 2z = s:
- if n is odd, doubling is bijective;
- if m is even, the two roots differ by n/2 = (m/2)h, and π(n/2) = m/2 ≠ 0.
Classify:
- a, b ∈ Y: only if 2i ≡ 0, i.e. i = m/2. At most (q+1)(q+2)/2 values. This case and the c = x_{−i} case above never occur together, since −i = i there.
- a ∈ X, b ∈ Y: π(a) = 2i, so at most q+1 values.
- a, b ∈ X: at most (t+2)/2 values.
Total. With t ≤ m−2, the number of non-addable z in the coset is at most
(q+1)(q+2)/2 + (m−2)(q+1) + m(q+1)/2 + (m−2)m/2 + (q+1) + m/2 = [(q+1)(q+3m) + m(m−1)]/2.
This is < h = q²+q+1 ⇔ m² + 3mq + 2m < q² + q + 2. For m ≤ 3q/10 the left side is ≤ 0.99q² + 0.6q < q² + q + 2. So an addable x_i exists, and after m−1 steps Lemma 2 applies. Finally |A| = (q+1) + (m−1) = q + m. ∎
Numerical check (t1.py, primes q ≤ 23, several m including m > 3q/10): every output was verified by brute force to be Sidon and maximal (every z ∉ A blocked).

## [valid-routine] deep/C3 PROVED STRUCTURE
**Statement.** In Z_{q³−1}, let B = {log_g(θ+a) : a ∈ F_q}. Then the Singer set used for C1/C2 with m = q−1 is exactly Y = (q−1)·B ∪ {0}, the dilate by the non-unit multiplier q−1. Multiplicatively, Y = {(θ+a)^{q−1}} ∪ {1}, the image of the Singer line in the norm-one subgroup K = ker N_{F_{q³}/F_q} of order q²+q+1.
Moreover, every Sidon A ⊇ Y satisfies A ∩ H = Y and |A ∩ (x+H)| ≤ 1 for every coset x+H ≠ H. Hence every maximal Sidon set containing Y has size ≤ q+1+(m−1). It has size exactly q+m iff it contains a full transversal, and a full Sidon transversal is always maximal (Lemma 2).
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Singer 1938; Bose 1942 (Bose sets as projections of Singer lines, PG(2,q) = F_{q^3}^*/F_q^*); Halberstam–Roth, Sequences", "why": "Identifying (q−1)·B ∪ {0} with a Singer line in the norm-one subgroup is the classical Bose/Singer correspondence, and the coset/transversal statements follow in one line from Y being a perfect difference set in H. It concerns only the cyclic analogue and gives no progress on the interval problem.", "panel": [{"verdict": "routine", "cite": "Singer 1938; Bose 1942 (Bose sets as projections of Singer lines, PG(2,q) = F_{q^3}^*/F_q^*); Halberstam–Roth, Sequences", "significance": 0, "why": "Identifying (q−1)·B ∪ {0} with a Singer line in the norm-one subgroup is the classical Bose/Singer correspondence, and the co`
**Proof or evidence.**

- (q−1)·log(θ+a) = (q−1)·(log(θ+a) mod h), because (q−1)h = n. The residues log(θ+a) mod h, together with 0 = log 1, are the projective points of the F_q-span of 1 and θ, which is a line, i.e. a Singer set S. So (q−1)B ∪ {0} = mS with m = q−1.
- If a ≠ a′ lie in the same coset of H, then a−a′ ∈ H∖{0} = Y−Y, say a−a′ = y−y′, so a + y′ = a′ + y. This is a nontrivial relation unless {a, y′} = {a′, y}, i.e. a = y and a′ = y′. That can only happen in the coset H itself. In H, A ∩ H is Sidon, contains Y, and Y is a maximal Sidon subset of H (Lemma 2 with m = 1). Hence A ∩ H = Y. ∎
Remark: r1s2/C2(b) studied only unit multipliers t, i.e. B ∪ tB with gcd(t, n) = 1. The useful multiplier is the non-unit t = q−1, which collapses B onto the subgroup K. There the blocking is an exact coset tiling X + H = G rather than a discriminant half-cover (r1s2 C2(a)).

## [valid-routine] deep/C4r PROVED NEGATIVE
**Statement.** **Setting.**
- Let q be a prime power with **q ≥ 3** and gcd(3, q−1) = 1, i.e. q ≢ 1 (mod 3).
- Let θ ∈ F_{q³} ∖ F_q. Then F_{q³} = F_q(θ), and 1, θ, θ² is an F_q-basis.
- Let N : F_{q³}^* → F_q^* be the norm, N(u) = u^{1+q+q²}, and put K = ker N.
- Put ρ(u) = u^{q−1} and y_a := ρ(θ+a) for a ∈ F_q.
- Put Y = {y_a : a ∈ F_q} ∪ {1}.
- For an injective map r : F_q^*∖{1} → F_q, put x_λ := λ·ρ(θ − r(λ)) for λ ∈ F_q^*∖{1}, and X_r := {x_λ}.

**Definitions.**
- A subset S of an abelian group is *Sidon* if s₁s₂ = s₃s₄ with all s_i ∈ S implies {s₁,s₂} = {s₃,s₄} as multisets.
- A *violation* is an unordered pair of distinct 2-element multisets from S with equal products.

**Claim.**
0. F_{q³}^* = F_q^* × K (internal direct product). Y is a Sidon set of size q+1 in K, the Singer set.
1. X_r consists of q−2 distinct elements and is a transversal of the nontrivial cosets of K. Moreover, X_r ∩ Y = ∅.
2. The only nontrivial relations s₁s₂ = s₃s₄ in S = X_r ∪ Y are, up to swapping the two sides and reordering within each side,

  x_λ · x_{1/λ} = ψ(x_λ) · ψ(x_{1/λ}), with ψ(x_λ) := ρ(θ − r(λ)) ∈ Y, for λ ∈ F_q^*∖{1}.

  In particular, S has:
  - no nontrivial relation of the forms xx′ = x″y, xx′ = x″x‴, xy = x′y′, xy = y′y″, or yy′ = y″y‴;
  - for each λ, exactly one representation of x_λx_{1/λ} as a product of two elements of Y.
3. The number of violations equals the number of orbits of λ ↦ 1/λ on F_q^*∖{1}:
  - (q−1)/2 if q is odd;
  - (q−2)/2 if q is even.

  Since q ≥ 3, this number is ≥ 1, so X_r ∪ Y is never Sidon. (For q = 2, X_r = ∅ and X_r ∪ Y = Y is Sidon.)
**Beyond.** this pinpoints why the algebraic route to C2 fails. The B₃ structure kills exactly the expensive constraints, the 3- and 4-term relations, which carry ≈ 2h load in the union bound. It violates exactly the cheap pair constraints, which C1′ handles at no cost by Fourier pairing. The two mechanisms are incompatible, because modifying any x_λ destroys the polynomial-identity structure.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Singer (1938) / Bose–Chowla difference-set structure; decomposition F_{q^3}^* = F_q^* × K when gcd(3,q−1)=1", "why": "Projecting to the F_q^* × K components and using the Sidon property of the Singer set gives every case in a few lines, and the violations are just the identity λ·λ^{-1}=1. It is a negative result about one bespoke construction and bears little on the actual problem.", "panel": [{"verdict": "routine", "cite": "Singer (1938) / Bose–Chowla difference-set structure; decomposition F_{q^3}^* = F_q^* × K when gcd(3,q−1)=1", "significance": 0, "why": "Projecting to the F_q^* × K components and using the Sidon property of the Singer set gives every case in a few lines, and the violations are just the identity λ·λ^{-1}=1. It is a neg`
**Proof or evidence.**

**Step 0: the direct product decomposition.**
- For c ∈ F_q^*, N(c) = c³.
- Cubing is a bijection of F_q^* because gcd(3, q−1) = 1. Hence F_q^* ∩ K = {1}.
- N is surjective onto F_q^*, so |K| = (q³−1)/(q−1).
- Therefore |F_q^*|·|K| = |F_{q³}^*|, and F_{q³}^* = F_q^* × K. Let π₁, π₂ be the two projections; both are homomorphisms.

**Step 1: the map ρ.**
- ρ(u) = 1 iff u ∈ F_q^*.
- N(ρ(u)) = N(u)^{q−1} = 1, so ρ maps into K.
- |im ρ| = (q³−1)/(q−1) = |K|, so ρ : F_{q³}^* → K is surjective with kernel F_q^*.

**Step 2: Y has size q+1.**
Let L = {θ+a : a ∈ F_q} ∪ {1}, so that Y = ρ(L). Suppose ℓ, ℓ′ ∈ L and ρ(ℓ) = ρ(ℓ′). Then ℓ = cℓ′ for some c ∈ F_q^*. Compare θ-coefficients in the basis 1, θ:
- If ℓ = θ+a, then cℓ′ must be θ+b with c = 1, so a = b.
- If ℓ = 1, then ℓ′ is constant, so ℓ′ = 1.

Hence ρ is injective on L. Note that θ+a ∉ F_q, so y_a ≠ 1. Thus |Y| = q+1.

**Step 3: Y is Sidon.**
- Write each ℓ_i ∈ L as f_i(θ) with f_i ∈ {T+a} ∪ {1} ⊂ F_q[T]. Every f_i is monic of degree ≤ 1.
- Suppose ρ(ℓ₁)ρ(ℓ₂) = ρ(ℓ₃)ρ(ℓ₄). Then ℓ₁ℓ₂ = cℓ₃ℓ₄ for some c ∈ F_q^*.
- So f₁f₂ − cf₃f₄ has degree ≤ 2 and vanishes at θ. The minimal polynomial of θ has degree 3, so f₁f₂ = cf₃f₄ in F_q[T].
- Comparing leading coefficients of these monic polynomials gives c = 1.
- By unique factorization in F_q[T], the multisets of monic linear factors agree, and then the number of factors equal to 1 agrees as well. Hence {f₁,f₂} = {f₃,f₄}.
- By Step 2, this gives {ρ(ℓ₁),ρ(ℓ₂)} = {ρ(ℓ₃),ρ(ℓ₄)}.

This proves item 0.

**Step 4: components of the elements of S.**
- θ − r(λ) ≠ 0, so ρ(θ−r(λ)) ∈ Y ⊂ K.
- Hence π₁(x_λ) = λ ≠ 1 and π₂(x_λ) = y_{−r(λ)} =: ψ(x_λ).
- For y ∈ Y, π₁(y) = 1 and π₂(y) = y. Set ψ(y) = y.
- So ψ := π₂|_S maps S into Y.

**Step 5: item 1.**
- x_λK = λK. Distinct λ give distinct cosets, and the cosets of K are exactly cK for c ∈ F_q^*. So X_r is a transversal of the nontrivial cosets, and |X_r| = q−2.
- X_r ∩ K = ∅ while Y ⊂ K, so X_r ∩ Y = ∅.

**Step 6: fibers of ψ.**
- ψ is injective on X_r, because r is injective and a ↦ y_a is injective by Step 2.
- So the fiber of ψ over y_a is {y_a} ∪ {x_λ : r(λ) = −a}, which has size 1 or 2.
- The fiber over 1 is {1}.
- Two distinct elements of one fiber are therefore of the form {y, x_λ}, and they have π₁-values 1 ≠ λ.

**Step 7: item 2 (classification of relations).**
Let s₁s₂ = s₃s₄ with s_i ∈ S and {s₁,s₂} ≠ {s₃,s₄}. Apply π₂ and π₁:
- π₂ gives ψ(s₁)ψ(s₂) = ψ(s₃)ψ(s₄). Since Y is Sidon, after swapping s₃ and s₄ we may assume ψ(s₁) = ψ(s₃) and ψ(s₂) = ψ(s₄).
- π₁ gives π₁(s₁)π₁(s₂) = π₁(s₃)π₁(s₄).

Now split into cases:
- **s₁ = s₃ and s₂ = s₄.** The relation is trivial, which is excluded.
- **s₁ = s₃ and s₂ ≠ s₄.** Cancelling gives π₁(s₂) = π₁(s₄). But s₂ and s₄ are distinct elements of one fiber, which is impossible by Step 6.
- **s₁ ≠ s₃ and s₂ = s₄.** Impossible by the symmetric argument.
- **s₁ ≠ s₃ and s₂ ≠ s₄.** Then {s₁,s₃} = {x_λ, y} and {s₂,s₄} = {x_μ, y′}, where y = ψ(x_λ) and y′ = ψ(x_μ). There are two sub-cases:
  - The two x's are on the same side, e.g. s₁ = x_λ and s₂ = x_μ. Then π₁ gives λμ = 1.
  - The two x's are on opposite sides, e.g. s₁ = x_λ and s₄ = x_μ. Then π₁ gives λ = μ. So s₁ = s₄ and s₂ = s₃, and the relation is trivial, which is excluded.

Hence every nontrivial relation is x_λx_{1/λ} = ψ(x_λ)ψ(x_{1/λ}) up to symmetry. Conversely, this relation holds, since λ·λ⁻¹ = 1. It is nontrivial, since X_r ∩ Y = ∅.

The list of excluded forms in item 2 follows immediately. The Y-side of each relation is forced to be {ψ(x_λ), ψ(x_{1/λ})}, so the representation is unique.

**Step 8: item 3 (counting).**
- By Step 7, violations correspond bijectively to unordered pairs {λ, 1/λ} ⊂ F_q^*∖{1}; the X-side determines the pair.
- λ = 1/λ with λ ≠ 1 iff λ = −1 ≠ 1, which happens iff q is odd.
- So the orbit count on q−2 points is (q−3)/2 + 1 = (q−1)/2 for q odd, and (q−2)/2 for q even.
- For q ≥ 3:
  - If q is odd, the count is ≥ 1.
  - If q is even, the condition gcd(3, q−1) = 1 forces q = 2^k with k odd, so q ≥ 8 and the count is ≥ 3.

Hence X_r ∪ Y is not Sidon. When λ = −1 the violation reads x_{−1}² = ψ(x_{−1})². ∎

## [valid-routine] r1s1/C1 PROVED REDUCTION
**Statement.** Let N, L ≥ 1 and let Y ⊆ [1,N] be a Sidon set such that every d ∈ [1,L] equals y−y′ for some y,y′ ∈ Y.
Then every Sidon set A with Y ⊆ A ⊆ [1,N] satisfies: any two distinct a,b ∈ A with |a−b| ≤ L both lie in Y.
Consequently |A∖Y| ≤ ⌈N/(L+1)⌉, and minMaximalSidonSet(N) ≤ |Y| + ⌈N/(L+1)⌉.
**Beyond.** Monotonicity/greedy completion (KNOWN) bounds the completion cost by the number of unblocked points. That count is Θ(N) here.
The blackboard route needed G2 (greedy/LLL transversal with gap control) and G3 (boundary, all N). C1 shows both are automatic.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "The lemma is a one-line Sidon-property argument (b−a=y−y′ ⇒ b+y′=a+y), the same mechanism as the known certificate lemma, so it is not new. It yields O(N^{1/3}) only if a Sidon Y of size O(√L) with Y−Y ⊇ [1,L] exists, which is an open near-perfect-ruler construction at least as hard as the problem.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "The lemma is a one-line Sidon-property argument (b−a=y−y′ ⇒ b+y′=a+y), the same mechanism as the known certificate lemma, so it is not new. It yields O(N^{1/3}) only if a Sidon Y of size O(√L) with Y−Y ⊇ [1,L] exists, which is an open near-perfect-ruler construction at least as hard as the problem."}, {"verdict": "routine", "cite": null, "significance": 1, "`
**Proof or evidence.**

Let a > b be in A with d = a−b ∈ [1,L]. Write d = y−y′ with y,y′ ∈ Y, y ≠ y′. Then a + y′ = b + y, and all four lie in A.
Since A is Sidon, {a,y′} = {b,y} as multisets. Because a ≠ b, we get a = y and b = y′, so a,b ∈ Y.
Hence the elements of A∖Y are pairwise more than L apart. Partition [1,N] into ⌈N/(L+1)⌉ blocks of at most L+1 consecutive
integers. Each block contains at most one element of A∖Y, so |A∖Y| ≤ ⌈N/(L+1)⌉.
Y is a Sidon subset of [1,N], and [1,N] is finite, so Y extends to an inclusion-maximal Sidon A ⊆ [1,N] (keep adding
admissible points). Apply the bound to that A. ∎
(The same argument shows that each element of A∖Y is at distance > L from every element of Y.)

## [valid-routine] r1s1/C1 PROVED REDUCTION
**Statement.** Let Y be Sidon in [1,N] and M := [1,L] ∖ (Y−Y). Let ω(M) be the maximum size of a set Z ⊆ [0,L] all of whose
positive differences lie in M. Then every Sidon A with Y ⊆ A ⊆ [1,N] has |A∖Y| ≤ ω(M)·⌈N/(L+1)⌉.
If M is sum-free (M ∩ (M+M) = ∅), then ω(M) ≤ 2.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "If a−a′=y−y′ with a,a′∈A∖Y then a+y′=a′+y violates Sidon, so differences of A∖Y within distance L lie in M; partitioning [1,N] into windows of length L+1 gives the bound, and three points would give d1,d2,d1+d2∈M, contradicting sum-freeness. This is a short standard pigeonhole observation that only bounds completion cost and does not advance the construction.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "If a−a′=y−y′ with a,a′∈A∖Y then a+y′=a′+y violates Sidon, so differences of A∖Y within distance L lie in M; partitioning [1,N] into windows of length L+1 gives the bound, and three points would give d1,d2,d1+d2∈M, contradicting sum-freeness. This is a short standard pigeonhole observation that onl`
**Proof or evidence.**

As in C1, any two elements of A∖Y have their difference outside (Y−Y)∖{0}. So within a block of L+1 consecutive
integers, A∖Y is a set whose positive differences all lie in M. If z1<z2<z3 were in such a set, then
z3−z1 = (z3−z2)+(z2−z1) ∈ M ∩ (M+M), so a sum-free M gives ω(M) ≤ 2. ∎
Remark: this lets Y−Y miss a sum-free set, e.g. all odd numbers. But "Y−Y ⊇ all even d ≤ L" is just G1\* for 2·Y′, so
nothing is gained for that M. For Singer lifts, M has density ≈ d/m and many Schur triples, so the holes version gives only polynomially worse bounds.

## [valid-routine] r1s1/C3 PROVED NEGATIVE
**Statement.** Let Y′ = Y + s with [1,L] ⊆ Y−Y, and let X ⊆ [1,N] satisfy X ∩ Y′ = ∅, min X < min Y′ ≤ max Y′ < max X, and X ∪ Y′ Sidon.
Then X has a gap of length ≥ 2L+2. So the lemma "X with all gaps in (L,2L+1] and X ∪ (Y+⌊N/2⌋) Sidon" is false whenever X spans [N].
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Same Sidon identity as the team's Barrier 3: in a disjoint Sidon union X ∪ Y′, every |x − y| avoids Y′ − Y′ ⊇ [1, L], so the gap of X containing any point of Y′ has length ≥ 2L + 2. It only refutes one internal lemma candidate and gives no progress on the O(N^{1/3}) question.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Same Sidon identity as the team's Barrier 3: in a disjoint Sidon union X ∪ Y′, every |x − y| avoids Y′ − Y′ ⊇ [1, L], so the gap of X containing any point of Y′ has length ≥ 2L + 2. It only refutes one internal lemma candidate and gives no progress on the O(N^{1/3}) question."}, {"verdict": "routine", "cite": null, "significance": 0, "why": "If y∈Y′ sits between consecutive x_i<x_`
**Proof or evidence.**

Let y ∈ Y′ and |x−y| ≤ L with x ∉ Y′. If x = y, then x ∈ Y′, which is excluded. Otherwise x−y = ±(y1−y2) with y1,y2 ∈ Y′, and this gives a nontrivial
relation x + y2 = y + y1 (or the symmetric one), contradicting Sidon. So X ∩ [y−L, y+L] = ∅, and the gap of X containing y is ≥ 2L+2. ∎
(The fix: put Y at the start and use C1, so no gap control is needed. Heuristically, centring Y at N/2 is also bad
because x+x′ = y+y′ has Θ(|X|) expected solutions: X+X has density ≍ 1/(λ²N^{1/3}) near N, and |Y+Y| ≍ σλN^{2/3}.)

## [valid-routine] r1s2/C1 PROVED NEGATIVE
**Statement.** Let q be a prime power, m = q³−1, and θ ∈ F_{q³} ∖ F_q. Let g be a primitive element and B = {log_g(θ+a) : a ∈ F_q} ⊂ Z_m. Let t ∈ Z with m/gcd(t,m) > H ≥ 1, let s ∈ Z_m, and let J ⊂ Z_m be any arc of L consecutive residues. Then
  | #{a : t·log_g(θ+a) + s ∈ J} − qL/m | ≤ 6q/(H+1) + (8/π)√q (1 + ln H).
In particular, take H = 23 and q ≥ 1775. If m/gcd(t,m) > 23 (e.g. gcd(t,m) = 1), then tB+s is not contained in any arc of length ≤ m/2, and indeed meets every arc of length ≥ m/2.
Consequence: no A ⊆ Z_m containing such a tB+s lies in an arc of length < m/2. So the T4 transfer (confine to a half-arc, then lift to [1, m/2]) is impossible for any construction built on a Bose–Chowla copy, including all multiplier twists. The same holds for any arc of length δm once q ≫_δ 1.
**Beyond.** The frontier lists T4 (arc confinement) as the way around the wrap-around barrier, and the assignment proposed finding a "special t" with tB in a half-arc. This claim shows that no such t exists for large q, uniformly in t. Numerically, the best arc over all t and s grows: 0.30, 0.36, 0.51, 0.51, 0.56 of m for q = 5, 7, 11, 13, 17.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "N. M. Katz, 'An estimate for character sums', JAMS 2 (1989); F. Chung, 'Diameters and eigenvalues', JAMS 2 (1989); Erdős–Turán inequality", "why": "The arc-equidistribution bound follows directly from the Erdős–Turán inequality combined with Katz's bound |Σ_a χ(θ+a)| ≤ 2√q for θ of degree 3; the hypothesis m/gcd(t,m) > H just ensures the characters χ^{th} are nontrivial. It usefully rules out the T4 half-arc transfer for Bose–Chowla-based constructions, but that is a minor negative result about one approach, not progress on the problem itself.", "panel": [{"verdict": "routine", "cite": "N. M. Katz, 'An estimate for character sums', JAMS 2 (1989); F. Chung, 'Diameters and eigenvalues', JAMS 2 (1989); Erdős–Turán inequality", "significance":`
**Proof or evidence.**

1. Let x_a = (t·log_g(θ+a) + s)/m mod 1, for a ∈ F_q. These are q points of [0,1).
2. For an integer h, put χ_h(g^j) := e(htj/m). This is well defined because j is taken mod m, and it is a multiplicative character of F_{q³}^*. Then Σ_a e(h x_a) = e(hs/m) Σ_{a∈F_q} χ_h(θ+a).
3. χ_h is trivial ⇔ m | ht ⇔ (m/d) | h, where d = gcd(t,m), because gcd(t/d, m/d) = 1. So χ_h is nontrivial for 1 ≤ h ≤ H < m/d.
4. Katz (N. Katz, "An estimate for character sums", JAMS 2 (1989) 197–200): if θ generates F_{q^n} over F_q and χ is a nontrivial multiplicative character of F_{q^n}, then |Σ_{a∈F_q} χ(θ+a)| ≤ (n−1)√q. Here n = 3. Since 3 is prime, θ ∉ F_q generates F_{q³}. Hence |Σ_a e(h x_a)| ≤ 2√q for 1 ≤ h ≤ H. Numerical check: max_{h≠0} |Ŝ_B(h)|/√q = 1.80, 1.90, 1.94, 1.96, 1.99, 1.99 for q = 5, …, 19.
5. Erdős–Turán (Kuipers–Niederreiter, Ch. 2, Thm 2.5): D ≤ 6/(H+1) + (4/π) Σ_{h≤H} (1/h)·|(1/q) Σ_a e(h x_a)|. Here D is the sup over intervals [α,β) ⊂ [0,1) of |#{x_a ∈ [α,β)}/q − (β−α)|. With step 4 this gives D ≤ 6/(H+1) + (8/(π√q))(1 + ln H), using Σ_{h≤H} 1/h ≤ 1 + ln H.
6. Wrap-around. Replace s by s − j₀, where j₀ is the first residue of J. The bound in step 5 is uniform in s, and J becomes {0, …, L−1}, which corresponds to [0, L/m). This proves the displayed inequality.
7. Suppose tB+s ⊂ I with |I| ≤ m/2. Apply step 6 to the complementary arc J, which has length L ≥ m/2 and contains no points. Then 0 ≥ q/2 − qD, so D ≥ 1/2.
8. With H = 23: D ≤ 1/4 + 2.5465·4.1355/√q = 1/4 + 10.531/√q. This is < 1/2 iff √q > 42.13, i.e. q ≥ 1775. That contradicts step 7. ∎
(For general δ, letting H → ∞ slowly shows D ≪ log q/√q.)

## [valid-routine] r1s2/C2 PROVED STRUCTURE
**Statement.** Keep the setup of C1, and write elements of F_{q³} in the basis 1, θ, θ² as y = y₀ + y₁θ + y₂θ².
(a) For y = g^x with x ∉ B, the following are equivalent:
  - x = b₁ + b₂ − b₃ for some b_i = log(θ+a_i) with a₃ ∉ {a₁, a₂};
  - y₂ ≠ 0 and, with c := (1 − (yθ)₂)/y₂ and y(θ+c) =: θ² + σ₁θ + σ₂, the polynomial z² − σ₁z + σ₂ has its roots in F_q and c is not one of them.
  Exactly q²(q−1)/2 points of Z_m ∖ B are triple-blocked by B. Since half-sums add at most q(q−1) more, B blocks a fraction 1/2 + O(1/q) of Z_m.
(b) For t ∈ {q, −q, q², −q²}: (B−B) ∩ t(B−B) = {0} ⇔ 1, θ, θ^q are F_q-linearly independent.
  - Independence fails iff θ^q = uθ + v with u³ = 1 and v(u²+u+1) = 0. That happens only when char = 3 (u = 1), or when q ≡ 1 (mod 3) and θ is an affine Kummer generator (u ≠ 1).
  - So independence always holds when q ≡ 2 (mod 3).
**Beyond.** The frontier listed the discriminant half-cover as "derivation, unverified". It is now proved and checked at every point for q ≤ 19. Part (b) is the clean answer to the assignment's step (b) for Galois twists.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Bose–Chowla (1962) B_h construction; standard splitting-of-quadratics count over F_q and Frobenius linear-algebra argument", "why": "Part (a) is a direct unpacking of y(θ+a₃)=(θ+a₁)(θ+a₂) plus the standard count q²(q−1)/2, and part (b) is elementary Frobenius/linear-independence field theory; both are cyclic-group facts that only diagnose why Bose–Chowla blocks about half the points, without advancing the O(N^{1/3}) construction in [N].", "panel": [{"verdict": "routine", "cite": "Bose–Chowla (1962) B_h construction; standard splitting-of-quadratics count over F_q and Frobenius linear-algebra argument", "significance": 1, "why": "Part (a) is a direct unpacking of y(θ+a₃)=(θ+a₁)(θ+a₂) plus the standard count q²(q−1)/2, and part (b) is elemen`
**Proof or evidence.**

(a)
1. Since log is a bijection Z_m → F*, x = b₁ + b₂ − b₃ ⇔ y(θ+a₃) = (θ+a₁)(θ+a₂) = θ² + (a₁+a₂)θ + a₁a₂. The right side has degree ≤ 2, so no reduction is needed and its coordinates are (a₁a₂, a₁+a₂, 1).
2. The θ²-coordinate of y(θ+c) is (yθ)₂ + c·y₂.
3. Case y₂ ≠ 0: this coordinate equals 1 for exactly one c, namely c = (1−(yθ)₂)/y₂. Then σ₁ = a₁+a₂ and σ₂ = a₁a₂ are forced, and a₁, a₂ exist in F_q iff the quadratic splits.
4. Case y₂ = 0: write y = y₀ + y₁θ. Then (yθ)₂ = y₁, so we need y₁ = 1, i.e. y = θ + y₀ ∈ B. Then (θ+y₀)(θ+c) = (θ+a₁)(θ+a₂) as polynomials of degree ≤ 2, which forces c ∈ {a₁, a₂}, an excluded case.
5. Counting. B is B₃ (Bose–Chowla), so a₁+a₂−a₃ = a₁′+a₂′−a₃′ ⇒ {a₁, a₂, a₃′} = {a₁′, a₂′, a₃}. Since a₃ ∉ {a₁, a₂}, this gives a₃ = a₃′ and then {a₁, a₂} = {a₁′, a₂′}. So the map is injective on (multiset {a₁,a₂}, a₃ ∉ {a₁,a₂}). The number of such pairs is q(q−1) + C(q,2)(q−2) = q²(q−1)/2.
6. The values avoid B: if a₁+a₂−a₃ = e ∈ B, then the Sidon property gives {a₁,a₂} = {a₃,e}, contradicting a₃ ∉ {a₁,a₂}.
7. Numerical check: the criterion agrees with the brute-force blocked set at all points, for q = 5, 7, 11, 13, 17, 19.
(b)
1. Because (θ+a)^q = θ^q + a, we have q(B−B) = {log((θ^q+c)/(θ^q+d))}.
2. A common nonzero element means (θ+a)(θ^q+d) = (θ+b)(θ^q+c) with a ≠ b and c ≠ d. Expanding, this is (d−c)θ + (a−b)θ^q + (ad−bc) = 0.
3. If 1, θ, θ^q are independent, then d = c, a contradiction.
4. Conversely, if θ^q = uθ + v, then u ≠ 0 since θ ∉ F_q. Take a−b = 1, d−c = −u and c = au − v; this solves the equation.
5. The other multipliers: −D = D, so D ∩ (−q)D = D ∩ qD. And q(q²D ∩ D) = D ∩ qD because q³ ≡ 1 (mod m), so the q² cases reduce to the q case.
6. Dependence analysis: θ^q = uθ + v ⇒ θ^{q²} = u²θ + uv + v ⇒ θ = θ^{q³} = u³θ + v(u²+u+1). Hence u³ = 1 and v(u²+u+1) = 0. If u = 1, then v ≠ 0, so 3 = 0. If u ≠ 1, then F_q contains a primitive cube root of unity, so q ≡ 1 (mod 3). ∎

## [valid-routine] r1s3/C2 PROVED STRUCTURE
**Statement.** Let S⊂[0,L] be an integer set whose reduction mod h is a perfect difference set (|S|=q+1, h=q²+q+1), and put w=h−L. Then (a) T=S−S ⊇ [−(w−1), w−1]; (b) hence (q+1)² ≥ 2.434(w−1) (Leech/Bernshteyn–Tait), i.e. w ≤ 0.411h+O(q); (c) w−1 ≤ h√q(1+ln h)/(q+1) < h(1+ln h)/√q for every multiplier image and rotation; so w/h → 0.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Folklore: |Ŝ(a)|²=q for perfect difference sets plus the Erdős–Turán discrepancy inequality (gaps in Singer sets are O(q^{3/2} log q)); part (b) is Leech / Bernshteyn–Tait", "why": "Part (a) is immediate from uniqueness of differences mod h, part (b) is direct substitution into Leech/Bernshteyn–Tait, and part (c) is the standard flat-Fourier-spectrum plus Erdős–Turán argument showing Singer sets have gaps o(h). It only closes the arc-confined-lift route (T4) as a barrier and does not advance the construction.", "panel": [{"verdict": "routine", "cite": "Folklore: |Ŝ(a)|²=q for perfect difference sets plus the Erdős–Turán discrepancy inequality (gaps in Singer sets are O(q^{3/2} log q)); part (b) is Leech / Bernshteyn–Tait", "significance": `
**Proof or evidence.**

(a) Each nonzero residue r has exactly one representative in S−S, and that representative is r or r−h (0<r<h). For 0<r<w we have |r−h| > h−w = L ≥ max|T|, so r∈T; T is symmetric. (b) Apply Leech's bound to Y=S, n=w−1. (c) uS is again a perfect difference set, so |Ŝ(ξ)|²=q for ξ≢0. If an arc I of length g contains no point of S, then 0 = |S∩I| = (q+1)g/h + E with |E| ≤ (1/h)Σ_{ξ≠0}|Ŝ(ξ)||1̂_I(ξ)| ≤ √q·(1/h)Σ_{ξ≠0} h/(2‖ξ‖) ≤ √q(1+ln h). So g ≤ h√q(1+ln h)/(q+1). A lift S⊂[0,L] with 0,L∈S leaves the arc (L,h) empty, and that arc has g=w−1 integers. So w−1 ≤ h√q(1+ln h)/(q+1).
Data check: best w/h over all multipliers is 0.386, 0.361, 0.306, 0.296, 0.257, 0.231, 0.219 for q = 7, 11, 13, 17, 19, 23, 29 (all below 0.411).

## [valid-routine] r1s3/C1r PROVED SPECIAL
**Statement.** **Setup.** Let $m\ge 2$, $h\ge 1$, $y_0\in[0,m)$. Let $S\subset[0,h)$ be a set of integers. (In the intended application, $S$ is an integer lift of a Singer set for a prime $q$, with $h=q^2+q+1$ and $|S|=q+1$. Neither fact is used below.) Write $T=S-S$, taken in $\mathbb Z$, and $Y=\{ms+y_0: s\in S\}$.

For each column $i\in[0,m)\setminus\{y_0\}$, let $t_i,d_i$ be integers with $0\le t_i<t_i+d_i<h$ and
$$[0,h)\subseteq (t_i+T)\cup(t_i+d_i+T). \qquad (\mathrm{Cov})$$
Put $a_i=i+mt_i$, $b_i=i+m(t_i+d_i)$, $X=\{a_i,b_i: i\ne y_0\}$ and $A=X\cup Y$.

A set $B$ is *Sidon* if $a+b=c+d$ with $a,b,c,d\in B$ implies $\{a,b\}=\{c,d\}$. An integer $z\notin A$ is *blocked* if $A\cup\{z\}$ is not Sidon.

**Theorem.**
1. $A\subset[0,mh)$ and $|A|=|S|+2(m-1)$.
2. **(Column blocking, unconditional.)** Every $z\in[0,mh)\setminus A$ with $z\not\equiv y_0\pmod m$ is blocked.
3. **(Column $y_0$, sufficient condition.)** If $[0,h)\setminus S\subseteq S+S-S$, then every $z\in[0,mh)\setminus A$ with $z\equiv y_0\pmod m$ is blocked.
4. **(Necessary condition.)** If $A$ is Sidon, then $d_i\notin T$ for every $i\neq y_0$.
5. **(Maximality.)** Suppose $A$ is Sidon (a hypothesis, not a conclusion) and the hypothesis of 3 holds. Then $A$ is a maximal Sidon subset of $[0,mh)$. Equivalently, $A+1$ is a maximal Sidon subset of $[1,mh]$.
6. **(Explicit instance.)** Take $q=2$, $h=7$, $S=\{0,1,3\}$, $m=2$, $y_0=0$, $t_1=2$, $d_1=4$. Then $A=\{0,2,5,6,13\}$, and $A+1=\{1,3,6,7,14\}$ is a maximal Sidon set in $[1,14]$ of size $5=q+1+2(m-1)$.

No claim is made about any other computed cases.
**Beyond.** first explicit structured integer certificates of the blackboard "X ⊔ Y" type that need no greedy completion. They are finite only; ratios 2.06–2.37 are no better than greedy at these sizes.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Column blocking is a direct application of the elementary certificate lemma (z = x + y − y′), and maximality is conditional on assuming A is Sidon, which is the real difficulty. The only unconditional content is a single tiny example in [1,14], with no asymptotic family and no gain over greedy.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Column blocking is a direct application of the elementary certificate lemma (z = x + y − y′), and maximality is conditional on assuming A is Sidon, which is the real difficulty. The only unconditional content is a single tiny example in [1,14], with no asymptotic family and no gain over greedy."}, {"verdict": "routine", "cite": "Certificate lemma (blackboard/sta`
**Proof or evidence.**

Write each $z\in[0,mh)$ uniquely as $z=i+mx$ with $i\in[0,m)$ and $x\in[0,h)$. Call $i$ the column of $z$.

**(1) Range and size.**
- $0\le ms+y_0\le m(h-1)+m-1=mh-1$, so $Y\subset[0,mh)$.
- Similarly, $a_i,b_i\in[0,mh)$ because $0\le t_i<t_i+d_i\le h-1$.
- Elements in different columns are distinct.
- $Y$ lies in column $y_0$ and has $|S|$ distinct elements.
- For each $i\ne y_0$, column $i$ contains exactly $a_i$ and $b_i$, and $a_i\ne b_i$ since $d_i>0$.
- Hence $|A|=|S|+2(m-1)$.

**(2) Column blocking.** Let $z=i+mx\notin A$ with $i\ne y_0$. By (Cov) there is $c\in\{a_i,b_i\}$ with column coordinate $c=i+mu$, $u\in\{t_i,t_i+d_i\}$, and $s,s'\in S$ with $x-u=s-s'$. Then
$$z-c=m(s-s')=(ms+y_0)-(ms'+y_0),$$
so
$$z+(ms'+y_0)=c+(ms+y_0).$$
All four terms lie in $A\cup\{z\}$. Since $z\notin A$ and $c,\,ms+y_0\in A$, we have $z\notin\{c,\,ms+y_0\}$. So the two multisets differ, and $A\cup\{z\}$ is not Sidon.

**(3) Column $y_0$.** Let $z=y_0+mx\notin A$. Then $x\notin S$, since otherwise $z\in Y$. By hypothesis $x=s_1+s_2-s_3$ with $s_j\in S$. Then
$$z+(ms_3+y_0)=y_0+m(s_1+s_2)+y_0=(ms_1+y_0)+(ms_2+y_0).$$
As before, $z\notin A$ appears on the left but not on the right. So $z$ is blocked.

**(4) Necessary condition.** Suppose $d_i=s-s'\in T$ with $s,s'\in S$. Then $b_i-a_i=md_i=(ms+y_0)-(ms'+y_0)$, so
$$b_i+(ms'+y_0)=a_i+(ms+y_0).$$
Here $b_i,a_i$ lie in column $i\ne y_0$, while $ms+y_0,ms'+y_0$ lie in column $y_0$. The multisets are therefore different unless $b_i=a_i$, which is impossible. So $A$ is not Sidon, a contradiction.

**(5) Maximality.**
- By hypothesis, $A$ is Sidon.
- By (2) and (3), every $z\in[0,mh)\setminus A$ is blocked.
- So $A$ is maximal Sidon in $[0,mh)$.
- Translation by $1$ preserves additive relations $a+b=c+d$, so $A+1$ is maximal Sidon in $[1,mh]$.

**(6) Instance.**
- *Singer set.* The differences of $S=\{0,1,3\}$ mod $7$ are $\pm1,\pm2,\pm3$, i.e. $1,\dots,6$ each exactly once. So $S$ is a Singer set for $q=2$.
- *(Cov).* $T=\{-3,\dots,3\}$. Then $t_1+T=[-1,5]$ and $t_1+d_1+T=[3,9]$, which together cover $[0,6]$. Also $t_1+d_1=6<7$.
- *Elements.* $a_1=1+4=5$ and $b_1=1+12=13$. $Y=\{0,2,6\}$, so $A=\{0,2,5,6,13\}$. Note $d_1=4\notin T$, consistent with (4).
- *$A$ is Sidon.* The ten positive differences are
  - $2,5,6,13$ (from $0$),
  - $3,4,11$ (from $2$),
  - $1,8$ (from $5$),
  - $7$ (from $6$).

  These are pairwise distinct, so $A$ is Sidon.
- *Hypothesis of (3).* $[0,7)\setminus S=\{2,4,5,6\}$, and
  - $2=1+1-0$,
  - $4=3+1-0$,
  - $5=3+3-1$,
  - $6=3+3-0$.

  All lie in $S+S-S$.
- *Conclusion.* By (5), $A+1=\{1,3,6,7,14\}$ is maximal Sidon in $[1,14]$, with $|A|=5=q+1+2(m-1)$. Spot checks of the blocking relations:
  - $z=1$: $1+6=5+2$.
  - $z=9$: $9+6=13+2$.

∎

## [valid-routine] r2s1/C1 PROVED STRUCTURE
**Statement.** Let G be a finite abelian group, H ≤ G, π: G→G/H, and S ⊂ G/H a Sidon set. Let A = ⊔_{s∈S} A_s with π(A_s) = {s}. Then A is Sidon iff (a) each A_s is Sidon, and (b) the difference sets A_s − A_s (⊂ H) are pairwise disjoint apart from 0.
**Beyond.** generalises the r1s2 fiber-scalar criterion (which was unrefereed) to any quotient, and includes the 2-torsion case.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Elementary fiber-decomposition check: project a+b=c+d to G/H, use that S is Sidon to match fibers, then within-fiber Sidonness or difference-set disjointness finishes; the converse is immediate. It concerns only the Sidon property, not maximality or blocking, so it makes no progress on the O(N^{1/3}) question.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Elementary fiber-decomposition check: project a+b=c+d to G/H, use that S is Sidon to match fibers, then within-fiber Sidonness or difference-set disjointness finishes; the converse is immediate. It concerns only the Sidon property, not maximality or blocking, so it makes no progress on the O(N^{1/3}) question."}, {"verdict": "routine", "cite": nu`
**Proof or evidence.**

Suppose a+b = c+d with a,b,c,d ∈ A. Applying π gives π(a)+π(b) = π(c)+π(d) in S, so {π(a),π(b)} = {π(c),π(d)} since S is Sidon; relabel so that π(a)=π(c)=s and π(b)=π(d)=s′. Then a−c = d−b ∈ (A_s−A_s) ∩ (A_{s′}−A_{s′}).
- If s ≠ s′, (b) forces a=c and b=d.
- If s = s′, all four lie in A_s, and (a) gives {a,b} = {c,d}.
Conversely, a violation inside some A_s violates Sidon for A. If 0 ≠ δ = a−c = d−b with a,c ∈ A_s and b,d ∈ A_{s′} (s≠s′), then a+b = c+d is a nontrivial relation, because {a,b} = {c,d} would force a=d, impossible since π(a)≠π(d). ∎
In F_{q³}* with H = F_q* and S = the Singer line {[θ+a]} ∪ {[1]}, this is the fiber-scalar criterion. Note that −1 ∉ A_s−A_s (multiplicatively, κ and −κ both in K_s gives κ² = (−κ)²), so D ⊆ H∖{1,−1} and Σ|K_s|(|K_s|−1) ≤ q−3 for q odd.

## [valid-routine] r2s1/C2r PROVED NEGATIVE
**Statement.** **Setting (general part).**
- $G$ is a finite abelian group, written additively in (1)–(2), and $H\le G$ with $\pi:G\to G/H$.
- $|G/H|=q^2+q+1$, which is odd.
- $S\subset G/H$ is a perfect difference set with $|S|=q+1$: every nonzero element of $G/H$ is uniquely $s-s'$ with $s,s'\in S$.
- For $s\in S$ let $A_s\subset\pi^{-1}(s)$, and put $A=\bigcup_{s\in S}A_s$. Assume $A$ is Sidon: $x_1+x_2=x_3+x_4$ with $x_i\in A$ implies $\{x_1,x_2\}=\{x_3,x_4\}$ as multisets.
- $y\notin A$ is *blocked* if $A\cup\{y\}$ is not Sidon.
- $D=\bigcup_s\{b-c: b\ne c\in A_s\}\subset H$.
- $\mathrm{Mid}=\{t\in G/H: 2t=s+s' \text{ for some } s\ne s'\in S\}$.

**(1)** Let $t\in S$ and $y\in\pi^{-1}(t)\setminus A$. Then $y$ is blocked iff one of the following holds:
- $y\in A_t+D$;
- $2y=a+a'$ with $a\ne a'\in A_t$;
- $2y=2a$ with $a\in A_t$ (automatically $y\neq a$).

**(2)** Let $t\notin S$.
- The representations $t=s_1+s_2-s_3$ with $s_i\in S$ and $s_3\notin\{s_1,s_2\}$ are in bijection with $s_2\in S$, so there are exactly $q+1$ ordered ones.
- They pair off under $s_1\leftrightarrow s_2$, giving $(q+1+f_t)/2$ unordered ones, where $f_t=\#\{s\in S:2s-t\in S\}$.
- $|\mathrm{Mid}|=q(q+1)/2$ and $\mathrm{Mid}\cap S=\emptyset$. For $t\in\mathrm{Mid}$ the pair $\{s,s'\}$ with $2t=s+s'$, $s\neq s'$, is unique.
- $y\in\pi^{-1}(t)$ is blocked iff
$$y\in\bigcup_{\text{reps}}(A_{s_1}+A_{s_2}-A_{s_3})\quad\text{or}\quad\bigl(t\in\mathrm{Mid}\ \text{and}\ 2y\in A_s+A_{s'}\bigr).$$

**Corollary 1.**
- If $A_t=\emptyset$ for some $t\in S$, every point of $\pi^{-1}(t)$ is unblocked, so $A$ is not maximal.
- In particular, let $G=\mathbb F_{q^3}^*$ with $\mathbb F_{q^3}=\mathbb F_q(\theta)$ and $H=\mathbb F_q^*$. No Sidon set $A\subset E=\{\kappa(\theta+a):\kappa\in\mathbb F_q^*,\,a\in\mathbb F_q\}$ is maximal in $\mathbb F_{q^3}^*$: every $y\in\mathbb F_q^*$ is unblocked.

**Corollary 2 (corrected).**
Hypotheses:
- $G=\mathbb F_{q^3}^*$ (written multiplicatively), $q$ odd, $H=\mathbb F_q^*$, and $S$ as above.
- For each $s\in S$ fix $\sigma_s\in\pi^{-1}(s)$ and put $A_s=\sigma_sK_s$, where:
  - for $(q-3)/2$ indices $s$, $K_s=\{1,\zeta_s\}$, with the pairs $\{\zeta_s^{\pm1}\}$ partitioning $H\setminus\{\pm1\}$;
  - for the other $(q+5)/2$ indices, $K_s=\{1\}$.
- For each $t\in G/H$ fix $\gamma_t\in\pi^{-1}(t)$.

Conclusions:
- (i) $A$ is Sidon.
- (ii) Every point of $\pi^{-1}(S)\setminus A$ is blocked.
- (iii) $A$ is maximal iff for every $t\notin S$
$$H=\bigcup_{\text{reps }(s_1,s_2,s_3)} c_{t}(s_1,s_2,s_3)\,K_{s_1}K_{s_2}K_{s_3}^{-1}\ \cup\ M_t,$$
where:
  - $c_t(s_1,s_2,s_3)=\sigma_{s_1}\sigma_{s_2}\sigma_{s_3}^{-1}\gamma_t^{-1}\in H$;
  - for $t\in\mathrm{Mid}$ with $2t=s+s'$, $M_t=\{h\in H: h^2\in d_tK_sK_{s'}\}$, $d_t=\sigma_s\sigma_{s'}\gamma_t^{-2}\in H$, and $|M_t|=2\,|d_tK_sK_{s'}\cap H^2|\le 2|K_s||K_{s'}|$;
  - for $t\notin\mathrm{Mid}$, $M_t=\emptyset$.
**Beyond.** the r1s2 C2(a) law covered only Bose–Chowla (all K_a = {1}). This is the bookkeeping for the whole fiber family the lead asked about, and it shows that family alone cannot be maximal.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Fibre-by-fibre blocking characterisation over a Singer perfect difference set follows immediately from uniqueness of differences in S, and Corollary 1 (empty fibre ⇒ unblocked) is a one-line consequence. Corollary 2(iii) just restates maximality within the family without resolving it, and everything is in the cyclic group F_{q^3}^*, not [N].", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Fibre-by-fibre blocking characterisation over a Singer perfect difference set follows immediately from uniqueness of differences in S, and Corollary 1 (empty fibre ⇒ unblocked) is a one-line consequence. Corollary 2(iii) just restates maximality within the family without resolving it, and everything is in the cycli`
**Proof or evidence.**

**Preliminaries.**

*$S$ is Sidon.* Suppose $s+s'=u+u'$ in $S$ with $s\ne u$. Then $s-u=u'-s'\ne0$, and uniqueness of differences gives $s=u'$, $u=s'$.

*Doubling is a bijection on $G/H$*, since $|G/H|=q^2+q+1$ is odd.

*Which relations block $y$.* Let $y\notin A$. A nontrivial relation in $A\cup\{y\}$ must contain $y$.
- If $y$ occurs on both sides, then either $y+u=y+v$ gives $u=v$ (trivial), or $y+y=y+v$ gives $y=v\in A$ (impossible).
- So $y$ occurs on one side only, and the relation is nontrivial automatically because $y$ is not on the other side.
- Hence $y$ is blocked iff $y\in A+A-A$ (that is, $y+c=a+b$) or $2y\in A+A$.
- In $y=a+b-c$, $c\notin\{a,b\}$ holds automatically, since $c=a$ would give $y=b\in A$.

**(1)** Let $y=a+b-c\in\pi^{-1}(t)$ with $t\in S$.
- Then $t+\pi(c)=\pi(a)+\pi(b)$, so by Sidon $\{t,\pi(c)\}=\{\pi(a),\pi(b)\}$.
- Relabel so that $\pi(a)=t$ and $\pi(b)=\pi(c)=:s$.
- Since $b\ne c$, we get $y=a+(b-c)\in A_t+D$.
- Conversely, $a\in A_t$ and $b\ne c\in A_s$ give $y=a+b-c\in A+A-A$.

For midpoints, let $2y=a+a'$.
- Then $t+t=\pi(a)+\pi(a')$, so $\pi(a)=\pi(a')=t$ by Sidon.
- This gives the two midpoint cases ($a\ne a'$ or $a=a'$).

**(2)** Let $t\notin S$.

*Representations.* For each $s_2\in S$, $t-s_2\ne0$, so there are unique $s_1\ne s_3$ in $S$ with $s_1-s_3=t-s_2$.
- $s_3\ne s_2$, else $t=s_1\in S$.
- Conversely, in any representation $s_1\ne s_3$, else $t=s_2\in S$.
- Hence there are exactly $q+1$ ordered representations, one for each $s_2$.
- The involution $(s_1,s_2,s_3)\mapsto(s_2,s_1,s_3)$ maps representations to representations. Its fixed points are those with $s_1=s_2=s$ and $s_3=2s-t\in S$, which number $f_t$. This gives $(q+1+f_t)/2$ orbits.

*Triple blocks.* Let $y=a+b-c\in\pi^{-1}(t)$.
- Then $t=\pi(a)+\pi(b)-\pi(c)$.
- $\pi(c)\ne\pi(a)$, else $t=\pi(b)\in S$; similarly $\pi(c)\ne\pi(b)$. So this is a representation.
- Conversely, every point of $A_{s_1}+A_{s_2}-A_{s_3}$ lies in $A+A-A$ and is not in $A$, since $A\subset\pi^{-1}(S)$.

*Midpoint blocks.* Let $2y=a+a'$ with $\pi(a)=s$, $\pi(a')=s'$.
- Then $2t=s+s'$.
- If $s=s'$ then $2(t-s)=0$, so $t=s\in S$ by oddness, a contradiction. Hence $s\ne s'$ and $t\in\mathrm{Mid}$.
- The pair $\{s,s'\}$ is unique because $S$ is Sidon.

*Counting $\mathrm{Mid}$.* The map $\{s,s'\}\mapsto s+s'$ on the $q(q+1)/2$ unordered pairs of distinct elements is injective (Sidon). Halving is bijective, so $|\mathrm{Mid}|=q(q+1)/2$. Moreover $\mathrm{Mid}\cap S=\emptyset$: if $t\in S$ and $2t=s+s'$, Sidon forces $s=s'=t$.

**Corollary 1.**

*General statement.* By (1), with $A_t=\emptyset$ the sets $A_t+D$ and $A_t+A_t$ are empty, so no $y\in\pi^{-1}(t)$ (all $\notin A$) is blocked. Since $H\ne\emptyset$, $A$ is not maximal.

*The family $E$, by direct check.* Let $y\in\mathbb F_q^*$ and $u_i=\kappa_i(\theta+a_i)\in A$.
- If $y=u_1u_2u_3^{-1}$, then $y\kappa_3(\theta+a_3)=\kappa_1\kappa_2(\theta^2+(a_1+a_2)\theta+a_1a_2)$. The left side has $\theta^2$-coefficient $0$ and the right side has $\kappa_1\kappa_2\ne0$. This contradicts the fact that $1,\theta,\theta^2$ is a basis ($\theta$ has degree 3).
- $y^2=u_1u_2$ fails the same way.
- $y\notin A$, because elements of $E$ have $\theta$-coefficient $\kappa\ne0$.
- So $A\cup\{y\}$ is Sidon whenever $A$ is.

**Corollary 2.** Write everything multiplicatively.

*(i) $A$ is Sidon.* Suppose $ab=cd$ with $a,b,c,d\in A$.
- Projecting and using Sidon of $S$, we may take $\pi(a)=\pi(c)=s$ and $\pi(b)=\pi(d)=s'$.
- If $s\ne s'$: $ac^{-1}=db^{-1}$ lies in $(A_sA_s^{-1})\cap(A_{s'}A_{s'}^{-1})$. Here $A_sA_s^{-1}\setminus\{1\}=\{\zeta_s^{\pm1}\}$ or $\emptyset$, and these sets are pairwise disjoint over $s$. Hence $a=c$ and $b=d$.
- If $s=s'$ with $A_s=\{x,x\zeta\}$: the possible products are $x^2,\ x^2\zeta,\ x^2\zeta^2$. These are distinct because $\zeta\ne\pm1$, so the multiset $\{a,b\}$ is determined.

*(ii) Fibres over $S$ are fully blocked.* Let $t\in S$, $y\in\pi^{-1}(t)\setminus A$, $a=\sigma_t\in A_t$, and write $y=a\eta$ with $\eta\in H$.
- $\eta=1$ is impossible, since $y\notin A$.
- If $\eta=-1$: then $y\cdot y=a\cdot a$ with $y\ne a$, which is a nontrivial relation.
- Otherwise $\eta=\zeta_s^{\varepsilon}$ for a unique $s$ and $\varepsilon=\pm1$. Put $b=\sigma_s\zeta_s$, $c=\sigma_s$ (swapped if $\varepsilon=-1$). Then $y\,c=a\,b$ with $y\notin\{a,b\}$, a nontrivial relation.

*(iii) Outer fibres.* All points over $t\notin S$ lie outside $A$, so by (ii) $A$ is maximal iff every such point is blocked. By (2), $y=\gamma_th$ is blocked iff one of the following holds:
- $y\in\sigma_{s_1}\sigma_{s_2}\sigma_{s_3}^{-1}K_{s_1}K_{s_2}K_{s_3}^{-1}$ for some representation. This is equivalent to $h\in c_t(s_1,s_2,s_3)K_{s_1}K_{s_2}K_{s_3}^{-1}$, where $c_t\in H$ because $\pi(\sigma_{s_1}\sigma_{s_2}\sigma_{s_3}^{-1})=t$.
- $t\in\mathrm{Mid}$ and $y^2\in\sigma_s\sigma_{s'}K_sK_{s'}$. This is equivalent to $h^2\in d_tK_sK_{s'}$, where $d_t\in H$ because $2t=s+s'$.

Squaring on the cyclic group $H$ of even order $q-1$ has kernel $\{\pm1\}$, so each element of $H^2$ has exactly 2 square roots. Hence $|M_t|=2|d_tK_sK_{s'}\cap H^2|\le2|K_s||K_{s'}|$. ∎

## [valid-routine] r2s2/C1 PROVED CONDITIONAL
**Statement.** (a) [Ruler reduction] Let N ≥ 1, L ≥ 1, Y ⊆ [1,N] Sidon with [1,L] ⊆ Y−Y. Then minMaximalSidonSet(N) ≤ |Y| + ⌈N/(L+1)⌉.
(b) [Conditional bound, repaired G1*] Suppose σ, ρ > 0 and for every large L there is a Sidon Y_L ⊆ [1, ρL^{3/2}] with
[1,L] ⊆ Y_L − Y_L and |Y_L| ≤ √(σL). Then for every 0 < λ ≤ ρ^{−2/3} and all large N,
minMaximalSidonSet(N) ≤ (√(σλ) + 1/λ)·N^{1/3} + 1. If ρ ≤ (σ/4)^{1/2}, taking λ=(4/σ)^{1/3} gives 3(σ/4)^{1/3}N^{1/3}+1.
**Beyond.** repairs r1s1/C2 (the hypothesis [1,L] ⊆ Y_L−Y_L is now in the statement, and the span condition needed for Y_L ⊆ [1,N] is explicit).
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Part (a) is immediate greedy completion: each added point x blocks x+(Y−Y) ⊇ [x,x+L]; part (b) is parameter optimisation. The hypothesis (a Sidon near-optimal difference basis for [1,L] with span O(L^{3/2})) is unproven and carries essentially all the difficulty, so this is a clean reformulation of a sufficient condition rather than progress.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "Part (a) is immediate greedy completion: each added point x blocks x+(Y−Y) ⊇ [x,x+L]; part (b) is parameter optimisation. The hypothesis (a Sidon near-optimal difference basis for [1,L] with span O(L^{3/2})) is unproven and carries essentially all the difficulty, so this is a clean reformulation of a sufficient co`
**Proof or evidence.**

(a) Extend Y to a maximal Sidon A ⊆ [1,N] (finite, greedy). If a<a' in A with d=a'−a ≤ L, write d=y'−y, y,y'∈Y⊆A.
Then a'+y = a+y', so Sidon gives {a',y}={a,y'}; a'≠a forces a'=y', a=y. So any two elements of A∖Y differ by ≥ L+1;
z_1<…<z_m in [1,N] with gaps ≥ L+1 gives (m−1)(L+1) ≤ N−1, m ≤ ⌊(N−1)/(L+1)⌋+1 = ⌈N/(L+1)⌉. A is in the sInf set, so minMax ≤ |A|.
(b) L=⌊λN^{2/3}⌋ (large with N). ρL^{3/2} ≤ ρλ^{3/2}N ≤ N, so Y_L ⊆ [1,N]. |Y_L| ≤ √(σλ)N^{1/3}; L+1 > λN^{2/3} gives
⌈N/(L+1)⌉ ≤ N^{1/3}/λ + 1. Apply (a). Optimisation: f(λ)=√σ λ^{1/2}+λ^{−1}, f'=0 at λ^{3/2}=2/√σ, f=3(σ/4)^{1/3}.
Remark: any Y with [1,L]⊆Y−Y has |Y|²≥2.434L (Leech), so σ ≥ 2.434 is forced; the bound can never beat 3(0.6085)^{1/3}≈2.54 N^{1/3}.

## [valid-routine] r2s2/C2 PROVED REDUCTION
**Statement.** [Cluster compression; G1* without span cap reduces to a capped one] Let C_1,…,C_r ⊆ [0,w] (w ≥ 1) be Sidon sets
with pairwise disjoint difference sets, (C_i−C_i) ∩ (C_j−C_j) = {0} for i ≠ j. Let B = {b_1<…<b_r} ⊆ Z_{≥0} be Sidon. Then
Y = ⋃_i (3w·b_i + C_i) is Sidon, has span ≤ 3w·b_r + w, and has Y−Y ⊇ ⋃_i (C_i−C_i). With B from Erdős–Turán ({2pk+(k² mod p)},
p ≥ r prime, p ≤ 2r) we get b_r < 8r², so span(Y) ≤ 25·w·r². Hence the far-separated-cluster (no-span-cap) form of G1*, with
r clusters of span w, feeds C1(b) whenever 25·w·r² ≤ ρL^{3/2}. For example r = O(1) and w = O(L³ᐟ²) both suffice.
**Beyond.** makes "test G1* without the span cap" precise. Unbounded-span Sidon rulers are exactly far-separated clusters with disjoint
difference sets, and this lemma says how much span re-packing costs.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard substitution/blow-up construction for Sidon sets (block placement along a Sidon set, e.g. Erdős–Turán set {2pk+(k^2 mod p)}); folklore", "why": "Placing difference-disjoint Sidon clusters at 3w-scaled positions of a Sidon set is the standard blow-up argument, verified in a few lines, and the span bound is direct arithmetic. It is an internal reduction step that does not address the near-exact covering core of the problem.", "panel": [{"verdict": "routine", "cite": "Standard substitution/blow-up construction for Sidon sets (block placement along a Sidon set, e.g. Erdős–Turán set {2pk+(k^2 mod p)}); folklore", "significance": 0, "why": "Placing difference-disjoint Sidon clusters at 3w-scaled positions of a Sidon set is the standard `
**Proof or evidence.**

The translated clusters occupy disjoint intervals [t_i, t_i+w], where t_i = 3w·b_i and t_j − t_i ≥ 3w. A positive difference
δ of a pair inside one cluster satisfies δ ≤ w. A pair from clusters i<j has δ = 3wβ + (c_j−c_i) with β = b_j−b_i ≥ 1 and
|c_j−c_i| ≤ w, so δ ∈ [3wβ−w, 3wβ+w] ⊆ [2w, ∞). These intervals are disjoint for distinct β, since consecutive ones are 3w apart
and each has length 2w. So δ determines whether the pair is internal, and for a cross pair it determines β, hence (i,j), because B
is Sidon. Now suppose two distinct pairs share δ.
(i) Both internal, in clusters i ≠ i′: then δ ∈ (C_i−C_i) ∩ (C_{i′}−C_{i′}), which is impossible.
(ii) Both internal, in the same cluster: this contradicts the Sidon property of C_i.
(iii) Both cross, for the same (i,j): then c_j−c_i = c′_j−c′_i gives c_j−c′_j = c_i−c′_i ∈ (C_j−C_j) ∩ (C_i−C_i) = {0}, so it is the
same pair.
Internal differences are unchanged by translation, so Y−Y ⊇ ⋃(C_i−C_i). The span bound is immediate. 8r²: b_k = 2pk + (k² mod p)
< 2p² ≤ 8r².

## [valid-routine] r2s4/C1 PROVED OTHER
**Statement.** Let A ⊆ [1,N] be Sidon, i.e. a+b=c+d with a,b,c,d∈A implies {a,b}={c,d} as multisets. Let X,Y ⊆ A be arbitrary; they need not be disjoint or cover A. Suppose every z∈[1,N]∖A satisfies one of:
 (T) z + y′ = x + y for some x∈X, y,y′∈Y;
 (R) z + x = y + y′ for some x∈X, y,y′∈Y, where y=y′ is allowed;
 (L) z + y = x + x′ for some x,x′∈X, y∈Y, where x=x′ is allowed.
Then A is maximal Sidon in [1,N]. In particular, [N] ⊆ A ∪ (X+(Y−Y)) ∪ ((Y+Y)−X) ∪ (X+X−Y) implies maximality.
**Beyond.** Extends the round-1 certificate lemma (family T only) to the families R and L. It is an instance of the general blocking lemma, so it is routine.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard blocking criterion for maximal Sidon sets (Bl(A) = (A+A−A) ∪ (A+A)/2), as used in [ESS94] and [Ru98b]", "why": "Each of (T), (R), (L) is a nontrivial relation z+a=b+c among elements of A∪{z} because z∉A, so this is just the definition of being blocked, restricted to subsets X, Y of A. It does not touch the core covering problem.", "panel": [{"verdict": "routine", "cite": "Standard blocking criterion for maximal Sidon sets (Bl(A) = (A+A−A) ∪ (A+A)/2), as used in [ESS94] and [Ru98b]", "significance": 0, "why": "Each of (T), (R), (L) is a nontrivial relation z+a=b+c among elements of A∪{z} because z∉A, so this is just the definition of being blocked, restricted to subsets X, Y of A. It does not touch the core covering problem."}, {"v`
**Proof or evidence.**

Fix z∈[1,N]∖A. In each case we have i₁+i₂=j₁+j₂ with i₁=z and i₂,j₁,j₂∈A, so all four lie in A∪{z}. Sidon for A∪{z} would need (z=j₁ ∧ i₂=j₂) or (z=j₂ ∧ i₂=j₁). But j₁,j₂∈A and z∉A, so z≠j₁ and z≠j₂. Both disjuncts fail and A∪{z} is not Sidon. Together with A ⊆ [1,N] and A Sidon, this is exactly maximality. No case needs distinctness: y=y′ in (T) gives z=x∈A, which is excluded by z∉A, and y=y′ in (R) or x=x′ in (L) gives a legitimate violation z+x=2y or z+y=2x. All equalities are additive, so the statement transfers verbatim to ℕ with no truncated subtraction. ∎

## [valid-routine] r2s4/C3 PROVED NEGATIVE
**Statement.** Let A = X ⊔ Y be Sidon, D = (Y−Y)∖{0}, S = Y+Y.
 (a) Collisions x₁+d₁ = x₂+d₂ with x₁≠x₂ and d_i∈D are 3-vs-3 relations (x₁+y₁+y₄ = x₂+y₂+y₃), and Sidon sets do contain them. Explicit example: A={0,1,3,7,12}, X={7,12}, Y={0,1,3}, with 10 = 7+(3−0) = 12+(1−3) and 9 = 7+(3−1) = 12+(0−3).
 (b) The only 2-vs-2 constraints linking X to the families T = X+D and R = S−X are X ∩ (X+D) = ∅ ⇔ (X−X)∩(Y−Y) = {0}, and X ∩ (S−X) = ∅ ⇔ (X+X)∩(Y+Y) = ∅. They are of identical type, and neither forces translates or reflected copies to be disjoint.
 (c) There is no infinite Sidon X ⊂ Z and finite nonempty Y with S−X tiling Z (every integer exactly once as s−x). The same holds with D∪{0} in place of S, which is Barrier 3.
**Beyond.** Corrects the round-1 "reflection slack" heuristic, which said (Y+Y)−X may have any multiplicity while Barrier 3 binds only X+(Y−Y). Both families have unrestricted multiplicity and symmetric avoidance constraints, so reflection by itself gives no structural escape from Barrier 3.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Newman, 'Tesselation of integers' (J. Number Theory 1977) for (c); (a),(b) are direct unwinding of the Sidon definition", "why": "Parts (a) and (b) are one-line consequences of the definition of a Sidon set (with a correct small example), and (c) is Newman's periodicity theorem applied to the tile S, i.e. the same argument as the team's existing Barrier 3. It only corrects an internal heuristic and makes no progress on the near-exact covering core.", "panel": [{"verdict": "routine", "cite": "Newman, 'Tesselation of integers' (J. Number Theory 1977) for (c); (a),(b) are direct unwinding of the Sidon definition", "significance": 0, "why": "Parts (a) and (b) are one-line consequences of the definition of a Sidon set (with a correct small exam`
**Proof or evidence.**

(a) A is Sidon: its positive differences 1,3,7,12,2,6,11,4,9,5 are all distinct. The identities are arithmetic, and both were checked by exp3.py. In general, x₁+y₁−y₂ = x₂+y₃−y₄ ⇔ x₁+y₁+y₄ = x₂+y₃+y₂, and Sidon says nothing about 3-term sums.
 (b) x = x′+y₁−y₂ with x≠x′ gives x+y₂ = x′+y₁, a nontrivial 2-vs-2 relation. Conversely, any such relation gives the equality. Likewise, x = y₁+y₂−x′ gives x+x′ = y₁+y₂, and {x,x′}≠{y₁,y₂} because X∩Y = ∅.
 (c) Suppose S−X = S+(−X) is a tiling of Z by translates of the finite set S. Newman's theorem says the translate set −X is periodic: −X+p = −X for some p ≥ 1. Then X ≠ ∅ is p-periodic. Pick a∈X; then a, a+p, a+2p ∈ X and a+(a+2p) = (a+p)+(a+p), so X is not Sidon. The finite-window analogue (periodic sets of period < 8 over 4 periods are never Sidon) was also checked in exp3.py. ∎

## [valid-known] r2s4/C2 PROVED STRUCTURE
**Statement.** A Sidon A ⊆ [1,N] is maximal iff every z∈[1,N]∖A satisfies (i) z+c=a+b for some a,b,c∈A, or (ii) 2z=a+b for some a≠b in A.
**Beyond.** Already on the blackboard (blocking lemma); recorded here only so that C1 is seen as a special case.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "known", "significance": 0, "cite": "Standard blocking criterion; implicit in Erdős–Sárközy–Sós [ESS94] (greedy ≫ N^{1/3} count) and Ruzsa [Ru98b]", "why": "This is the elementary characterization of when z can be added to a Sidon set (z = a+b−c or 2z = a+b with a≠b), used in every lower-bound and completion argument for this problem. It is correct but contributes nothing toward the O(N^{1/3}) question.", "panel": [{"verdict": "known", "cite": "Standard blocking criterion; implicit in Erdős–Sárközy–Sós [ESS94] (greedy ≫ N^{1/3} count) and Ruzsa [Ru98b]", "significance": 0, "why": "This is the elementary characterization of when z can be added to a Sidon set (z = a+b−c or 2z = a+b with a≠b), used in every lower-bound and completion argument for this problem. It is correct but co`
**Proof or evidence.**

(⇐) Case (i) is as in C1. In case (ii), z+z=a+b with z∉{a,b}. (⇒) Suppose A∪{z} is not Sidon, witnessed by i₁+i₂=j₁+j₂ with the multisets differing. Since A is Sidon, z occurs. If z occurs on both sides, cancel it to get w=w′, so the multisets agree, a contradiction. So z occurs on one side only, say on the left. If it occurs once, then z+c=a+b with a,b,c∈A, which is (i). If twice, then 2z=a+b with a≠b, since a=b would give z=a∈A; this is (ii). ∎

## [broken] deep/C4 PROVED NEGATIVE
**Statement.** Let q ≡ 2 (mod 3) be a prime power, or more generally q with gcd(3, q−1) = 1. Then F_{q³}^* = F_q^* × K with K = ker N, and Y = {(θ+a)^{q−1}} ∪ {1} ⊂ K is the Singer set of C3. For any injective r : F_q^*∖{1} → F_q, put X_r = {x_λ := λ·(θ − r(λ))^{q−1} : λ ∈ F_q^*∖{1}}. Then:
(i) X_r is a transversal of the nontrivial cosets of K.
(ii) X_r ∪ Y has no nontrivial relation of the forms x x′ = x″ y or x x′ = x″ x‴ (x's in X_r, y ∈ Y).
(iii) For every λ ≠ 1, x_λ x_{1/λ} = y y′ holds with y = (θ−r(λ))^{q−1} and y′ = (θ−r(1/λ))^{q−1}. This gives exactly (q−1)/2 violations for q odd. So X_r ∪ Y is never Sidon.
**Beyond.** this pinpoints why the algebraic route to C2 fails. The B₃ structure kills exactly the expensive constraints, the 3- and 4-term relations, which carry ≈ 2h load in the union bound. It violates exactly the cheap pair constraints, which C1′ handles at no cost by Fourier pairing. The two mechanisms are incompatible, because modifying any x_λ destroys the polynomial-identity structure.
**Referee.** `{"valid": false, "first_error": "(iii): the claim of 'exactly (q−1)/2 violations' never rules out the relation forms xy=x′y′, xy=y′y″, yy′=y″y‴, or multiple representations of x_λx_{1/λ} as yy′ (all easy via norms and the Singer Sidon property, but unproved). Also the conclusion 'X_r ∪ Y is never Sidon' is false for q=2, which satisfies the hypotheses: X_r=∅ and Y is Sidon. The deduction needs some λ≠1, i.e. q≥3.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "Edge case: q = 2 satisfies q ≡ 2 (mod 3) and gcd(3, q−1) = 1, but F_2^*∖{1} is empty, so X_r is empty and X_r ∪ Y = Y, the Singer set {1,2,4} mod 7, which IS Sidon. This contradicts 'X_r ∪ Y is never Sidon'. For all admissible q ≥ 3, (i)–(iii) check out. The xx=yy relations with μ = 1/λ are the only violations, there is exactly one per pair {λ,1/λ} since Y is Sidon, and the count is (q−1)/2 for q odd. Fix: assume q ≥ 3. The 'incompatibility' commentary is heuristic and unproved.", "severity": "fixable"}`
**Proof or evidence.**

(i) N(x_λ) = λ³·N(θ−r)^{q−1} = λ³, since N(u^{q−1}) = N(u)^{q−1} = 1. The map λ ↦ λ³ is a bijection of F_q^* when gcd(3, q−1) = 1, so the cosets of K, which are the norm classes, are hit once each, and λ ≠ 1 gives the nontrivial ones.
(ii) Take norms. x_λ x_μ = x_ν y forces λ³μ³ = ν³, so λμ = ν, and then [(θ−r(λ))(θ−r(μ))]^{q−1} = [(θ−r(ν))(θ+a)]^{q−1}. Since ker(u ↦ u^{q−1}) = F_q^*, this means (θ−r(λ))(θ−r(μ)) = c(θ−r(ν))(θ+a) with c ∈ F_q^*. Both sides have degree ≤ 2 in the basis 1, θ, θ², so this is a polynomial identity, and it forces r(ν) ∈ {r(λ), r(μ)}. But ν = λμ ≠ λ, μ because λ, μ ≠ 1, and r is injective: contradiction. For y = 1 the degrees differ. The case λ = μ is identical. For x x′ = x″ x‴, the same argument gives {r(λ), r(μ)} = {r(ν), r(ρ)}, i.e. the relation is trivial.
(iii) x_λ x_{1/λ} = (θ−r(λ))^{q−1}(θ−r(1/λ))^{q−1}, and both factors lie in Y. The relation is nontrivial because x's ∉ K. For λ = −1 it reads x_{−1}² = y². ∎

## [broken] r1s1/C2 PROVED CONDITIONAL
**Statement.** G1\* ⇒ minMaximalSidonSet(N) = O(N^{1/3}). More precisely, if Y_L exist with |Y_L|² ≤ σL and Y_L ⊆ [1, C L^{3/2}],
then minMaximalSidonSet(N) ≤ (√(σλ) + 1/λ + o(1))·N^{1/3} for any fixed λ with C λ^{3/2} ≤ 1, taking L = ⌊λN^{2/3}⌋.
**Beyond.** It replaces the blackboard's three gaps G1, G2, G3 with the single gap G1\*, and relaxes G1's span to O(L^{3/2}).
**Referee.** `{"valid": false, "first_error": "Step 'Apply C1': the proof only verifies Y_L ⊆ [1,N] and never checks that Y_L satisfies the other hypotheses C1 must need (e.g., Y_L−Y_L covering an interval of length ~L, Sidon compatibility of Y_L with the ~N/(L+1) added points, and maximality). Size and span alone cannot suffice: Y_L = ∅ satisfies G1* for every σ and every C>0, and with C small and λ = C^{-2/3} the claim would give minMaximalSidonSet(N) ≤ (1/λ+o(1))N^{1/3} with λ arbitrarily large. That contradicts the standard bound |A| ≥ cN^{1/3}, since A+A−A ∪ (A+A)/2 must cover [1,N]. So the claimed reduction of G1,G2,G3 to G1* is false as stated.", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

Set L = ⌊λN^{2/3}⌋. Then C L^{3/2} ≤ Cλ^{3/2}N ≤ N, so Y_L ⊆ [1,N]. Apply C1:
|Y_L| + ⌈N/(L+1)⌉ ≤ √(σλ)N^{1/3} + N^{1/3}/λ + 1. ∎

## [broken] r1s3/C1 PROVED SPECIAL
**Statement.** Let q be prime, h=q²+q+1, S⊂[0,h) an integer lift (after multiplier u and rotation) of a Singer perfect difference set mod h, T=S−S, m≥2, y0∈[0,m), Y={m s+y0}. Suppose that for every column i∈[0,m)∖{y0} there are t_i, d_i with 0≤t_i<t_i+d_i<h, d_i∉T, and [0,h)⊆(t_i+T)∪(t_i+d_i+T). Put X={i+m t_i, i+m(t_i+d_i)}. If A=X∪Y is Sidon, then A is Sidon and every z∈[0,mh) in a column i≠y0 is blocked; the column y0 still has to be checked separately. Computationally, A+1 ⊂ [1,mh] was a maximal Sidon set with |A| = q+1+2(m−1) in each case below.
**Beyond.** first explicit structured integer certificates of the blackboard "X ⊔ Y" type that need no greedy completion. They are finite only; ratios 2.06–2.37 are no better than greedy at these sizes.
**Referee.** `{"valid": false, "first_error": "The theorem's content (A Sidon, column y0 blocked, existence of t_i,d_i with the coverage property) rests entirely on an unshown computation: 'each case below' lists no cases (no q, m, y0, S, t_i, d_i or A), so nothing is verifiable. The statement 'if A is Sidon then A is Sidon' is circular and never proves the Sidon property. The column-blocking lemma itself is correct.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

The certificate lemma (KNOWN) plus the brute-force check (script bc.py, run8 + brute_maximal).

## [broken] r2s1/C2 PROVED NEGATIVE
**Statement.** In C1 assume S ⊂ G/H is a perfect difference set (every nonzero element of G/H is uniquely s−s′). Write D = ⋃_s (A_s−A_s) ⊂ H.
(1) For t ∈ S and y ∈ π^{-1}(t)∖A: y is blocked by A iff y ∈ A_t + D, or 2y = a+a′ with a ≠ a′ ∈ A_t, or 2y = 2a with a ∈ A_t, y ≠ a.
(2) For t ∉ S, the representations t = s1+s2−s3 with s_i ∈ S and s3 ∉ {s1,s2} are exactly the ones with s2 ranging over S (s1, s3 then unique): q+1 ordered ones, i.e. about (q+1)/2 unordered ones. y ∈ π^{-1}(t) is blocked by a triple iff y ∈ ⋃_{reps} (A_{s1}+A_{s2}−A_{s3}), together with midpoints 2y ∈ A_s+A_{s′}, 2πy = s+s′.
COROLLARY. If A_t = ∅ for some t ∈ S, the whole fibre π^{-1}(t) (|H| points) is unblocked. In particular the fiber-scalar family {κ(θ+a)} (with no scalar fibre) leaves all of F_q* unblocked, so it is never maximal in F_{q³}*.
COROLLARY 2. In F_{q³}* (q odd) take every A_t nonempty and use the maximal pairing D = H∖{1,−1}, i.e. (q−3)/2 fibres K_s = σ_s{1,ζ_s} with the {ζ_s^{±1}} partitioning F_q*∖{±1}. Then every fibre over S is fully blocked. Proof: write y = a·η with a ∈ A_t and η ∈ H. If η = 1 then y = a. If η = −1 then y² = a² with y ≠ a, a nontrivial relation. Otherwise η ∈ D and y ∈ A_t·D. So the entire leftover lies in the q² fibres over t ∉ S. There the problem is exactly: cover H ≅ Z_{q−1} by the ≈(q+1)/2 translates c_rep + (K_{s1}K_{s2}K_{s3}^{-1}) from C2(2).
**Beyond.** the r1s2 C2(a) law covered only Bose–Chowla (all K_a = {1}). This is the bookkeeping for the whole fiber family the lead asked about, and it shows that family alone cannot be maximal.
**Referee.** `{"valid": false, "first_error": "Corollary 2, final reduction: it claims the leftover problem over t ∉ S is 'exactly' covering H by the ≈(q+1)/2 translates c_rep·K_{s1}K_{s2}K_{s3}^{-1}, omitting the midpoint blocks y² ∈ A_s A_{s'} (2πy = s+s', s≠s') that C2(2) itself lists. Exactly q(q+1)/2 of the q² outer fibres carry such a condition, each blocking up to 2|A_s||A_{s'}| points, so covering by translates is stronger than the true maximality condition, not equivalent. Parts (1), (2) and Corollary 1 (fibre-scalar family never maximal) check out.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "Parts (1), (2) and Corollary 1 are correct. Corollary 2's final reduction is misstated. It says the leftover over t∉S is 'exactly' covering H by the translates c·K_{s1}K_{s2}K_{s3}^{-1}, but this omits the midpoint relations y² = a·a′ that C2(2) itself lists. For a∈A_s, a′∈A_{s′} with s≠s′, t=(s+s′)/2 is well-defined since |G/H| is odd. t∉S, because otherwise 2t=s+s′ in S would force s=s′=t by the Sidon property. Whenever a·a′ is a square in F_{q³}*, the fibre over t contains two blocked points not accounted for by the translates. So the stated covering problem overstates the leftover. Fix: include the midpoint points in the covering problem.", "severity": "fixable"}`
**Proof or evidence.**

(1) Suppose y = a+b−c with c ∉ {a,b}, y ∈ π^{-1}(t), t ∈ S. Then t+π(c) = π(a)+π(b) in S, so by Sidon {t,π(c)} = {π(a),π(b)}, say π(a) = t, π(b) = π(c). Then y = a + (b−c) ∈ A_t + D, with b ≠ c since c ∉ {a,b}. Conversely, a ∈ A_t and b,c ∈ A_s with b≠c give y = a+b−c, and then c ∉ {a,b} unless c = a, which would mean y = b ∈ A.
For midpoints: 2y = a+a′ gives 2t = π(a)+π(a′), so π(a) = π(a′) = t by Sidon.
(2) For t ∉ S: t − s2 ≠ 0, so t − s2 = s1 − s3 has a unique solution with s1 ≠ s3. And s3 ≠ s2, since s3 = s2 would give t = s1 ∈ S.
Corollary: for y ∈ F_q* (log ≡ 0 mod q²+q+1), suppose y = u1u2/u3. Then y·κ3(θ+c) = κ1κ2(θ+a)(θ+b). The left side has θ²-coefficient 0 and the right side has θ²-coefficient κ1κ2 ≠ 0, which is impossible since 1, θ, θ² is a basis. Midpoints y² = u1u2 fail in the same way. And y ∉ A, since its θ-coefficient is 0. ∎
CHECK: SAT (pysat/CaDiCaL) found no maximal set inside the fiber-scalar family for q=5,7, even without a size bound. Enumeration with all of E = {κ(θ+a)} found the never-coverable points to be exactly the q−1 scalars, for q=5,7,11.

## [not validated] deep/C2 CONJECTURED ANALOGUE
**Statement.** For every prime power q (numerically: every prime q ≤ 67 and every prime power q ≤ 32), the random-greedy transversal of C1 with m = q−1 succeeds. Hence Z_{q³−1} has a maximal Sidon set of size 2q−1 = (2+o(1)) n^{1/3}.
**Beyond.** this is the assignment's target group Z_{q³−1}, obtained via H = (q−1)Z_n of order q²+q+1. It does NOT need B ∪ B′ ∪ E.
**Proof or evidence.**

t2.py (seed 2026), t3.py (seed 7) and t4.py (seed 11):
- t2: success in 5/5 trials for q = 5, …, 29 and 2/2 trials for q = 31, …, 47.
- t3: success with brute-force verification for q = 53, 59, 61, 67.
- t4: 5/5 verified successes for each prime power q = 2, 3, 4, 8, 9, 16, 25, 27, 32.
- Not one failure among the m = q−1 runs.
WHAT A PROOF NEEDS: after C1′, the pair constraints are free. A proof must show that a Sidon transversal exists despite a 3-/4-term load of ≈ 2h per coset at c = 1, i.e. that the forbidden lines, ovals and points overlap far more than the union bound allows. A random-greedy/differential-equation analysis of the free fraction (≈ 0.06h observed) would do it, as would an exact algebraic transversal. C4 shows the obvious algebraic one fails.
- Outputs for q ≤ 31 were verified by brute force (Sidon, maximal, |A| = 2q−1).
- The minimum number of free candidates in any coset during the run is a stable fraction of h, between 0.045 and 0.067 (q = 17, …, 47). It does not decay.
MECHANISM: the forbidden set in the last coset consists of:
- a translate of Y+Y (≈ h/2);
- ≈ 1.5c·q lines of the cyclic projective plane (translates of S);
- ≈ c·q/2 ovals (translates of −S);
- ≈ c²q²/2 points.
The Poisson heuristic predicts a free fraction ≈ ½·exp(−1.5c − 0.5c²) ≈ 0.07 at c = 1, which matches the data. The C1 union bound fails exactly because 1/2 + 1.5c + 0.5c² > 1 for c > 0.303.

## [not validated] r1s1/C4 CONJECTURED OTHER
**Statement.** L*(k) = max L such that some k-element Sidon set Y ⊂ [0,S) has [1,L] ⊆ Y−Y (span cap S = min(3L+2, 60)):
k=3..9 → L ≥ 3, 6, 9, 13, 18, 21, 28 (exact maxima under the cap). So σ_k = k²/L*(k) ≈ 2.67–3.05, with no visible growth.
**Proof or evidence.**

(none)

## [not validated] r1s2/C3 CONJECTURED NEGATIVE
**Statement.** Let A = B ∪ qB in Z_{q³−1}, with θ as in C2(b).
- A is not Sidon. It has exactly 5(q−1) coincident differences, observed for every prime q = 7, …, 31.
- Let r(x) be the number of representations x = a+b−c, with {a,b} a multiset from A and c ∉ {a,b}. Then r(x) is asymptotically distributed as Ber(½) + Ber(½) + Poisson(λ−1), with λ = 4 − o(1).
- Hence the unblocked fraction tends to e^{−3}/4 ≈ 0.012–0.013, i.e. Θ(m) points, not O(q).
- More generally, r twists leave a fraction ≈ 2^{−r}·e^{−λ_mixed} > 0.
- Consequently Galois/multiplier twists of B cannot produce the near-exact cover needed for O(m^{1/3}).
**Beyond.** This tests the frontier's escape clause from the Poisson barrier ("does not rule out structured (algebraic or B_3-like) sets") on the most natural algebraic candidates. They behave like Poisson in the mixed part. The deterministic B₃ part only contributes independent half-covers.
**Proof or evidence.**

P(r=0) observed vs model:

| q | observed | model ¼e^{−(λ−1)} |
|---|---|---|
| 11 | 0.0069 | 0.0142 |
| 17 | 0.0098 | 0.0134 |
| 23 | 0.0104 | 0.0131 |
| 31 | 0.0130 | 0.0130 |
| 37 | 0.0141 | 0.0130 |
| 41 | 0.0134 | 0.0130 |

Mechanism:
- r_B and r_{qB} are deterministic {0,1} indicators of two discriminant conditions, which are asymptotically independent quadratic characters.
- The mixed relations (b₁ + qb₂ − b₃, …) are ≈ 3q³ values with no further algebraic structure, so they behave as Poisson.
- Greedy completion (random order, 5 runs each) gives the same final size from the empty set, from B, from B∪qB made Sidon, and from the Galois orbit B∪qB∪q²B made Sidon. Sizes/m^{1/3}: 1.94 (q=7), 2.17 (13), 2.28 (19), 2.46 (31), 2.52 (37). This tracks (log m)^{1/3} (1.80 → 2.21), with ratio ≈ 1.08–1.14.

## [not validated] r1s3/C3 CONJECTURED NEGATIVE
**Statement.** For the column-pair construction of C1, the number of distinct d∈[1,h) for which some t gives an exact two-translate cover [0,h)⊆(t+T)∪(t+d+T) is o(q), uniformly over multipliers and rotations. So C1 cannot reach m≍q, i.e. it cannot give |A|=O(N^{1/3}) along N=mh. More generally, any certificate that uses O(1) translates of a single Singer difference set per column needs coverage that a quasi-random T (density 1/2, |Ŝ|=√q) cannot supply exactly.
**Proof or evidence.**

distinct exact d = 19, 33, 31, 42, 23, 16, 2 for q = 7, 11, 13, 17, 19, 23, 29. With up to 2 uncovered points allowed: 25, 42, 50, 56, 44, 44, 9. For the median multiplier the exact counts are 17, 8, 15, 1, 2, 0, 0.
MECHANISM: exact covers occur only when T contains a long core interval (−w,w) (C2a), and w/h→0 by C2(c). Without the core, T restricted to a window looks like a density-1/2 quasi-random set, so two windows overlap in ≈h/4 points and cover ≈3h/4, not h. A rigorous proof would need a windowed lower bound on #{u∈window: u∈T, u−d∈T}, i.e. on windowed counts of s1−s2−s3+s4=d for Sidon S.

## [not validated] r1s3/C4 CONJECTURED NEGATIVE
**Statement.** Seeding with the Bose–Chowla B_3 set B⊂Z_{q³−1} (which blocks exactly half the group, since a+b−c is injective by B_3) and completing greedily, whether randomly, linearly, or by max gain, gives no gain over seedless greedy. k/N^{1/3} keeps growing in every variant.
**Proof or evidence.**

see Data.

## [not validated] r1s4/C1 PROVED QUANT
**Statement.** For a probability measure μ on [0,1], let f_μ be the law of a+b−c with a,b,c i.i.d. ~ μ. For δ>0 set
c(δ) = sup_μ inf{ f_μ(I)/|I| : I ⊆ [0,1] a closed interval, |I| ≥ δ }.
(i) For every δ>0, every maximal Sidon A ⊆ [N] with k = |A| satisfies N ≤ (c(δ)/2)·k³ + (k²+k+1)/δ (taking a limit in the choice of I). Hence liminf k³/N ≥ 2/c(δ).
(ii) There is δ>0 with c(δ) < 1. Consequently minMaximalSidonSet(N) ≥ (1−o(1))(2N/c)^{1/3} for some absolute c < 1.
**Beyond.** KNOWN item 1 gives only (1−o(1))(2N)^{1/3}, the constant from the plain count.
**Proof or evidence.**

(i) Blocking lemma: x ∈ [N]∖A is blocked iff x ∈ A+A−A with c ∉ {a,b} (multiset {a,b}), or 2x = a+b with a ≠ b.
Let μ_A be uniform on {a/N : a ∈ A} and let I ⊆ [0,1] be a closed interval. At least N|I| − 1 integers x ∈ [1,N] have x/N ∈ I. Each one lies in A (≤ k of them), or is a midpoint (≤ k²/2), or equals a+b−c with (a+b−c)/N ∈ I.
The number of triples ({a,b} multiset, c) of the last kind is ≤ (#ordered triples + #diagonal)/2 ≤ (k³ f_{μ_A}(I) + k²)/2.
So N|I| − 1 ≤ k + k² + (k³/2) f_{μ_A}(I). By the definition of c(δ), for every ε>0 there is an I with |I| ≥ δ and f_{μ_A}(I) ≤ (c(δ)+ε)|I|. Dividing by |I| ≥ δ gives N ≤ (c(δ)+ε)k³/2 + (k²+k+1)/δ.
If k ≥ N^{0.4} there is nothing to prove; otherwise k²/δ = o(N), and the claim follows.
(ii) Note c(δ) ≤ 1, since I = [0,1] has f([0,1]) ≤ 1. Suppose c(1/n) = 1 for all n. Pick μ_n with f_{μ_n}(I) ≥ (1−1/n)|I| for all closed I ⊆ [0,1] with |I| ≥ 1/n.
By Prokhorov, pass to a subsequence with μ_n → μ weakly. Then μ_n^{⊗3} → μ^{⊗3}, and pushing forward by the continuous map (a,b,c) ↦ a+b−c gives f_n → f := f_μ weakly. By portmanteau, f(I) ≥ limsup f_n(I) ≥ |I| for every closed I ⊆ [0,1] of positive length.
Hence f((s,t)) ≥ t−s for open intervals (take increasing closed subintervals), so f(U) ≥ λ(U) for open U ⊆ (0,1). By outer regularity, f ≥ λ on Borel subsets of (0,1).
Since f has total mass 1, f = λ on (0,1) and f gives zero mass to the complement. So supp f = [0,1].
Let S = supp μ, α = min S, β = max S. Then supp f = S+S−S (a compact set), which contains 2β−α and 2α−β. Both lie in [0,1], so 3(β−α) ≤ 1.
Var(a+b−c) = 3Var(μ) must equal Var(Unif[0,1]) = 1/12, so Var(μ) = 1/36. By Popoviciu, Var(μ) ≤ (β−α)²/4 ≤ 1/36, with equality only for μ = ½δ_α + ½δ_β. But then f is atomic, not λ. Contradiction. ∎
(The proof was checked step by step; the only non-elementary tools are Prokhorov, portmanteau, outer regularity and Popoviciu's inequality.)

## [not validated] r1s4/C2 CONJECTURED QUANT
**Statement.** c* := lim_{δ→0} c(δ) satisfies 0.71 ≲ c* < 1. The lower bound from C1's method is therefore at best ≈ (2.8N)^{1/3}.
**Proof or evidence.**

cstar.py runs exponentiated-gradient ascent over μ on a 241-point grid, using M = 24 bins of [0,1]. It reaches a minimum bin coverage M·f(B_j) of 0.7125, with 0.18 of f's mass outside [0,1].
The optimiser puts ≈ 0.46 of the mass in an atom near 1/2 plus a spread-out remainder. Mechanism: with an atom w at 1/2, f ≥ w²(2μ + reflected μ), so the atom "copies" μ.
For comparison, exact small data (largest n with a maximal k-set: 144 at k = 8) gives k³/n ≈ 3.56, i.e. an effective 2/c ≈ 3.56 at small k.

## [not validated] r1s4/C3 CONJECTURED OTHER
**Statement.** the random greedy maximal Sidon set has k³/(N ln N) → const ≈ 2.6–2.7, and k³/N does not flatten.
**Proof or evidence.**

see Data (N up to 1e7).

## [not validated] r1s4/C4 CONJECTURED NEGATIVE
**Statement.** Adaptive choice does not beat the log. In best-of-s greedy, each step adds the candidate (among s random unblocked points) that blocks the most new points. This lowers the constant (k³/(N ln N) ≈ 1.8–2.3 for s = 8–64) but k³/N keeps growing.
Heuristic mechanism: with leftover U of density p, an element x ∈ U blocks ~3k²p points of U. Covering U is then a dominating-set problem in a random-like graph of degree d = 3k²p, which costs ≈ (N/(3k²))·log d elements. Getting p down to d/(3k²) by random means needs k³ ≍ N log N anyway.
So any route that leaves a Poisson-like leftover loses log N, whatever (adaptive) completion is used, unless relations among the completion elements (Z+Z−A, of size |Z|²k) are themselves structured.
**Proof or evidence.**

(none)

## [not validated] r2s1/C3 CONJECTURED NEGATIVE
**Statement.** Take Sidon lifts of the full Singer line through F_q* in F_{q³}*: |K_s| ∈ {1,2}, pair differences ±d_s disjoint, |A| = (3q−1)/2, λ = |A|³/(2m) → 27/16. Even with the best choice of fibre scalars σ_s, the unblocked count stays ≥ c·q³ with c ≈ 0.12. That is, the structured family beats Poisson by a constant factor only.
**Proof or evidence.**

see Data. The ratio unblocked/m is 0.064 (q=7), 0.100 (11), 0.109 (13), 0.118 (17), 0.126 (19), and is rising towards the σ≡0 value ≈0.13. Mechanism: the fibre offsets are the distinct B_3 values, given by the quadratic-character law (blocked set in a fibre = {ν : χ(P_t(ν)) ≥ 0}, with P_t quadratic). Multiplying them by K's of size ≤ 2 is a bounded perturbation that cannot correlate with q² independent fibre conics.

## [not validated] r2s3/C2 OTHER REDUCTION
**Statement.** For every N, m(N)³ ≥ (2/c* − o(1))N, where c* is the continuum constant above. Moreover c* ≥ 0.6746: the histogram
density on 40 cells found in s1.py gives law(X+Y−Z) ≥ 0.6746·Leb on [0,1]. It has an atom-like spike of mass ≈ 0.44 at x ≈ 0.49.
**Beyond.** makes the triple-counting lower bound an explicit extremal problem. If c* ≈ 0.675, the method gives about 1.436·N^{1/3}.
**Proof or evidence.**

see C1. The histogram μ is a genuine measure, and its bin masses are computed exactly from the kernel (1/6, 2/3, 1/6) of
U1+U2−U3. So 0.6746 is a rigorous lower bound on c*, up to floating point. This means C1's method can never exceed (2/0.6746)^{1/3} ≈ 1.436.

## [not validated] r2s4/C4 CONJECTURED NEGATIVE
**Statement.** Place an Erdős–Turán Sidon cluster Y of size c·N^{1/3} (c ∈ {1,2}) at the centre of [N], then complete by best-of-32 greedy, i.e. pick the sampled unblocked point that blocks the most new points. The final size is ≈ 1.2·(N log N)^{1/3}, so the log factor is not removed. Reflection-type blocks (R ∪ L) cover only 0.2–2% of points that no other family covers.
**Beyond.** Tests the "central cluster plus spread X" shape suggested by the r1s4 optimiser. With a greedy X it behaves like plain greedy.
**Proof or evidence.**

See Data. Total family coverage is ≈ 2.9 times the number of non-elements, which is the redundancy predicted by the Poisson barrier.

## Frontier map

=== DIRECTION
**TRUE**, confidence **0.65**.

**Notation.** k = |A|. Bl(A) = {x ∉ A : A ∪ {x} is not Sidon}. A is maximal in [N] iff [N] ∖ A ⊆ Bl(A).

**Strongest evidence for TRUE:**
1. Ruzsa's construction misses O(N^{1/3}) by only a factor (log N)^{1/3}. That factor is exactly the coupon-collector loss of a random covering, not a structural obstruction.
2. The cyclic analogue holds for infinitely many n via a Singer subgroup plus a greedy transversal. This is blackboard work, unverified.
3. The relation a+b−c = a′+b′−c′ is the B_3 equation. So a B_3 set has an injective triple map. The Bose–Chowla B_3 set in Z_{q³−1} has size q ≈ n^{1/3}. By the computation in KNOWN (unverified) it blocks about half of the group, with zero redundancy. The near-injective "half cover" that the problem needs therefore exists algebraically.
4. The only lower-bound mechanism known is counting, and it gives (2N)^{1/3}.

**Evidence against TRUE:**
- In the exact small data, the integer ratio N/k³ falls: 0.336, 0.310, 0.294, 0.281 for k = 5, …, 8. This is consistent with a slow (log-type) decay as well as with a constant.
- No method controls the wrap-around and boundary effects in Z.

**The formal statement.** It is faithful to the problem. The set inside sInf is never empty, since some maximal Sidon set always exists, so there is no degenerate shortcut. A proof needs an explicit witness for every large N.

=== KNOWN
- Every maximal Sidon A ⊆ [N] satisfies N − k ≤ k²(k+1)/2 + k(k−1)/2, hence k ≥ (1−o(1))(2N)^{1/3} | standard; the blackboard's weaker form is (N/2)^{1/3} | count x = a+b−c with {a,b} a multiset, and x = (a+b)/2.
- The greedy maximal Sidon set has size ≫ N^{1/3} | [ESS94], "easy" | the same count.
- There is a maximal Sidon set in [N] of size ≪ (N log N)^{1/3} | Ruzsa [Ru98b] | algebraic Sidon set, random thinning, greedy completion.
- The random greedy Sidon process gives size ≳ (N log N)^{1/3} w.h.p. | Bennett–Bohman 2016, random greedy independent sets (recalled, check) | differential-equations and nibble analysis.
- A Sidon set in [N] has size ≤ √N + O(N^{1/4}), and √N(1−o(1)) is attained | Erdős–Turán, Lindström, Singer, Bose; the constant 0.998 is from Balogh–Füredi–Roy, and 0.99703 from O'Bryant | counting and finite fields.
- Bose–Chowla: B_3 sets of size q exist in Z_{q³−1}, hence B_3 sets in [N] of size (1−o(1))N^{1/3} | standard | {log_g(θ+a) : a ∈ F_q} with F_{q³} = F_q(θ).
- Difference bases: if [1,n] ⊆ Y−Y then |Y|² ≥ 2.434n (Leech; 2.4344 by Bernshteyn–Tait), and |Y|² ≤ (2.6458+o(1))n is achievable (Golay) | literature (recalled) | counting and Fourier.
- Perfect difference sets: there are Sidon A ⊂ Z with A−A = Z and A(x) ≥ x^{√2−1+o(1)} | Cilleruelo–Nathanson 2008 (recalled) | built on Ruzsa's Sidon set.
- F_2^n analogue: maximal Sidon sets of size close to 2^{n/3} | Redman–Rose–Walker; Nagy, "saturating Sidon-type sets" (recalled; exact form to be checked) | linear-algebraic constructions.
- Exact small data:
  - Largest n admitting a maximal k-set in [n]: 10, 22, 42, 67, 101, 144 for k = 3, …, 8.
  - Cyclic analogue c(k): 14, 30, 50, 84, 126 for k = 3, …, 7.
  - Source: forum, OEIS A382397/A399118, Huber 2026 | exhaustive search.
- Certificate lemma: if A = X ⊔ Y is Sidon and X + ((Y−Y) ∪ {0}) ⊇ [N], then A is maximal | blackboard (elementary, correct) | z = x+y−y′ ⇒ z+y′ = x+y.
- Monotonicity: Bl(A) ⊆ Bl(A′) for Sidon A ⊆ A′. Hence a Sidon A₀ with u unblocked points completes to a maximal set of size ≤ |A₀| + u | standard | greedy completion.
- Cyclic analogue: maximal Sidon sets of size O(n^{1/3}) in Z_n for n = m(q²+q+1) | blackboard (unverified) | Singer subgroup plus greedy transversal.
- Bose–Chowla B = {log(θ+a)} in Z_{q³−1} blocks y = g^x roughly when z² − σ₁z + σ₂ splits over F_q | this memo (derivation, unverified; check numerically) | the triple map is injective (B_3) and covers about q³/2 points.
  - c is forced to be c = (1 − (yθ)₂)/y₂ by the θ²-coordinate.
  - Then σ₁ and σ₂ are read off the θ- and 1-coordinates of y(θ+c).
  - Over F_p³ the moment curve gives the same picture: the cubic in u degenerates to a linear equation, leaving one quadratic.

=== BARRIERS
- **Counting.** The triples give ≤ k³/2 values, so the cover must have bounded average multiplicity | this defeats any construction with ω(1) redundancy | it does not rule out a cover with constant redundancy.
- **Coupon collector / Poisson.** If the multiplicities r(x) are asymptotically Poisson with mean λ ≍ k³/N, then the unblocked fraction is e^{−λ}, which forces k ≳ (N log N)^{1/3}. Greedy completion over a random leftover also costs (N/k²)·log N | this defeats Ruzsa-type random thinning, nibble, and random greedy | it does not rule out structured (algebraic or B_3-like) sets whose blocking correlations are far from Poisson.
- **Tiling rigidity.** A finite D tiles Z only periodically (Newman), and a Sidon X is never periodic. Also, in any certificate X ⊔ Y one needs (X−X) ∩ (Y−Y) = {0}, which makes X+D a packing as well as a covering | this defeats exact tilings, and any D containing a full interval of length ≥ (max gap of X) at a reachable distance (e.g., the "T + interval" construction) | it does not rule out near-tilings with O(N^{1/3}) defects, or D with holes aligned to X−X.
- **Wrap-around (half-difference).** The integer lift of a Singer set realises exactly one of r and m−r as a positive difference. Second blocks given by a translate, a reflection, or a set with the same difference set are never Sidon | this defeats the direct cyclic-to-interval transfer | it does not rule out arc-confined cyclic sets (T4), or blocks with genuinely different difference sets.
- **Difference-basis constant.** By Leech and Bernshteyn–Tait, a Sidon Y with Y−Y ⊇ [1,L] wastes at least 0.21L differences beyond L | this defeats "perfect" interval-difference schemes and turns G2 into an explicit constant game | it does not rule out O(1) slack.
- **No monotonicity in N.** Restricting a maximal set from [N′] to [N] loses blockings | this defeats naive interpolation from special N | it does not rule out the robust arc-reduction of T4.
- **Endpoint profile.** A uniformly distributed A blocks the ends of [N] at only half the average rate, so it needs k ≥ (4N)^{1/3} | this defeats nothing at the level of O(N^{1/3}), but every tight construction must be non-uniform | it says nothing about the order of magnitude.

=== CORE
**What remains.** For all large N, construct a Sidon A ⊆ [N] with |A| ≤ C·N^{1/3} and [N] ∖ A ⊆ Bl(A). Equivalently, construct a Sidon A₀ of size O(N^{1/3}) leaving only O(N^{1/3}) unblocked points; this means a covering of [N] by a+b−c with bounded multiplicity, missing only o(k) points.

**Why it is hard:**
- The cover has to be almost exact (miss ≤ N^{−2/3} of all points). Random methods leave a constant fraction exp(−λ) uncovered.
- Exact algebraic objects (Singer and Bose sets, B_3 sets) live in cyclic groups or F_q^d. Their integer lifts lose half the relations and break at the boundary.
- Structured certificates X ⊔ Y must be packing-and-covering at once (Barrier 3), and every constraint family has density Θ(1), so constants decide.
- Any formal proof also needs an explicit witness family valid for every N.

=== TARGET T1
TYPE: QUANT
STATEMENT: For all large N, minMaximalSidonSet(N) ≤ C·N^{1/3}(log N)^{1/3−c} for absolute C and c > 0. A weaker version replaces (log N)^{1/3−c} with (log N/ log log N)^{1/3}.
BEYOND: Ruzsa's (N log N)^{1/3}, which has stood since 1998. No improvement of the log factor is known.
VALUE: Breaking the log requires defeating the Poisson barrier, which is the only barrier between Ruzsa and CORE. The mechanism (structured leftover or correlated blocking) would likely scale to O(N^{1/3}).
SIGNIFICANCE: 2
TEST: Implement Ruzsa's construction and the candidate. For N ≤ 10^8, plot k³/N and k³/(N log N) and check which one flattens.

=== TARGET T2
TYPE: QUANT
STATEMENT: Define κ* = inf over probability measures μ on [0,1] of 2/ess inf_{x∈[0,1]} (dν/dx), where ν is the law of U+V−W with U, V, W i.i.d. ~ μ. Then:
- 2 < κ* ≤ 4;
- every maximal Sidon A ⊆ [N] has |A| ≥ (1−o(1))(κ*N)^{1/3};
- κ* is computed to 3 digits.
BEYOND: The counting bound (2N)^{1/3}. Strictness κ* > 2 is plausible: equality forces ν = Unif[0,1] with supp μ of length 1/3, i.e. μ̂ = e^{iαξ}·sinc(ξ)^{1/3}. That is not entire, which contradicts Paley–Wiener.
VALUE: This is the first improvement of the lower-bound constant. It also produces the optimal density profile that any tight construction must imitate.
SIGNIFICANCE: 1
TEST: Discretise μ on a grid and solve the LP/SDP (maximise the minimum density of the triple convolution). Compare with the exact data (k³/N ≈ 1/0.281 for k = 8).

=== TARGET T3
TYPE: SPECIAL
STATEMENT: liminf_{N→∞} minMaximalSidonSet(N)/N^{1/3} < ∞. Concretely, there is an explicit sequence N_j → ∞, for instance N_j ≍ q_j³ with q_j prime, with maximal Sidon sets of size ≤ C·N_j^{1/3}.
BEYOND: Ruzsa gives the log loss for every N. No sequence achieving O(N^{1/3}) is known in Z.
VALUE: Combined with T4 (if the construction is arc-confined in some Z_m) or with any interpolation lemma, it gives CORE. It would already settle the "existence" reading for infinitely many N.
SIGNIFICANCE: 3
TEST: Build the candidate for q ≤ 60 and verify maximality exhaustively by bitset checks of A ∪ {x}.

=== TARGET T4
TYPE: REDUCTION
STATEMENT: Let c < 1/2. Suppose that for a sequence m_j → ∞ with m_{j+1} ≤ (1/(2c) − ε)·m_j, each Z_{m_j} contains a maximal Sidon set S_j of size ≤ C·m_j^{1/3} lying in an arc of length c·m_j. Then CORE holds.
- Proof (complete). Translate S_j into [1, c·m_j]. Fix N ∈ [c·m_j, (m_j−1)/2].
- Integer equality implies congruence, so S_j is Sidon in Z.
- For x ∈ [1,N] ∖ S_j, Z_m-maximality gives a nontrivial congruence u+v ≡ w+z among elements of S_j ∪ {x} ⊆ [1,N].
- Since |u+v−w−z| ≤ 2N−2 < m, the congruence is an integer equality, so x ∈ Bl(S_j) in Z.
- The intervals [c·m_j, (m_j−1)/2] cover all large N. ∎
BEYOND: The implication is new and strictly one-way, since a maximal set in [N] need not be maximal in Z_{2N+1}. Known cyclic constructions (subgroup-based) are spread out, not arc-confined.
VALUE: It moves CORE entirely into Z_m, where Singer and Bose–Chowla algebra lives. The only extra requirement is confinement to under half the circle.
SIGNIFICANCE: 1
TEST: Search Z_m (m ≤ 300) for maximal Sidon sets confined to arcs of length < m/2, and record the minimum size versus m^{1/3}.

=== TARGET T5
TYPE: ANALOGUE
STATEMENT: For every n ≥ 1, Z_n contains a maximal Sidon set of size ≤ C·n^{1/3}.
BEYOND: Only structured n (e.g. n = m(q²+q+1), blackboard, unverified) are covered.
VALUE: The cyclic problem without boundary is the "model" of CORE. Handling all n requires a non-subgroup mechanism (for prime n there are no subgroups). That mechanism is exactly what T4 needs.
SIGNIFICANCE: 2
TEST: Extend veljjanoski's code to compute c(8), c(9) and the smallest maximal size in Z_n for prime n ≤ 2000.

=== TARGET T6
TYPE: ANALOGUE
STATEMENT: Let q be odd and B = {log_g(θ+a) : a ∈ F_q} ⊂ Z_{q³−1}.
- (i) Bl(B) has density 1/2 + O(1/q), and the triple map of B is injective.
- (ii) There is a set B′ of size O(q) such that B ∪ B′ is a maximal Sidon set in Z_{q³−1}.
- (iii) The same holds in F_p³ starting from the moment curve {(t, t², t³)}.
BEYOND: Part (i) is derived in this memo but unverified. Parts (ii) and (iii) are new, for a family not covered by the blackboard's subgroup method. Nagy's F_q^n results should be checked for (iii).
VALUE: This is a purely algebraic, zero-redundancy half-cover. Completing it shows that the Poisson barrier is avoidable by a construction with a chance of arc-confinement or integer lifting.
SIGNIFICANCE: 2
TEST: For q ≤ 31, compute Bl(B) exactly. Search for B′ among dilates tB (t coprime to q³−1), Frobenius images, and the elements log(θ′+a) for other generators θ′, after deleting Sidon conflicts. Measure the residual uncovered set.

=== TARGET T7
TYPE: STRUCTURE
STATEMENT: Let A_N be maximal Sidon sets with |A_N| ≤ (κN)^{1/3}, and let μ be any weak limit of the scaled counting measures. Then:
- (κ/2)·(law of U+V−W) ≥ Lebesgue on [0,1];
- hence diam supp μ ≥ 1/3 + η(κ) with η(κ) > 0;
- if κ < 4, then μ ≠ Lebesgue: A_N is not equidistributed, and has excess mass near both ends.
BEYOND: Nothing is known about the shape of small maximal Sidon sets.
VALUE: It tells constructions where the mass must go. It also gives the endpoint behaviour that every T3/T4 witness must reproduce.
SIGNIFICANCE: 1
TEST: Plot the element distribution of the exact minimal witnesses (k ≤ 8) and of the T2 LP optimiser.

=== TARGET T8
TYPE: QUANT
STATEMENT: Define σ_Sid = liminf_L min{|Y|²/L : Y Sidon, Y ⊂ [0, C₀L], [1,L] ⊆ Y−Y}. Prove σ_Sid < ∞, ideally σ_Sid ≤ 4. This is a "Sidon difference basis", gap G1 on the blackboard.
BEYOND: Leech and Golay concern difference bases without the Sidon condition. Cilleruelo–Nathanson concern infinite perfect difference sets with density x^{√2−1}, which is far from √x locally. No finite Sidon version with O(√L) is known to us; check the literature on complete Golomb rulers.
VALUE: G1 is the input of the X ⊔ Y certificate route. With it, G2 becomes an explicit local constant game (A1).
SIGNIFICANCE: 2
TEST: Search over unions of r ≤ 3 Singer or Bose blocks at generic shifts with pairwise disjoint difference sets. Maximise L/|Y|² for L ≤ 10^5.

=== TARGET T9
TYPE: NEGATIVE
STATEMENT: Suppose A₀ ⊂ [N] is Sidon of size k, and its blocking multiplicities are asymptotically Poisson. Precisely: for every fixed finite set of points, the joint factorial moments of (r(x)) converge to those of independent Poisson(λ(x)). Then any maximal Sidon A ⊇ A₀ in which the added elements are chosen uniformly from the unblocked points has |A| ≥ c(N log N)^{1/3} w.h.p. In particular, Ruzsa's construction and its random variants are tight at (N log N)^{1/3}.
BEYOND: Bennett–Bohman bound only the uniform random greedy process. This statement covers random seeds of the Ruzsa type followed by any completion.
VALUE: It certifies that T1 and CORE require correlated (structured) blocking, and redirects effort to A2–A4.
SIGNIFICANCE: 1
TEST: Simulate Ruzsa seeds plus greedy completion for N ≤ 10^7, and fit the final k³/(N log N).

=== TARGET T10
TYPE: CONDITIONAL
STATEMENT: Assume Schinzel's Hypothesis H, in the form: there are infinitely many primes q with q²+q+1 prime, with consecutive such q of ratio → 1. Then CORE holds. The intended mechanism:
- Z_m with m = q²+q+1 prime carries a Singer set whose multiplier group ⟨q⟩ ≅ Z_3 acts freely.
- The aim is a Z_3-equivariant arc-confined maximal set, as required by T4.
BEYOND: No conditional proof of CORE under any named conjecture is known. We know of no implication; the honest content is to find the arithmetic input that makes T4's confinement exact.
VALUE: If any named hypothesis suffices, the problem is reduced to an unconditional arithmetic question. If none plausibly suffices, that indicates the difficulty is combinatorial rather than arithmetic.
SIGNIFICANCE: 2
TEST: For primes q ≤ 100 with q²+q+1 prime, search Z_3-invariant subsets of Singer translates for arc-confined maximal sets.

=== ANGLE A1
TECHNIQUE: Singer/Bose certificate X ⊔ Y, with the transversal chosen by the Lovász Local Lemma (Moser–Tardos), not greedily.
IDEA:
- Fix Y from T8 with D = Y−Y ⊇ [−L, L], where L = λN^{2/3}.
- Put x_i = x_{i−1} + g_i with gaps g_i ∈ (L, 2L+1]. Coverage of [N] by X + D is then automatic.
- Sample the g_i at random from an allowed window, avoiding D ∩ (L, 2L+1] and the sets of partial gap sums that land in D.
- The remaining bad events, all of density O(λ^{−3/2}) for large λ, are sparse and long-range: x_i ∈ X+X−X, x_i ∈ X−X+Y, and 2x_i = x_j + x_k.
- Kill them with LLL resampling. The total size is N^{1/3}(√(σλ) + O(1/λ)).
BARRIERS:
- Tiling rigidity is avoided because D has no interval at the reachable distance beyond 2L.
- Wrap-around is avoided because Y is a genuine integer Sidon difference basis.
- It must beat the difference-basis constant. The local accounting needs (excess of D in (L, CL]) / L < 1 − (LLL slack), which is an explicit inequality in σ_Sid.
FIRST STEP: Lemma. Assume Y Sidon, Y ⊂ [0, ρL], |Y|² ≤ σL and Y−Y ⊇ [1,L], with σ(ρ+1) < 1 + ... (to be computed). Then for N ≥ L^{3/2}·λ³ there exists X ⊂ [N] with gaps in (L, 2L+1] such that X ∪ (Y + ⌊N/2⌋) is Sidon. Verify numerically with the T8 search output.

=== ANGLE A2
TECHNIQUE: Algebraic B_3 half-covers, completed by Galois twists (Chebotarev / character sums over F_q), then transferred to Z via T4.
IDEA:
- In Z_{q³−1} (or F_p³), B = Bose–Chowla (resp. the moment curve) blocks exactly the y whose discriminant Δ(y) = σ₁² − 4σ₂ is a square. Δ is an explicit rational function of the coordinates of y.
- Find a second algebraic family B′ = {log(φ(a))}, with φ a different linear or quadratic map into F_{q³}, satisfying:
  - (a) the mixed relations B+B′−B and B′+B′−B cover the nonsquare locus;
  - (b) the cross differences B−B and B′−B′ meet in O(1) points; this is a curve-intersection count via Weil.
- Delete O(1) conflicts and greedily complete the o(q) remainder.
- For the integer problem, take m = q³−1 and look for a multiplier t with tB confined to an arc of length < m/2 (equidistribution of tB fails for special t).
BARRIERS:
- Poisson does not apply: blocking is governed by a quadratic character, which is deterministic.
- Wrap-around is avoided by T4.
- It must beat the confinement requirement of T4, where the BARRIER "no monotonicity" is replaced by arc geometry.
FIRST STEP: Verify the half-cover formula for B in Z_{q³−1}, q ≤ 31, computationally. Then prove (b) for B′ = tB, giving the number of t for which (B−B) ∩ t(B−B) = {0}, via Weil bounds on the curve (θ+a)(θ+b)^{−1} = ((θ+c)(θ+d)^{−1})^t.

=== ANGLE A3
TECHNIQUE: Iterative absorption (Keevash / Glock–Kühn–Lo–Osthus style), i.e. leftover confinement.
IDEA:
- Reserve an absorber R: a structured Sidon set of size εN^{1/3} (e.g. a scaled Bose block on a sublattice dZ ∩ [N]).
- Build the main part A₁ so that every point not in dZ is blocked. A₁ is a Singer–transversal on [N] ∖ dZ, an essentially cyclic problem modulo d.
- The leftover is then confined to the AP dZ ∩ [N], of size N/d. R blocks it as a rescaled copy of the original problem at size N/d, recursively.
- Constants telescope geometrically: N^{1/3}·Σ_j d^{−j/3} = O(N^{1/3}).
BARRIERS:
- The Poisson barrier is beaten because the leftover is structured, so completion never faces a random set.
- It must beat the cross-Sidon conditions between levels. Using scales dZ guarantees that differences at different levels are distinct modulo d.
FIRST STEP: Lemma. If A ⊂ dZ is Sidon and maximal in dZ ∩ [N], and A′ ⊂ [N] is Sidon with Bl(A′) ⊇ [N] ∖ dZ, A′ ∩ dZ = ∅ and (A′−A′) ∩ (A−A) = {0}, then A ∪ A′ is Sidon up to O(|A|+|A′|) deletable conflicts. Prove it, and identify which cross relations a′₁+a′₂ = a₁+a₂ survive modulo d.

=== ANGLE A4
TECHNIQUE: Recursive concatenation constructions from covering codes and saturating sets (Davydov's q^m-concatenation), applied in Z_{m₁m₂} ≅ Z_{m₁} × Z_{m₂} via CRT.
IDEA:
- Maximal Sidon sets in an abelian group G correspond to "radius-3" saturating sets.
- Davydov-type constructions build saturating sets of size ≍ |G|^{1/3} for product groups from smaller ones, using a "lift plus fibre" pattern: for each a in a small saturating set of the base, place a Sidon fibre over it.
- Port this to G = Z_{m₁} × Z_{m₂} with gcd(m₁, m₂) = 1 to get every squarefree-ish n (T5).
- Then pick the CRT representative so that the set falls in an arc (T4).
BARRIERS:
- Subgroup-free: it works for all n by factorisation, not by Singer structure.
- It must beat arc confinement, since CRT scatters elements; this is addressed by choosing fibres in residue windows.
FIRST STEP: Prove that if S₁ is maximal Sidon in G₁ and S₂ is maximal Sidon in G₂, then some subset of (S₁ × G₂-section) ∪ (G₁-section × S₂) of size O(|S₁||G₂|^{1/3} + |G₁|^{1/3}|S₂|) is maximal Sidon in G₁ × G₂. Test exhaustively for |G₁|, |G₂| ≤ 30.

=== ANGLE A5
TECHNIQUE: Continuous relaxation, then discretisation via B_3 sets (calculus of variations, then Freiman-model rounding).
IDEA:
- Solve T2's LP for an optimal profile μ* with (κ/2)·ν ≥ 1 on [0,1].
- Realise μ* as a union of O(1) dilated and shifted Bose–Chowla B_3 integer blocks, each injective on its own triples.
- The blocks are placed with block masses and positions matching a step approximation of μ*, so that the sum of their triple-pushforwards dominates Lebesgue with slack 1+ε.
- Cross-block Sidon conflicts are counted by Fourier/Weil and deleted. Local uncovered pockets are absorbed by A3.
BARRIERS: Poisson does not apply, since B_3 blocks are exactly injective. It must beat the wrap-around of integer lifts of Bose–Chowla, which is handled by using only the central third of each lift, where the triple map is "honest".
FIRST STEP: Compute, for the integer lift of Bose–Chowla B ⊂ [0, q³−1), the exact set of integers x with x = a+b−c in Z, and its density profile. Check whether two dilates (factors 1 and 2) already cover a central interval with multiplicity ≤ 3.

=== ANGLE A6
TECHNIQUE: Stability of near-tilings: Fourier and cyclotomic tiling theory (Coven–Meyerowitz, Greenfeld–Tao), used to attack FALSE or to prune constructions.
IDEA:
- A maximal set of size (κN)^{1/3} yields a near-tiling: Σ_x r(x) = k³/2, with r ≥ 1 on [N].
- Write r = 1 + e with ‖e‖₁ ≤ (κ/2 − 1)N.
- Exploit the identity ∑ r̂ = (1/2)Â²·conj(Â) + (lower-order terms), which says the Fourier transform of r is essentially (1/2)·Â(ξ)²·conj(Â(ξ)) apart from the midpoint and trivial terms.
- An interval indicator has Fourier zeros at multiples of 1/N, so |Â(j/N)|³ must be small at those frequencies, at many scales simultaneously.
- Aim for a multiscale incompatibility with the Sidon bound Σ|Â|⁴ ≈ 2k³ that forces κ → ∞ (FALSE). If that fails, extract the precise e-budget that constructions must meet.
BARRIERS: The counting and Poisson barriers concern constructions, not lower bounds. This angle must beat the existence of exact cyclic examples, so any contradiction must use the boundary or non-periodicity of [N]. That is exactly where T7's endpoint deficit lives.
FIRST STEP: Prove that ∑_{0 < |j| ≤ N/2} |Â(j/N)|⁶ · min(1, |j|^{−2}) ≥ c(κ)k⁶ for every maximal Sidon A with |A| = (κN)^{1/3}. Then test whether it conflicts with Σ_j |Â(j/N)|⁴ ≤ 2Nk² + O(k⁴) when κ is bounded.

## Meta-review

=== STATE
Validated this round (all rated routine by novelty review; none settles CORE):
- **r1s1/C1, ruler reduction.** If Y ⊆ A is Sidon and [1,L] ⊆ Y−Y, then every close pair of A (distance ≤ L) lies in Y. Hence |A∖Y| ≤ ⌈N/(L+1)⌉ and minMax(N) ≤ |Y| + ⌈N/(L+1)⌉.
- **r1s1/C1′, clique version.** With M = [1,L]∖(Y−Y), |A∖Y| ≤ ω(M)·⌈N/(L+1)⌉, and ω ≤ 2 if M is sum-free. Checked here: mod-r or half-interval choices of M give exactly the same bound after rescaling L, so this version brings no gain.
- **r1s1/C3, instance of Barrier 3.** If X ∪ (Y+s) is Sidon with [1,L] ⊆ Y−Y, then X has a gap ≥ 2L+2 around Y+s. So no X with all gaps in (L, 2L+1] can straddle the cluster.
- **r1s2/C1, Bose–Chowla equidistribution.** By Erdős–Turán plus Katz, every multiplier twist tB+s of B (with m/gcd(t,m) > 23 and q ≥ 1775) meets every arc of length ≥ m/2. So T4 arc-confinement is dead for any construction containing a Bose–Chowla copy.
- **r1s2/C2(a), exact blocking law.** For x ∉ B with y = g^x, B triple-blocks x iff y₂ ≠ 0 and z² − σ₁z + σ₂ splits over F_q with c not a root. Exactly q²(q−1)/2 points are triple-blocked, so B blocks 1/2 + O(1/q) of Z_m. The rule is deterministic: a quadratic-character condition, not a Poisson one.
- **r1s2/C2(b).** (B−B) ∩ q^{±1,±2}(B−B) = {0} iff 1, θ, θ^q are linearly independent over F_q. This always holds for q ≡ 2 (mod 3).
- **r1s3/C2.** A Singer integer lift with window deficit w has T ⊇ [−(w−1), w−1], and w/h → 0 for every multiplier and rotation. This is a second, independent death of T4.

Broken:
- **r1s1/C2.** The hypothesis [1,L] ⊆ Y_L−Y_L was dropped from the statement. The fix is mechanical.
- **r1s3/C1.** The statement is circular ("if A is Sidon then A is Sidon") and the cited cases are missing.

Best unvalidated ideas:
- **r1s4/C1(ii), improved lower bound.** c(δ) < 1, so minMax ≥ (2N/c)^{1/3} with c < 1. I see a rigorous route:
  - Suppose c(δ) ≥ 1 for all δ. Prokhorov compactness gives a limit μ with f_μ ≥ Leb on [0,1]. Total mass 1 then forces f_μ = Leb on [0,1].
  - Then φ(t)²φ(−t) = (e^{it}−1)/(it) as entire functions. At t₀ = 2πn the left side vanishes to order ≥ 3, since ord_{t₀}φ(−·) = ord_{t₀}φ by conjugate symmetry. The right side has a simple zero there, a contradiction.
- **Fiber-scalar family (derived this round, needs a referee).**
  - Setup: A = {log κ(θ+a) : a ∈ F_q, κ ∈ K_a ⊆ F_q*}.
  - Sidon criterion: A is Sidon iff each K_a is Sidon in F_q* and the quotient sets K_a/K_a are pairwise disjoint apart from 1. Proof: compare the θ² coefficients, then use that 1, θ, θ² are independent.
  - Size: this forces Σ|K_a|(|K_a|−1) ≤ q−2, so |A| ≤ ≈1.5q. The triple count is then ≈ 1.7·q³, i.e. constant redundancy is available.
- **Intersective characters.** If three structured blocks have blocking discriminants with Δ₁Δ₂Δ₃ a square (as functions of y), then every non-degenerate y is blocked exactly, because among a, b, ab some element is a square.
- **Reflection slack (observed this round).**
  - In A = X ⊔ Y, the relation z = y+y′−x is a 3-vs-3 relation, so (Y+Y)−X may have any multiplicity.
  - Barrier 3's packing constraint binds only the family X+(Y−Y).
  - The C2 optimizer of r1s4 (an atom of ≈0.46 at 1/2) independently points to the shape "central cluster Y plus spread X".
- **Supporting data.**
  - r1s2/C3: twists act as independent characters, leaving 2^{−r}e^{−λ} unblocked.
  - r1s4/C4: adaptive greedy keeps the log.
  - r1s1/C4: σ_k ≈ 3 for k ≤ 9, under a span cap.

=== LESSONS
- **G1\* goes the wrong direction.** The ruler reduction turns a bounded-multiplicity cover (CORE) into an exact one: Sidon forces each d ≤ L to occur exactly once. G1\* is therefore at least as rigid as CORE, as the referee said, and also faces the difference-basis constant and Barrier 3. The span-capped data (σ ≈ 3) cannot test this.
- **C2 broke on bookkeeping, not mathematics.** The covering hypothesis was omitted. r1s3/C1 broke because nothing was actually exhibited.
- **The cyclic-to-interval transfer is now closed twice.** Bose–Chowla twists are equidistributed (r1s2/C1), and Singer lifts have w/h → 0 (r1s3/C2). The wrap-around barrier bit every lift attempt.
- **Combining structured sets independently reproduces Poisson.** Twists give independent quadratic characters, and seeded greedy and adaptive greedy all keep the log. The Poisson barrier bit every random or greedy completion.
- **Most alive angle: Bose–Chowla's own blocking is exact.** It blocks precisely the split-discriminant half. So the leftover is an algebraic set, not a random one. Blocks should be combined so that their characters are *dependent*, in the intersective, Legendre-product way, rather than independent.
- **Second angle: reflection triples y+y′−x.** These evade the packing constraint behind Barrier 3, and the extremal measure profile already favours this shape.

=== NEXT
1. **[PUSH r1s2/C2(a) → cyclic CORE]** Use exact character bookkeeping on the fiber-scalar family A = {log κ(θ+a) : κ ∈ K_a}.
   - First step: prove the Sidon criterion stated in STATE.
   - Then derive the blocking discriminant of each mixed triple (κ₁, κ₂, κ₃) symbolically for K_a = {1, κ(a)}, with κ(a) linear or Möbius in a.
   - Then compute the blocking-indicator vectors for primes q ≤ 31, and search for choices whose discriminants multiply to a square (an intersective cover).
   - Report the leftover size, aiming for O(q). If counting falls short, add a second line ℓ′.
2. **[REPAIR r1s1/C2]** Restate G1\* with [1,L] ⊆ Y_L−Y_L and prove the conditional bound √(σλ) + 1/λ in Lean 4 together with C1 and the certificate lemma, so the explicit witness family exists formally. Then test G1\* without the span cap.
   - First step: exhaustive search over Sidon Y with span ≤ L^{3/2}, k ≤ 13, recording L*(k).
   - Also try to prove a Newman/generating-function obstruction to a Sidon set that is perfect on the prefix [1,L].
3. **[COMBINE r1s4/C1 + Fourier zeros]** Make the improved lower bound rigorous.
   - First step: write the compactness argument (Prokhorov plus closed-interval upper semicontinuity), which yields f_μ = Leb on [0,1].
   - Then rule this out via the order ≥ 3 zeros of φ(t)²φ(−t) against the simple zeros of (e^{it}−1)/(it).
   - Then make δ and c explicit through a quantitative version: a Beurling–Selberg minorant of the interval tested against φ³ on a fixed window.
   - Target: minMax(N) ≥ (2N/c)^{1/3} with a stated c < 1, the first improvement over (2N)^{1/3}.
4. **[CORE, reflection certificate]** Prove the extended certificate lemma: if [N] ⊆ A ∪ (X+(Y−Y)) ∪ ((Y+Y)−X) ∪ (X+X−Y), then A is maximal.
   - Tabulate exactly which Sidon constraints bind each family; only X+(Y−Y) should be packing.
   - Then build Y as a central Singer/Bose block and X as an Erdős–Turán-type set {2pi + [i²]} placed so that the gaps of N−X match the structure of Y+Y.
   - First step: compute the leftover numerically for N up to 10⁶ and check whether (Y+Y) − X covers with bounded multiplicity, i.e. whether the leftover stays ≪ N^{1/3}.

## Deep dive

GOAL: **Target theorem (cyclic analogue, exact algebraic cover).** There is an absolute constant C such that for infinitely many prime powers q (for example all q ≡ 2 mod 3, the case in which C2(b) gives independence of 1, θ, θ^q), the cyclic group Z_n with n = q³−1 contains a maximal Sidon set A with |A| ≤ C·q = O(n^{1/3}).

The construction is "Bose–Chowla plus a complementary algebraic layer". Let B = {log_g(θ+a) : a ∈ F_q}. Then A = B ∪ B′ ∪ E, where:
- B′ is a second algebraic layer of size O(q).
- E is a correction set of size O(q).
- B′ is chosen so that its pure and mixed triples cover the set left unblocked by B. That set is explicit: by C2(a) it is the locus where the quadratic z² − σ₁z + σ₂ does not split, together with lower-dimensional exceptional loci. After B′ is added, all but O(q) points must be blocked.

The same statement for G = F_q³ with the moment curve {(t,t²,t³)} is the warm-up. It counts as a result only if Step 0 shows it is not already in Nagy's or Redman–Rose–Walker's work.

**Required fallback, provable either way.** A rigorous negative theorem. Let A be a union of r = O(1) "quadratic-locus" layers: Sidon sets whose triple-blocked sets are, up to O(q²) exceptions, of the form {y : χ(Δ_i(y)) = 1} with Δ_i of bounded degree. Then either some product of the Δ_i is a constant times a square on a dense set, an explicit algebraic identity, or the set A leaves at least c_r·q³ points unblocked (Weil bound). This converts r1s2/C3 and r2s1/C3, which are currently only numerical, into a theorem. It also tells you exactly which identity a successful B′ must satisfy.

**Why an expert would rate this 2.** It would be the first maximal Sidon sets of size O(|G|^{1/3}) in a cyclic group, provided Step 0 confirms this. That is the first demonstration in a cyclic setting that the Poisson/log barrier, which stops Ruzsa's construction, random greedy and the nibble, is not intrinsic. The fallback is a sharp structural barrier for algebraic constructions and would r
