## Result
**Cyclic analogue of #156, PROVED for infinitely many n (C1, C1′).**
- C1: for every prime power q and every integer 1 ≤ m ≤ 3q/10, Z_n with n = m(q²+q+1) contains a maximal Sidon set of size exactly q+m.
- C1′: the same holds for every m ≤ q/2 once q ≥ 160. For m = ⌊q/2⌋ this gives |A| = (1.89+o(1))·n^{1/3}, against the trivial lower bound (2n)^{1/3} ≈ 1.26·n^{1/3}.
- Construction: A = Y ⊔ X.
  - Y is a Singer perfect difference set placed inside the subgroup H = mZ_n of order q²+q+1, so Y−Y = H.
  - X is a Sidon transversal of the nonzero cosets of H, chosen greedily (C1) or in ±-pairs with a Fourier bound (C1′).
  - Maximality is automatic: X + (Y−Y) = G is an exact coset tiling. So the coupon-collector/Poisson log loss never arises.
- Status: this turns the blackboard's unverified claim into a proof with explicit constants. It also answers the assignment's core aim, an O(|G|^{1/3}) maximal Sidon set in cyclic groups, but by a different mechanism than B ∪ B′ ∪ E.
- Novelty against the external literature is UNCHECKED, because there is no internet access here.
- In Bose–Chowla language (C3), Y = (q−1)·B ∪ {0}: B dilated by the non-unit multiplier q−1. Earlier runs only tried unit multipliers.

**Assignment target Z_{q³−1} (m = q−1): CONJECTURED (C2).** Random greedy succeeded in 100% of trials for all primes q ≤ 67 and all prime powers q ≤ 32 (2, 3, 4, 8, 9, 16, 25, 27, 32), giving |A| = 2q−1. Every output was verified maximal by brute force. The free fraction stays ≈ 0.04–0.07 of h, matching a Poisson heuristic. The union bound/LLL proof fails at m = q−1 by a constant factor (load ≈ 2h vs h), and I found no exact algebraic transversal.

**No transfer to [N]:** the integer analogue needs a Sidon Y with Y−Y ⊇ [1,L] (r1s1's G1*), and the wrap-around barrier still applies.

## Claims

### C1
STATEMENT: Let q be a prime power, h = q²+q+1, and m ≥ 1 an integer with m² + 3mq + 2m < q² + q + 2. For instance any m ≤ 3q/10 qualifies. Then Z_n, n = mh, contains a maximal Sidon set A with |A| = m + q. (Sidon in the group sense: a+b = c+d implies {a,b} = {c,d}, including 2a = c+d. Maximal means A ∪ {z} is not Sidon for every z ∉ A.) In particular, for m = ⌊3q/10⌋ we get |A|/n^{1/3} → 1.3/0.3^{1/3} = 1.942.
STATUS: PROVED
TYPE: ANALOGUE
BEYOND: KNOWN lists "Cyclic analogue: maximal Sidon sets of size O(n^{1/3}) in Z_n for n = m(q²+q+1)" as blackboard (unverified). This is a complete proof with explicit constants, and the hypotheses are checked. Novelty against the external literature could NOT be checked: there is no internet in the sandbox. I do not recall a published cyclic O(n^{1/3}) construction, but it may be folklore.
PROOF:
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

### C1′
STATEMENT: Let q ≥ 160 be a prime power and 1 ≤ m ≤ q/2. Then Z_{m(q²+q+1)} contains a maximal Sidon set of size q+m. More generally, for any fixed c < (√17−3)/2 = 0.5616, the same holds for m ≤ cq once q ≥ q₀(c). With m = ⌊q/2⌋, |A|/n^{1/3} → 1.5/2^{−1/3} = 1.890. This is the optimum of (1+c)/c^{1/3} over the whole family.
STATUS: PROVED
TYPE: ANALOGUE
BEYOND: improves C1's constant from 1.942 to 1.890. The method shows that the pair constraint x_i + x_{−i} ∉ Y+Y, which costs h/2 in C1, costs nothing when the pair is chosen jointly. What remains is the load from 3- and 4-term relations, ≈ (1.5c + 0.5c²)h. This isolates exactly what a proof of C2 (c = 1) must beat.
PROOF: The notation, Y, Lemmas 1–2 and the half-sum fact are as in C1. The fact is that each coset of H contains at most one root of 2z = s, because h is odd.
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

### C2
STATEMENT: For every prime power q (numerically: every prime q ≤ 67 and every prime power q ≤ 32), the random-greedy transversal of C1 with m = q−1 succeeds. Hence Z_{q³−1} has a maximal Sidon set of size 2q−1 = (2+o(1)) n^{1/3}.
STATUS: CONJECTURED
TYPE: ANALOGUE
BEYOND: this is the assignment's target group Z_{q³−1}, obtained via H = (q−1)Z_n of order q²+q+1. It does NOT need B ∪ B′ ∪ E.
EVIDENCE: t2.py (seed 2026), t3.py (seed 7) and t4.py (seed 11):
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

### C3
STATEMENT (structure; links to the Bose–Chowla framework). In Z_{q³−1}, let B = {log_g(θ+a) : a ∈ F_q}. Then the Singer set used for C1/C2 with m = q−1 is exactly Y = (q−1)·B ∪ {0}, the dilate by the non-unit multiplier q−1. Multiplicatively, Y = {(θ+a)^{q−1}} ∪ {1}, the image of the Singer line in the norm-one subgroup K = ker N_{F_{q³}/F_q} of order q²+q+1.
Moreover, every Sidon A ⊇ Y satisfies A ∩ H = Y and |A ∩ (x+H)| ≤ 1 for every coset x+H ≠ H. Hence every maximal Sidon set containing Y has size ≤ q+1+(m−1). It has size exactly q+m iff it contains a full transversal, and a full Sidon transversal is always maximal (Lemma 2).
STATUS: PROVED
TYPE: STRUCTURE
PROOF:
- (q−1)·log(θ+a) = (q−1)·(log(θ+a) mod h), because (q−1)h = n. The residues log(θ+a) mod h, together with 0 = log 1, are the projective points of the F_q-span of 1 and θ, which is a line, i.e. a Singer set S. So (q−1)B ∪ {0} = mS with m = q−1.
- If a ≠ a′ lie in the same coset of H, then a−a′ ∈ H∖{0} = Y−Y, say a−a′ = y−y′, so a + y′ = a′ + y. This is a nontrivial relation unless {a, y′} = {a′, y}, i.e. a = y and a′ = y′. That can only happen in the coset H itself. In H, A ∩ H is Sidon, contains Y, and Y is a maximal Sidon subset of H (Lemma 2 with m = 1). Hence A ∩ H = Y. ∎
Remark: r1s2/C2(b) studied only unit multipliers t, i.e. B ∪ tB with gcd(t, n) = 1. The useful multiplier is the non-unit t = q−1, which collapses B onto the subgroup K. There the blocking is an exact coset tiling X + H = G rather than a discriminant half-cover (r1s2 C2(a)).

### C4
STATEMENT (exact obstruction for the algebraic Bose–Chowla transversal). Let q ≡ 2 (mod 3) be a prime power, or more generally q with gcd(3, q−1) = 1. Then F_{q³}^* = F_q^* × K with K = ker N, and Y = {(θ+a)^{q−1}} ∪ {1} ⊂ K is the Singer set of C3. For any injective r : F_q^*∖{1} → F_q, put X_r = {x_λ := λ·(θ − r(λ))^{q−1} : λ ∈ F_q^*∖{1}}. Then:
(i) X_r is a transversal of the nontrivial cosets of K.
(ii) X_r ∪ Y has no nontrivial relation of the forms x x′ = x″ y or x x′ = x″ x‴ (x's in X_r, y ∈ Y).
(iii) For every λ ≠ 1, x_λ x_{1/λ} = y y′ holds with y = (θ−r(λ))^{q−1} and y′ = (θ−r(1/λ))^{q−1}. This gives exactly (q−1)/2 violations for q odd. So X_r ∪ Y is never Sidon.
STATUS: PROVED. Checked numerically for q = 5, 11, 17, 23 with 3 random r each (t6.py, seed 5). The violation count is exactly 2, 5, 8, 11 = (q−1)/2, all of type (x x′ = y y′).
TYPE: NEGATIVE
BEYOND: this pinpoints why the algebraic route to C2 fails. The B₃ structure kills exactly the expensive constraints, the 3- and 4-term relations, which carry ≈ 2h load in the union bound. It violates exactly the cheap pair constraints, which C1′ handles at no cost by Fourier pairing. The two mechanisms are incompatible, because modifying any x_λ destroys the polynomial-identity structure.
PROOF:
(i) N(x_λ) = λ³·N(θ−r)^{q−1} = λ³, since N(u^{q−1}) = N(u)^{q−1} = 1. The map λ ↦ λ³ is a bijection of F_q^* when gcd(3, q−1) = 1, so the cosets of K, which are the norm classes, are hit once each, and λ ≠ 1 gives the nontrivial ones.
(ii) Take norms. x_λ x_μ = x_ν y forces λ³μ³ = ν³, so λμ = ν, and then [(θ−r(λ))(θ−r(μ))]^{q−1} = [(θ−r(ν))(θ+a)]^{q−1}. Since ker(u ↦ u^{q−1}) = F_q^*, this means (θ−r(λ))(θ−r(μ)) = c(θ−r(ν))(θ+a) with c ∈ F_q^*. Both sides have degree ≤ 2 in the basis 1, θ, θ², so this is a polynomial identity, and it forces r(ν) ∈ {r(λ), r(μ)}. But ν = λμ ≠ λ, μ because λ, μ ≠ 1, and r is injective: contradiction. For y = 1 the degrees differ. The case λ = μ is identical. For x x′ = x″ x‴, the same argument gives {r(λ), r(μ)} = {r(ν), r(ρ)}, i.e. the relation is trivial.
(iii) x_λ x_{1/λ} = (θ−r(λ))^{q−1}(θ−r(1/λ))^{q−1}, and both factors lie in Y. The relation is nontrivial because x's ∉ K. For λ = −1 it reads x_{−1}² = y². ∎

## Data
- t7.py (seed 3), sanity check of C1′, for (q, m) = (17, 8), (23, 11), (31, 15):
  - The joint-relation list (c1)–(c5) matched a direct Sidon test on 30 random pairs per step, with 0 mismatches.
  - The exact number of good pairs was never below the proved lower bound α|G₁||G₂| − M√(|G₁||G₂|) − K(|G₁|+|G₂|). The bound is negative at these small q, as expected, since C1′ needs q ≥ 160.
  - The paired construction ended Sidon and maximal, with |A| = q+m = 25, 34, 46.
- t4.py, prime powers, n = q³−1, m = q−1. Singer set S = {i mod h : Tr_{F_{q³}/F_q}(g^i) = 0}, checked to be a perfect difference set. Results: 5/5 successes for each q = 2, 3, 4, 8, 9, 16, 25, 27, 32, all verified Sidon and maximal with |A| = 2q−1. Min free fraction: 0.23 (q=3), 0.095 (4), 0.041 (8), 0.033 (9), 0.048 (16), 0.060 (25), 0.055 (27), 0.061 (32).
- Reproducibility. Singer sets for prime q come from the first (c0, c1, c2) in lexicographic order with x³ = c0 + c1x + c2x² primitive over F_q, taking S = {i < h : (x^i)₂ = 0}. Then Y = mS and X is random greedy with Python random.Random(seed): seed 1 (t1), 2026 (t2), 7 (t3), 11 (t4). Coset order is shuffled, and a uniform addable value is picked in each coset.
- t3.py (a), check of C1's accounting. Take m = m_max(q), the largest m with m²+3mq+2m < q²+q+2: m = 2, 3, 4, 5, 5, 7, 8, 9, 11, 12 for q = 7, 11, …, 41. The maximum observed number of non-addable values in a coset never exceeded the proved bound [(q+1)(q+3m)+m(m−1)]/2, both for first-fit and for random order. Examples: q = 41, m = 12, h = 1723: observed 1187 and 1191, bound 1683. All outputs were verified Sidon and maximal by brute force, with |A| = q+m.
- t3.py (b), n = q³−1 with m = q−1 for q = 53, 59, 61, 67: success, with minimum free fraction 0.066, 0.072, 0.069, 0.067. Brute-force verified maximal, |A| = 2q−1. The run stopped at q = 71 only because the naive primitive-polynomial search timed out.
- Primes q ≡ 1 (mod 3) (7, 13, 19, 31, 37, 43, 61, 67) behave the same as q ≡ 2 (mod 3). The construction does not need gcd(q−1, h) = 1.
- t1.py: random greedy, 20 trials each (6 for q = 23), primes q = 5…23, m ∈ {q/4, q/2, q−1, q, q+2}. Success is ~100% except q = 5 with m = 7 (5/20). All verified maximal. |A|/n^{1/3} ranges over 1.80–2.00.
- t2.py (b): empirical threshold. Success is 4/4 at m = q, 2–4/4 at m ≈ 1.5q, and 0/4 at m = 2q (q = 11, 17).

## Dead ends
- **The assignment's B ∪ B′ ∪ E route was not pursued further, because it was superseded.** Every Sidon set containing a subgroup Singer set Y is Y plus a partial transversal (C3), and a full transversal is automatically maximal. The Bose–Chowla B (a quotient lift of the Singer set) blocks only half the group (r1s2 C2a), so a second "complementary" layer would need near-exact quadratic-twist identities, whereas the subgroup version needs none. The required Weil-type fallback was therefore not proved; C4 is the sharp negative statement relevant to this line instead.
- **Hybrid "algebraic B₃ half + greedy half" for m = q−1.** A greedy element still carries all its ≈ 1.5q three-term relations with the algebraic elements, a load of ≈ 1.5h + 0.5h, so the union bound fails again.
- **Rigorous proof of C2 (m = q−1) by union bound.** The per-coset load is ½h (pair partner −i) + ≈1.5h (lines and ovals from i+j = k relations) + ≈½h (4-term relations), about 2.5h > h. The symmetric and asymmetric LLL are worse: they need Σp ≈ 4(1.5c+0.5c²) ≲ 1/e, i.e. c ≲ 0.06. Bonferroni truncations also fail at λ ≈ 2.5.
- **Fully algebraic transversal via the B₃ family (C4).** It kills the 3- and 4-term relations and always fails the pair relations. Twisting by a fixed w, using Frobenius θ^q, or inverting (oval family) makes the mixed relations a generic curve condition with ≈ q violations. So I found no exact algebraic solution.
