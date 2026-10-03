# Blueprint (proof)

=== STEP S1: Basic facts about n
KIND: lemma
STATEMENT: Let n ∈ ℕ with n ≠ 0, and suppose n ≠ p^k for every prime p and every k ∈ ℕ. Then:
(a) n ≥ 2.
(b) For every prime p and every d ∈ ℕ with p^d ∣ n, we have n ≥ 2·p^d.
(c) n = ∏_{p ∈ n.primeFactors} p^{a_p}, where a_p := n.factorization p ≥ 1, and the factors p^{a_p} are pairwise coprime.
USES: none
PROOF: (a) Taking k = 0 gives n ≠ 1, and n ≠ 0 by hypothesis, so n ≥ 2.
(b) Write n = p^d·m. Then m ≠ 0. If m = 1 then n = p^d, which is excluded. So m ≥ 2 and n ≥ 2p^d.
(c) This is the prime factorization of n ≠ 0 (Nat.factorization_prod_pow_eq_self). Distinct primes give coprime prime powers.

=== STEP S2: Monotonicity and symmetry of binomial coefficients
KIND: lemma
STATEMENT: For all n, k ∈ ℕ with k ≤ n we have C(n,k) = C(n,n−k). For all n, j, k ∈ ℕ with j ≤ k and 2k ≤ n we have C(n,j) ≤ C(n,k). For k ≤ n we have C(n,k) ≥ 1.
USES: none
PROOF: Symmetry is Nat.choose_symm. For monotonicity it suffices to treat k = j+1 with 2(j+1) ≤ n. Use (j+1)·C(n,j+1) = (n−j)·C(n,j) (Nat.succ_mul_choose_eq / Nat.choose_succ_right_eq). Since n−j ≥ j+1, this gives C(n,j+1) ≥ C(n,j). Then induct on k−j. Positivity is Nat.choose_pos.

=== STEP S3: Valuation lower bound (K2)
KIND: lemma
STATEMENT: For every prime q and all n, i ∈ ℕ with 1 ≤ i ≤ n: v_q(i) + v_q(C(n,i)) ≥ v_q(n). Equivalently, q^{v_q(n)} ∣ i·C(n,i).
USES: none
PROOF: We have the identity i·C(n,i) = n·C(n−1,i−1) (Nat.succ_mul_choose_eq applied with n−1 and i−1). So n ∣ i·C(n,i), and hence q^{v_q(n)} ∣ i·C(n,i). Taking q-adic valuations (both sides are nonzero) gives v_q(i) + v_q(C(n,i)) ≥ v_q(n).

=== STEP S4: Valuations of C(n,p^d) (K1)
KIND: lemma
STATEMENT: Let p be prime, n ≥ 1, a = v_p(n), and 1 ≤ d ≤ a. Then:
(a) C(n,p^d) = p^{a−d}·u with p ∤ u.
(b) For every prime q ≠ p, q^{v_q(n)} ∣ C(n,p^d).
USES: S3
PROOF: By the identity in S3, p^d·C(n,p^d) = n·C(n−1,p^d−1).
(b) By S3, q^{v_q(n)} ∣ p^d·C(n,p^d). Since q^{v_q(n)} is coprime to p^d, it divides C(n,p^d).
(a) First claim: p ∤ C(n−1,p^d−1). Write C(n−1,p^d−1)·∏_{t=1}^{p^d−1} t = ∏_{t=1}^{p^d−1} (n−t). For 1 ≤ t < p^d we have p^d ∣ n, so v_p(n−t) = v_p(t), because v_p(t) < d. Hence both products have the same p-valuation, and v_p(C(n−1,p^d−1)) = 0. Then d + v_p(C(n,p^d)) = a + 0, so v_p(C(n,p^d)) = a − d. Write C(n,p^d) = p^{a−d}u with p ∤ u.

=== STEP S5: Digit injectivity (abstract)
KIND: lemma
STATEMENT: Let p be prime, a ≥ 1, and let g_1,…,g_a ∈ ℤ with g_d = p^{a−d}u_d and p ∤ u_d. Let e, e' : {1..a} → {0..p−1} satisfy Σ_d e_d g_d ≡ Σ_d e'_d g_d (mod p^a). Then e = e'.
USES: none
PROOF: Suppose e ≠ e', and let d0 be the largest d with e_d ≠ e'_d. Then 0 ≡ Σ_{d ≤ d0} (e_d − e'_d)p^{a−d}u_d (mod p^a), and p^{a−d0+1} ∣ p^a since d0 ≥ 1.
For d < d0, the d-term is divisible by p^{a−d0+1}.
The d0-term equals (e_{d0} − e'_{d0})u_{d0}·p^{a−d0}. Here 0 < |e_{d0} − e'_{d0}| < p and p ∤ u_{d0}, so p ∤ (e_{d0} − e'_{d0})u_{d0}. Hence the d0-term is not divisible by p^{a−d0+1}.
So the whole sum is not ≡ 0 mod p^{a−d0+1}, which contradicts its being ≡ 0 mod p^a.

=== STEP S6: Digit bijection and support (L1)
KIND: lemma
STATEMENT: Same hypotheses as S5. Let V = {e : {1..a} → {0..p−1}} and D(e) = Σ e_d g_d mod p^a ∈ ℤ/p^a.
(a) D is a bijection V → ℤ/p^a. Write δ(x) ∈ V for the digit vector of x ∈ ℤ, i.e. the unique e with D(e) ≡ x (mod p^a).
(b) For 0 ≤ j ≤ a: if p^{a−j} ∣ x then δ(x)_d = 0 for all d > j.
(c) δ(0) = 0, and if e ∈ V satisfies Σ e_d g_d ≡ x (mod p^a) then δ(x) = e.
USES: S5
PROOF: (a) D is injective by S5, and |V| = p^a = |ℤ/p^a|, so D is a bijection (Fintype.bijective_iff_injective_and_card).
(b) Let V_j be the set of e ∈ V supported on {d ≤ j}; it has p^j elements. For e ∈ V_j, every term e_d g_d with d ≤ j is divisible by p^{a−d}, hence by p^{a−j}. So D maps V_j injectively into the multiples of p^{a−j} in ℤ/p^a, a set with exactly p^j elements. Therefore D maps V_j onto that set. If p^{a−j} ∣ x, the residue of x is therefore D(e) for some e ∈ V_j, and by injectivity δ(x) = e.
(c) This is injectivity again. The zero vector represents 0.

=== STEP S7: Definition of φ and its basic properties (L2)
KIND: lemma
STATEMENT: Let n be as in S1. For p ∈ n.primeFactors put a = a_p and g^{(p)}_d = C(n,p^d) for 1 ≤ d ≤ a. These satisfy the hypotheses of S5 by S4(a); let δ_p be the digit map of S6.
For r ∈ ℤ define φ_p(r) = Σ_{d=1}^{a_p} δ_p(r)_d·g^{(p)}_d and φ(r) = Σ_{p ∈ n.primeFactors} φ_p(r). Then:
(a) φ(r) ≥ 0, and φ_p(r) depends only on r mod p^{a_p}.
(b) φ(r) ≡ r (mod n).
(c) φ(r+n) = φ(r) and φ(r−n) = φ(r).
(d) φ(0) = 0.
(e) φ(X) = X, where X = erdos_727285_X n.
USES: S1, S4, S6
PROOF: (a) All digits and all g are nonnegative. Dependence only on r mod p^{a_p} is by definition of δ_p.
(b) Fix p. By S6, φ_p(r) ≡ r (mod p^{a_p}). For q ≠ p, each g^{(q)}_d is divisible by p^{a_p} by S4(b), so φ_q(r) ≡ 0. Hence φ(r) ≡ r (mod p^{a_p}) for every p. Since n is the product of the pairwise coprime p^{a_p} (S1(c)), φ(r) ≡ r (mod n) (Chinese remainder theorem; Finset.prod_dvd_of_coprime).
(c) n ≡ 0 mod every p^{a_p}, then use (a).
(d) δ_p(0) = 0 by S6(c).
(e) Fix p. The summands of X for q ≠ p are divisible by p^{a_p} (S4(b)), so X ≡ Σ_d (p−1)g^{(p)}_d (mod p^{a_p}). The constant vector (p−1,…,p−1) lies in V, so δ_p(X) is that vector by S6(c), and φ_p(X) = (p−1)Σ_{d=1}^{a_p} C(n,p^d). Summing over p gives exactly the definition of X.

=== STEP S8: Support bound (L3)
KIND: lemma
STATEMENT: With the notation of S7, let p ∈ n.primeFactors, 0 ≤ j ≤ a_p, and r ∈ ℤ with p^{a_p−j} ∣ r. Then φ_p(r) ≤ (p−1)·Σ_{d=1}^{j} g^{(p)}_d.
USES: S6, S7
PROOF: By S6(b), δ_p(r)_d = 0 for d > j. For d ≤ j we have δ_p(r)_d ≤ p−1 and g^{(p)}_d ≥ 0.

=== STEP S9: Doubling of C(n,p^j)
KIND: lemma
STATEMENT: Let n be as in S1, p prime, and 1 ≤ j < d with p^d ∣ n. Then 2·C(n,p^j) ≤ C(n,p^{j+1}).
USES: S1, S2
PROOF: Put k = p^j ≥ 2 and K = pk = p^{j+1} ≤ p^d. By S1(b), n ≥ 2p^d ≥ 2K ≥ 4k.
Since 2k ≤ K and 2K ≤ n, S2 gives C(n,K) ≥ C(n,2k).
Next, C(n,2k)·∏_{t=k+1}^{2k} t = C(n,k)·∏_{t=k+1}^{2k}(n+1−t), using iterated Nat.succ_mul_choose_eq in the form (t)·C(n,t) = (n+1−t)·C(n,t−1). For k+1 ≤ t ≤ 2k we have n+1−t ≥ 2k+1 > t, so every factor ratio is ≥ 1. The factor t = k+1 satisfies n−k ≥ 3k ≥ 2(k+1), because k ≥ 2. Hence C(n,2k) ≥ 2C(n,k).

=== STEP S10: Carry lemma (L4)
KIND: lemma
STATEMENT: Let n be as in S1, p ∈ n.primeFactors, and 1 ≤ d ≤ a_p. Then Σ_{d'=1}^{d−1} C(n,p^{d'}) < C(n,p^d).
USES: S2, S9
PROOF: Let S_m = Σ_{d'=1}^{m−1} C(n,p^{d'}). We show S_m < C(n,p^m) for 1 ≤ m ≤ d by induction.
For m = 1: S_1 = 0 < C(n,p) by S2.
Step from m to m+1 ≤ d: S_{m+1} = S_m + C(n,p^m) < 2C(n,p^m) ≤ C(n,p^{m+1}), by S9 with p^d ∣ n.

=== STEP S11: Tower generators (L5)
KIND: lemma
STATEMENT: With the notation of S7, for all r ∈ ℤ, p ∈ n.primeFactors and 1 ≤ d ≤ a_p: φ(r + g^{(p)}_d) ≤ φ(r) + g^{(p)}_d.
USES: S4, S6, S7, S10
PROOF: For q ≠ p, g^{(p)}_d ≡ 0 (mod q^{a_q}) by S4(b), so φ_q is unchanged by S7(a). It remains to show φ_p(r+g_d) ≤ φ_p(r) + g_d. Write a = a_p, g = g^{(p)}, e = δ_p(r).
Case e_d < p−1. Raising e_d by 1 gives a vector in V representing r + g_d. By S6(c) it equals δ_p(r+g_d), so φ_p increases by exactly g_d.
Case e_d = p−1. Then r + g_d ≡ Σ_{d'>d} e_{d'}g_{d'} + y with y = Σ_{d'<d} e_{d'}g_{d'} + p·g_d.
- Each term of y is divisible by p^{a−d+1}: by S4(a), v_p(g_{d'}) = a−d' ≥ a−d+1 for d' < d, and v_p(p g_d) = a−d+1.
- By S6(b) with j = d−1, f := δ_p(y) is supported on {d' < d}.
- The vector equal to e_{d'} for d' > d, 0 at d, and f_{d'} for d' < d lies in V and represents r + g_d. By S6(c) it is δ_p(r+g_d).
- Hence φ_p(r+g_d) − φ_p(r) = Σ_{d'<d} (f_{d'} − e_{d'})g_{d'} − (p−1)g_d ≤ (p−1)(Σ_{d'<d} g_{d'} − g_d) < 0 ≤ g_d, by S10.

=== STEP S12: The monoid T and the lower bound (L6)
KIND: lemma
STATEMENT: Let T ⊆ ℤ be the additive submonoid generated by n and by all C(n,p^d) with p ∈ n.primeFactors and 1 ≤ d ≤ a_p. Then:
(a) φ(r) ∈ T for every r ∈ ℤ.
(b) Every t ∈ T satisfies t ≥ φ(t).
USES: S7, S11
PROOF: (a) φ(r) = Σ_p Σ_d δ_p(r)_d·g^{(p)}_d is an ℕ-combination of generators.
(b) Use AddSubmonoid.closure_induction on the predicate P(t): t ≥ φ(t).
- P(0) holds by S7(d).
- P(n) holds since φ(n) = φ(0) = 0 by S7(c).
- P(g^{(p)}_d) holds by S11 with r = 0.
- If P(s) and P(t), then φ(s+t) ≤ φ(s) + t. To see this, write t as a sum of generators and apply S11 and S7(c) one generator at a time. A cleaner arrangement: prove ∀ t ∈ T, ∀ r, φ(r+t) ≤ φ(r) + t by closure induction (the generators by S7(c) and S11, addition by chaining). Then set r = 0 and use S7(d).

=== STEP S13: Ratio monotonicity (#)
KIND: lemma
STATEMENT: For all k, i, n ∈ ℕ with k ≤ i and 2i ≤ n: C(n,k)·C(2i,i) ≤ C(2i,k)·C(n,i).
USES: none
PROOF: Induct on n ≥ 2i. The base n = 2i is equality.
For the step n → n+1 (with n ≥ 2i, so n+1 > i ≥ k), use C(n+1,j)·(n+1−j) = (n+1)·C(n,j) for j ≤ n. This gives C(n+1,k)·(n+1−k)·C(n,i) = C(n+1,i)·(n+1−i)·C(n,k).
Since n+1−k ≥ n+1−i > 0, we get C(n+1,k)·C(n,i) ≤ C(n+1,i)·C(n,k). Multiply by C(2i,i) and use the induction hypothesis C(n,k)C(2i,i) ≤ C(2i,k)C(n,i). Cancel the positive C(n,i).

=== STEP S14: Arithmetic inequality for s
KIND: lemma
STATEMENT: (a) For integers q ≥ 2 and J ≥ 0: (q−1)J ≤ q^J − 1.
(b) For a finite family of integers x_k ≥ 1: Σ(x_k − 1) ≤ ∏x_k − 1.
USES: none
PROOF: (a) q^J − 1 = (q−1)Σ_{m<J} q^m ≥ (q−1)J.
(b) Induction on the family. With A = ∏ of the earlier terms ≥ 1 and x ≥ 1: Ax − 1 − (A−1) − (x−1) = (A−1)(x−1) ≥ 0.

=== STEP S15: Exponential inequality
KIND: lemma
STATEMENT: For every c ≥ 8: 3^c·(4c+2) ≤ 5^c.
USES: none
PROOF: For c = 8: 6561·34 = 223074 ≤ 390625. For the step c → c+1: 3^{c+1}(4c+6) ≤ 5·3^c(4c+2) ≤ 5^{c+1}, since 3(4c+6) ≤ 5(4c+2) ⟺ 8 ≤ 8c.

=== STEP S16: Central ratio bound F(i) ≥ i−1
KIND: lemma
STATEMENT: For every i ≥ 35, with h = ⌊i/2⌋: C(2i,i) ≥ (i−1)·C(2i,h).
USES: S15
PROOF: We have C(2i,i)·∏_{t=h+1}^{i} t = C(2i,h)·∏_{t=h+1}^{i}(2i+1−t), the same identity as in S9.
- For h < t ≤ i, 2i+1−t > t, so every factor ratio is ≥ 1.
- For t ≤ ⌊3i/4⌋, 8t ≤ 6i < 6i+3, so 3(2i+1−t) ≥ 5t.
Let c = ⌊3i/4⌋ − h. Then 3^c·C(2i,i) ≥ 5^c·C(2i,h) (work in ℚ, or clear denominators factor by factor).
Since 4⌊3i/4⌋ ≥ 3i−3 and 4h ≤ 2i, we get 4c ≥ i−3. So c ≥ 8 (as i ≥ 35) and i−1 ≤ 4c+2. By S15, 5^c ≥ 3^c(4c+2) ≥ 3^c(i−1). Hence C(2i,i) ≥ (i−1)C(2i,h).

=== STEP S17: Finite check for small i
KIND: lemma
STATEMENT: For each integer 4 ≤ i ≤ 34, define J*_q for primes q ∣ i by J*_q = v_q(i) − 1 if i = q^{v_q(i)}, and J*_q = v_q(i) otherwise. Then
Σ_{q ∈ i.primeFactors} (q−1)·Σ_{d=1}^{J*_q} C(2i,q^d) ≤ C(2i,i).
USES: none
PROOF: Finite computation over the 31 values of i (decide / norm_num [Nat.choose] by interval_cases i). The referee's script s2.py checked this for all 2 ≤ i < 200. The smallest ratio C(2i,i)/LHS is 1.826, at i = 6.

=== STEP S18: Setup for the bound on C(n,i) (L7, first part)
KIND: lemma
STATEMENT: Let n be as in S1, 1 ≤ i ≤ n/2, and suppose i ≠ p^j for all p ∈ n.primeFactors and 1 ≤ j ≤ a_p. For q ∈ n.primeFactors let J_q = max(0, a_q − v_q(C(n,i))) and P = {q : J_q ≥ 1}. Suppose P ≠ ∅, and put L = ∏_{q∈P} q^{J_q} and M = max_{q∈P} q^{J_q}. Then:
(a) J_q ≤ min(a_q, v_q(i)).
(b) L ∣ i.
(c) i ≥ 2M ≥ 4.
(d) For q ∈ P and 1 ≤ d ≤ J_q: q^d ≤ M < i, and 2M ≤ n, and 2i ≤ n.
USES: S3
PROOF: (a) J_q ≤ a_q is clear. Since C(n,i) ≥ 1, J_q ≤ v_q(i) by S3.
(b) The q^{J_q} are pairwise coprime and each divides i by (a).
(c) If |P| ≥ 2, then L = M·(product of the others) ≥ 2M, and i ≥ L since L ∣ i and i ≥ 1.
If P = {p}, then p^{J_p} ∣ i with 1 ≤ J_p ≤ a_p, so i ≠ p^{J_p} by hypothesis, and i ≥ 2p^{J_p} = 2M.
In both cases M ≥ 2, so i ≥ 4.
(d) q^d ≤ q^{J_q} ≤ M ≤ i/2 < i. Also 2M ≤ i ≤ n/2 and 2i ≤ n.

=== STEP S19: L7 in the case i ≥ 35
KIND: lemma
STATEMENT: In the situation of S18, assume i ≥ 35. Then C(n,i) ≥ R := Σ_{q∈P}(q−1)Σ_{d=1}^{J_q} C(n,q^d).
USES: S2, S13, S14, S16, S18
PROOF: By S18(d) and S2, each C(n,q^d) ≤ C(n,M), so R ≤ s·C(n,M) with s = Σ_{q∈P}(q−1)J_q. By S14, s ≤ Σ(q^{J_q} − 1) ≤ L − 1 ≤ i − 1, using S18(b).
Let h = ⌊i/2⌋. Then:
- C(n,M)·C(2i,i) ≤ C(2i,M)·C(n,i), by S13 with k = M ≤ i and 2i ≤ n;
- C(2i,M) ≤ C(2i,h), by S2, since M ≤ h and 2h ≤ 2i;
- C(2i,i) ≥ (i−1)C(2i,h), by S16.
So (i−1)C(n,M)C(2i,h) ≤ C(n,i)C(2i,h). Since C(2i,h) > 0, C(n,i) ≥ (i−1)C(n,M) ≥ s·C(n,M) ≥ R.

=== STEP S20: L7 in the case i ≤ 34
KIND: lemma
STATEMENT: In the situation of S18, assume i ≤ 34. Then C(n,i) ≥ R, with R as in S19.
USES: S13, S17, S18
PROOF: By S18(c), 4 ≤ i ≤ 34.
First, J_q ≤ J*_q for q ∈ P, where J*_q is as in S17. We have J_q ≤ v_q(i) by S18(a). If J_q = v_q(i) and i = q^{v_q(i)}, then i = q^{J_q} with q ∈ n.primeFactors and 1 ≤ J_q ≤ a_q, which contradicts the hypothesis of S18. Also P ⊆ i.primeFactors, by S18(b).
By S13 (k = q^d < i, 2i ≤ n), C(n,q^d)·C(2i,i) ≤ C(2i,q^d)·C(n,i). Hence
R·C(2i,i) ≤ C(n,i)·Σ_{q∈P}(q−1)Σ_{d≤J_q} C(2i,q^d) ≤ C(n,i)·Σ_{q ∣ i}(q−1)Σ_{d≤J*_q} C(2i,q^d) ≤ C(n,i)·C(2i,i).
The second inequality holds because all terms are nonnegative; the third is S17. Divide by C(2i,i) > 0.

=== STEP S21: Every C(n,i) lies in T (S ⊆ T)
KIND: lemma
STATEMENT: Let n be as in S1. For every 1 ≤ i < n, C(n,i) ∈ T (T as in S12).
USES: S1, S2, S7, S8, S12, S18, S19, S20
PROOF: Let g = C(n,i) = C(n,n−i) (S2).
If i or n−i equals p^j with p ∈ n.primeFactors and 1 ≤ j ≤ a_p, then g is a generator of T.
Otherwise, replace i by min(i, n−i). This leaves g and the hypothesis unchanged, so we may assume 1 ≤ i ≤ n/2. Define J_q and P as in S18.
- For each q, v_q(g) ≥ a_q − J_q, so q^{a_q−J_q} ∣ g with 0 ≤ J_q ≤ a_q. By S8, φ_q(g) ≤ (q−1)Σ_{d≤J_q} C(n,q^d).
- Summing over q gives φ(g) ≤ R, with R = 0 if P = ∅. If P ≠ ∅, then R ≤ g by S19 or S20, according to whether i ≥ 35 or i ≤ 34. So in all cases φ(g) ≤ g.
- By S7(b), g − φ(g) = kn for some integer k, and k ≥ 0 because φ(g) ≤ g.
- Hence g = φ(g) + k·n ∈ T, using S12(a) and closure of T under addition.

=== STEP S22: Conclusion
KIND: glue
STATEMENT: For all n ≠ 0 with n ≠ p^k for every prime p and k ∈ ℕ: ¬ erdos_727285_Rep n (erdos_727285_X n − n).
USES: S1, S7, S12, S21
PROOF: Suppose X − n = Σ_{i∈Ico 1 n} c_i·C(n,i) with c_i ∈ ℕ. Each C(n,i) ∈ T by S21. T is an additive submonoid, so it is closed under ℕ-multiples (AddSubmonoid.nsmul_mem) and finite sums (AddSubmonoid.sum_mem), and therefore X − n ∈ T.
By S12(b), X − n ≥ φ(X − n). By S7(c) and S7(e), φ(X − n) = φ(X) = X. Hence X − n ≥ X, i.e. n ≤ 0, which contradicts n ≥ 2 (S1(a)).
