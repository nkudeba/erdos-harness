# Research engine: problem 41635, run 20261013-211446-601153-discover-erdos41635

Spend $37.2382; 36 claim(s); 1 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] r1s1/C1 PROVED QUANT
**Statement.** Let n be large. For each prime P, let G_P be a graph whose vertices are primes < P. Suppose no 4-cycle u-q-v-q' (on distinct vertices) has uq, vq' ∈ G_P and qv, q'u ∈ G_Q for some primes P ≠ Q. Then
Σ_P #{edges pq∈G_P : pqP ≤ n} ≤ #{(q,P): 3≤q<P, qP≤n/2} + O(n/log n) = (1/2+o(1)) n L/log n.
Corollaries (use C2):
(a) every valid A has #{a∈A: squarefree, ω(a)=3} ≤ (1/2+o(1)) nL/log n;
(b) every valid A has #{a∈A: squarefree, ω(a)≤3} ≤ π(n)+1+#{q<P: qP≤n} + O(n/log n) = (1+o(1)) nL/log n.
Sharpness:
- B = {2qP : 2<q<P, 2qP≤n} is valid. If a square-product 4-multiset from B is given, the halves qP form a square-product 4-multiset of ω=2 squarefree numbers, which has an equal pairing by R5; multiplying by 4 preserves that pairing. |B| ~ (n/2)L/log n.
- The ω≤2 set (R5) gives (1+o(1))nL/log n.
**Beyond.** KNOWN only bounds the ω=3 layer trivially, by #{ω=3} ~ nL²/(2 log n). This claim determines the sharp constant for the ω=3 layer and for ω≤3, and it proves the angle's FIRST STEP lemma.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "As far as I know, no prior work gives a sharp constant for the ω=3 (or ω≤3) layer of valid sets, and the cross-P alternating-C4 graph lemma is not a standard Zarankiewicz result. But it covers only the bottom layers and does not address the uniform-in-k upper bound that is the actual open core.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "As far as I know, no prior work gives a sharp constant for the ω=3 (or ω≤3) layer of valid sets, and the cross-P alternating-C4 graph lemma is not a standard Zarankiewicz result. But it covers only the bottom layers and does not address the uniform-in-k upper bound that is the actual open core."}, {"verdict": "new", "cite": null, "significance": 1, "why": "As far as I k`
**Proof or evidence.**

Notation. Edge uq with u<q in G_P is placed in cell (P,q) with colour u. C(P,q) = {u : uq∈G_P, uqP≤n}. For corollary (b), each a = c·q·P (P the largest prime, q the second largest, c∈{1}∪{primes<q}) is placed in cell (P,q) with colour c. Total = Σ_cells |C(cell)|.
Step 1 (crossing). Take colours u≠v, P≠Q, q≠q' with u∈C(P,q)∩C(Q,q') and v∈C(P,q')∩C(Q,q). Then the cycle u-q-v-q' alternates, and its vertices are distinct because u,v < q,q'. This is excluded by the hypothesis (for (a) and (b), by C2). Hence for u≠v the set I(u,v) = {cells containing both u and v} is rectangle-free: no P≠Q, q≠q' with all four of (P,q),(P,q'),(Q,q),(Q,q') in I(u,v).
Step 2 (KST). If I ⊆ R×N is rectangle-free, then |I| ≤ |R| + |N|·|R|^{1/2}. Each pair of columns lies in at most one row, so Σ_rows C(s_P,2) ≤ N²/2. By Jensen, this sum is ≥ S(S−r)/(2r), where S=|I| and r=|R|. Hence (S−r)² ≤ S(S−r) ≤ rN² when S > r.
Step 3. Σ_cells |C| ≤ #{nonempty cells} + X, where X = Σ_cells #{v∈C(cell): v > min C(cell)}.
- For C1 and (a), a nonempty cell has 2qP ≤ n with 3 ≤ q < P. For (b), it has qP ≤ n. By Landau, these counts are (1/2+o(1))nL/log n and (1+o(1))nL/log n.
Step 4: the non-minimal colours v > V := n^{1/6}. Each such colour gives a triple V<v<q<P with vqP≤n. The number of such triples is ≤ Σ_{v,q>V} π(n/(vq)). Here n/(vq) ≥ P > n^{1/6}, so π(n/(vq)) ≤ 12n/(vq·log n). By Mertens, the total is ≤ (12n/log n)(Σ_{n^{1/6}<p≤n} 1/p)² = O(n/log n).
Step 5: the non-minimal colours v ≤ V. Let u = min C(cell) < v. Then the cell lies in I(u,v), which sits inside the region v<q<P, vqP≤n, so P < n/v².
- Split the rows dyadically, P∈(Z,2Z]. In a block, the columns satisfy q < min(2Z, n/(vZ)) and there are ≤ 2Z rows.
- Step 2 applied block by block gives |I(u,v)| ≤ π(n/v²) + Σ_Z min(2Z,n/(vZ))·(2Z)^{1/2} ≤ π(n/v²) + C(n/v)^{3/4}. The geometric sums peak at Z = (n/v)^{1/2}.
- There are ≤ π(v)+1 ≤ 2π(v) choices of u. Hence the contribution is ≤ Σ_{v≤V} 2π(v)[π(n/v²) + C(n/v)^{3/4}].
- First part: for v ≤ n^{1/6}, π(n/v²) ≤ 3n/(v² log n) and π(v) ≤ 1.3v/log v, so it is ≤ (8n/log n)·Σ_p 1/(p log p) = O(n/log n), since Σ_p 1/(p log p) < ∞.
- Second part: ≤ C n^{3/4} V^{5/4} = C n^{23/24}.
Hence X = O(n/log n). ∎

## [valid-restatement] program/C4 PROVED REDUCTION
**Statement.** The formal statement `erdos_41635` holds. Write

- f(n) := Nat.findGreatest (p n) n,
- g(n) := n·ln ln n / ln n.

Then f =Θ[atTop] g as real functions. Explicitly, there exist constants 0 < c ≤ C and N₀ such that c·g(n) ≤ f(n) ≤ C·g(n) for all n ≥ N₀.
**Beyond.** a complete argument assembled by the research program from lemmas each of which passed a referee and an adversary
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "The claimed Θ(n·loglog n/log n) bound is the lower bound R5 (routine) plus the upper bound F_sf(n)=O(n·loglog n/log n), which is exactly the team's stated open CORE; proving it solves the problem up to constants, so the multi-lemma proof needs end-to-end scrutiny, especially uniformity across Ω-layers and the R3 error terms.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "The claimed Θ(n·loglog n/log n) bound is the lower bound R5 (routine) plus the upper bound F_sf(n)=O(n·loglog n/log n), which is exactly the team's stated open CORE; proving it solves the problem up to constants, so the multi-lemma proof needs end-to-end scrutiny, especially uniformity across Ω-layers and the R3 error terms`
**Proof or evidence.**

**Step 0: f(n) is the maximum valid cardinality.**
- p n 0 holds, witnessed by A = ∅.
- Any A with RequiredCondition A n satisfies A ⊆ Ioc 0 n, so |A| ≤ n.

Hence Nat.findGreatest (p n) n is the largest k with p n k. Two consequences follow:
- By Nat.findGreatest_spec, there is a valid A with |A| = f(n).
- By Nat.le_findGreatest, f(n) ≥ k for every k ≤ n with p n k.

**Upper bound.** Let A be the valid set with |A| = f(n). By C1, for n ≥ 16,
f(n) = |A| ≤ C·g(n).

**Lower bound.**
- By C2, S_n is valid, so p n |S_n| holds.
- |S_n| ≤ n, since S_n ⊆ Ioc 0 n.
- Therefore f(n) ≥ |S_n|.
- By C3, |S_n| ≥ (1/2)·g(n) for n ≥ N₀.

**Positivity.** For n ≥ 16 we have ln n > 0 and ln ln n ≥ ln ln 16 > 0. So g(n) > 0 and f(n) ≥ 0, and the norms in IsBigO are just f and g.

**Conclusion.** For all n ≥ max(16, N₀), (1/2)·g(n) ≤ f(n) ≤ C·g(n). This gives:
- f =O[atTop] g, with constant C;
- g =O[atTop] f, with constant 2.

That is f =Θ[atTop] g, which is the formal statement.

## [valid-restatement] r1s2/C2 PROVED QUANT
**Statement.** There is an absolute constant C such that every A ⊆ [1,n] satisfying RequiredCondition has
|A| ≤ C·n·loglog n/log n (n ≥ 16). Together with R5: max|A| = Θ(n loglog n/log n).
**Beyond.** This is the CORE upper bound (the whole open direction). KNOWN had only O(n).
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "Combined with the known lower bound (R5) and the squarefree reduction (R3), the claimed O(n loglog n/log n) upper bound is exactly the open core of this Erdős–Sárközy–Sós problem and would settle it up to constants; I know of no published proof. A proof would be major progress, but as a full resolution of an open Erdős problem it needs the strictest verification.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "Combined with the known lower bound (R5) and the squarefree reduction (R3), the claimed O(n loglog n/log n) upper bound is exactly the open core of this Erdős–Sárközy–Sós problem and would settle it up to constants; I know of no published proof. A proof would be major progress, but as `
**Proof or evidence.**

Let L = ln ln n, K = ⌊log2 n⌋, T = (ln n · L)^8, and let P(m) be the largest prime factor (P(1)=1).
- Elements a = 1 or a prime: at most π(n)+1.
- Decomposition: if Ω(a) ≥ 2, put P = P(a), q = P(a/P) ≤ P and s = a/(qP), so that P(s) ≤ q. Then
  φ(a) = (s,q,P) is injective, with sqP = a.
- Boxes: let l = ⌊log2 s⌋, j = ⌊log2 q⌋ ≥ 1, k = ⌊log2 P⌋. Then j ≤ k and l+j+k ≤ K. Also s ∈ Z_{l,j} :=
  {s ∈ [2^l,2^{l+1}) : P(s) < 2^{j+1}}, q ∈ Q_j = the primes in [2^j,2^{j+1}), and P ∈ P_k.
  Put B = Z_{l,j}×Q_j×P_k. The map a ↦ φ(a) is injective into T_B (C1's T for this box), so
  |A∩φ^{-1}(B)| ≤ (3/m_B)^{1/8}|B|.
- Facts used:
  - (F1) if j ≥ l then |Z_{l,j}| = 2^l, since s < 2^{l+1} ≤ 2^{j+1};
  - (F2) if j < l then |Z_{l,j}| ≥ 2^j, because s = 2^{l-j}t with t ∈ [2^j,2^{j+1}) works (here 2 < 2^{j+1} as j ≥ 1);
  - (F3) |Q_j| ≤ C1·2^j/j (Chebyshev), and |Q_j| ≥ c·2^j/j for 2^j ≥ x0 (PNT).
- Mass: Σ_B |B| ≤ Σ_{1≤j≤k} C1^2 2^{j+k}/(jk) · Σ_{l≤K-j-k} 2^l ≤ 2C1^2 n (1+ln K)^2.
  Numerically, mass/n ≈ 2.4–2.9 at n ≤ 2·10^5.
- Case G (all sides ≥ T): the contribution is ≤ (3/T)^{1/8}·2C1^2 n(1+ln K)^2 = O(nL/log n).
- Case S (j ≥ l, |Q_j| ≥ T, |P_k| ≥ T, 2^l < T): here m_B ≥ 2^l by F1.
  - For fixed l, l ≤ K/3 (because 3l ≤ l+j+k). Then
    Σ_{j≥l, j≤k≤K-l-j} 2^l|Q_j||P_k| ≤ C n Σ_{j ≤ (K-l)/2} 1/(j(K-l-j)) ≤ C n (1+ln K)·2/(K-l) ≤ C' nL/K.
    This uses Σ_{k≤N} 2^k/k ≤ C2^N/N.
  - Summing 3^{1/8} 2^{-l/8} over l gives O(nL/log n).
- Case E (everything else): one of the following holds.
  - |Q_j| < T: then by F3, q < y0 := 2·max(x0, C T ln T).
  - |P_k| < T: then q ≤ P < y0.
  - j < l and |Z_{l,j}| < T: then by F2, 2^j < T, so q < 2T ≤ y0.
  In every subcase a/P(a) = sq is y0-smooth, and ln y0 = O(L). The number of a ≤ n with a/P(a) y0-smooth is at most
  Σ_{m≤√n, y0-smooth} π(n/m) + n·Σ_{m>√n, y0-smooth} 1/m.
  - The first sum is ≤ (4n/ln n)·Π_{p<y0}(1-1/p)^{-1} ≤ C n ln y0/ln n = O(nL/log n).
  - For the second sum use Rankin with δ = 1/ln y0: it is ≤ n·e^{-ln n/(2 ln y0)}·(ln y0)^{e}·C = o(n/log n).
- Total: |A| = O(nL/log n). ∎

## [valid-unrated] p1L2/C1 PROVED SPECIAL
**Statement.** For n ≥ 1, let S_n := {pq ≤ n : p < q primes}. Then S_n satisfies RequiredCondition S_n n. That is:
- S_n ⊆ Ioc 0 n;
- for all a, b, c, d ∈ S_n (repetitions allowed) with a ≤ b ≤ c ≤ d and abcd a perfect square, ad = bc.
**Beyond.** Settles skeleton lemma L2 (lower-bound construction) with a complete elementary proof, independent of R4.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(i) Every element is pq with p<q primes, so pq ≥ 2·3 = 6 > 0, and pq ≤ n by definition. (If n < 6, S_n = ∅ and (ii)
is vacuous.)

Preliminary facts. Every x ∈ S_n is squarefree with exactly two distinct prime factors; distinct elements of S_n
have distinct prime pairs (unique factorisation). For a prime p, v_p(x) ∈ {0,1} for x ∈ S_n.
(F) If y,z ∈ S_n and yz is a perfect square, then y = z. Indeed for every prime p, v_p(y)+v_p(z) is even and both
lie in {0,1}, so v_p(y) = v_p(z); hence y = z.

Let a ≤ b ≤ c ≤ d in S_n with abcd = r².

Case A: two of a,b,c,d are equal. Say the multiset {a,b,c,d} contains x twice; remove these two copies and call the
remaining two entries y,z. Then yz = r²/x² = (r/x)², a rational square that is an integer, hence a perfect square
(r/x is rational with integer square, so it is an integer). By (F), y = z. So the multiset is {x,x,y,y} (x = y
allowed). Its sorted form is (min,min,max,max), i.e. a = b and c = d, whence ad = bc (= ac).

Case B: a < b < c < d, all distinct. For each prime p, v_p(abcd) = #{e ∈ {a,b,c,d} : p | e} ∈ {0,...,4}, and it
is even, so it is 0, 2 or 4.
 B1. No prime divides all four: otherwise a=pa', b=pb', c=pc', d=pd' with a',b',c',d' primes ≠ p, pairwise distinct
     (as a,b,c,d are distinct), and a'b'c'd' = r²/p⁴ = (r/p²)² would be a perfect square (same integrality argument),
     but a product of four distinct primes has all exponents 1 — contradiction.
 B2. Hence every prime dividing abcd divides exactly two of a,b,c,d. Counting prime-element incidences:
     4 elements × 2 primes = 8 = 2·(#primes dividing abcd), so exactly 4 distinct primes occur.
 B3. Structure. Write a = p₁p₂ (p₁ ≠ p₂). p₂ divides exactly one other element e = p₂p₃; p₃ ≠ p₂, and p₃ ≠ p₁
     since otherwise e = a. p₃ divides exactly one element other than e, call it f = p₃p₄; f ≠ a since p₃ ∤ a, and
     f ≠ e. p₄ ≠ p₃; p₄ ≠ p₂ because p₂ already divides exactly the two elements a,e and f ∉ {a,e}.
     If p₄ = p₁: then p₁ (in a,f), p₂ (in a,e), p₃ (in e,f) each already occur in two elements, so the fourth
     element h ∉ {a,e,f} has both its prime factors outside {p₁,p₂,p₃}, giving at least 5 distinct primes,
     contradicting B2. So p₄ is a fourth prime distinct from p₁,p₂,p₃, and these are the four primes of B2.
     The fourth element h is divisible by neither p₂ nor p₃ (each already used twice), so h's two primes lie in
     {p₁,p₄}: h = p₁p₄. Thus {a,b,c,d} = {p₁p₂, p₂p₃, p₃p₄, p₄p₁}, and (p₁p₂)(p₃p₄) = (p₂p₃)(p₄p₁) = p₁p₂p₃p₄.
     So the four distinct numbers split into two pairs with equal products.
 B4. Which pairing. The three pairings of {a,b,c,d} are {a,b}|{c,d}, {a,c}|{b,d}, {a,d}|{b,c}. Since all are
     positive and a<b<c<d: ab < cb < cd (so the first pairing is unequal) and ac < bc < bd (second unequal).
     Hence the equal pairing from B3 is {a,d}|{b,c}, i.e. ad = bc.
In both cases ad = bc. ∎

## [valid-unrated] p1L3/C1 PROVED QUANT
**Statement.** There is N₀ such that for all n ≥ N₀,
|S_n| ≥ (1/2)·n·ln ln n / ln n.
**Beyond.** Lemma L3 of the skeleton. It was open in the skeleton; it is the counting half of R5 with an explicit constant and N₀.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

Fix an integer n ≥ e^{81}. Put y := n^{1/3} (a real number). We have y ≥ e^{27} > 2 and n/y = n^{2/3} ≥ e^{54} > 17.
For real t ≥ 0, π(t) denotes #{primes ≤ t}.

Step 1 (injection). Let P := {(p,q) : p, q prime, p ≤ y < q ≤ n/p}. For (p,q) ∈ P we have p ≤ y < q, so p < q,
and pq ≤ p·(n/p) = n. Hence pq ∈ S_n. The map (p,q) ↦ pq is injective on P. Indeed, if pq = p'q' with p<q and p'<q' all
prime, then unique factorisation gives {p,q} = {p',q'}, and ordering by size gives p=p', q=q'. For a prime p ≤ y we have
n/p ≥ n/y = n^{2/3} ≥ y, so #{q prime : y < q ≤ n/p} = π(n/p) − π(y) ≥ 0. Therefore
  |S_n| ≥ |P| = Σ_{p ≤ y} (π(n/p) − π(y)).

Step 2 (main term). Rosser–Schoenfeld 1962 (Illinois J. Math. 6, Cor. 1, (3.5)) gives π(x) > x/ln x for all real x ≥ 17.
For a prime p ≤ y we have x = n/p ≥ n^{2/3} > 17, and 0 < ln(n/p) ≤ ln n. Hence
  π(n/p) > (n/p)/ln(n/p) ≥ n/(p ln n).

Step 3 (error term). The primes ≤ y lie in {2,…,⌊y⌋}, so π(y) ≤ y. The sum in Step 1 has π(y) ≤ y terms, so
Σ_{p≤y} π(y) = π(y)² ≤ y² = n^{2/3}. Combining Steps 1–3,
  |S_n| ≥ (n/ln n)·Σ_{p≤y} 1/p − n^{2/3}.

Step 4 (elementary Mertens lower bound). Claim: for every real x > 1, Σ_{p≤x} 1/p > ln ln x − 1. Proof:
- For each prime p, (1 − 1/p)^{-1} = Σ_{k≥0} p^{-k}, a convergent series of positive terms.
- Multiply these finitely many series over p ≤ x and use unique factorisation. The product is Π_{p≤x}(1−1/p)^{-1} =
  Σ 1/m, summed over the m ≥ 1 whose prime factors are all ≤ x.
- Every m ≤ x has this property, so the product is ≥ Σ_{m≤x} 1/m ≥ ∫_1^{⌊x⌋+1} dt/t = ln(⌊x⌋+1) > ln x > 0.
- Take logarithms: Σ_{p≤x} −ln(1 − 1/p) > ln ln x.
- For 0 ≤ t < 1, −ln(1−t) = Σ_{k≥1} t^k/k ≤ t + Σ_{k≥2} t^k = t + t²/(1−t). With t = 1/p this gives −ln(1−1/p) ≤
  1/p + 1/(p(p−1)).
- Σ_{p≤x} 1/(p(p−1)) ≤ Σ_{m≥2} 1/(m(m−1)) = 1.
- Hence Σ_{p≤x} 1/p > ln ln x − 1. ∎
Apply this with x = y = n^{1/3} > 1. Since ln ln y = ln((ln n)/3) = ln ln n − ln 3, and n/ln n > 0, Step 3 gives
  |S_n| > (n/ln n)·(ln ln n − ln 3 − 1) − n^{2/3}.                                   (★)

Step 5 (conclusion). Write u := ln n ≥ 81. Dividing (★) by n/ln n > 0, it suffices to show
  ln u − ln 3 − 1 − u·e^{−u/3} ≥ (1/2)·ln u,
i.e. (1/2)·ln u ≥ ln 3 + 1 + u e^{−u/3}. Here n^{2/3}·(ln n)/n = u e^{−u/3}.
- h(u) = u e^{−u/3} has h'(u) = e^{−u/3}(1 − u/3) < 0 for u > 3. So for u ≥ 81, h(u) ≤ 81e^{−27} < 2·10^{−10}.
- (1/2) ln u ≥ (1/2) ln 81 = 2.19722… .
- ln 3 + 1 + 2·10^{−10} < 2.09862.
So the inequality holds, and |S_n| ≥ (1/2)·n·ln ln n/ln n for all n ≥ e^{81}. Take N₀ = ⌈e^{81}⌉. ∎

## [valid-unrated] program/C1 PROVED OTHER
**Statement.** There is an absolute constant C such that every A ⊆ [1,n] satisfying RequiredCondition has
|A| ≤ C·n·loglog n/log n (n ≥ 16). Together with R5: max|A| = Θ(n loglog n/log n).
**Proof or evidence.**

=== LEMMA S1
STATEMENT: Let A be valid (RequiredCondition). Let X, Y, Z be finite nonempty sets of positive integers and
T = {(x,y,z) ∈ X×Y×Z : xyz ∈ A}. Then |T| ≤ (3/m)^{1/8}·|X||Y||Z|, where m = min(|X|,|Y|,|Z|).
PROOF:
(a) Suppose T contains (x1,y1,z1), (x1,y2,z2), (x2,y1,z2), (x2,y2,z1) with x1≠x2, y1≠y2, z1≠z2. Let a1..a4 be
the four products. Then a1a2a3a4 = (x1x2y1y2z1z2)^2 is a square. Compare the three pairings:
- a1a4 vs a2a3: these are W·z1^2 vs W·z2^2 with W = x1x2y1y2;
- a1a2 vs a3a4: these are x1^2 vs x2^2 times y1y2z1z2;
- a1a3 vs a2a4: these are y1^2 vs y2^2 times x1x2z1z2.
None of the three is an equality. Sort the four as a≤b≤c≤d. Then ad=bc is one of these three pairings, so A violates
the condition.
(b) Write hom for the number of 6-tuples (x1,x2,y1,y2,z1,z2) with all 8 triples (x_a,y_b,z_c) in T, and set
d = |T|/(XYZ). For fixed (z1,z2), put g(x,y) = 1_T(x,y,z1)·1_T(x,y,z2). The S4 count of g is
Σ_{y1,y2}(Σ_x g(x,y1)g(x,y2))^2 ≥ (Σ g)^4/(XY)^2.
Summing over the Z^2 pairs (z1,z2) and applying the power mean Σa_i^4 ≥ (Σa_i)^4/N^3 gives
hom ≥ (Σ_{z1,z2} Σ g)^4 / (Z^6 (XY)^2). Here Σ_{z1,z2} Σ g = Σ_{x,y}(Σ_z 1_T)^2 ≥ |T|^2/(XY), hence
hom ≥ d^8 (XYZ)^2.
(c) Each such 6-tuple contains the 4 Pasch triples, so by (a) it has x1=x2, y1=y2 or z1=z2. Therefore
hom ≤ XY^2Z^2 + X^2YZ^2 + X^2Y^2Z, and so d^8 ≤ 1/X + 1/Y + 1/Z ≤ 3/m. ∎

=== THEOREM S2
STATEMENT: There is an absolute constant C such that every A ⊆ [1,n] satisfying RequiredCondition has
|A| ≤ C·n·loglog n/log n (n ≥ 16). Together with R5: max|A| = Θ(n loglog n/log n).
PROOF:
Let L = ln ln n, K = ⌊log2 n⌋, T = (ln n · L)^8, and let P(m) be the largest prime factor (P(1)=1).
- Elements a = 1 or a prime: at most π(n)+1.
- Decomposition: if Ω(a) ≥ 2, put P = P(a), q = P(a/P) ≤ P and s = a/(qP), so that P(s) ≤ q. Then
  φ(a) = (s,q,P) is injective, with sqP = a.
- Boxes: let l = ⌊log2 s⌋, j = ⌊log2 q⌋ ≥ 1, k = ⌊log2 P⌋. Then j ≤ k and l+j+k ≤ K. Also s ∈ Z_{l,j} :=
  {s ∈ [2^l,2^{l+1}) : P(s) < 2^{j+1}}, q ∈ Q_j = the primes in [2^j,2^{j+1}), and P ∈ P_k.
  Put B = Z_{l,j}×Q_j×P_k. The map a ↦ φ(a) is injective into T_B (S1's T for this box), so
  |A∩φ^{-1}(B)| ≤ (3/m_B)^{1/8}|B|.
- Facts used:
  - (F1) if j ≥ l then |Z_{l,j}| = 2^l, since s < 2^{l+1} ≤ 2^{j+1};
  - (F2) if j < l then |Z_{l,j}| ≥ 2^j, because s = 2^{l-j}t with t ∈ [2^j,2^{j+1}) works (here 2 < 2^{j+1} as j ≥ 1);
  - (F3) |Q_j| ≤ S1·2^j/j (Chebyshev), and |Q_j| ≥ c·2^j/j for 2^j ≥ x0 (PNT).
- Mass: Σ_B |B| ≤ Σ_{1≤j≤k} S1^2 2^{j+k}/(jk) · Σ_{l≤K-j-k} 2^l ≤ 2C1^2 n (1+ln K)^2.
  Numerically, mass/n ≈ 2.4–2.9 at n ≤ 2·10^5.
- Case G (all sides ≥ T): the contribution is ≤ (3/T)^{1/8}·2C1^2 n(1+ln K)^2 = O(nL/log n).
- Case S (j ≥ l, |Q_j| ≥ T, |P_k| ≥ T, 2^l < T): here m_B ≥ 2^l by F1.
  - For fixed l, l ≤ K/3 (because 3l ≤ l+j+k). Then
    Σ_{j≥l, j≤k≤K-l-j} 2^l|Q_j||P_k| ≤ C n Σ_{j ≤ (K-l)/2} 1/(j(K-l-j)) ≤ C n (1+ln K)·2/(K-l) ≤ C' nL/K.
    This uses Σ_{k≤N} 2^k/k ≤ S2^N/N.
  - Summing 3^{1/8} 2^{-l/8} over l gives O(nL/log n).
- Case E (everything else): one of the following holds.
  - |Q_j| < T: then by F3, q < y0 := 2·max(x0, C T ln T).
  - |P_k| < T: then q ≤ P < y0.
  - j < l and |Z_{l,j}| < T: then by F2, 2^j < T, so q < 2T ≤ y0.
  In every subcase a/P(a) = sq is y0-smooth, and ln y0 = O(L). The number of a ≤ n with a/P(a) y0-smooth is at most
  Σ_{m≤√n, y0-smooth} π(n/m) + n·Σ_{m>√n, y0-smooth} 1/m.
  - The first sum is ≤ (4n/ln n)·Π_{p<y0}(1-1/p)^{-1} ≤ C n ln y0/ln n = O(nL/log n).
  - For the second sum use Rankin with δ = 1/ln y0: it is ≤ n·e^{-ln n/(2 ln y0)}·(ln y0)^{e}·C = o(n/log n).
- Total: |A| = O(nL/log n). ∎

## [valid-unrated] program/C2 PROVED OTHER
**Statement.** For n ≥ 1, let S_n := {pq ≤ n : p < q primes}. Then S_n satisfies RequiredCondition S_n n. That is:
- S_n ⊆ Ioc 0 n;
- for all a, b, c, d ∈ S_n (repetitions allowed) with a ≤ b ≤ c ≤ d and abcd a perfect square, ad = bc.
**Proof or evidence.**

=== THEOREM S1
STATEMENT: For n ≥ 1, let S_n := {pq ≤ n : p < q primes}. Then S_n satisfies RequiredCondition S_n n. That is:
- S_n ⊆ Ioc 0 n;
- for all a, b, c, d ∈ S_n (repetitions allowed) with a ≤ b ≤ c ≤ d and abcd a perfect square, ad = bc.
PROOF:
(i) Every element is pq with p<q primes, so pq ≥ 2·3 = 6 > 0, and pq ≤ n by definition. (If n < 6, S_n = ∅ and (ii)
is vacuous.)

Preliminary facts. Every x ∈ S_n is squarefree with exactly two distinct prime factors; distinct elements of S_n
have distinct prime pairs (unique factorisation). For a prime p, v_p(x) ∈ {0,1} for x ∈ S_n.
(F) If y,z ∈ S_n and yz is a perfect square, then y = z. Indeed for every prime p, v_p(y)+v_p(z) is even and both
lie in {0,1}, so v_p(y) = v_p(z); hence y = z.

Let a ≤ b ≤ c ≤ d in S_n with abcd = r².

Case A: two of a,b,c,d are equal. Say the multiset {a,b,c,d} contains x twice; remove these two copies and call the
remaining two entries y,z. Then yz = r²/x² = (r/x)², a rational square that is an integer, hence a perfect square
(r/x is rational with integer square, so it is an integer). By (F), y = z. So the multiset is {x,x,y,y} (x = y
allowed). Its sorted form is (min,min,max,max), i.e. a = b and c = d, whence ad = bc (= ac).

Case B: a < b < c < d, all distinct. For each prime p, v_p(abcd) = #{e ∈ {a,b,c,d} : p | e} ∈ {0,...,4}, and it
is even, so it is 0, 2 or 4.
 B1. No prime divides all four: otherwise a=pa', b=pb', c=pc', d=pd' with a',b',c',d' primes ≠ p, pairwise distinct
     (as a,b,c,d are distinct), and a'b'c'd' = r²/p⁴ = (r/p²)² would be a perfect square (same integrality argument),
     but a product of four distinct primes has all exponents 1 — contradiction.
 B2. Hence every prime dividing abcd divides exactly two of a,b,c,d. Counting prime-element incidences:
     4 elements × 2 primes = 8 = 2·(#primes dividing abcd), so exactly 4 distinct primes occur.
 B3. Structure. Write a = p₁p₂ (p₁ ≠ p₂). p₂ divides exactly one other element e = p₂p₃; p₃ ≠ p₂, and p₃ ≠ p₁
     since otherwise e = a. p₃ divides exactly one element other than e, call it f = p₃p₄; f ≠ a since p₃ ∤ a, and
     f ≠ e. p₄ ≠ p₃; p₄ ≠ p₂ because p₂ already divides exactly the two elements a,e and f ∉ {a,e}.
     If p₄ = p₁: then p₁ (in a,f), p₂ (in a,e), p₃ (in e,f) each already occur in two elements, so the fourth
     element h ∉ {a,e,f} has both its prime factors outside {p₁,p₂,p₃}, giving at least 5 distinct primes,
     contradicting B2. So p₄ is a fourth prime distinct from p₁,p₂,p₃, and these are the four primes of B2.
     The fourth element h is divisible by neither p₂ nor p₃ (each already used twice), so h's two primes lie in
     {p₁,p₄}: h = p₁p₄. Thus {a,b,c,d} = {p₁p₂, p₂p₃, p₃p₄, p₄p₁}, and (p₁p₂)(p₃p₄) = (p₂p₃)(p₄p₁) = p₁p₂p₃p₄.
     So the four distinct numbers split into two pairs with equal products.
 B4. Which pairing. The three pairings of {a,b,c,d} are {a,b}|{c,d}, {a,c}|{b,d}, {a,d}|{b,c}. Since all are
     positive and a<b<c<d: ab < cb < cd (so the first pairing is unequal) and ac < bc < bd (second unequal).
     Hence the equal pairing from B3 is {a,d}|{b,c}, i.e. ad = bc.
In both cases ad = bc. ∎

## [valid-unrated] program/C3 PROVED OTHER
**Statement.** There is N₀ such that for all n ≥ N₀,
|S_n| ≥ (1/2)·n·ln ln n / ln n.
**Proof or evidence.**

=== THEOREM S1
STATEMENT: There is N₀ such that for all n ≥ N₀,
|S_n| ≥ (1/2)·n·ln ln n / ln n.
PROOF:
Fix an integer n ≥ e^{81}. Put y := n^{1/3} (a real number). We have y ≥ e^{27} > 2 and n/y = n^{2/3} ≥ e^{54} > 17.
For real t ≥ 0, π(t) denotes #{primes ≤ t}.

Step 1 (injection). Let P := {(p,q) : p, q prime, p ≤ y < q ≤ n/p}. For (p,q) ∈ P we have p ≤ y < q, so p < q,
and pq ≤ p·(n/p) = n. Hence pq ∈ S_n. The map (p,q) ↦ pq is injective on P. Indeed, if pq = p'q' with p<q and p'<q' all
prime, then unique factorisation gives {p,q} = {p',q'}, and ordering by size gives p=p', q=q'. For a prime p ≤ y we have
n/p ≥ n/y = n^{2/3} ≥ y, so #{q prime : y < q ≤ n/p} = π(n/p) − π(y) ≥ 0. Therefore
  |S_n| ≥ |P| = Σ_{p ≤ y} (π(n/p) − π(y)).

Step 2 (main term). Rosser–Schoenfeld 1962 (Illinois J. Math. 6, Cor. 1, (3.5)) gives π(x) > x/ln x for all real x ≥ 17.
For a prime p ≤ y we have x = n/p ≥ n^{2/3} > 17, and 0 < ln(n/p) ≤ ln n. Hence
  π(n/p) > (n/p)/ln(n/p) ≥ n/(p ln n).

Step 3 (error term). The primes ≤ y lie in {2,…,⌊y⌋}, so π(y) ≤ y. The sum in Step 1 has π(y) ≤ y terms, so
Σ_{p≤y} π(y) = π(y)² ≤ y² = n^{2/3}. Combining Steps 1–3,
  |S_n| ≥ (n/ln n)·Σ_{p≤y} 1/p − n^{2/3}.

Step 4 (elementary Mertens lower bound). Claim: for every real x > 1, Σ_{p≤x} 1/p > ln ln x − 1. Proof:
- For each prime p, (1 − 1/p)^{-1} = Σ_{k≥0} p^{-k}, a convergent series of positive terms.
- Multiply these finitely many series over p ≤ x and use unique factorisation. The product is Π_{p≤x}(1−1/p)^{-1} =
  Σ 1/m, summed over the m ≥ 1 whose prime factors are all ≤ x.
- Every m ≤ x has this property, so the product is ≥ Σ_{m≤x} 1/m ≥ ∫_1^{⌊x⌋+1} dt/t = ln(⌊x⌋+1) > ln x > 0.
- Take logarithms: Σ_{p≤x} −ln(1 − 1/p) > ln ln x.
- For 0 ≤ t < 1, −ln(1−t) = Σ_{k≥1} t^k/k ≤ t + Σ_{k≥2} t^k = t + t²/(1−t). With t = 1/p this gives −ln(1−1/p) ≤
  1/p + 1/(p(p−1)).
- Σ_{p≤x} 1/(p(p−1)) ≤ Σ_{m≥2} 1/(m(m−1)) = 1.
- Hence Σ_{p≤x} 1/p > ln ln x − 1. ∎
Apply this with x = y = n^{1/3} > 1. Since ln ln y = ln((ln n)/3) = ln ln n − ln 3, and n/ln n > 0, Step 3 gives
  |S_n| > (n/ln n)·(ln ln n − ln 3 − 1) − n^{2/3}.                                   (★)

Step 5 (conclusion). Write u := ln n ≥ 81. Dividing (★) by n/ln n > 0, it suffices to show
  ln u − ln 3 − 1 − u·e^{−u/3} ≥ (1/2)·ln u,
i.e. (1/2)·ln u ≥ ln 3 + 1 + u e^{−u/3}. Here n^{2/3}·(ln n)/n = u e^{−u/3}.
- h(u) = u e^{−u/3} has h'(u) = e^{−u/3}(1 − u/3) < 0 for u > 3. So for u ≥ 81, h(u) ≤ 81e^{−27} < 2·10^{−10}.
- (1/2) ln u ≥ (1/2) ln 81 = 2.19722… .
- ln 3 + 1 + 2·10^{−10} < 2.09862.
So the inequality holds, and |S_n| ≥ (1/2)·n·ln ln n/ln n for all n ≥ e^{81}. Take N₀ = ⌈e^{81}⌉. ∎

## [valid-routine] r1s1/C2 PROVED STRUCTURE
**Statement.** Let A be valid and let a,b,c,d ∈ A be squarefree. Write a = c1·q·P, b = c2·q'·P, c = c2·q·Q, d = c1·q'·Q with P≠Q, q≠q', c1≠c2 (any positive integers). Then this cannot happen. Equivalently, in the cell/colour encoding of all squarefree elements with ω≥2 (cell (P(a), second-largest prime), colour = cofactor), different colours never form a crossing rectangle.
**Beyond.** This is a new structural fact that controls cross-P consistency for every layer at once.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Immediate from the definition (team's R2); it is the 3-partite Pasch pattern already listed in R4", "why": "abcd is the square of c1·c2·q·q'·P·Q, and the three pairings are equal only if P=Q, q=q', or c1=c2 respectively, so the configuration is forbidden directly by R2; it is the Pasch pattern of R4 and gives no quantitative progress on the O(nL/log n) upper bound.", "panel": [{"verdict": "routine", "cite": "Immediate from the definition (team's R2); it is the 3-partite Pasch pattern already listed in R4", "significance": 0, "why": "abcd is the square of c1·c2·q·q'·P·Q, and the three pairings are equal only if P=Q, q=q', or c1=c2 respectively, so the configuration is forbidden directly by R2; it is the Pasch pattern of R4 and gives no quan`
**Proof or evidence.**

- The product abcd = (c1c2qq'PQ)² is a square.
- The three pairings are all unequal: ab/cd = P²/Q² ≠ 1; ac/bd = q²/q'² ≠ 1; ad/bc = c1²/c2² ≠ 1.
- Sorting the four elements as w≤x≤y≤z, validity forces wz = xy, which is one of the three pairings. Contradiction. Repeated values are harmless.

## [valid-routine] r1s1/C3r PROVED NEGATIVE
**Statement.** **Setup.** Let M, m ≥ 1. A *cell* is a pair (P, q) ∈ [M] × [m], where [N] = {1, …, N}. A *coloured incidence system* on the grid consists of:
- a set 𝒦 of colour labels, and
- for each label u ∈ 𝒦, a set C_u ⊆ [M] × [m] (the colour class of u).

A cell x *has colour* u if x ∈ C_u. A *crossing rectangle* is a choice of P ≠ P′ in [M], q ≠ q′ in [m], and labels u, v ∈ 𝒦 (not necessarily distinct) such that:
- (P, q) and (P′, q′) both lie in C_u, and
- (P, q′) and (P′, q) both lie in C_v.

In words, both diagonals of a non-degenerate axis-parallel rectangle are each monochromatic.

**Theorem.** For all integers M, m ≥ 1 and t ≥ 0 there is a coloured incidence system on [M] × [m] such that:
1. every cell has exactly t + 2 colours;
2. every colour class meets each row {P} × [m] in at most one cell, or meets each column [M] × {q} in at most one cell, or both;
3. there is no crossing rectangle.

**Corollary (meta-statement, made precise).** Consider any assertion of the form "if a coloured incidence system on [M] × [m] has no crossing rectangle, then some cell has at most C colours", where C does not depend on M or m. Every such assertion is false.

So any lemma bounding the number of colours per cell (such as the intended "Ω = 3 lemma") must use information beyond the incidence structure. In the intended application, that extra information is the size constraint u·q·P ≤ n on the colours u. This corollary is the only negative conclusion claimed.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Colour classes that are single cells (or full rows/columns plus singleton padding) never contain a diagonal pair, so they give any number of colours per cell with no crossing rectangle; the 'theorem' is immediate. The corollary only says a purely incidence-based lemma cannot work, which tells us nothing about F(n).", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Colour classes that are single cells (or full rows/columns plus singleton padding) never contain a diagonal pair, so they give any number of colours per cell with no crossing rectangle; the 'theorem' is immediate. The corollary only says a purely incidence-based lemma cannot work, which tells us nothing about F(n)."}, {"verdict": "routine", `
**Proof or evidence.**

**Construction.** Use the following labels:
- a line label L_{s,b} for each s ∈ {1, …, t} and each b ∈ ℤ, with C_{L_{s,b}} = {(P, q) ∈ [M] × [m] : q = sP + b};
- a row label R_{P₀} for each P₀ ∈ [M], with C_{R_{P₀}} = {P₀} × [m];
- a column label K_{q₀} for each q₀ ∈ [m], with C_{K_{q₀}} = [M] × {q₀}.

Labels are distinct formal objects, even when two of them have the same class.

**(1) Exactly t + 2 colours per cell.** Fix a cell (P, q).
- For each s ∈ {1, …, t}, the cell lies in C_{L_{s,b}} exactly when b = q − sP. So it lies on exactly one line label of each slope s, giving t line colours.
- It lies in C_{R_P} and in no other row class.
- It lies in C_{K_q} and in no other column class.

The total is t + 2.

**(2) Row and column structure.** Each row class meets each column in exactly one cell. Each column class meets each row in exactly one cell. A line class C_{L_{s,b}} meets row P only at q = sP + b, so it meets each row in at most one cell.

**(3) No crossing rectangle.** Suppose P ≠ P′, q ≠ q′, and labels u, v satisfy (P, q), (P′, q′) ∈ C_u and (P, q′), (P′, q) ∈ C_v.

First we identify u.
- u is not a row label: a row class contains only cells with one first coordinate, but P ≠ P′.
- u is not a column label: a column class contains only cells with one second coordinate, but q ≠ q′.
- So u = L_{s,b} with 1 ≤ s ≤ t. Then q = sP + b and q′ = sP′ + b. Subtracting gives q′ − q = s(P′ − P).

The same argument applied to v shows v = L_{s′,b′} with 1 ≤ s′ ≤ t. From q′ = sP + b′... more precisely, from q′ = s′P + b′ and q = s′P′ + b′, subtracting gives q − q′ = s′(P′ − P).

Adding the two identities gives 0 = (s + s′)(P′ − P). Since P′ ≠ P, this forces s + s′ = 0. But s + s′ ≥ 2, a contradiction. Hence no crossing rectangle exists.

**Corollary.** Given any constant C, choose t with t + 2 > C. The theorem then produces a crossing-free system in which every cell has more than C colours. This contradicts the assertion. ∎

## [valid-routine] r1s1/C5r PROVED QUANT
**Statement.** **Notation.** Throughout:
- A set A is *valid* if, whenever a ≤ b ≤ c ≤ d are in A and abcd is a square, ad = bc.
- L = log log n, ℓ(x) = log log(x + e^e) ≥ 1, and π_j(t) = #{m ≤ t squarefree : ω(m) = j}.

**Hypothesis (C1, as stated).** For every n and every valid A ⊆ [n],
#{a ∈ A squarefree : ω(a) = 3} ≤ T_2(n) + O(n/log n),
where T_2(n) = #{primes 3 ≤ q < P : 2qP ≤ n}.

**Counting function U_j.** For j ≥ 2 and real x, y, let U_j(x,y) be the number of tuples (q, P′, p_3, …, p_j) of primes such that:
- 3 ≤ q < P′,
- p_3 < p_4 < … < p_j < y,
- 2qP′p_3⋯p_j ≤ x.

Note that U_2(x,y) = T_2(x), and no order is imposed between {q, P′} and the chain p_3 < … < p_j. Write U_j(n) = U_j(n, n+1).

**Theorem.** Assume C1. Fix k ≥ 3. For every valid A ⊆ [n],

#{a ∈ A squarefree : ω(a) = k} ≤ U_{k−1}(n) + O_k(n L^{k−3}/log n) ≤ (1 + o(1)) · (k−1) n L^{k−2} / (4 (k−3)! log n).

The number of squarefree a ≤ n with ω(a) = k is ~ n L^{k−1}/((k−1)! log n). So the theorem bounds the proportion of them that A can contain by (1 + o(1))(k−1)²(k−2)/(4L), which tends to 0. For k = 3 this is the original constant: 1/2, i.e. a proportion of 1/L.

**Remark.** If C1's proof in fact yields the y-refined base (with T_2(x,y), largest prime < y), the original constant 1/(2(k−2)!) follows by the same argument. That refinement is not used here.
**Beyond.** KNOWN only has the trivial layer bound, and "recursion loses a factor". Plain recursion with the trivial base gives a bound worse than trivial. Using C1 as the base gains a factor L on every layer.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "Conditional on the unproven ω=3 bound C1, the layer-k bounds follow from the standard observation that dividing A by a common prime preserves validity, plus naive recursion and Sathe–Selberg counting. The bounds are not uniform in k and sum to about n·L², worse than trivial, so even granting C1 this does not reach the CORE upper bound.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "Conditional on the unproven ω=3 bound C1, the layer-k bounds follow from the standard observation that dividing A by a common prime preserves validity, plus naive recursion and Sathe–Selberg counting. The bounds are not uniform in k and sum to about n·L², worse than trivial, so even granting C1 this does not reach the CO`
**Proof or evidence.**

**Claim H_k (k ≥ 3).** There is C_k such that for all real x ≥ 1, all y, and every valid A′ ⊆ [x] whose elements have all prime factors < y:

#{a ∈ A′ squarefree : ω(a) = k} ≤ U_{k−1}(x,y) + E_k(x), where E_k(x) = C_k x ℓ(x)^{k−3}/log(x+2).

**Base case H_3.** U_2(x,y) = T_2(x) = T_2(⌊x⌋), so H_3 does not depend on y.
- For ⌊x⌋ ≥ n_0, apply C1 with n = ⌊x⌋.
- For x < n_0, the count is at most x ≤ C x/log(x+2).
- Taking C_3 large enough covers both ranges.

**Step H_k ⇒ H_{k+1}.** Let A′ be as in H_{k+1}'s hypothesis.

1. *Splitting.* Each squarefree a ∈ A′ with ω(a) = k+1 is a = P·m, where P = P(a) < y is its largest prime and m is squarefree with ω(m) = k and all primes < P. Let N(P) = {a/P : a ∈ A′ squarefree, ω(a) = k+1, P(a) = P}. Then N(P) ⊆ [x/P].

2. *N(P) is valid.* Take a′ ≤ b′ ≤ c′ ≤ d′ in N(P) with a′b′c′d′ a square. Then Pa′ ≤ Pb′ ≤ Pc′ ≤ Pd′ lie in A′, and their product is P⁴·a′b′c′d′, a square. Validity of A′ gives P²a′d′ = P²b′c′, so a′d′ = b′c′.

3. *Applying H_k.* An element with ω ≥ 3 is at least 2·3·5 = 30, so N(P) = ∅ unless x/P ≥ 30. When N(P) is nonempty, H_k with parameters (x/P, P) gives |N(P)| ≤ U_{k−1}(x/P, P) + E_k(x/P). Since U ≥ 0,

   count ≤ Σ_{P<y} U_{k−1}(x/P, P) + Σ_{P ≤ x/30} E_k(x/P).

4. *Main term.* Classify tuples by their last coordinate p_k = P. This shows Σ_{P<y} U_{k−1}(x/P, P) = U_k(x,y) exactly, directly from the definition.

5. *Error term: reduction.* The sum is empty for x < 60. For x ≥ 60:
   - ℓ is increasing, so ℓ(x/P) ≤ ℓ(x).
   - x/P ≥ 30 gives log(x/P + 2) ≥ log(x/P).
   
   Hence Σ_{P ≤ x/30} E_k(x/P) ≤ C_k ℓ(x)^{k−3} · x · S(x), where S(x) = Σ_{P ≤ x/30} 1/(P log(x/P)).

6. *Bounding S(x) = O(ℓ(x)/log x).*
   - **Primes P ≤ √x.** Here log(x/P) ≥ ½ log x. Mertens gives Σ 1/P ≤ log log x + O(1), so this part is O(ℓ/log x).
   - **Primes in (√x, x/30].** Cover them by I_j = (x/2^{j+1}, x/2^j] for 4 ≤ j ≤ J, where J is the least j with x/2^{J+1} ≤ √x. Then J ≤ log_2 x, and x/2^j > √x for j ≤ J.
     - Chebyshev's bound π(t) ≤ c t/log t gives Σ_{P∈I_j} 1/P ≤ (2^{j+1}/x) π(x/2^j) ≤ 2c/log(x/2^j) ≤ 4c/log x.
     - On I_j we have log(x/P) ≥ j log 2.
     - So this part is at most (4c/(log 2 · log x)) Σ_{j≤J} 1/j = O(log log x/log x) = O(ℓ/log x).

7. *Closing the induction.* Steps 5 and 6 give Σ_{P ≤ x/30} E_k(x/P) ≤ C′ C_k x ℓ(x)^{k−2}/log(x+2). Take C_{k+1} = C′ C_k. This proves H_{k+1}.

**Conclusion.** Apply H_k with x = n and y = n+1. Since ℓ(n) = L + o(1),

count ≤ U_{k−1}(n) + O_k(n L^{k−3}/log n).

**Size of U_j(n), j = k−1 ≥ 2.** For j = 2, U_2 = T_2 ≤ π_2(n/2). For j ≥ 3, split the tuples into two kinds.

**(i) All j primes distinct.**
- The product m is squarefree, ω(m) = j, and m ≤ n/2.
- The tuple is determined by m together with the choice of which two primes form {q, P′}. So each m has at most C(j,2) preimages.
- By Landau, π_j(n/2) ~ (n/2) L^{j−1}/((j−1)! log n).
- With j = k−1 this gives a contribution ≤ (1+o(1)) C(k−1,2)(n/2) L^{k−2}/((k−2)! log n) = (1+o(1))(k−1) n L^{k−2}/(4(k−3)! log n).

**(ii) Some p_i equals q or P′.** There are at most 2(j−2) choices of which coincidence occurs.
- Given the choice, delete the duplicated chain entry. The tuple is then determined by the repeated prime p and an ordered (j−2)-tuple of primes with product ≤ n/p².
- Let N_i(t) be the number of ordered i-tuples of primes with product ≤ t. Then N_i(t) ≤ i!·#{m ≤ t : Ω(m) = i}.
  - Landau's theorem for Ω with i fixed gives N_i(t) ≪_i t ℓ(t)^{i−1}/log(t+2).
  - Trivially, N_i(t) ≤ i!·t.
- For p ≤ n^{1/4}, log(n/p²) ≥ ½ log n. Summing over these p gives ≪ n L^{j−3}/log n.
- For p > n^{1/4}, Σ n/p² ≪ n^{3/4}.
- So (ii) = O_k(n L^{k−4}/log n), which is absorbed into the error term.

This proves the theorem. The final proportion follows by dividing by π_k(n) ~ n L^{k−1}/((k−1)! log n), which gives (k−1)²(k−2)/(4L)·(1 + o(1)).

## [valid-routine] r1s2/C1 PROVED STRUCTURE
**Statement.** Let A be valid (RequiredCondition). Let X, Y, Z be finite nonempty sets of positive integers and
T = {(x,y,z) ∈ X×Y×Z : xyz ∈ A}. Then |T| ≤ (3/m)^{1/8}·|X||Y||Z|, where m = min(|X|,|Y|,|Z|).
**Beyond.** R4 states Pasch only for coprime atoms. Here there is no coprimality, and the result is a quantitative
supersaturation statement.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard Cauchy–Schwarz supersaturation for Pasch/2x2x2-box configurations (Erdős 1964 box theorem; Kővári–Sós–Turán-type counting)", "why": "A valid A forces T to avoid non-degenerate Pasch configurations, and the (3/m)^{1/8} bound is exactly what the routine three-step Cauchy–Schwarz count of Pasch configurations minus degenerate ones gives. It only bites at density about m^{-1/8}, far above the 1/log n regime the problem needs, as the team's own barrier notes.", "panel": [{"verdict": "routine", "cite": "Standard Cauchy–Schwarz supersaturation for Pasch/2x2x2-box configurations (Erdős 1964 box theorem; Kővári–Sós–Turán-type counting)", "significance": 1, "why": "A valid A forces T to avoid non-degenerate Pasch configurations, and the (3/`
**Proof or evidence.**

(a) Suppose T contains (x1,y1,z1), (x1,y2,z2), (x2,y1,z2), (x2,y2,z1) with x1≠x2, y1≠y2, z1≠z2. Let a1..a4 be
the four products. Then a1a2a3a4 = (x1x2y1y2z1z2)^2 is a square. Compare the three pairings:
- a1a4 vs a2a3: these are W·z1^2 vs W·z2^2 with W = x1x2y1y2;
- a1a2 vs a3a4: these are x1^2 vs x2^2 times y1y2z1z2;
- a1a3 vs a2a4: these are y1^2 vs y2^2 times x1x2z1z2.
None of the three is an equality. Sort the four as a≤b≤c≤d. Then ad=bc is one of these three pairings, so A violates
the condition.
(b) Write hom for the number of 6-tuples (x1,x2,y1,y2,z1,z2) with all 8 triples (x_a,y_b,z_c) in T, and set
d = |T|/(XYZ). For fixed (z1,z2), put g(x,y) = 1_T(x,y,z1)·1_T(x,y,z2). The C4 count of g is
Σ_{y1,y2}(Σ_x g(x,y1)g(x,y2))^2 ≥ (Σ g)^4/(XY)^2.
Summing over the Z^2 pairs (z1,z2) and applying the power mean Σa_i^4 ≥ (Σa_i)^4/N^3 gives
hom ≥ (Σ_{z1,z2} Σ g)^4 / (Z^6 (XY)^2). Here Σ_{z1,z2} Σ g = Σ_{x,y}(Σ_z 1_T)^2 ≥ |T|^2/(XY), hence
hom ≥ d^8 (XYZ)^2.
(c) Each such 6-tuple contains the 4 Pasch triples, so by (a) it has x1=x2, y1=y2 or z1=z2. Therefore
hom ≤ XY^2Z^2 + X^2YZ^2 + X^2Y^2Z, and so d^8 ≤ 1/X + 1/Y + 1/Z ≤ 3/m. ∎

## [valid-routine] r1s2/C3 PROVED NEGATIVE
**Statement.** For each prime q and each finite set Z of primes, there is a valid A with boxes X, Y (|X|=|Y|=m=q²+q+1),
Z, for which |T| = (q+1)·|Y||Z| = ((q+1)/m)·|X||Y||Z| > m^{-1/2}|X||Y||Z|. Hence in C1 the exponent 1/8 can be
raised to at most 1/2. The sharper lemma proposed in leg 1's NEXT, |T| ≤ C·|Y||Z| (saving ~1/|X|, from alternating-C4
colourings), is FALSE: the ratio |T|/(|Y||Z|) = q+1 is unbounded.
**Beyond.** This is a new obstruction to the route that leg 1 proposed for the constant.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Reiman 1958; Brown 1966; Erdős–Rényi–Sós 1966 (projective-plane incidence graphs are extremal C4-free / sharp for Kővári–Sós–Turán)", "why": "The counterexample is the standard projective-plane incidence construction showing Zarankiewicz/KST bounds are sharp at exponent 1/2, so ruling out a bounded-degree lemma is a textbook observation. It only refutes an internal proof route and does not change the known bounds for F(n).", "panel": [{"verdict": "routine", "cite": "Reiman 1958; Brown 1966; Erdős–Rényi–Sós 1966 (projective-plane incidence graphs are extremal C4-free / sharp for Kővári–Sós–Turán)", "significance": 0, "why": "The counterexample is the standard projective-plane incidence construction showing Zarankiewicz/KST bounds are sharp `
**Proof or evidence.**

Let x_1..x_m, y_1..y_m and the primes of Z be distinct primes. Let L_1..L_m be the lines of PG(2,q) on point set
[m]. Any two lines meet in exactly one point. Put A = {x_i y_j z : j ∈ L_i, z ∈ Z}, T = {(x_i,y_j,z)}, so |T| = m(q+1)|Z|.
Validity: take a 4-multiset with square product. Each coordinate multiset (x's, y's, z's) has even multiplicities, so
it is {u,u,u,u} or {u,u,v,v}.
- Case x = {x,x,x',x'} with x≠x'. Let the y's in row x be y1,y2 and in row x' be y3,y4. If y1≠y2, then
  {y3,y4}={y1,y2}, so rows x and x' share two points. That is impossible. So y1=y2=y and y3=y4=y'. The elements are
  (x,y,z1),(x,y,z2),(x',y',z3),(x',y',z4).
  - If z1=z2, then z3=z4, and a1a3 = a2a4.
  - If z1≠z2, then {z3,z4}={z1,z2}. Pair a1 with the element that has z2, and a2 with the one that has z1: both
    products equal xyx'y'z1z2.
- Case all x equal: the same argument on (y,z) gives an equal pairing (y's {y,y,y',y'}: the z's at y and y' coincide as
  multisets or pair up; y's all equal: the z's pair up).
So every square 4-multiset has an equal pairing, and by R2, A is valid. ∎

## [valid-routine] r1s3/C1 PROVED REDUCTION
**Statement.** Suppose there is a constant C such that for all n ≥ 3, every valid A ⊆ [1,n], and every y ∈ [2,n],
N_y(A) := #{a∈A : P(a)∈(y,2y]} ≤ C·n/(ln 2y · ln(2n/y)).  (X)
Then every valid A ⊆ [1,n] satisfies |A| ≤ 2 + (2C/ln2)·n·(1+ln(log₂n+1))/ln n. In particular F(n) = O(n·L/log n), which is CORE (L = ln ln n).
**Beyond.** This is the assigned implication T9, with explicit constants.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "The implication is just a dyadic decomposition by largest prime factor followed by a harmonic-sum computation, which is standard. All of CORE's difficulty is moved into hypothesis (X), a scale-uniform, essentially sharp per-window bound that is as hard as the original upper bound (and Erdős–Sárközy–Sós 1995 should be checked for whether the n·loglog n/log n upper bound is already known).", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "The implication is just a dyadic decomposition by largest prime factor followed by a harmonic-sum computation, which is standard. All of CORE's difficulty is moved into hypothesis (X), a scale-uniform, essentially sharp per-window bound that is as hard as the original `
**Proof or evidence.**

Let K = ⌈log₂ n⌉ − 1. Then 2^K < n ≤ 2^{K+1}, so y_k = 2^k ∈ [2,n] for 1 ≤ k ≤ K.
Every a ∈ A with a ≥ 2 and P(a) ≥ 3 has P(a) in exactly one interval (2^k, 2^{k+1}] with 1 ≤ k ≤ K, because 3 ≤ P(a) ≤ n ≤ 2^{K+1}.
The remaining elements are 1 and the powers of 2. By R1 (distinct kernels), A contains at most one element of kernel 1 and at most one element of kernel 2. So there are at most 2 such elements.
Hence |A| ≤ 2 + Σ_{k=1}^K C·n/(ln 2^{k+1} · ln(2n/2^k)).
Since n > 2^K, we have 2n/2^k > 2^{K+1−k}. So the k-th term is ≤ C n/((ln2)²(k+1)(K+1−k)).
Put j = k+1 ∈ [2, K+1]. Then 1/(j(K+2−j)) = (1/(K+2))(1/j + 1/(K+2−j)), so Σ_k ≤ 2H_{K+1}/(K+2).
Now K+2 > log₂ n = ln n/ln 2 and H_{K+1} ≤ 1 + ln(K+1) ≤ 1 + ln(log₂ n + 1).
Hence |A| ≤ 2 + (2C/ln 2)·n·(1 + ln(log₂n+1))/ln n. ∎
Remarks:
- It suffices to have X for squarefree A, because R3 then transfers the bound to all A.
- Restricting to a range of scales gives the matching local statement. If X holds only for y ∈ [y₀(n), n], the remaining part is bounded by #{a ≤ n : P(a) ≤ 2y₀}, a smooth-number count Ψ(n, 2y₀).

## [conditional] deep/C2 PROVED QUANT
**Statement.** There is an absolute C such that for all n ≥ 2, every valid A ⊆ [1,n] (not necessarily squarefree) and every y ∈ [2,n],
N_y(A) ≤ C·n/(ln 2y·min(ln 2y, ln(2n/y))).
Moreover (Theorem M): for n ≥ n₀ and n^{1/(6L)} ≤ y ≤ √n(ln 2n)^4, with z = n/y,
N_y(A) ≤ 3.18(1+o(1))·n/(ln 2y·ln z) + 5n/ln²(2y) + o(n/ℓ²),
where the o(·) terms are uniform in y and A.
**Conditional on** deep/C4, deep/C5 (its own proof passed as valid-restatement).
**Beyond.** This is the assigned target X̃. Its equivalent form is X on y ≥ n^δ with C(δ) = O(1/δ). It was never proved in KNOWN. The r1s3/C6 sketch was unvalidated: it was non-uniform and cited de Bruijn outside a checked range. That sketch is re-derived and repaired here.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "Reading N_y as elements whose largest prime factor lies in (y,2y], summing the bound over dyadic y ≥ n^{1/(6L)} gives F(n)=O(n loglog n/log n), which is exactly the open upper bound (CORE) matching the Erdős–Sárközy–Sós lower bound. As a claimed full solution, its uniformity and smooth-number ranges need the most careful checking.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "Reading N_y as elements whose largest prime factor lies in (y,2y], summing the bound over dyadic y ≥ n^{1/(6L)} gives F(n)=O(n loglog n/log n), which is exactly the open upper bound (CORE) matching the Erdős–Sárközy–Sós lower bound. As a claimed full solution, its uniformity and smooth-number ranges need the most care`
**Proof or evidence.**

Cited inputs (all classical):
- (Ch) π(x) < 1.26x/ln x for x > 1 (Rosser–Schoenfeld).
- (Me1) Σ_{p≤x} 1/p ≤ lnln x + 1 for x ≥ 2.
- (Me2) |Σ_{p≤x} ln p/p − ln x| ≤ 2 for x ≥ 2 (Mertens). Both were checked numerically to 2·10⁶: maxima −0.13 and 1.33.
- (E) Erdős: a multiplicatively Sidon M ⊆ [1,x] (ab = cd ⇒ {a,b} = {c,d}) has |M| ≤ G(x) ≤ π(x) + C_E x^{3/4} for x ≥ 1 (KNOWN).
- (La) #{m ≤ n : ω(m) = 2} = (1+o(1))nL/ℓ (Landau, KNOWN).

Lemma V (R2). For a ≤ b ≤ c ≤ d with abcd a square: ad = bc iff some pairing has equal products. Indeed ab = cd forces a=b=c=d, and ac = bd forces a=b and c=d; each gives ad = bc. So validity means every 4-multiset with square product has a pairing with equal products. The fibre M_P = {m : mP ∈ A} of a valid A is valid: multiply a bad quadruple by P. Hence (R1) the elements of M_P have distinct squarefree kernels.

Lemma A. Let A be valid and P ≠ Q primes. Let m₁,…,m₄ be distinct, coprime to PQ, with m_iP ∈ A and m_iQ ∈ A for all i, and Πm_i a square. This is impossible. Proof:
- At most one of E12: m₁m₂ = m₃m₄, E13, E14 holds, because any two of them force a coincidence.
- Take a split {i,j}|{k,l} and the 4 elements m_iP, m_jP, m_kQ, m_lQ. They are distinct, since Q ∤ m_i. Their product is square.
- The pairing m_im_jP² = m_km_lQ² is impossible, because v_P differs.
- So validity needs E_{ik} ∨ E_{il}. Concretely, split 12|34 needs E13 ∨ E14, 13|24 needs E12 ∨ E14, and 14|23 needs E12 ∨ E13.
- These cannot all hold when at most one E is true.
Tested on all square 4-sets of [1,40], [1,60], [1,80] with (P,Q) = (7,11), (5,13), (3,7), i.e. P, Q < z (the mid-range case): 0 exceptions.

Lemma Q. Q4(z) ≤ (ζ(2)/24)·z²(1+ln z)^6 for z ≥ 1.
- Write m_i = s_i r_i² with s_i squarefree. The product is a square iff s_i = g·Π_{j≠i} x_{ij}, with g and the x_{ij} pairwise coprime and squarefree. This decomposition is injective.
- The number of ordered tuples is ≤ Σ Π_i √(z/s_i) = z²·Σ g^{−2}·Π_{i<j} x_{ij}^{−1} ≤ z²·ζ(2)·H_z^6.
- Divide by 4!.

Lemma R (Rankin). Let X ≥ Y ≥ 2 and u = ln X/ln Y.
(a) If ln Y ≥ max(2, 4 ln u), then Ψ(X,Y) ≤ e^{3.1}·X·(ln Y)·e^{2u}·u^{−u}.
(b) Always Ψ(X,Y) ≤ X^{7/8}·exp(8Y^{1/8} + 2.1).
Proof:
- For any σ ∈ [3/4, 1], Ψ ≤ Σ_{P(m)≤Y} (X/m)^σ = X^σ·Π_{p≤Y}(1−p^{−σ})^{−1}.
- The logarithm of the product is ≤ Σ_{p≤Y} p^{−σ} + Σ_p Σ_{k≥2} p^{−3k/4}. The second sum is ≤ Σ_p p^{−3/2}/(1−2^{−3/4}) ≤ 2.0989 (computed).
- (a) Take σ = 1 − ln u/ln Y ≥ 3/4, so X^σ = X·u^{−u}.
  - p^{−σ} = p^{−1}e^{(ln u)t} with t = ln p/ln Y ∈ (0,1].
  - By convexity e^{(ln u)t} ≤ 1 + ut.
  - So Σ p^{−σ} ≤ Σ 1/p + (u/ln Y)·Σ ln p/p ≤ lnln Y + 1 + u(1 + 2/ln Y) ≤ lnln Y + 1 + 2u, by (Me1), (Me2) and ln Y ≥ 2.
  - Then e^{1+2.1} = e^{3.1}.
- (b) Take σ = 7/8. Then Σ_{p≤Y} p^{−7/8} ≤ Σ_{m≤Y} m^{−7/8} ≤ 8Y^{1/8}.
- Numerically checked on 4 cases (with slack).

Lemma K (KST supersaturation). Let G be bipartite with centre set U, |U| ≤ x, and other side V, |V| ≤ w. Let e be the number of edges, S = Σ_{v∈U} C(d_v,2), and c4 the number of C4s.
(K1) S ≤ w² + w√(2·c4).
(K2) e ≤ 2x + 2√x·w + 2^{5/4}√(xw)·c4^{1/4}.
(K3) e ≤ |U| + S.
Proof:
- c4 = Σ_{pairs in V} C(codeg,2), and Σ codeg = S over N ≤ w²/2 pairs.
- By Jensen, c4 ≥ S(S/N − 1)/2 ≥ S²/(2w²) when S ≥ w².
- If e ≥ 2x, then S ≥ e(e/x − 1)/2 ≥ e²/(4x), so e ≤ 2√(xS); then apply (K1).
- C(d,2) ≥ d − 1.

Lemma S (supersaturated Sidon). Let z ≥ 2 and 0 < γ₀ < β < 1, with ε' = 1−β and 0 < ε ≤ ε'/4. Take a grid γ₀ < … < γ_I = β with gaps ≤ ε. Then every M ⊆ [1,z]∩ℕ satisfies, with s = s(M),
|M| ≤ π(z) + E + z^{ε'}√(2s) + I·2^{5/4}z^{(1+ε)/2}s^{1/4}, where E = Ψ(z, z^{γ₀}) + z^{2ε'} + I·(2z^{1−γ₀} + 2z^{1−3ε'/8}).
Proof. Classify each m ∈ M by Q = P(m), and set r = m/Q. The map m ↦ (r,Q) is injective.
- Class C: Q ≤ z^{γ₀}. This class has ≤ Ψ(z, z^{γ₀}) elements.
- Class B_i: Q ∈ (z^{γ_i}, z^{γ_{i+1}}].
  - Centres are r < x = z^{1−γ_i}, and the other side is Q ≤ w = z^{γ_{i+1}}.
  - A C4 {r₁,r₂}×{Q₁,Q₂} gives the 4 distinct elements r_jQ_k of M, whose product is (r₁r₂Q₁Q₂)². Distinct C4s give distinct 4-sets, so c4 ≤ s.
  - (K2) applies, with (1−γ_i)/2 + γ_{i+1} ≤ (1+ε+β)/2 ≤ 1 − 3ε'/8 and √(xw) ≤ z^{(1+ε)/2}.
- Class A: Q > z^β.
  - Centres are the primes Q (at most π(z) of them), and the other side is r < z^{ε'}.
  - (K3) and (K1) give e ≤ π(z) + z^{2ε'} + z^{ε'}√(2s).
- Sum over the classes.
- (K2) was verified class by class on 5 test sets in [1,4000], including all integers and the ω≤2 set. The worst ratio e/bound was 0.126, and there were 0 failures.

Lemma T (top range, = r1s3/C5 re-checked). Let Y ≥ √n, z = n/Y and T = {a∈A : P(a) > Y}. Then |T| ≤ Σ_{Y<P≤n} G(n/P) + Q4(z). The same holds for N_y with y ≥ √n, using Σ_{P∈W} and Q4(n/y).
Proof:
- Fibre elements satisfy m ≤ n/P < z ≤ √n ≤ Y < P, Q. So Lemma A gives that each square 4-set of [1,z] lies in ≤ 1 fibre, and hence Σ_P s(M_P) ≤ Q4(z).
- Delete one element from each square 4-set of M_P. What remains is multiplicatively Sidon:
  - distinct a, b, c, d with ab = cd would form a square 4-set, which was deleted;
  - a = b would give cd = a², and then c = d = a by R1.
- So |M_P| ≤ G(n/P) + s(M_P).
Sharp form, with Y = Y₁ = √n(ln 2n)^4:
- Σ π(n/P) ≤ #{pP ≤ n : p < P} ≤ (1+o(1))nL/ℓ by (La), using p ≤ n/P < √n < P.
- C_E·Σ_{P≤n}(n/P)^{3/4} = O(n/ℓ), by partial summation with (Ch).
- Q4(n/Y₁) ≤ 0.07(n/Y₁)²(1+ℓ)^6 = O(n/ℓ²).
X-form for y ≥ Y₁, with z = n/y ≤ √n/(ln 2n)^4:
- Q4(z) ≤ 0.07z√n(ln 2n)² ≤ yz/(ln 2n)² ≤ n/(ln 2y·ln 2z).
- By (E), (Ch) and monotonicity of G, Σ_{P∈W} G(n/P) ≤ #W·G(z) ≤ C′n/(ln 2y·ln(2n/y)).

Theorem M (mid range). Let n ≥ n₀, n^{1/(6L)} ≤ y ≤ Y₁ and z = n/y. Then ℓ/3 ≤ ln z ≤ ℓ for large n.
- Discard D: the a with P(a) = P ∈ W and a further prime of W dividing a/P (this includes P² | a).
  - #D ≤ (n/2)(Σ_W 1/p)² + n#W/y².
  - We have #W ≤ π(2y) ≤ 2.52y/ln 2y and Σ_W 1/p ≤ 2.52/ln 2y.
  - Since ln(2y)/y ≤ 0.7, this gives #D ≤ 5n/ln²(2y).
- The remaining a = mP have m free of window primes, so P, Q ∤ m. Put M_P = {such m} ⊆ [1,z].
- By Lemma A, Σ_P s(M_P) ≤ Q4(z) ≤ 4.39z²ℓ^6.
- Apply Lemma S to each M_P with ε' = 1/(24L), ε = 1/(96L), γ₀ = 1/(6L), β = 1 − ε', γ_i = γ₀ + iε, and I ≤ 1 + 96L.
  - Lemma R(a) applies with u = 6L, since ln z^{γ₀} ≥ ℓ/(18L) ≥ max(2, 4 ln 6L). It gives Ψ(z, z^{γ₀}) ≤ e^{3.1}z·ℓ^{13−6ln(6L)} = o(z/ℓ).
  - z^{2ε'} = o(z/ℓ).
  - I·ℓ·z^{−γ₀} ≤ (1+96L)ℓ·e^{−ℓ/(18L)} → 0.
  - I·ℓ·z^{−3ε'/8} ≤ (1+96L)ℓ·e^{−ℓ/(192L)} → 0.
  - So E = o(z/ln z), uniformly.
- Hölder:
  - Σ_P √s_P ≤ √(#W·Q4).
  - Σ_P s_P^{1/4} ≤ #W^{3/4}·Q4^{1/4}.
  - #W ≤ 2y.
- Error terms:
  - Err1 ≤ 4.2·n·z^{ε'}ℓ³/√y ≤ 4.2·n·ℓ³·e^{−ℓ/(24L)} = o(n/ℓ²), using √y ≥ n^{1/(12L)} and z^{ε'} ≤ n^{1/(24L)}.
  - Err2 ≤ 5.8(1+96L)·n·z^{ε/2}ℓ^{1.5}/y^{1/4} ≤ 5.8(1+96L)·n·ℓ^{1.5}·e^{−7ℓ/(192L)} = o(n/ℓ²).
  - Both use ℓ/L ≫ L.
- Main term: #W·π(z) ≤ 3.18n/(ln 2y·ln z), and #W·E = o(n/(ln 2y·ln z)). This gives Theorem M.

Proof of X̃. Fix n₀ large (all the o(·) terms above below 1).
- Range I, y ≥ Y₁: Lemma T, X-form.
- Range II, n^{1/(6L)} ≤ y < Y₁: Theorem M.
  - If y ≤ √n, then ln z ≥ ln y ≥ ½ln 2y, and n/ℓ² ≤ 4n/ln²2y.
  - If y > √n, then ln z ≥ ℓ/3, ln(2n/y) ≤ ln 2y and ln(2n/y) ≤ ℓ, so every term is ≤ C·n/(ln 2y·ln(2n/y)).
- Range III, y < n^{1/(6L)}: N_y ≤ Ψ(n, Y) with Y = 2y.
  - If ln Y < 2: Ψ ≤ (1 + log₂n)^4 ≤ n/ℓ².
  - If 2 ≤ ln Y < 4 ln u: then Y < ℓ⁴, and R(b) gives Ψ ≤ n^{7/8}e^{8√ℓ+2.1} ≤ n/ℓ².
  - Otherwise R(a) applies with u ≥ 6L − 1. Then Ψ·ln²Y/n ≤ e^{3.1}ℓ³e^{−u(ln u−2)}u^{−3} → 0.
  - In all cases N_y ≤ n/ln²(2y).
- n < n₀: N_y ≤ n ≤ (ln 2n₀)²·n/(ln 2y·min(…)). ∎

## [conditional] deep/C5r PROVED STRUCTURE
**Statement.** Notation:
- ℓ = ln n and L = ln ℓ.
- P(m) is the largest prime factor of m, with P(1) = 1.
- A ⊆ [1,n] is *valid* if, whenever a ≤ b ≤ c ≤ d lie in A and abcd is a square, ad = bc.
- N_y(A) = #{a ∈ A : P(a) ∈ (y, 2y]}.
- A *square 4-set* is a set of 4 distinct positive integers whose product is a square.

**Theorem.** For every K > 0 there is n₀(K) with the following property. Let n ≥ n₀, let A ⊆ [1,n] be valid (not necessarily squarefree), and let y satisfy n^{1/(6L)} ≤ y and 2y ≤ (n/y)^{1−1/(24L)}. Then N_y(A) ≤ n/ℓ^K.

The proof uses only the *statements* of three results of C2:
- **Lemma A.** For valid A and primes P ≠ Q, a square 4-set of integers coprime to PQ cannot lie in both M_P and M_Q.
- **Lemma Q.** The number Q4(z) of square 4-sets in [1,z) is at most 4.39 z²ℓ⁶ whenever 1 + ln z ≤ 2ℓ.
- **Lemma R(a).** This is applied with u = 6L under its stated hypothesis ln z^{1/(6L)} ≥ max(2, 4 ln 6L). It gives Ψ(z, z^{1/(6L)})/z ≤ e^{3.1} ℓ^{13−6 ln(6L)}.

Theorem M′ is withdrawn; see CHANGES.
**Conditional on** deep/C2 (its own proof passed as validated-new).
**Beyond.** X̃ (C2) allowed C·n/ln²y in these windows. Here they are super-polylogarithmically small. Theorem M′ also removes C2's discard term 5n/ln²(2y), which was the bottleneck of the leg-1 NEXT.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 2, "cite": null, "why": "No known result restricts the largest-prime-factor distribution of valid sets; showing that windows of P(a) from n^{1/(6L)} up to just below sqrt(n) carry only n/(log n)^K elements is a genuine structural reduction, consistent with the omega<=2 constructions. It does not touch the P(a) >~ sqrt(n) regime, where the main term and the remaining CORE live.", "panel": [{"verdict": "new", "cite": null, "significance": 2, "why": "No known result restricts the largest-prime-factor distribution of valid sets; showing that windows of P(a) from n^{1/(6L)} up to just below sqrt(n) carry only n/(log n)^K elements is a genuine structural reduction, consistent with the omega<=2 constructions. It does not touch the P(a) >~ sqrt(n) regime, where t`
**Proof or evidence.**

**Setup.** Put z = n/y, W = primes in (y, 2y], ε′ = 1/(24L) and γ₀ = 1/(6L).

From 2y ≤ z^{1−ε′} we get y^{2−ε′} ≤ n^{1−ε′}. Hence y ≤ √n, so z ≥ √n and ln z ∈ [ℓ/2, ℓ]. Then y² ≤ y^{ε′} n^{1−ε′} ≤ n^{1−ε′/2}.

**(1) Fibres.** For P ∈ W let M_P = {m : mP ∈ A, P(m) < P}. Then M_P ⊆ [1, z).

Take a ∈ A with P(a) = P. Either a = Pm with m ∈ M_P, or P² | a. The number of a ≤ n with P² | a for some P > y is at most n·Σ_{k>y} k⁻² ≤ 2n/y. Therefore

  N_y(A) ≤ Σ_{P∈W} |M_P| + 2n/y.

Let s_P be the number of square 4-sets contained in M_P.

**(2) Disjointness (unchanged).** Take P ≠ Q in W, and suppose a square 4-set lies in M_P ∩ M_Q. Each of its elements m has P(m) < min(P,Q), so each is coprime to PQ. Lemma A then says this cannot happen. So every square 4-set of [1,z) lies in at most one fibre. Lemma Q applies because 1 + ln z ≤ 2ℓ, and gives

  Σ_P s_P ≤ Q4(z) ≤ 4.39 z²ℓ⁶.

**(3) Lemma F (self-contained).** Let M ⊆ [1, z) with P(m) < 2y for all m ∈ M, and let s = s(M). Then

  |M| ≤ Ψ(z, z^{γ₀}) + 2y + 4.83 z^{1−γ₀/2} + 2^{3/4}(2ℓ)^{3/4} z^{1/2} s^{1/4}.

*Proof of Lemma F.*

*Smooth part.* Elements with P(m) ≤ z^{γ₀} number at most Ψ(z, z^{γ₀}).

*Dyadic classes.* For the remaining elements, let q = P(m) ∈ (z^{γ₀}, 2y). Set Z_j = 2^j z^{γ₀} for j = 0, …, J, where J is the largest index with Z_J < 2y. The intervals (Z_j, 2Z_j] cover (z^{γ₀}, 2y). Also J + 1 ≤ log₂(2y) + 1 ≤ 2ℓ.

Fix j and write Z = Z_j. Let M_j = {m : P(m) ∈ (Z, 2Z]} and e = |M_j|. Form the bipartite graph between:
- Q = the primes in (Z, 2Z], with |Q| ≤ Z, and
- R = [1, z/Z), with |R| ≤ z/Z.

The edges are the pairs (q, r) with qr ∈ M_j and q = P(qr). Each element of M_j is exactly one edge.

*Rectangles give square 4-sets.* A rectangle is q ≠ q′ in Q and r ≠ r′ in R with all four edges present. It yields {qr, qr′, q′r, q′r′}. These four integers are distinct, since their P-values or cofactors differ, and their product (qq′rr′)² is a square. The rectangle can be read back from the 4-set: the two P-values give {q, q′}, and the cofactors give {r, r′}. Different classes give 4-sets with P-values in disjoint ranges. Hence, writing ρ_j for the number of rectangles in class j, Σ_j ρ_j ≤ s.

*Counting rectangles.* Let d_q be the degree of q, and let c(r, r′) be the codegree of the pair {r, r′}. Set T = Σ_q C(d_q, 2) = Σ_{{r,r′}} c(r, r′) and N = |R|²/2. The number of pairs {r, r′} is at most N, so Jensen gives

  ρ_j = Σ C(c, 2) ≥ T(T/N − 1)/2.

If T ≥ 2N this gives ρ_j ≥ T²/(4N). So in all cases T ≤ 2N + 2√(N ρ_j).

*Bounding e.* By Cauchy–Schwarz, 2T = Σ d_q² − e ≥ e²/|Q| − e. Hence e ≤ |Q| + √(2|Q|T). Substituting the bound on T:

  e ≤ |Q| + √(4|Q|N) + 2|Q|^{1/2} N^{1/4} ρ_j^{1/4}
   ≤ |Q| + √2·z/√Z + 2^{3/4} z^{1/2} ρ_j^{1/4}.

*Summing over classes.* Σ_j |Q_j| ≤ π(2y) ≤ 2y. Next, Σ_j √2·z·Z_j^{−1/2} ≤ √2/(1 − 2^{−1/2})·z^{1−γ₀/2} ≤ 4.83 z^{1−γ₀/2}. Finally, by Hölder, Σ_j ρ_j^{1/4} ≤ (J+1)^{3/4} s^{1/4} ≤ (2ℓ)^{3/4} s^{1/4}. This proves Lemma F. ∎

**(4) Summation.** Apply Lemma F to each M_P; this is allowed because P(m) < P ≤ 2y. Use #W ≤ y and yz = n. By Hölder and step (2),

  Σ_P s_P^{1/4} ≤ #W^{3/4}(4.39 z²ℓ⁶)^{1/4} ≤ 1.45 y^{3/4} z^{1/2} ℓ^{1.5}.

This gives

  N_y(A) ≤ n·Ψ(z, z^{γ₀})/z + 2y² + 4.83 n z^{−γ₀/2} + 4.1 n ℓ^{2.25} y^{−1/4} + 2n/y.

Now bound each term:
- **Smooth term.** ln z^{γ₀} ≥ ℓ/(12L) ≥ max(2, 4 ln 6L) for large n, so Lemma R(a) gives Ψ/z ≤ e^{3.1} ℓ^{13−6 ln 6L}.
- **2y² term.** 2y² ≤ 2n·e^{−ℓ/(48L)}, since y² ≤ n^{1−ε′/2}.
- **z^{−γ₀/2} term.** z^{−γ₀/2} ≤ e^{−ℓ/(24L)}, since ln z ≥ ℓ/2.
- **y^{−1/4} term.** y^{−1/4} ≤ e^{−ℓ/(24L)}, since y ≥ n^{1/(6L)}.
- **2n/y term.** 2n/y ≤ 2n·e^{−ℓ/(6L)}.

Since ℓ = e^L, we have e^{−ℓ/(cL)} = ℓ^{−ℓ/(cL²)}, and ℓ/(cL²) → ∞. Also 13 − 6 ln 6L → −∞. So each of the five terms is at most n ℓ^{−K}/5 for n ≥ n₀(K). Hence N_y(A) ≤ n/ℓ^K. ∎

## [conditional] deep/C8g1 PROVED QUANT
**Statement.** Notation.
- ℓ = ln n and L = ln ℓ.
- P(a) is the largest prime factor of a, with P(1) = 1. Letters p, q, P, Q denote primes.
- B_n = {m ∈ [2,n] : m squarefree, ω(m) ≤ 2} and S₂(n) = |B_n|.
- A ⊆ [1,n] is *valid* if a ≤ b ≤ c ≤ d in A (repetition allowed) with abcd a square forces ad = bc. F(n) is the maximum size of a valid set.
- A *square 4-set* is a set of 4 distinct positive integers whose product is a square. Q4(z) is the number of square 4-sets in [1,z].
- An *H-set* has no square product of 2 distinct or of 4 distinct elements. H(k) is the largest size of an H-set in [1,k], h(k) = H(k) − π(k) − 1, and c* = Σ_{k≥1} h(k)/(k(k+1)).
- Y₁ = √n(ln 2n)⁴, and λ(A) = #{a ∈ A : P(a) ≤ Y₁}.
(a) For every n ≥ 1, every real Y ≥ √n and every valid A ⊆ [1,n]:
    #{a ∈ A : P(a) > Y} ≤ #{b ∈ B_n : P(b) > Y} + Σ_{Y<P≤n} h(⌊n/P⌋) + Q4(n/Y).
(b) 0 ≤ h(k) ≤ C_E k^{3/4}, so c* < ∞. Moreover Σ_{Y₁<P≤n} h(⌊n/P⌋) ≤ (c* + o(1))n/ℓ and Q4(n/Y₁) = O(n/ℓ²).
(c) (LOW) There is an absolute C with λ(A) ≤ C·nL/ℓ² for every valid A ⊆ [1,n], n ≥ n₀.
(d) Hence every valid A ⊆ [1,n] has |A| ≤ S₂(n) + (c* + ε(n))n/ℓ, with ε(n) → 0 independent of A. So
    limsup (F(n) − S₂(n))ℓ/n ≤ c*. Together with C7 (cited): c₀ ≤ liminf ≤ limsup ≤ c*, which is claim C8.
(e) The referee's objection is false. C4's statement (Y = n) and C7's statement are mutually inconsistent.
**Conditional on** deep/C7, deep/C4 (its own proof passed as valid-restatement).
**Gap-closing version** of deep/C8.
**Beyond.** KNOWN gives only F(n) = (1+o(1))·n·lnln n/ln n (R5 plus the trivial bounds). C1 gives a second-order upper bound:
F(n) ≤ S₂(n) + (c* + o(1))n/ln n, where c* is an explicit series of exact finite extremal numbers. In particular
F(n) − S₂(n) = O(n/ln n), proved here without the broken C4/C5. That alone gives the Θ in the Lean statement, with the
lower bound from R5.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 2, "cite": null, "why": "The bound |A| ≤ S₂(n) + O(n/ln n) implies the open core F_sf(n) ≤ C·n·lnln n/ln n and so settles the problem asymptotically, with an explicit second-order bound beyond it. The difficulty is concentrated in part (c), and the team's own framing is inconsistent: it calls the first-order asymptotic known while its frontier map lists it as open.", "panel": [{"verdict": "new", "cite": null, "significance": 2, "why": "No known result gives F(n) = S2(n) + Theta(n/ln n) or an explicit constant c* from finite extremal numbers h(k), so this second-order refinement appears new. If the first-order upper bound is in fact open, as CORE states, then part (c) carries the whole problem and needs the strictest scrutiny."}, {"verdict": "resta`
**Proof or evidence.**

Step 0 (fibres). Let A be valid, P prime and M_P = {m : mP ∈ A}.
 - If m₁ ≤ … ≤ m₄ lie in M_P with Πm_i a square, then m₁P ≤ … ≤ m₄P lie in A with square product P⁴Πm_i. So m₁m₄ = m₂m₃,
   and M_P is valid. Every subset of a valid set is valid.
 - (R1) In a valid set, m < m′ with mm′ a square is impossible: (m,m,m,m′) has square product m²mm′, so mm′ = m², i.e. m′ = m.
Step 1 (Lemma A). Let A be valid, P ≠ Q primes, and m₁,…,m₄ distinct, coprime to PQ, with m_iP, m_iQ ∈ A. Then Πm_i is not a
square.
 Proof. Suppose it is. For a perfect matching μ of {1,2,3,4} let E(μ) mean that the two pair-products of the m's are equal.
 - Any two E's force a coincidence. E(12|34) & E(13|24) give m₂² = m₃². E(12|34) & E(14|23) give m₂ = m₄. E(13|24) & E(14|23)
   give m₃ = m₄. So at most one E holds.
 - For a split {i,j}|{k,l}: m_iP, m_jP, m_kQ, m_lQ ∈ A are distinct, since Q | m_kQ and Q ∤ m_iP. Their product P²Q²Πm is a square.
 - Validity applied to their sorted order gives an equal pairing. The pairing m_im_jP² = m_km_lQ² is impossible, since v_P
   differs (2 vs 0). So E(ik|jl) ∨ E(il|jk).
 - Over the three splits this forces at least two E's, a contradiction. ∎
Step 2 (Lemma Q). Q4(z) ≤ (ζ(2)/24)z²(1 + ln z)⁶ ≤ 0.07z²(1 + ln z)⁶ for z ≥ 1.
 - Write m_i = s_ir_i² with s_i squarefree. Πm_i is a square iff each prime divides 0, 2 or 4 of the s_i.
 - Let g be the product of the primes dividing all four s_i, and x_{ij} the product of the primes dividing exactly s_i and s_j.
   Then s_i = gΠ_{j≠i}x_{ij}, and (s_i) ↦ (g, x_{ij}) is injective. Each of g, x_{ij} is ≤ z.
 - There are ≤ √(z/s_i) choices of r_i. So the number of ordered tuples is
   ≤ z²Σ g^{−2}Π_{i<j}x_{ij}^{−1} ≤ z²ζ(2)(Σ_{m≤z}1/m)⁶ ≤ z²ζ(2)(1 + ln z)⁶.
 - Each square 4-set appears as 24 ordered tuples. ∎
Step 3 (proof of (a)). Let Y ≥ √n and a ∈ A with P = P(a) > Y.
 - P² > n ≥ a, so a = mP with P ∤ m and m ≤ n/P < √n < P. Hence a ↦ (P, m) is a bijection onto {(P,m) : Y < P ≤ n, m ∈ M_P}.
   Every m in these fibres is < √n, so m is coprime to every prime > Y.
 - Let s_P be the number of square 4-sets inside M_P. By Lemma A, each square 4-set of [1, n/Y] lies in at most one M_P (P > Y).
   So Σ_{P>Y}s_P ≤ Q4(n/Y).
 - Deleting one element of each square 4-set of M_P leaves M′_P, with |M′_P| ≥ |M_P| − s_P. M′_P has no square 4-set, and no
   square 2-product by (R1) for the valid set M′_P. So M′_P is an H-set in [1, ⌊n/P⌋], and
   |M_P| ≤ π(⌊n/P⌋) + 1 + h(⌊n/P⌋) + s_P.
 - The b ∈ B_n with P(b) = P > Y ≥ √n are P and the pP with p ≤ n/P (here p < P automatically). Hence
   #{b ∈ B_n : P(b) > Y} = Σ_{Y<P≤n}(π(⌊n/P⌋) + 1).
 - Summing over P gives (a). ∎
Step 4 (proof of (b)).
 - h ≥ 0: {1} ∪ primes ≤ k is an H-set.
 - An H-set satisfies: ab = cd with a ≤ b, c ≤ d implies (a,b) = (c,d).
   - If a,b,c,d are distinct, then abcd = (ab)² would be a square 4-product.
   - If a = b, then cd = a² forces c = d = a.
   - If a = c, then b = d.
   So an H-set is multiplicatively Sidon in the strongest sense, and Erdős (KNOWN: G(k) = π(k) + O(k^{3/4})) gives
   h(k) ≤ C_E k^{3/4}. Hence c* ≤ C_E Σ k^{−5/4} < ∞.
 - Fix K ∈ ℕ and take n with n/(K+1) > Y₁.
   - Main part. ⌊n/P⌋ = k iff n/(k+1) < P ≤ n/k. By the PNT for fixed k, π(n/k) − π(n/(k+1)) = (1 + o(1))n/(k(k+1)ℓ).
     So Σ_{n/(K+1)<P≤n} h(⌊n/P⌋) ≤ (c* + o(1))n/ℓ.
   - Tail (Y₁ < P ≤ x := n/(K+1)). Partial summation with π(t) ≤ 1.26t/ln t (Rosser–Schoenfeld) gives
     Σ_{p≤x}p^{−3/4} ≤ 1.26x^{1/4}/ln x + 0.945∫₂^x t^{−3/4}/ln t dt.
     Splitting the integral at √x, this is ≤ 8.82x^{1/4}/ln x + 5.46x^{1/8} ≤ 9x^{1/4}/ln x for x large. So the tail is
     ≤ 9C_E n^{3/4}x^{1/4}/ln x ≤ 10C_E n/(K^{1/4}ℓ) for n ≥ n₀(K).
   - Let K → ∞.
 - By Lemma Q with z = n/Y₁ = √n/(ln 2n)⁴: Q4 ≤ 0.07n(1 + ℓ)⁶/(ln 2n)⁸ = O(n/ℓ²). ∎
Step 5 (Lemma R, Rankin). Let X ≥ Y ≥ 2 and u = ln X/ln Y with ln Y ≥ max(2, 4 ln u). Then
Ψ(X,Y) ≤ e^{3.1}X(ln Y)e^{2u}u^{−u}.
 - For σ ∈ [3/4, 1]: Ψ ≤ Σ_{P(m)≤Y}(X/m)^σ = X^σΠ_{p≤Y}(1 − p^{−σ})^{−1}.
 - The log of the product is ≤ Σ_{p≤Y}p^{−σ} + Σ_p p^{−3/2}/(1 − 2^{−3/4}) ≤ Σ_{p≤Y}p^{−σ} + 2.1, using Σ_p p^{−3/2} < 0.85.
 - Take σ = 1 − ln u/ln Y; σ ≥ 3/4 by hypothesis. Then X^σ = Xu^{−u}.
 - p^{−σ} = p^{−1}e^{(ln u)t} with t = ln p/ln Y ∈ (0,1]. Convexity gives e^{(ln u)t} ≤ 1 + ut.
 - By Mertens, Σ_{p≤Y}1/p ≤ lnln Y + 1 and Σ_{p≤Y}ln p/p ≤ ln Y + 2. So Σ_{p≤Y}p^{−σ} ≤ lnln Y + 1 + u(1 + 2/ln Y) ≤ lnln Y + 1 + 2u. ∎
Step 6 (Lemma F). Let z ≥ 2, 0 < γ₀ < 1 and w ≥ 2. Let M ⊆ [1,z] with P(m) < w for all m ∈ M, and let s = s(M) be the number
of square 4-sets in M. Suppose log₂z + 1 ≤ 2ℓ. Then
  |M| ≤ Ψ(z, z^{γ₀}) + π(min(w,z)) + 4.83z^{1−γ₀/2} + 2^{3/4}(2ℓ)^{3/4}z^{1/2}s^{1/4}.
 Proof.
 - At most Ψ(z, z^{γ₀}) elements have P(m) ≤ z^{γ₀}. The others have q = P(m) ∈ (z^{γ₀}, min(w,z)].
 - Let Z_j = 2^jz^{γ₀} for j = 0..J, with Z_J < min(w,z). Then J + 1 ≤ log₂z + 1 ≤ 2ℓ.
 - Class j is M_j = {m : P(m) ∈ (Z_j, 2Z_j]}. Write Z = Z_j. Its bipartite graph has sides Q_j = the primes in (Z, 2Z] with
   Q_j ≤ min(w,z), so |Q_j| ≤ Z, and R = [1, z/Z), with an edge (q, r) for each m = qr ∈ M_j with q = P(m). Edges correspond
   bijectively to the elements of M_j; e = |M_j|.
 - A rectangle {q,q′}×{r,r′} gives 4 distinct elements of M with product (qq′rr′)². The 4-set determines the rectangle: its
   P-values give {q,q′} and its cofactors give {r,r′}. Different classes have disjoint P-value ranges. So Σ_jρ_j ≤ s, where
   ρ_j is the number of rectangles in class j.
 - Let T = Σ_qC(d_q,2) = Σ_{{r,r′}}codeg, and N = |R|²/2 (at least the number of pairs).
   - Jensen gives ρ_j ≥ T(T/N − 1)/2. So T ≤ 2N + 2√(Nρ_j).
   - Cauchy–Schwarz gives 2T ≥ e²/|Q_j| − e, so e ≤ |Q_j| + √(2|Q_j|T).
   - Hence e ≤ |Q_j| + √2z/√Z + 2^{3/4}z^{1/2}ρ_j^{1/4}, using |Q_j| ≤ Z and N ≤ z²/(2Z²).
 - Sum over j:
   - Σ|Q_j| ≤ π(min(w,z)), since the Q_j are disjoint sets of primes ≤ min(w,z).
   - Σ_j√2zZ_j^{−1/2} ≤ (√2/(1 − 2^{−1/2}))z^{1−γ₀/2} ≤ 4.83z^{1−γ₀/2}.
   - Hölder gives Σρ_j^{1/4} ≤ (2ℓ)^{3/4}s^{1/4}. ∎
Step 7 (proof of (c), LOW). Let n be large, γ₀ = 1/(6L), k₁ = ⌈log₂n^{1/(6L)}⌉ and k₂ = ⌊log₂Y₁⌋. For k₁ ≤ k ≤ k₂ let
y = 2^k, W = primes in (y, 2y], z = n/y and N_y = #{a ∈ A : P(a) ∈ W}. Then
λ(A) ≤ Ψ(n, 2^{k₁}) + Σ_{k=k₁}^{k₂}N_y.
 - Smooth part. 2^{k₁} ≤ 2n^{1/(6L)} ≤ n^{1/(5L)}. Lemma R with u = 5L applies, since ℓ/(5L) ≥ max(2, 4 ln 5L). It gives
   Ψ ≤ e^{3.1}nℓ^{11−5 ln 5L} ≤ n/ℓ².
 - Fibres in a window. Put M_P = {m : mP ∈ A, P(m) < P} for P ∈ W.
   - If a has P(a) = P ∈ W, then either a = mP with m ∈ M_P, m ≤ n/P < z, or P² | a. At most Σ_{t>y}n/t² ≤ 2n/y integers ≤ n are
     divisible by P² for some P > y. So N_y ≤ Σ_{P∈W}|M_P| + 2n/y.
   - If m ∈ M_P ∩ M_Q with P ≠ Q in W, then P(m) < min(P,Q), so m is coprime to PQ. By Lemma A, Σ_{P∈W}s(M_P) ≤ Q4(z).
     By Lemma Q this is ≤ 0.07z²(2ℓ)⁶ ≤ 4.48z²ℓ⁶, since z ≤ n.
   - Lemma F applies to each M_P with w = 2y. Sum it using #W ≤ π(2y) ≤ y, Hölder Σs_P^{1/4} ≤ #W^{3/4}Q4(z)^{1/4}, and yz = n:
     N_y ≤ n·Ψ(z, z^{γ₀})/z + π(2y)·π(min(2y,z)) + 4.83nz^{−γ₀/2} + 4.2nℓ^{2.25}y^{−1/4} + 2n/y.
 - Bounds, with z ≥ n/Y₁ ≥ n^{1/3} and y ≥ n^{1/(6L)}:
   (i) Ψ(z, z^{γ₀})/z. Lemma R with u = 6L applies, since γ₀ ln z ≥ ℓ/(18L) ≥ max(2, 4 ln 6L). It gives ≤ e^{3.1}ℓ^{13−6 ln 6L} ≤ ℓ^{−4}.
       Over ≤ 2ℓ windows the total is ≤ 2n/ℓ³.
   (ii) 4.83nz^{−γ₀/2} ≤ 4.83n·e^{−ℓ/(36L)}. Over ≤ 2ℓ windows this is o(n/ℓ²).
   (iii) Σ_k4.2nℓ^{2.25}y^{−1/4} ≤ 26nℓ^{2.25}e^{−ℓ/(24L)} = o(n/ℓ²), and Σ_k2n/y ≤ 4n·e^{−ℓ/(6L)}.
   (iv) The class term π(2y)·π(min(2y,z)), using π(t) ≤ 1.26t/ln t:
       - y ≤ n^{1/4}: ≤ 4y² ≤ 4√n.
       - n^{1/4} < y ≤ √n: ≤ (2.52y/ln 2y)² ≤ 102y²/ℓ². Summed over dyadic y ≤ √n this is ≤ 136n/ℓ².
       - √n < y ≤ Y₁: ≤ (2.52y/ln 2y)(1.26z/ln z) ≤ 3.18n/((ℓ/2)(ℓ/3)) = 19.1n/ℓ², since ln z ≥ ℓ/2 − 4 lnln 2n ≥ ℓ/3. There
         are ≤ 4log₂ln(2n) + 1 ≤ 6L + 2 such windows.
       - So the class terms total ≤ 8ℓ√n + 136n/ℓ² + 19.1(6L + 2)n/ℓ².
 - Altogether λ(A) ≤ 120·nL/ℓ² + 300n/ℓ² ≤ C·nL/ℓ² for n ≥ n₀. The bound is uniform in A. ∎
Step 8 (proof of (d)). |A| = λ(A) + #{a : P(a) > Y₁}. Apply (a) with Y = Y₁ ≥ √n, then (b) and (c), and use
#{b ∈ B_n : P(b) > Y₁} ≤ S₂(n). All error terms depend only on n. The lower bound is C7. ∎
Step 9 (proof of (e)).
 - Lemma A excludes a square 4-set from two fibres whenever its elements are coprime to PQ. This holds in the top range
   (m < √n < P, Q) and in windows (by the definition P(m) < P).
 - {P,2P,3P,6P,Q,2Q,3Q,6Q} is invalid for all P ≠ Q: {P, 6P, 2Q, 3Q} has product 36P²Q² and pair products 6P²|6Q², 2PQ|18PQ,
   3PQ|12PQ, so no equal pairing. Validity (R2) is order-free, so the referee's condition "P′/P ≥ m₂/m₁" is irrelevant.
 - C4 at Y = n gives F(n) ≤ S₂(n) + o(n/ℓ), while C7 gives F(n) ≥ S₂(n) + 0.0424n/ℓ. ∎

## [conditional] deep/C4g1 PROVED QUANT
**Statement.** Notation:
- ℓ = ln n and L = ln ℓ. Letters p, q, P, Q denote primes, and P(a) is the largest prime factor of a, with P(1) = 1.
- B_n = {m ∈ [2,n] : m squarefree, ω(m) ≤ 2} and S₂(n) = |B_n|.
- Valid means: a ≤ b ≤ c ≤ d in A (repeats allowed) with abcd a square forces ad = bc. F(n) is the maximum size of a valid A ⊆ [1,n].
- G(x) is the largest size of a multiplicatively Sidon set M ⊆ [1,x], where ab = cd with a,b,c,d ∈ M forces {a,b} = {c,d} as multisets. Put g(x) = G(x) − π(x) − 1 ≥ 0.
- Y₁ = √n(ln 2n)⁴.

(a) There is an absolute C₀ such that every valid A ⊆ [1,n] has |A| ≤ S₂(n) + C₀n/ℓ. Hence F(n) = n(L + O(1))/ℓ.
(b) There are an absolute C₁ and ε(n) → 0 with the following property. For all n ≥ 2, every valid A ⊆ [1,n] and every real Y with Y₁ ≤ Y ≤ n^{2/3}:
  |A| ≤ S₂(n) + Σ_{Y<P≤n} g(n/P) + (ε(n) + C₁·ln(2Y/Y₁)/ℓ)·n/ℓ.
  In particular, the o(n/ℓ)-form holds for every Y = Y(n) ≥ Y₁ with ln(Y/Y₁) = o(ℓ).
(c) (refutation of the unrestricted form) For every n ≥ 2, F(n) ≥ S₂(n) + π(n/35) − π(√n) − 6. Consequently, for every Y = Y(n) ∈ [n/7, n], the inequality F(n) ≤ S₂(n) + Σ_{Y<P≤n} g(n/P) + o(n/ℓ) is FALSE for all large n.
**Conditional on** deep/C5, deep/C2 (its own proof passed as valid-restatement).
**Gap-closing version** of deep/C4.
**Beyond.** KNOWN gives only S₂(n) ≤ F(n) ≤ (6/π²+o(1))n. Part (a) pins F(n) to within O(n/ℓ), the size of the prime term. Part (c) shows that the excess over S₂ is genuinely Θ(n/ℓ), since liminf (F−S₂)ℓ/n ≥ 1/35. It also shows that the localisation in (b) cannot be pushed to Y ≥ n/7.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "restatement", "significance": 3, "cite": null, "why": "Part (a), |A| ≤ S₂(n)+O(n/log n), is the frontier's CORE upper bound (and sharper), so with the known lower bound it would determine F(n) = n(loglog n + O(1))/log n and solve the problem; I know of no prior source (ESS 1995 should be rechecked), and the proof needs maximal scrutiny on layer-uniformity. Parts (b)–(c) are refinements, with (c) a routine construction.", "panel": [{"verdict": "restatement", "cite": null, "significance": 3, "why": "Part (a), |A| ≤ S₂(n)+O(n/log n), is the frontier's CORE upper bound (and sharper), so with the known lower bound it would determine F(n) = n(loglog n + O(1))/log n and solve the problem; I know of no prior source (ESS 1995 should be rechecked), and the proof needs maximal scrutiny o`
**Proof or evidence.**

Cited and classical inputs:
- C5 with K = 3.
- C2 (crude bound and Theorem M).
- Lemma A, Lemma Q (cited statements).
- R1 and R5 (KNOWN).
- (E) Erdős: G(x) ≤ π(x) + C_E x^{3/4} for x ≥ 1 (KNOWN multiplicative-Sidon bound).
- (RS) Rosser–Schoenfeld:
  - x/ln x < π(x) for x ≥ 17;
  - π(x) < (x/ln x)(1 + 3/(2ln x)) for x > 1;
  - π(x) < 1.26x/ln x.
- (Me) Mertens: lnln x ≤ Σ_{p≤x} 1/p ≤ lnln x + 1 for x ≥ 3, and |Σ_{p≤x} ln p/p − ln x| ≤ 2 for x ≥ 2.

Lemma R (Rankin). Let X ≥ Y ≥ 2, u = ln X/ln Y and ln Y ≥ max(2, 4 ln u). Then Ψ(X,Y) := #{1 ≤ m ≤ X : P(m) ≤ Y} ≤ e^{3.1}X(ln Y)e^{2u}u^{−u}.
Proof.
- For σ = 1 − ln u/ln Y ∈ [3/4, 1]: Ψ ≤ Σ_{P(m)≤Y}(X/m)^σ = X^σ Π_{p≤Y}(1−p^{−σ})^{−1}, and X^σ = X u^{−u}.
- The logarithm of the product is at most Σ_{p≤Y} p^{−σ} + Σ_p Σ_{k≥2} p^{−3k/4}, and the second sum is ≤ 2.0989.
- Write p^{−σ} = p^{−1}e^{t ln u} with t = ln p/ln Y ∈ (0,1]. Convexity gives e^{t ln u} ≤ 1 + ut.
- So Σ p^{−σ} ≤ lnln Y + 1 + (u/ln Y)(ln Y + 2) ≤ lnln Y + 1 + 2u.
- Exponentiate: e^{lnln Y} = ln Y and e^{1 + 2.0989} ≤ e^{3.1}. ∎

Lemma T. Let A be valid, Y ≥ √n, z = n/Y and T = {a ∈ A : P(a) > Y}. Then |T| ≤ Σ_{Y<P≤n} G(n/P) + Q4(z), where Q4(z) is the number of square 4-sets (4 distinct integers with square product) in [1,z).
Proof.
- Put M_P = {m : mP ∈ A}. If a ∈ T with P(a) = P, then a = mP with m ≤ n/P < z ≤ √n ≤ Y < P. Hence T = ⊔_{P>Y} P·M_P, M_P ⊆ [1,z), and every element of every such M_P is < Y, hence coprime to every prime > Y.
- Lemma A then gives that a square 4-set of [1,z) lies in at most one M_P. So Σ_P s(M_P) ≤ Q4(z), where s(M) is the number of square 4-sets in M.
- M_P is valid: if m₁ ≤ … ≤ m₄ lie in M_P with square product, then the m_iP have square product P⁴Πm_i, so m₁m₄ = m₂m₃.
- Delete one element of each square 4-set of M_P, leaving M′_P. Suppose ab = cd in M′_P with {a,b} ≠ {c,d}.
  - Then a ∉ {c,d}, since a = c gives b = d.
  - If a,b,c,d are distinct, then abcd = (ab)² is a square 4-set of M′_P, which is impossible.
  - Otherwise, up to symmetry, a = b and c ≠ d, so cd = a² with c, d distinct. This contradicts R1 for M_P.
- So M′_P is multiplicatively Sidon, and |M_P| ≤ G(n/P) + s(M_P). Sum over P. ∎

Lemma U. Σ_{P≤n} P^{−3/4} ≤ C_U n^{1/4}/ℓ.
Proof. By partial summation and (RS),
Σ_{P≤n} P^{−3/4} = π(n)n^{−3/4} + (3/4)∫₂ⁿ π(t)t^{−7/4}dt ≤ 1.26n^{1/4}/ℓ + 0.95[∫₂^{√n} t^{−3/4}/ln 2 dt + (2/ℓ)∫_{√n}^n t^{−3/4}dt] ≤ 1.26n^{1/4}/ℓ + 5.5n^{1/8} + 7.6n^{1/4}/ℓ. ∎

Proof of (b). Fix n ≥ n₀ (n₀ absolute; for n < n₀, (b) holds by taking ε(n) large). Fix a valid A and Y ∈ [Y₁, n^{2/3}]. Put Y_s = n^{1/(5L)} and ε′ = 1/(24L). Every a ∈ A lies in (i), (ii) or (iii) below; overlaps only over-count.

(i) P(a) ≤ Y_s, which includes a = 1. Apply Lemma R with X = n, Y = Y_s, u = 5L.
- Its hypothesis ln Y_s = ℓ/(5L) ≥ max(2, 4 ln 5L) holds for large n.
- Since e^{2u} = ℓ^{10} and u^{−u} = ℓ^{−5ln(5L)}, the count is ≤ e^{3.1}nℓ^{11−5ln(5L)} = o(n/ℓ).

(ii) Windows (y,2y] with y = 2^k and k₀ := ⌊log₂ Y_s⌋ ≤ k ≤ k₁ := ⌊log₂ Y⌋. These cover (Y_s, Y], and each y ≥ Y_s/2 ≥ n^{1/(6L)}.
- (ii-a) Windows with y ≤ Y₁ and 2y ≤ (n/y)^{1−ε′}. C5 (K = 3) gives N_y ≤ n/ℓ³. There are ≤ log₂n + 1 ≤ 2ℓ windows, so the total is ≤ 2n/ℓ².
- (ii-b) Windows with y ≤ Y₁ and 2y > (n/y)^{1−ε′}.
  - Then (2−ε′)ln y > (1−ε′)ℓ − ln 2, so ln y ≥ ℓ/2 − ε′ℓ/2 − 1 ≥ ℓ/3.
  - Also ln z = ln(n/y) ≥ ℓ/2 − 4 ln ln 2n ≥ ℓ/3.
  - Theorem M (C2; its range n^{1/(6L)} ≤ y ≤ Y₁ holds) gives N_y ≤ 9·3.18(1+o(1))n/ℓ² + 45n/ℓ² + o(n/ℓ²) ≤ 75n/ℓ².
  - The number of such k is ≤ (ℓ/(48L) + 1 + 4 ln ln 2n)/ln 2 + 2. So the total is ≤ 75n/ℓ²·(ℓ/(33L) + 6L + 10) = o(n/ℓ).
- (ii-c) Windows with y > Y₁ (so y ≤ Y ≤ n^{2/3}).
  - Here ln 2y ≥ ℓ/2 and ln(2n/y) ≥ ℓ/3.
  - The C2 crude bound gives N_y ≤ Cn/(ln 2y·min(ln 2y, ln(2n/y))) ≤ 6Cn/ℓ².
  - The number of such k is ≤ log₂(2Y/Y₁), so the total is ≤ 9C·ln(2Y/Y₁)·n/ℓ².

(iii) P(a) > Y. Lemma T applies, since Y ≥ Y₁ ≥ √n. It gives |T| ≤ Σ_{Y<P≤n}(π(n/P) + 1) + Σ_{Y<P≤n} g(n/P) + Q4(z), with z = n/Y.
- Since n/P < √n < P, the map (p,P) ↦ pP (p ≤ n/P), together with P ↦ P, is injective into B_n. Hence Σ_{Y<P≤n}(π(n/P)+1) ≤ S₂(n).
- z ≤ √n/(ln 2n)⁴, so 1 + ln z ≤ 2ℓ, and Lemma Q gives Q4(z) ≤ 4.39z²ℓ⁶ ≤ 4.39n/ℓ².

Summing (i)–(iii) gives (b), with ε(n) collecting the o(1) terms. These depend only on n, through C5's n₀(3), Theorem M's o(·) and Lemma R. They do not depend on A or Y. Put C₁ = 9C, with C the constant of the C2 crude bound. ∎

Proof of (a).
- Take Y = Y₁ in (b). By (E), 0 ≤ g(x) ≤ C_E x^{3/4} for x ≥ 1, and n/P ≥ 1 for P ≤ n.
- By Lemma U, Σ_{P≤n} g(n/P) ≤ C_E n^{3/4}C_U n^{1/4}/ℓ = O(n/ℓ).
- The other error is (ε(n) + C₁ ln 2/ℓ)n/ℓ.
- For F(n) = n(L+O(1))/ℓ, it remains to show S₂(n) = n(L+O(1))/ℓ.
  - Upper: S₂(n) ≤ π(n) + Σ_{p≤√n} π(n/p). By (RS), π(n/p) ≤ (1+3/ℓ)(n/p)/ln(n/p), and 1/ln(n/p) ≤ (1 + 2ln p/ℓ)/ℓ for p ≤ √n. With (Me) this gives ≤ (n/ℓ)(1+3/ℓ)(L + 1 + 2(ℓ/2+2)/ℓ) + 1.26n/ℓ = n(L+O(1))/ℓ.
  - Lower: S₂(n) ≥ Σ_{17≤p≤n^{1/3}}(π(n/p) − π(p)) ≥ (n/ℓ)(Σ_{p≤n^{1/3}} 1/p − Σ_{p<17}1/p) − n^{2/3} ≥ (n/ℓ)(L − ln 3 − 1.6) − n^{2/3}.
  - Combine with R5. ∎

Proof of (c). Let I = {P prime : √n < P ≤ n/35}, R = {2,3,5,7,10,14}, N = {6P, 35P : P ∈ I} and A* = (B_n \ (I ∪ R)) ∪ N.
- Size: A* ⊆ [2,n], and N ∩ B_n = ∅ since ω = 3. Hence |A*| ≥ S₂(n) − |I| − 6 + 2|I|.
- Validity, step 1 (repeats are harmless). All elements of A* are squarefree and distinct. A 4-multiset with a repeated element and square product is {x,x,y,y}, because xy square forces x = y for distinct squarefree numbers. The pairing (x,y),(x,y) then has equal products, so ad = bc by R2 (the ordering argument of KNOWN).
- So take 4 distinct elements with square product. If none lies in N, they lie in B_n and are fine by R5.
- Step 2 (the prime P). Otherwise one of them is Pm₁ with P ∈ I and m₁ ∈ {6,35}.
  - The elements of A* divisible by P are exactly P·M_P with M_P = {primes p ≤ n/P} ∪ {6,35}.
    - From B_n, these are pP with p ≤ n/P < √n < P; P itself was removed.
    - From N, 6Q or 35Q is divisible by P only if Q = P, since Q > √n > 7.
  - Elements of M_P are < √n < Q for every Q ∈ I.
  - P divides an even number of the 4 elements.
  - Four is impossible: M_P has no square 4-set. A prime p > 7 lies only in the element p itself. Each of 2 and 3 lies only in {2 or 3, 6}, and each of 5 and 7 only in {5 or 7, 35}. A parity check leaves no 4-subset (checked by computer).
  - So exactly two of the elements are Pm₁, Pm₂ (m₁ ≠ m₂ ∈ M_P), and c, d are coprime to P with m₁m₂cd a square.
  - The pairing (Pm₁)(Pm₂) = cd is impossible, so we need m₁c = m₂d or m₁d = m₂c.
- Case c ∈ N or d ∈ N, say c = Qm₃ with Q ∈ I, Q ≠ P, m₃ ∈ {6,35}.
  - Q ∤ Pm_i, since m_i < Q. So Q | d, i.e. d = Qm₄ with m₄ ∈ M_Q \ {m₃}, and m₁m₂m₃m₄ is a square.
  - The map {m,m′} ↦ core(mm′), for m ∈ {6,35} and m′ ∈ (primes ∪ {6,35}) \ {m}, is injective. The values are:
    - 6,2 → 3; 6,3 → 2; 35,5 → 7; 35,7 → 5;
    - 6,35 → 210; 6,p → 6p (p ∉ {2,3}); 35,p → 35p (p ∉ {5,7}).
    - A collision would need 6p ≡ 35q (mod squares), which is impossible. Checked by computer for p < 60.
  - Hence {m₁,m₂} = {m₃,m₄}. If m₃ = m₁, then m₁·m₄ = m₂·m₃ gives (Pm₁)(Qm₂) = (Pm₂)(Qm₁). If m₃ = m₂, the other pairing works.
- Case c, d ∈ B_n \ (I ∪ R). Write c = gu and d = gv with g = gcd(c,d). Then uv = k := core(m₁m₂). A pairing works iff {u,v} = {m₁/h, m₂/h} with h = gcd(m₁,m₂). Run through the possibilities:
  - k ∈ {2,3,5,7}: the only split is {1,k}, which is the good one.
  - k = 6p (m₁ = 6, m₂ = p ∉ {2,3}), with ω(gu), ω(gv) ≤ 2. This forces g = 1 and {c,d} ∈ {{6,p}, {2,3p}, {3,2p}}. Only {6,p} is good, and the others contain 2 or 3 ∈ R.
  - k = 35p is the same, with 5, 7 ∈ R.
  - k = 210 (m₁,m₂ = 6,35). This forces g = 1 and {c,d} ∈ {{6,35}, {10,21}, {14,15}}. The bad ones contain 10 or 14 ∈ R.
  - So c, d ∉ R leaves only good splits, and A* is valid. ∎
- Consequence.
  - F(n) − S₂(n) ≥ π(n/35) − π(√n) − 6 = (1/35 + o(1))n/ℓ.
  - For Y ≥ n/7 and P > Y, ⌊n/P⌋ ≤ 6. The exact MaxSAT values are g(1..5) = 0 and g(6) = 1, with g(x) = g(⌊x⌋).
  - So Σ_{Y<P≤n} g(n/P) ≤ π(n/6) − π(n/7) = (1/42 + o(1))n/ℓ < (1/35)n/ℓ.
  - Hence the refined inequality with o(n/ℓ) fails for all large n. For Y = n the sum is empty, and the false assertion is F(n) ≤ S₂(n) + o(n/ℓ). ∎

## [broken] deep/C4 PROVED QUANT
**Statement.** Every valid A ⊆ [1,n] satisfies |A| ≤ S₂(n) + O(n/ln n). Hence S₂(n) ≤ F(n) ≤ S₂(n) + O(n/ln n), i.e. F(n) = n(lnln n + O(1))/ln n. More precisely, with g(x) := G(x) − π(x) − 1 ≥ 0 (G = strong-Sidon maximum, see C2 (E)) and any Y ≥ √n(ln 2n)^4: F(n) ≤ S₂(n) + Σ_{Y<P≤n} g(n/P) + o(n/ℓ).
**Beyond.** C1 had relative error O(1/ln L), i.e. F(n) ≤ S₂(n) + O(nL/(ℓ ln L)). This determines F(n) to within O(n/ℓ), which is the size of the prime term, and places the whole excess over S₂ in the top fibres (P > √n·polylog).
**Referee.** `{"valid": false, "first_error": "Statement of the refined bound: it is claimed for any Y ≥ √n(ln 2n)^4, but the proof only treats Y = 2^{K_b+1} ∈ (Y₁, 2Y₁] (extendable by g ≥ 0 only to Y ≤ 2^{K_b+1}). For larger Y (e.g. Y = n, which would give F(n) ≤ S₂(n) + o(n/ℓ)), the windows Y₁ < y < Y are not covered by Theorem M/M′, and the C2 crude bound sums to order nL/ℓ. The headline bound S₂(n) + O(n/ℓ) is fine modulo the cited lemmas.", "fixable": true}`
**Adversary.** `{"broken": true, "how": "The refined statement is claimed for ANY Y ≥ √n(ln 2n)^4, but the proof only handles Y0 = 2^{K_b+1} ∈ [Y1, 2Y1]. Since Σ_{Y<P≤n} g(n/P) decreases in Y, this implies the bound only for Y ≤ Y0. For larger Y (e.g. Y = n/m with g(m) ≥ 1, or Y = n, which would assert F(n) ≤ S2(n)+o(n/ℓ)), the dropped terms Σ_{Y0<P≤Y} g(n/P) can be Θ(n/ℓ), since there are ≍ n/(m^2 ℓ) primes with n/P ≈ m. These are not shown to be o(n/ℓ). The headline F(n) ≤ S2(n)+O(n/ℓ) and the bound with Y = Y1 are correctly derived from the cited lemmas; restricting the statement to Y1 ≤ Y ≤ Y0 fixes it.", "severity": "fixable"}`
**Proof or evidence.**

Fix n large and A valid. Put Y₁ = √n(ln 2n)^4, ε' = 1/(24L), and y₂ := the largest y with 2y ≤ (n/y)^{1−ε'}; then ln y₂ ≥ ℓ/2 − ε'ℓ/2 − 1.
Partition A by P(a):
(i) P(a) ≤ n^{1/(5L)}: by Lemma R(a) (u = 5L; ln Y = ℓ/(5L) ≥ max(2, 4ln 5L) for large n) this has ≤ e^{3.1}·n·ℓ^{11−5ln(5L)} = o(n/ℓ) elements. This part includes a = 1.
(ii) Dyadic windows (y,2y], y = 2^k, k from ⌊log₂ n^{1/(5L)}⌋ to K_b := ⌊log₂ Y₁⌋. Each has y ≥ n^{1/(5L)}/2 ≥ n^{1/(6L)}.
  - Windows with y ≤ y₂: C5 gives N_y ≤ n/ℓ³ each. There are ≤ ℓ such windows, so the total is ≤ n/ℓ².
  - Windows with y₂/2 < y ≤ Y₁: here ln 2y ≥ ℓ/3 and ln z ≥ ℓ/2 − 4·lnln(2n) − 1 ≥ ℓ/3, with z = n/y. Theorem M′ (C5 proof) gives N_y ≤ 3.18(1+o(1))n/(ln 2y·ln z) + o(n/ℓ²) ≤ 30n/ℓ². The number of these windows is ≤ log₂(Y₁/y₂) + 2 ≤ (ℓ/(48L) + 4·lnln(2n) + 2)/ln 2 + 2, where Y₁ = √n·(ln 2n)^4 gives ln Y₁ = ℓ/2 + 4·lnln 2n. So the total is O(n/(Lℓ)) + O(nL/ℓ²) = o(n/ℓ).
(iii) P(a) > Y := 2^{K_b+1} ≥ Y₁ ≥ √n. By Lemma T (C2), |T| ≤ Σ_{Y<P≤n} G(n/P) + Q4(n/Y) ≤ Σ_{Y<P≤n}(π(n/P)+1) + Σ_{Y<P≤n} g(n/P) + O(n/ℓ²).
  - For P > Y ≥ √n we have n/P < √n < P. So the pairs (p,P) with p ≤ n/P give distinct squarefree semiprimes pP ≤ n, and the P themselves are primes ≤ n. Hence Σ(π(n/P)+1) ≤ S₂(n).
  - By (E), g(x) ≤ C_E x^{3/4}. With Σ_{P≤n} P^{−3/4} = O(n^{1/4}/ℓ) (partial summation and (Ch)), Σ g(n/P) ≤ C_E n^{3/4}·O(n^{1/4}/ℓ) = O(n/ℓ).
Every a lies in (i), (ii) or (iii). Summing gives |A| ≤ S₂(n) + Σ_{P>Y} g(n/P) + o(n/ℓ) ≤ S₂(n) + O(n/ℓ). The lower bound is R5. ∎

## [broken] deep/C5 PROVED STRUCTURE
**Statement.** For every K > 0 there is n₀(K) such that for n ≥ n₀, every valid A ⊆ [1,n] (not necessarily squarefree) and every y with n^{1/(6L)} ≤ y and 2y ≤ (n/y)^{1−1/(24L)}, we have N_y(A) ≤ n/ℓ^K.
Moreover (Theorem M′, which is Theorem M of C2 without the discard term): for n^{1/(6L)} ≤ y ≤ Y₁,
N_y(A) ≤ 3.18(1+o(1))·n/(ln 2y·ln z) + o(n/ℓ²), with z = n/y.
**Beyond.** X̃ (C2) allowed C·n/ln²y in these windows. Here they are super-polylogarithmically small. Theorem M′ also removes C2's discard term 5n/ln²(2y), which was the bottleneck of the leg-1 NEXT.
**Referee.** `{"valid": false, "first_error": "Step (3): the per-fibre bound |M_P| ≤ E + I·2^{5/4} z^{(1+ε)/2} s_P^{1/4}, with the π(z) and class-A terms dropped, is taken from the proof of Lemma S, not its statement. No stated lemma gives this bound when class A is empty. Theorem M′ has the same problem with C2: removing the 5n/ln²(2y) term and getting #W·π(z) ≤ 3.18n/(ln2y ln z) and Err1 = o(n/ℓ²) rely on C2's internals, not its statement, and Y₁ is undefined. All arithmetic in steps (1), (2) and (4) checks.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(1) Fibres. For P ∈ W = (y,2y] put M_P = {m : mP ∈ A, P(m) < P}. Then m ≤ n/P < z. Elements a with P(a) = P and P ∤ a/P are exactly P·M_P. The rest have P² | a, and there are ≤ Σ_{P>y} n/P² ≤ 2n/y of them.
(2) Lemma A applies without discarding. If distinct m₁..m₄ lie in M_P ∩ M_Q with P ≠ Q, then P(m_i) < min(P,Q), so all m_i are coprime to PQ. Hence each square 4-set of [1,z) lies in at most one fibre, and Σ_{P∈W} s(M_P) ≤ Q4(z) ≤ 4.39z²ℓ^6 (Lemma Q, using 1+ln z ≤ 2ℓ).
(3) Lemma S on each M_P, with the C2 parameters: ε' = 1/(24L), ε = 1/(96L), γ₀ = 1/(6L), β = 1−ε', I ≤ 1+96L.
  - Every m ∈ M_P has P(m) < P ≤ 2y ≤ z^β by hypothesis. So class A of Lemma S is EMPTY.
  - Lemma S's proof (a sum over classes) then gives |M_P| ≤ E + I·2^{5/4}z^{(1+ε)/2}s_P^{1/4}.
  - The π(z) term and the class-A term z^{2ε'} + z^{ε'}√(2s) come only from class A, so both are absent.
(4) Sum over P with #W ≤ y, Hölder Σ s_P^{1/4} ≤ #W^{3/4}Q4^{1/4}, and yz = n:
N_y ≤ n·(E/z) + 3.45(1+96L)·n·z^{ε/2}ℓ^{1.5}y^{−1/4} + 2n/y.
Here y ≤ √n, so ln z ∈ [ℓ/2, ℓ]. The three terms:
  - E/z ≤ Ψ(z,z^{γ₀})/z + z^{−1/2} + 2(1+96L)(z^{−γ₀} + z^{−3ε'/8}).
    - Lemma R(a) with u = 6L applies: ln z^{γ₀} ≥ ℓ/(12L) ≥ max(2, 4ln 6L) for large n. It gives Ψ/z ≤ e^{3.1}ℓ^{13−6ln(6L)}.
    - z^{−γ₀} ≤ e^{−ℓ/(12L)} and z^{−3ε'/8} ≤ e^{−ℓ/(128L)}.
  - z^{ε/2}y^{−1/4} ≤ n^{1/(192L)}·n^{−1/(24L)} = e^{−7ℓ/(192L)}.
  - 2n/y ≤ 2n·e^{−ℓ/(6L)}.
  - Since ℓ = e^L, every factor e^{−cℓ/L}·poly(L,ℓ) and ℓ^{13−6ln 6L} is ≤ ℓ^{−K}/4 for n ≥ n₀(K).
Theorem M′: identical to C2's Theorem M, except that the discard D is replaced by step (1)'s 2n/y = o(n/ℓ²) and Lemma A is used via step (2). When class A is present, its terms give #W·π(z) ≤ 3.18n/(ln 2y ln z) and Err1 = o(n/ℓ²), as in C2. ∎

## [broken] deep/C7 PROVED QUANT
**Statement.** Let p₁ < p₂ < … be the primes and e_j = p_{2j−1}p_{2j} (6, 35, 143, 323, 667, …). Then for all large n,
F(n) ≥ S₂(n) + Σ_{j≥2} (π(n/e_j) − π(√n))^+ − O(√n), so liminf (F(n) − S₂(n))·ln n/n ≥ c₀ := Σ_{j≥2} 1/e_j > 0.0424.
Together with C4: F(n) − S₂(n) = Θ(n/ln n).
**Beyond.** R5 gave F ≥ S₂ only, and the leg-1 data suggested F = S₂. This shows the ω≤2 set is not second-order optimal. With C4, it pins F(n) − S₂(n) to the order n/ln n.
CONSTRUCTION:
- Put Y = ⌊√n⌋, H = {primes} ∪ Ê with Ê = {e_j}, and R = the primes dividing some e_j ≤ n/(Y+1).
- Top part: for each prime P > Y, let k = ⌊n/P⌋ (< √n < P).
  - If k ≥ 6, put M_P = H ∩ [1,k].
  - Otherwise put M_P = {1} ∪ {primes ≤ k}.
  - A_top = ∪_P P·M_P.
- Low part: A_low = {squarefree a ∈ [2,n] : ω(a) ≤ 2, P(a) ≤ Y}, minus the primes in R, minus the semiprimes pq with p, q ∈ R and pq ∉ Ê.
- A = A_top ∪ A_low.
COUNT:
- S₂'s elements with P(a) > Y are exactly the sets P·({1} ∪ primes ≤ k).
- Each fibre with k ≥ 6 gains #{j : e_j ≤ k} − 1 = #{j ≥ 2 : e_j ≤ k}.
- The losses are |R| + |R|² = O(√n), since e_j ≤ √n forces p_{2j−1} ≤ n^{1/4}.
- Then Σ_{j=2}^{J} π(n/e_j) ~ (n/ℓ)Σ_{j=2}^{J}1/e_j, for every fixed J (PNT).
- c₀ > 1/35 + 1/143 + 1/323 + 1/667 + 1/1147 + 1/1763 + 1/2491 + 1/3599 + 1/4757 = 0.04249.
VALIDITY PROOF. All elements are squarefree.
- Every top element is P·m with m ≤ k < √n < P, so it contains exactly one prime > Y. Low elements contain none.
- In a 4-multiset with square product, each top prime occurs an even number of times. So the cases are:
(a) No top element: A_low ⊆ S₂, which is valid by R5.
(b) All four in one fibre P: M_P is valid.
  - {1} ∪ primes is clear.
  - H has no square product of 4 distinct elements: the edges are disjoint, so each chosen edge forces both of its primes
**Referee.** `{"valid": false, "first_error": "Validity proof is truncated: case (b) (H has no nontrivial square 4-product) breaks off mid-sentence, and the two cross-group cases — two elements in fibre P with two in fibre Q, and two in one fibre with two low elements (the authors' 'case (d)') — are never argued. These are the cases where the design (1 and edges never share a fibre; removal of R-primes and non-edge R–R semiprimes) is needed, via the requirement that matching squarefree parts force equal ratios m2/m1 = m4/m3. Count, PNT step, numerics (0.042488) and the use of C4(a) are fine.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [broken] deep/C8 PROVED QUANT
**Statement.** Let H(k) be the largest subset of [1,k] with no square product of 2 or of 4 distinct elements, h(k) = H(k) − π(k) − 1, and c* = Σ_{k≥1} h(k)/(k(k+1)) < ∞. Then
c₀ ≤ liminf (F(n)−S₂(n))·ln n/n ≤ limsup (F(n)−S₂(n))·ln n/n ≤ c*.
Data: h(k) ≥ #{j≥2 : e_j ≤ k} (by C7's H), and Σ_{k≤60} h(k)/(k(k+1)) = 0.0642.
**Referee.** `{"valid": false, "first_error": "Bullet 2: 'Σ_P s(M_P) ≤ Q4(n/Y) = O(n/ℓ²)' is unproved. Each M_P ⊆ [1,n/P] only gives s(M_P) ≤ Q4(n/P), and Σ_{P>Y} Q4(n/P) ≈ n^{3/2}/(ln n)^4 ≫ n/ln n. Bounding by Q4(n/Y) assumes each multiplicative quadruple is counted for only one P, but the same quadruple (e.g. {1,2,3,6}) can validly lie in M_P and M_{P'} whenever P'/P ≥ m2/m1. A single M_P can contain ~(k/ln k)^2 square 4-sets (e.g. {p,2p,q,2q}). C4 as stated (only the g(n/P) inequality) gives no cross-P bound. So F(n) ≤ S₂(n)+Σ h(⌊n/P⌋)+o(n/ℓ), and hence limsup ≤ c*, is not established.", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

- Follow C4 exactly, but in Lemma T delete one element per square 4-set of M_P (P > Y).
- What remains is a valid subset of [1, n/P] with no square 4-set. Validity gives R1, i.e. no square pairs. So |M_P| ≤ H(⌊n/P⌋) + s(M_P), and Σ_P s(M_P) ≤ Q4(n/Y) = O(n/ℓ²).
- Hence F(n) ≤ S₂(n) + Σ_{P>Y} h(⌊n/P⌋) + o(n/ℓ).
- Fix K. For k ≤ K, PNT gives #{P : ⌊n/P⌋ = k} = (1+o(1))n/(k(k+1)ℓ).
- Tail: H ≤ G gives h(k) ≤ C_E k^{3/4}, so Σ_{P<n/K} h(n/P) ≤ C_E n^{3/4}Σ_{P<n/K}P^{−3/4} ≤ (4+o(1))C_E·n/(K^{1/4} ln n).
- Let K → ∞. The lower bound is C7. ∎

## [broken] deep/C1 PROVED QUANT
**Statement.** F(n) = (1+o(1))·n·lnln n/ln n. Hence the Lean theorem erdos_41635 (Θ) holds.
**Beyond.** KNOWN had only the lower bound (R5) and the trivial upper bound 6n/π². CORE (the O-bound) was the open part. This gives CORE together with the sharp constant 1.
**Referee.** `{"valid": false, "first_error": "Step (ii) (top part P(a) > Y1 = sqrt(n)(ln 2n)^4): the bound |T| <= (1+o(1)) n lnln n/ln n is taken from 'Lemma T below', which is neither given nor among the cited lemmas (only C2 is cited). Since Y1 > sqrt n, this range contains essentially the entire extremal pq construction and a positive-density set of integers, so this unstated lemma carries the whole sharp upper bound; steps (i) and (iii) only show the remaining parts are o(n lnln n/ln n). C2/Theorem M is used within its stated hypotheses (authors' concern resolved: no misuse). Secondary gap: Lemma R in (i) is also cited without statement.", "fixable": false}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

Lower bound: R5 (KNOWN). The squarefree pq ≤ n are valid, and there are (1+o(1))nL/ℓ of them (Landau).
Upper bound. Let A be valid and n large. Put u₁ = 3L/ln L and Y₁ = √n(ln 2n)^4. Split A into three parts.
(i) Smooth part: P(a) ≤ n^{1/u₁}.
- This part has at most Ψ(n, n^{1/u₁}) elements.
- Lemma R(a) applies with X = n, Y = n^{1/u₁}, u = u₁. Its hypothesis ln Y = ℓ ln L/(3L) ≥ max(2, 4 ln u₁) holds for large n.
- This gives Ψ ≤ e^{3.1}·n·ℓ·exp(−u₁ln u₁ + 2u₁).
- Here u₁ ln u₁ − 2u₁ = 3L − 3L(lnln L + 2 − ln 3)/ln L = 3L − o(L).
- So Ψ ≤ n·ℓ^{−2+o(1)} = o(n/ℓ).
(ii) Top part: P(a) > Y₁. This is the top-range bound T of Lemma T below:
|T| ≤ (1+o(1))nL/ℓ.
(iii) Middle part: P(a) ∈ (n^{1/u₁}, Y₁].
- Cover it by the dyadic windows y = 2^k with k₁ = ⌊log₂ n^{1/u₁}⌋ ≤ k ≤ ⌊log₂ Y₁⌋.
- Every such y satisfies y > n^{1/u₁}/2 ≥ n^{1/(6L)} and y ≤ Y₁, so Theorem M (in C2) applies:
  N_y ≤ 3.18(1+o(1))·n/(ln 2y·ln z) + 5n/ln²(2y) + o(n/ℓ²), with z = n/y.
- Sum over k:
  - The o(n/ℓ²) terms: there are ≤ log₂n windows, so they total o(n/ℓ).
  - The terms 5n/ln²(2^{k+1}): Σ_{j>k₁} 5n/(j ln2)² ≤ 5n/(k₁ ln²2). Since k₁ ≥ ℓ/(u₁ ln 2) − 1, this is O(n·u₁/ℓ) = O(nL/(ℓ ln L)) = o(nL/ℓ).
  - The main terms, y ≤ √n: ln z ≥ ℓ/2, so the sum is ≤ (2n/(ℓ ln 2))·Σ_{k₁<j≤ℓ/(2ln2)+1} 1/j = O(n·ln u₁/ℓ) = O(n ln L/ℓ) = o(nL/ℓ).
  - The main terms, √n < y ≤ Y₁: there are O(L) windows, each with ln 2y ≥ ℓ/2 and ln z ≥ ℓ/3. They total O(nL/ℓ²).
- Each a ∈ A lies in (i), (ii) or (iii), since the windows cover (2^{k₁}, 2^{⌊log₂Y₁⌋+1}] ⊇ (n^{1/u₁}, Y₁].
- So |A| ≤ (1+o(1))nL/ℓ.
Lean form: Nat.findGreatest (p n) n = F(n). Subsets of valid sets are valid, so p n k holds for all k ≤ F(n) ≤ n, and fails for k > F(n). ∎

## [broken] deep/C3 PROVED NEGATIVE
**Statement.** The plan's PITFALL "Rectangle supply fails below √n … a naive supersaturation argument gives nothing" is false as stated.
- Demand is quartic: a fibre of size π(z) + Δ contains ≥ c·(Δ/(I·z^{(1+ε)/2}))⁴ square 4-sets (Lemma S).
- Supply is only Q4(z) ≤ z²(1+ln z)^6 in total, and it cannot be shared between fibres (Lemma A).
- So once #W ≫ z^{2ε}·polylog, i.e. for y ≥ n^{C/L}, the average fibre has size ≤ (1+o(1))π(z).
**Beyond.** It identifies the exact reason the mid range is easy. Supersaturation must use the C4 count in the (r, P(m)) graph split by the scale of P(m) (KST with I ≈ L classes), not raw rectangle counts.
**Referee.** `{"valid": false, "first_error": "No proof is given; the argument rests on Lemma S (a fibre of size π(z)+Δ contains ≥ c(Δ/(I z^{(1+ε)/2}))^4 square 4-sets) and Lemma A (supply cannot be shared between fibres), both asserted without proof or stated hypotheses. Lemma S cannot follow from a dimension count in F_2^{π(z)}: Sidon sets in F_2^k of size ~2^{k/2} have no 4-term zero sums, so exceeding π(z) by Δ forces no square 4-sets without unproved arithmetic input. Lemma A has no injection argument from square 4-sets in fibres (elements up to n) into the Q4(z) pool of quadruples up to z.", "fixable": false}`
**Adversary.** `{"broken": true, "how": "No proof is given and the supply-demand mechanism is invalid. (1) Lemma A ('supply cannot be shared between fibres') is false for scaled fibres A_m={r: mr in A}: any square pattern r1r2r3r4=square yields a distinct square 4-set {m r_i} for every m, so Q4(z)<=z^2(1+ln z)^6 bounds per-fibre counts, not the total over #W fibres. The inequality #W*(Delta/(I z^{(1+eps)/2}))^4 <= Q4(z) is unjustified. (2) The argument is vacuous or circular. If Lemma S counts forbidden (ad != bc) 4-sets, a valid fibre has none, so each fibre alone already gives Delta <= I z^{(1+eps)/2}, supply is irrelevant and the #W >> z^{2eps} threshold is meaningless. If it counts rectangles too, rectangles are allowed and quartic demand yields no contradiction, which is exactly the pitfall. (3) Lemm`
**Proof or evidence.**

(none)

## [broken] r1s1/C3 PROVED NEGATIVE
**Statement.** Drop the arithmetic weight. Take rows P∈[M], columns q∈[m], and colour classes that are lines q = sP+b with slopes s∈{1..t}, plus one colour per row and one per column. Then no crossing rectangle exists, yet every cell has t+2 colours. So any proof of the Ω=3 lemma must use that colours u satisfy uqP≤n; incidence structure alone does not suffice. Likewise, Cauchy–Schwarz over (κ,ρ) classes (the assignment's sketch) cannot work as stated. Cross-consistency only says that, of the 3 matchings of a 4-set, at most one is used by ≥2 values of P. That saves at most a factor 3 in cherry counts, and the star-at-2 extremal example has every class shared by ~n/(qq' log n) primes P.
**Referee.** `{"valid": false, "first_error": "The grid/lines construction is correct (each cell lies on exactly one line per slope plus its row and column colour, giving t+2 colours; a crossing rectangle would need lines of slopes s and -s, impossible for s in {1..t}), though 'crossing rectangle' and the targeted Ω=3 lemma are never defined. The first real gap is the second half: the claim that Cauchy–Schwarz over (κ,ρ) classes 'cannot work' rests on undefined objects (κ,ρ classes, cross-consistency, star-at-2 example) and unproved assertions ('at most one matching used by ≥2 P', 'saves at most a factor 3', 'every class shared by ~n/(qq' log n) primes'). No configuration is given that defeats the method's inequality while the true answer stays small.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [broken] r1s1/C5 PROVED QUANT
**Statement.** For each fixed k≥3 and every valid A⊆[n]: #{a∈A squarefree, ω(a)=k} ≤ T_{k−1}(n) + O_k(n L^{k−3}/log n) ≤ (1/2+o(1))·n L^{k−2}/((k−2)! log n). Here T_j(n) = #{primes 3≤p1<…<pj : 2p1⋯pj ≤ n}. This is a fraction ≤ (k−1)/(2L) → 0 of all ω=k squarefree numbers. The trivial bound is ~nL^{k−1}/((k−1)! log n).
**Beyond.** KNOWN only has the trivial layer bound, and "recursion loses a factor". Plain recursion with the trivial base gives a bound worse than trivial. Using C1 as the base gains a factor L on every layer.
**Referee.** `{"valid": false, "first_error": "Base case H_3: it needs, for valid A' ⊆ [x] with all primes < y, the bound T_2(x,y) + O(x/log x), where the largest prime must be < y. C1 as stated only gives #{(q,P): 3≤q<P, qP≤x/2} + O(x/log x) = T_2(x), with no y-constraint. The proof invokes 'C1's proof' (cell counting, an exceptional term X) and C2, which are outside C1's statement. The y-refinement is essential: without it Σ_P T_{k-1}(x/P,P) = T_k(x,y) fails and the constant compounds.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

- Induction hypothesis H_k: if A' ⊆ [x] is valid and every prime factor of its elements is < y, then #{a∈A' sqfree, ω=k} ≤ T_{k−1}(x,y) + E_k(x). Here T_{k−1}(x,y) adds the constraint p_{k−1} < y, and E_k(x) = C_k x ℓ(x)^{k−3}/log(x+2) with ℓ(x) = loglog(x+e^e).
- Base k=3 is C1's proof. A nonempty cell (P',q) needs u<q<P'<y with uqP'≤x, so 2qP'≤x and q≥3. X = O(x/log x) holds for any valid set, and for small x a trivial bound with large C_3 covers it.
- Step: the elements of A' with ω=k+1 and largest prime P are P·N(P), with N(P) = {a/P}. N(P) is valid in [x/P]: multiplying a quadruple by P⁴ preserves square product and order, and Pa'·Pd' = Pb'·Pc' gives a'd' = b'c'. Its primes are < P, and it has ω=k. So the count is ≤ Σ_{P<y} [T_{k−1}(x/P,P) + E_k(x/P)].
- Σ_P T_{k−1}(x/P,P) = T_k(x,y) exactly.
- E_k(x/P) is needed only for x/P ≥ 30, because an element with ω≥3 is ≥ 30. Then Σ_{P≤x/30} (x/P)/log(x/P) ≤ x·S(x), where S(x) = Σ_{P≤x/30} 1/(P log(x/P)) = O(ℓ(x)/log x):
  - for P≤√x, log(x/P) ≥ ½log x, and Mertens applies;
  - for P∈(x/2^{j+1}, x/2^j] with x/2^j ≥ √x, Chebyshev gives Σ 1/P ≤ 8/log x and log(x/P) ≥ j log 2; summing 1/j over j ≤ log x gives O(ℓ/log x).
- Since ℓ(x/P) ≤ ℓ(x), we get E_{k+1} = O(C_k x ℓ^{k−2}/log x).
- Finally, T_{k−1}(n) ≤ #{odd squarefree m ≤ n/2 : ω(m)=k−1} ~ (n/2)L^{k−2}/((k−2)! log n) by Landau, for fixed k.

## [not validated] deep/C6 CONJECTURED OTHER
**Statement.** Exact maxima over squarefree candidates (MaxSAT, exactF2.py, RC2) give F_sf(n) = S₂(n) for n ∈ {110,130,150,170,250}, but F_sf(350) = 175 = S₂(350)+1. The optimum at 350 contains the ω=3 elements 30, 42, 70, 105, 154, 165, 182, 195, 238, 255, 266, 285, … and drops small primes.
All integers (exactF.py): F(n) = S₂(n) for n ∈ {20,…,100} (step 10).
**Proof or evidence.**

(none)

## [not validated] p1L2/C2 PROVED QUANT
**Statement.** For every n ≥ 14, |S_n| ≥ (1/2)·n·ln ln n/ln n, where S_n = {pq ≤ n : p<q primes}. (So L3 holds with N₀ = 14.)
**Beyond.** Closes skeleton lemma L3 with an explicit N₀; KNOWN had only the Landau asymptotic.
**Proof or evidence.**

Cited: (RS1) Rosser–Schoenfeld 1962, Cor. 1 (3.5): π(x) > x/ln x for real x ≥ 17.
(RS2) Rosser–Schoenfeld 1962, Thm 5 (3.20): Σ_{p≤x} 1/p > ln ln x + B − 1/(2 ln² x) for real x > 1, where
B = 0.2614972128... (Meissel–Mertens constant).
Let n ≥ 43000, L = ln n, y = n^{1/3}. Distinct pairs p<q give distinct products pq (unique factorisation), so |S_n| =
#{(p,q) primes : p<q, pq ≤ n}. For each prime p ≤ y we have p² ≤ n^{2/3} < n, so p < n/p, and the primes q with
p < q ≤ n/p number π(n/p) − π(p). Hence
 |S_n| ≥ Σ_{p≤y} π(n/p) − Σ_{p≤y} π(p).
Second sum: π(p) ≤ p ≤ y and there are ≤ y terms, so it is ≤ y² = n^{2/3}.
First sum: n/p ≥ n^{2/3} ≥ 17, so by RS1 π(n/p) > (n/p)/ln(n/p) ≥ (n/p)/L (0 < ln(n/p) ≤ L). By RS2 with x = y > 1
(ln y = L/3): Σ_{p≤y} 1/p > ln L − ln 3 + B − 9/(2L²). With κ := ln 3 − B = 0.83711...:
 |S_n| ≥ (n/L)(ln L − κ − 4.5/L²) − n^{2/3}.
So |S_n| ≥ ½ n ln L / L follows from h(L) ≥ 1, where h(t) := e^{t/3}·(½ ln t − κ − 4.5/t²)/t (divide by n/L, use
n^{1/3} = e^{L/3}). The factor φ(t) = ½ ln t − κ − 4.5/t² is increasing in t, and e^{t/3}/t is increasing for t > 3;
φ(10.66) = 0.3065 > 0, so h is increasing on [10.66, ∞) as a product of positive increasing functions, and
h(10.66) = 1.0044 ≥ 1. Since ln 43000 = 10.669 > 10.66, h(L) ≥ 1 for all n ≥ 43000.
For 14 ≤ n ≤ 2·10^7: exact sieve count of |S_n| for every n (test_L3.py, test_L3b.py); min of |S_n|/(½g(n)) over this
range is 1.092 (at n = 20), so floating-point error in g is irrelevant. The ranges overlap, giving all n ≥ 14. ∎

## [not validated] p1L3/C2 PROVED QUANT
**Statement.** For every fixed c < 1 there is N₀(c) such that |S_n| ≥ c·n·ln ln n/ln n for all n ≥ N₀(c). Consequently
liminf |S_n| / (n ln ln n/ln n) ≥ 1.
**Beyond.** This is a strengthening of C1 (constant 1/2 → any c < 1). It is standard (Landau), and is recorded only as a corollary.
**Proof or evidence.**

By (★) in C1, which is valid for all n with n^{2/3} ≥ 17 and n^{1/3} > 1, i.e. n ≥ 71,
|S_n|·(ln n)/n > ln ln n − ln 3 − 1 − (ln n)·n^{−1/3}. The last two terms are bounded (ln 3 + 1, plus (ln n)n^{−1/3} → 0).
So the right side is ≥ c·ln ln n once (1−c) ln ln n ≥ ln 3 + 1 + (ln n) n^{−1/3}, which holds for all large n. ∎

## [not validated] p1L3/C3 PROVED QUANT
**Statement.** For every integer n ≥ 14, |S_n| ≥ (1/2)·n·ln ln n/ln n. The threshold is optimal: the inequality fails at n = 13
(|S_13| = 2 < 2.15…). For 3 ≤ n ≤ 13 it fails exactly at n ∈ {3,4,5,7,8,9,11,12,13}.
**Beyond.** C1 with the explicit, optimal N₀ = 14 instead of e^{81}. This lets the glue (and a Lean formalisation) take
N₀ = 16, i.e. max(16, N₀) = 16. The leg-1 note said this would need RS (3.17)/(3.6) and would only reach e^{42}. Here a
computed base point Z₀ = 100 plus partial summation avoids all citations except RS (3.5).
**Proof or evidence.**

(a) Partial-summation Mertens bound. Claim: for real z ≥ 100, Σ_{p≤z} 1/p > ln ln z + c₀ + 1/ln z, where
c₀ := Σ_{p≤100} 1/p − π(100)/100 − ln ln 100 = 1.80281720… − 0.25 − 1.52717963… = 0.02563757… > 0.
Proof: each prime p with 100 < p ≤ z gives 1/p = 1/z + ∫_p^z dt/t². Summing,
Σ_{100<p≤z} 1/p = (π(z) − π(100))/z + ∫_{100}^z (π(t) − π(100))/t² dt = π(z)/z − π(100)/100 + ∫_{100}^z π(t)/t² dt.
For t ≥ 100 ≥ 17, RS (3.5) gives π(t) > t/ln t. So π(z)/z > 1/ln z and ∫_{100}^z π(t)/t² dt ≥ ∫_{100}^z dt/(t ln t) =
ln ln z − ln ln 100, with equality at z = 100. Adding Σ_{p≤100} 1/p proves the claim. π(100) = 25 and Σ_{p≤100}1/p were computed exactly
as a Fraction.
(b) n ≥ 10^6. Here y = n^{1/3} ≥ 100 and n/p ≥ n^{2/3} ≥ 10^4 > 17, so Steps 1–3 of C1 apply verbatim:
|S_n| ≥ (n/ln n)·Σ_{p≤y}1/p − n^{2/3}. By (a), with ln ln y = ln ln n − ln 3 and dropping 1/ln y > 0,
|S_n|·(ln n)/n > ln ln n − ln 3 + c₀ − u e^{−u/3}, where u = ln n. So it suffices that
(1/2) ln u ≥ ln 3 − c₀ + u e^{−u/3} for u ≥ u₀ := ln 10^6 = 13.8155…. At u₀: LHS = 1.31289…, RHS = 1.0986123 − 0.0256376 +
0.1381518 = 1.21113… . For u ≥ u₀ > 3 the LHS is increasing and u e^{−u/3} is decreasing, so the inequality holds for all u ≥ u₀.
(c) 14 ≤ n < 10^6: by exact computation (explicit_n0.py). An spf-sieve marks n = pq, p < q, as an increment of |S_n|. Prefix sums
give |S_n| exactly; this was cross-checked against brute force for n < 400. The minimum of |S_n| − g(n)/2 over 14 ≤ n ≤ 10^6
is 0.3375, at n = 20 (|S_20| = 4 vs 3.66250…), recomputed in 50-digit Decimal. The float margin 0.3375 vastly exceeds the
rounding error. The failures for 3 ≤ n ≤ 13 are listed in the statement. ∎

## [not validated] r1s1/C4 OTHER REDUCTION
**Statement.** - For valid squarefree A, |A| ≤ π(n) + 1 + #{q<P: qP≤n} + X(A), where X(A) = Σ_cells (|C(cell)|−1)^+ and colours are arbitrary cofactors c with P⁺(c) < q.
- Hence X(A) = O(nL/log n) for all valid A ⟹ CORE. X(A) = o(nL/log n) ⟹ F_sf(n) ~ nL/log n (sharp constant 1).
- Conjecture: X(A) = O(n/log n) always.
**Proof or evidence.**

(none)

## [not validated] r1s3/C6 PROVED QUANT
**Statement.** (a) For every δ ∈ (0,½] there are C(δ) = O(1/δ) and n₀(δ) such that X holds for n ≥ n₀ and y ∈ [n^δ, n].
(b) CORE: every valid A ⊆ [1,n] has |A| = O(n·L/ln n), where L = lnln n.
**Beyond.** This settles CORE. It extends C5, which covered only y ≥ √n·log⁴, down to y = n^{1/(3L)}. Below that, the smooth numbers are negligible.
**Proof or evidence.**

Notation. L = lnln n and u₀ = 3L. Consider a dyadic window y = 2^k with n^{1/u₀}/2 ≤ y ≤ √n(ln n)^4, and put z = n/y ≥ √n/(ln n)^4.
The elements with P(a) > √n(ln n)^4 are handled by C5(d): at most n(L+O(1))/ln n of them.
The elements with P(a) ≤ n^{1/u₀} number at most Ψ(n, n^{1/u₀}) = n/(ln n)^{3+o(1)} (de Bruijn; KNOWN).
Step D (discard). The a ∈ A with P(a) ∈ (y,2y] whose cofactor a/P(a) has a prime in (y,2y] number at most n(Σ_{y<p≤2y}1/p)² ≤ n(2/ln y)², by Brun–Titchmarsh. Summed over k ≥ log₂(n^{1/u₀}) − 1, this is ≤ Σ_k 4n/(k ln2)² = O(n·u₀/ln n) = O(nL/ln n).
For the rest, M_P = {m : mP ∈ A, P(mP) = P, m free of primes in (y,2y]} ⊆ [1,z].
Step A (Lemma A, as in C5). Take P ≠ Q window primes and 4 distinct m_i ∈ M_P ∩ M_Q with square product. Then A is invalid. The C5 proof used only that P,Q ∤ m_i, which Step D guarantees. Hence Σ_P s_P ≤ Q4(z) ≤ 0.07z²(1+ln z)^6 by C5(b), where s_P is the number of square 4-subsets of M_P.
Step S (Lemma S). For any M ⊆ [1,z], with s = s(M), choose parameters ε' = 1/(4u₀), ε = ε'/4, β = 1−ε', and γ₀ = 1/(3 lnln z). Choose γ₀ < γ₁ < … < γ_I = β with gaps ≤ ε, so I ≤ 1 + 1/ε. Split M by P(m):
- Class C: P(m) ≤ z^{γ₀}. There are at most Ψ(z, z^{γ₀}) = z/(ln z)^{3+o(1)} such m.
- Class B_i: P(m) = Q ∈ (z^{γ_i}, z^{γ_{i+1}}]. Write m = Qr with r < z^{1−γ_i}. Edge (r,Q) in a bipartite graph whose centre side has x = z^{1−γ_i} vertices and whose pair side has w = z^{γ_{i+1}} vertices.
- Class A: P(m) = Q > z^β. Write m = Qr with r < z^{1−β}. The centres are the primes Q and the pair side is r ≤ w = z^{ε'}.
Each graph C4 {Q₁,Q₂}×{r₁,r₂} gives a distinct 4-subset of M with ab = cd, which is a square product. So #C4 ≤ s.
KST supersaturation:
- Let S = Σ_centres C(d,2). Jensen over the pairs gives #C4 ≥ S²/(2w²) when S ≥ w². So S ≤ w² + w√(2s).
- Convex form: if e ≥ 2x then S ≥ e²/(4x). So e ≤ 2x + 2√x·w + 2^{5/4}√(xw)·s^{1/4}.
- Prime form: S ≥ e − #centres. So e_A ≤ π(z) + z^{2ε'} + z^{ε'}√(2s).
Exponents: in B_i, (1−γ_i)/2 + γ_{i+1} ≤ 1 − 3ε'/8, and √(xw) ≤ z^{(1+ε)/2}.
Hence |M| ≤ π(z) + E + z^{ε'}√(2s) + I·2^{5/4}z^{(1+ε)/2}s^{1/4}, where E = 1 + Ψ(z,z^{γ₀}) + z^{2ε'} + I(2z^{1−γ₀} + 2z^{1−3ε'/8}).
Since ln z ≥ ½ln n − 4L and ε' = 1/(12L), we get E = o(z/ln z) as n → ∞.
Step H (Hölder). Let #P ≤ 2y/ln y.
- The main term is Σ_P π(z) ≤ 2.52·n/(ln y ln z).
- The E term is o(n/(ln y ln z)).
- The s-terms are ≤ z^{ε'}√(2#P·Q4) + I·2^{5/4}z^{(1+ε)/2}#P^{3/4}Q4^{1/4}.
- Relative to #P·z/ln z, these are O(z^{ε'}(ln z)^4/√#P + I·z^{ε/2}(ln z)^{2.5}/#P^{1/4}).
- This → 0 uniformly, because #P ≥ n^{1/u₀−o(1)} = n^{1/(3L)−o(1)}, while z^{ε'} ≤ n^{1/(12L)} and I = O(L). Here ln n ≫ L² absorbs the polylog factors.
So N_y(A) ≤ (2.52+o(1))n/(ln y ln z) + 4n/ln² y.
Sum: Σ_k n/(ln y ln z) over this range is O(n ln L/ln n). Adding Step D, C5(d) and the smooth part gives |A| = O(nL/ln n). ∎
For (a), take u₀ = 1/δ fixed. The discard term 4n/ln²y ≤ (4/δ)·n/(ln y ln(n/y)).

## [not validated] r1s3/C5 PROVED QUANT
**Statement.** Let G(x) be the largest size of a multiplicatively Sidon set in [1,x], i.e. a set in which ab = cd implies {a,b} = {c,d}. Let Q4(z) be the number of 4-element subsets of {1,…,⌊z⌋} with square product.
(a) For every valid A ⊆ [1,n] and every Y ≥ √n:
#{a∈A : P(a) > Y} ≤ Σ_{Y<P≤n, P prime} G(n/P) + Q4(n/Y).
Restricting to P ∈ (y,2y] gives the same bound for N_y(A), with Q4(n/y), for any y ≥ √n.
(b) Q4(z) ≤ (ζ(2)/24)·z²(1+ln z)^6.
(c) Hence X holds for every y ≥ √n·(ln 2n)^4 with an absolute constant C.
(d) For Y = √n(ln n)^4: #{a∈A : P(a) > Y} ≤ n(lnln n + O(1))/ln n.
The ω≤2 construction has (1+o(1))·n·lnln n/ln n elements, almost all with P(a) > Y. So (d) is asymptotically sharp, and F(n) ≤ (1+o(1))·n·L/ln n + max_A #{a∈A : P(a) ≤ √n(ln n)^4}.
**Beyond.** KNOWN has only trivial bounds for these elements. Both Σ_{P>√n} n/P and the recursion Σ_P F(n/P) with trivial F give O(n), and KNOWN has no upper bound of order n·L/log n for any positive-proportion class. C5 gives the sharp constant 1 for the part of A that carries the extremal mass. It proves T9's hypothesis X on all scales y ≥ n^{1/2+o(1)}.
**Proof or evidence.**

Fix Y ≥ √n and let A' = {a∈A : P(a) > Y}; A' is valid as a subset of A. For a prime P > Y put M_P = {m : mP ∈ A'}. Then:
- M_P ⊆ [1, n/P] ⊆ [1, n/Y].
- Every m ∈ M_P satisfies m ≤ n/P < n/Y ≤ Y < any prime > Y. So no prime > Y divides any fibre element.
- |A'| = Σ_P |M_P|, because a ↦ (P(a), a/P(a)) is injective.
Step 1 (fibres are valid and have distinct kernels). As in C2(a), M_P is valid. By R1 its elements have distinct squarefree kernels.
Step 2 (Lemma A). Let P ≠ Q be primes > Y, and let m1,m2,m3,m4 be distinct elements of M_P ∩ M_Q with m1m2m3m4 a square. Then A' is invalid.
Proof:
- Let E12: m1m2 = m3m4, E13: m1m3 = m2m4, E14: m1m4 = m2m3.
- Any two of these force a coincidence. E12 ∧ E13 gives m2/m3 = m3/m2, so m2 = m3. E12 ∧ E14 gives m2 = m4. E13 ∧ E14 gives m3 = m4. So at most one holds.
- Consider the split {i,j}|{k,l}, i.e. the four elements m_iP, m_jP, m_kQ, m_lQ ∈ A'. These are distinct and their product (m1m2m3m4)P²Q² is a square.
- By R2 (sorted a≤b≤c≤d: ad = bc ⇔ some pairing has equal products), validity needs one of three equalities.
  - m_im_jP² = m_km_lQ² is impossible: the P-adic valuations are 2 and 0.
  - m_im_k = m_jm_l, or m_im_l = m_jm_k.
- So split 12|34 needs E13 ∨ E14, split 13|24 needs E12 ∨ E14, and split 14|23 needs E12 ∨ E13.
- With at most one E_ true, some split fails: none true → all fail; only E12 → 12|34 fails; only E13 → 13|24 fails; only E14 → 14|23 fails.
- That split gives a bad quadruple in A'. ∎
Step 3 (removal). Let s_P be the number of 4-subsets of M_P with square product. Delete one element of each such 4-subset to get M°_P with |M°_P| ≥ |M_P| − s_P.
M°_P is multiplicatively Sidon. Suppose ab = cd with a,b,c,d ∈ M°_P.
- If a,b,c,d are distinct, then abcd = (ab)² is a square, but every such 4-subset was destroyed.
- If a = c then b = d; if a = d then b = c.
- If a = b, then cd = a² is a square, so ker c = ker d, so c = d (Step 1), and then c = a.
- The case c = d is symmetric.
So |M_P| ≤ G(n/P) + s_P.
Step 4 (each square 4-set is used by one fibre). By Lemma A, each square 4-subset S of [1,n/Y] lies in at most one fibre. So Σ_P s_P ≤ Q4(n/Y), which gives (a).
Step 5, proof of (b). Count ordered 4-tuples (m_i) ∈ [1,z]^4 with square product.
- Write m_i = s_i r_i² with s_i squarefree; this map is injective, and r_i ≤ √(z/s_i).
- The product of the m_i is a square ⇔ s1s2s3s4 is a square ⇔ every prime divides exactly 2 or exactly 4 of the s_i.
- So s_i = g·Π_{j≠i} x_{ij}, where g is the product of the primes dividing all four and x_{ij} the product of those dividing exactly s_i and s_j. The g, x_{ij} are pairwise coprime, squarefree and ≤ z, and the map (s_i) ↦ (g, (x_{ij})) is injective.
- Hence the ordered count is ≤ Σ Π_i √(z/s_i) = z²·Σ g^{-2}·Π_{i<j} x_{ij}^{-1}. Each x_{ij} lies in two of the s's, so its exponent is 2·(−1/2) = −1.
- This is ≤ z²·ζ(2)·(H_z)^6 ≤ ζ(2)z²(1+ln z)^6. Divide by 4! for sets.
- Checked numerically: the ordered counts are 87585 / 585117 / 3.78e6 / 2.34e7 for z = 50, 100, 200, 400, far below the bound.
Step 6, proof of (c). Take y ≥ √n(ln2n)^4 ≥ √n and z = n/y ≤ √n, and apply (a) to the window (y,2y].
- Brun–Titchmarsh (Montgomery–Vaughan) gives π(2y) − π(y) ≤ 2y/ln y.
- Erdős (1938/1969, KNOWN) gives G(x) ≤ π(x) + O(x^{3/4}) ≤ C₂x/ln(2x) for x ≥ 1; for x < 16 use G(x) ≤ x.
- So the main term is ≤ C₃(y/ln 2y)(z/ln 2z) = C₃n/(ln 2y·ln(2n/y)).
- Error term: 0.07z²(1+ln z)^6 ≤ n/(ln2y·ln2z) ⇐ 0.07z(ln2n)^8 ≤ y. This uses 1+ln z ≤ ln 2n (true since z ≤ √n, n ≥ 3) and ln 2y, ln 2z ≤ ln 2n. It in turn follows from y² ≥ 0.07n(ln2n)^8, which holds.
Step 7, proof of (d). Take Y = √n(ln n)^4 and z = n/Y = √n/(ln n)^4.
- Q4(z) = O(z²(ln n)^6) = O(n/(ln n)²).
- Σ_{P>Y} G(n/P) ≤ Σ_{P>Y} π(n/P) + O(Σ_{P≤n} (n/P)^{3/4}) + π(n). The +π(n) absorbs the element 1 and small x.
- Prime-sum bound: Σ_{P≤n} P^{-3/4} = O(n^{1/4}/ln n) by partial summation with Chebyshev. So the middle term is O(n/ln n).
- Σ_{P>Y} π(n/P) ≤ #{(p,P) : pP ≤ n, p ≤ n/Y ≤ √n} ≤ Σ_{p≤√n} π(n/p).
- By PNT, π(x) = (x/ln x)(1 + O(1/ln x)), and ln(n/p) ≥ ½ln n. So this is (n/ln n)Σ_{p≤√n} 1/(p(1−u_p))·(1 + O(1/ln n)), with u_p = ln p/ln n ≤ ½.
- 1/(1−u) ≤ 1 + 2u, and by Mertens Σ_{p≤√n} 1/p = L + O(1) and Σ_{p≤√n} ln p/p = ½ln n + O(1). So the sum is L + O(1).
- Total: n(L + O(1))/ln n.
- Sharpness: the ω≤2 squarefree numbers with P > Y number at least (1−o(1))nL/ln n. Those with P ≤ Y are semiprimes pP with p ≥ √n/(ln n)^4, and there are O(n·lnln n/ln² n) of them. ∎

## [not validated] r1s3/C2 PROVED STRUCTURE
**Statement.** Let F(x) denote the maximum size of a valid subset of [1,x].
(a) For every valid A ⊆ [1,n] and y ∈ [2,n]: N_y(A) ≤ Σ_{y<p≤2y, p prime} F(n/p).
(b) Consequently, CORE (F(x) ≤ C₀·x·lnln x/ln x for x ≥ 16, with F(x) ≤ x always) implies
X′: N_y(A) ≤ C′·n·lnln(16n/y)/(ln 2y·ln(2n/y)).
(c) Summing X′ over dyadic y gives only Θ(n·L²/log n). So X′ cannot replace X in C1, and X is genuinely stronger than CORE's own scale-by-scale consequence.
**Beyond.** This places T9's hypothesis X exactly. X = X′ minus one loglog(n/y) factor at each scale. So X at scale y is exactly the statement that "cross-P constraints cost a factor loglog(n/y) over the fibrewise recursion bound". This is the KNOWN barrier "recursion loses a factor", now localised to a single scale.
**Proof or evidence.**

(a) For a prime p, set A_p = {m : mp ∈ A}. Then A_p ⊆ [1, n/p].
A_p is valid: if m1 ≤ m2 ≤ m3 ≤ m4 lie in A_p and m1m2m3m4 is a square, then m_i p are sorted in A with product (m1m2m3m4)p⁴, which is a square. Validity of A gives m1p·m4p = m2p·m3p, so m1m4 = m2m3.
The map a ↦ a/P(a) sends {a : P(a) = p} injectively into A_p.
(b) Apply (a). For y ≥ n/16, use the trivial bound #{a ≤ n : P(a)∈(y,2y]} ≤ Σ_p n/p = O(n/ln 2y), which is O(X′). Otherwise n/p ≥ 8 for p ≤ 2y. Then F(n/p) ≤ C₀(n/p)·lnln(16n/y)/ln(n/2y) up to a constant factor, and Mertens gives Σ_{y<p≤2y} 1/p = O(1/ln 2y). Finally ln(n/2y) ≍ ln(2n/y) in this range.
(c) Take X′ at y = 2^k with K = log₂n. For k ≤ K/2 the factor lnln(16n/y) ≥ lnln √n = L − ln2. Then Σ_{k≤K/2} 1/(k(K−k)) ≥ H_{K/2}/K ~ L/K, so this part alone is ≍ n·L²/ln n. Matching upper bound: lnln(16n/y) ≤ L + O(1) together with C1's computation.

## [not validated] r1s3/C3 PROVED STRUCTURE
**Statement.** Let n ≥ 4 and y ≥ √n, and let A ⊆ [1,n] with P(a) ∈ (y,2y] for all a ∈ A. Write a = m·P with P = P(a), and let M_P = {m : mP ∈ A}. Then A is valid iff both of the following hold:
(i) each M_P is valid;
(ii) for primes P ≠ Q, distinct m1,m2 ∈ M_P, and distinct m3,m4 ∈ M_Q with m1m2m3m4 a square, we have m1/m2 ∈ {m3/m4, m4/m3}.
Equivalently, label each unordered pair {m1,m2} by its class κ = ker(m1m2) and its ratio class {m1/m2, m2/m1}. Different fibres may share a class κ only with the same ratio class.
**Beyond.** This makes X at scales y ≥ √n a purely combinatorial packing problem on fibres.
- It overlaps r1s1's cherry classes (A1). Here it is proved as an exact equivalence at one scale.
- It shows that the constraint between different P is exactly the 2+2 split condition: no 3+1 or 4-distinct-prime interactions occur.
**Proof or evidence.**

- m ≤ n/P < n/y ≤ y < every prime in (y,2y]. So no window prime divides any m.
- Hence in a quadruple with square product, each window prime occurs an even number of times. The prime pattern is therefore {P,P,P,P} or {P,P,Q,Q}.
- Case {P,P,P,P}: this is validity of M_P (as in C2(a), with the converse identical).
- Case {P,P,Q,Q}: by R2, validity ⇔ some pairing has equal products. The pairing {m1P,m2P}|{m3Q,m4Q} would need m1m2P² = m3m4Q², which is impossible because P ∤ m3m4. So validity needs m1Pm3Q = m2Pm4Q or m1Pm4Q = m2Pm3Q, i.e. m1m3 = m2m4 or m1m4 = m2m3, i.e. m1/m2 ∈ {m4/m3, m3/m4}.
- If m1 = m2, then m3m4 is a square. Distinct kernels in M_Q (R1 applied to (i)) force m3 = m4, and then the condition holds. So only distinct pairs matter.
Corollaries (proved):
- If every fibre equals one set M, then M has no 4 distinct elements with square product. (Proof: see C5, Lemma A.) So |M| ≤ F_4(n/y) (ESS), and X holds for product-type sets.
- Example of a valid non-product family: fibres M_P = q_P·{primes ≤ n/(q_P P)}, with arbitrary centres q_P. All pair classes are {r1r2 ; r1|r2}, so they are consistent. Adding the primes back to fibres with different centres creates conflicts, e.g. {r, q r′} vs {q, r r′}.

## [not validated] r1s3/C4 CONJECTURED OTHER
**Statement.** Exact single-scale optima OPT(n,y) = max{N_y(A) : A valid} for n ∈ {60, 120, 200} and all dyadic y satisfy OPT·ln(2y)·ln(2n/y)/n ≤ 1.49. For y ≥ 16, OPT equals or nearly equals the count of squarefree ω≤2 numbers in the window.
**Proof or evidence.**

see Data. This is very small n and so only weak evidence. The mechanism behind X is the conjectured "cross-P cost" in C2/C3.

## Frontier map

=== DIRECTION
**Verdict: TRUE, confidence 0.80.**

I recall Erdős–Sárközy–Sós (1995) as the source and recall them stating this order, but I have not verified it. The team's first action is to retrieve ESS95 and the Erdős-problems entry. If the upper bound is already published, re-aim at the constant (T6) and the structure targets.

**Lower bound (rigorous).** Squarefree integers in [2,n] with ω ≤ 2 form a valid set (proof in KNOWN). There are (1+o(1))·n·loglog n/log n of them (Landau's count).

**Upper bound (heuristic, unproved).** Write a = m·P with P = P(a) the largest prime factor. Two quantities drive the heuristic:
- The cofactor sets N(P) = {m : mP ∈ A}.
- The loglog factor, which comes only from the harmonic mass Σ_{p ≤ √n} 1/p.

The valid configurations force these cofactor sets to be "C4-free / alternating-C4-free" across different P. For example, the ω = 3 layer {pqP} needs every cofactor graph G_P to avoid an alternating C4 with every other G_Q. Weighted computations then give each layer harmonic mass O(loglog n), not loglog² n. A star at the vertex 2 gives about (1/2)·nL/log n in that layer.

No construction beating constant ~1 is known to me.

**Lean details.**
- `Nat.findGreatest (p n) n` equals F(n), because p n k holds for every k ≤ F(n).
- `Finset.Ioc 0 n` excludes 0.
- Quadruples with repeated entries are allowed, and this matters: see R1.

Notation used throughout: L := log log n, and F(n) is the maximum size.

=== KNOWN
- **(R1) Distinct kernels.** If A is valid and c < d in A, then cd is not a square, so the squarefree kernels of A's elements are distinct. | standard (derived) | apply the condition to the quadruple (c,c,c,d): c³d is a square iff cd is, and then cd = c² forces d = c.
- **(R2) Equal-pairing form.** For a ≤ b ≤ c ≤ d: ab = cd forces a=b=c=d, and ac = bd forces a=b and c=d. So A is valid iff every 4-multiset from A with square product has some pairing with equal products. | standard (derived) | order comparison.
- **(R3) Squarefree reduction.** A_t := {s squarefree : st² ∈ A} is valid in [n/t²], so F(n) ≤ Σ_t F_sf(n/t²). Hence F_sf(x) ≤ C·x·loglog x/log x implies F(n) ≤ (ζ(2)C + o(1))·n·L/log n. | standard (derived) | split the sum at t = n^{1/4}.
- **(R4) Support-graph criterion.** Take squarefree a,b,c,d with square product. Write each as the common part g times "atoms" x_{uv} = primes lying in exactly the elements u and v; the atoms are pairwise coprime. The quadruple is allowed iff its atom-support graph on K4 is a subgraph of C4. It is bad iff the support contains a triangle or a K_{1,3}. Minimal bad patterns are {gx, gy, gz, gxyz} and {g, gxy, gxz, gyz}. The 3-partite Pasch pattern {x1y1z1, x1y2z2, x2y1z2, x2y2z1} is also bad. | derived here | an equal pairing exists iff both atoms of some perfect matching are empty.
- **(R5) Lower bound.** Every set of squarefree integers in [2,n] with ω ≤ 2 is valid: all support degrees are ≤ 2, and a triangle would need d = 1. The element 1 must be excluded, since {1, pq, pr, qr} is bad. Hence F(n) ≥ (1+o(1))·n·L/log n, and primes add a further (1+o(1))·n/log n. | Landau + (R4) | construction.
- **Trivial upper bound.** F(n) ≤ #{squarefree ≤ n} = (6/π² + o(1))·n. | (R1) | kernels.
- **Square-product problems F_k.** F_k(N) is the maximum size of a set with no product of k distinct elements a square. F_2(N) = (6/π² + o(1))N and F_3(N) = (1 − o(1))N. F_4(N) = o(N), I believe. The present ad = bc problem appears in the same paper. | Erdős–Sárközy–Sós 1995, "On product representations of powers I" (verify the exact bounds) | F_2-linear algebra plus graph and almost-prime counting.
- **Odd k (Erdős #121).** For odd k ≥ 5, F_k(N) ≤ (1 − c_k)N, so F_k is not (1 − o(1))N. | Tao 2024 (arXiv) | probabilistic and combinatorial.
- **Multiplicative Sidon sets** (ab = cd only trivially): maximum π(n) + Θ(n^{3/4}/(log n)^{3/2}). | Erdős 1938/1969 | write a = uv with u ≤ n^{2/3}, v ≤ n^{1/3}, plus C4-free graph bounds.
- **Even covers and squares.** Product representations of squares ↔ even covers in hypergraphs. | Naor–Verstraëte 2008 (Combinatorica); Verstraëte 2006 | Moore-type bounds and parity-check matrices.
- **Hypergraph Moore bound.** Feige's even-cover conjecture holds up to log factors. | Guruswami–Kothari–Manohar 2021 / Hsieh–Kothari–Mohanty | Kikuchi matrices.
- **Almost-prime counts.** #{n ≤ x : ω(n) = k} ~ x·(loglog x)^{k−1}/((k−1)!·log x) uniformly for k ≤ (2−ε)·loglog x. | Landau; Sathe–Selberg | analytic.
- **Smooth numbers.** Ψ(x, x^{1/u}) = x·u^{−u(1+o(1))}. With u = 3L, the smooth part is at most n/(log n)^{3+o(1)}, which is negligible. | de Bruijn; Hildebrand | standard.

=== BARRIERS
- **Extremal sets are full of square 4-products.** The ω ≤ 2 sets contain about n^{2−o(1)} C4-relations. | This defeats F_2-rank and even-cover existence counting (ESS / Naor–Verstraëte style), which bound sets with no short relations; here relations must merely be "structured". | It does not rule out methods that count only bad relations, i.e. triangle or K_{1,3} supports in R4.
- **Large multiplicative energy.** The semiprime set has energy E×(A) ≫ |A|² polylog. | This defeats energy and sum-product arguments that bound |A| via small E×. | It does not rule out comparing the "mod-squares" energy Q(A) with E×(A) (A4).
- **Weight concentration.** The mass sits on pairs (small p, large P) spread over all log-log scales of p. | This defeats unweighted Kővári–Sós–Turán / Zarankiewicz in the a = uv graph: that gives π(n) + O(n^{3/4}) in the Sidon problem, but here C4's are allowed and the forbidden pattern is an *alternating* C4 between different P. | It does not rule out harmonic-weighted Zarankiewicz bounds.
- **Recursion loses a factor.** The bound F(n) ≤ Σ_P F(n/P) is valid since each N(P) is valid, but it loses a loglog factor. | This defeats naive induction on n. | It does not rule out induction with cross-P consistency (ratio classes).
- **Layer counts grow with k.** The layer ω = k has size growing like L^{k−1}/(k−1)!. | This defeats layer-by-layer bounds unless the per-layer constants decay summably in k. | It does not rule out arguments in which cross-layer configurations dominate.
- **Density arguments stop at the sparse regime.** Pasch / box-theorem supersaturation needs positive density in a product grid 𝒳×𝒴×𝒵, but true extremal sets have relative density about 1/log n. | This limits removal and regularity arguments to o(n) or (log n)^{−c} bounds. | It does not rule out transference to a pseudorandom (Kubilius-model) host.

=== CORE
**What remains.** Since R5 settles the lower bound, CORE is the upper bound: F_sf(n) ≤ C·n·L/log n for valid squarefree A (by R3 this is the whole problem). Equivalently, by R4 and the smooth-number bound: squarefree P(a)-rough sets whose quadruples avoid triangle and K_{1,3} atom-supports have O(n·L/log n) elements.

**Why it is hard.**
- The forbidden patterns are sparse, non-uniform hypergraph configurations among integers with about L prime factors.
- The allowed C4 relations are abundant.
- The bound must be uniform across all Ω-layers and all log-log scales of the smallest prime factors.
- It must be sharp to within a constant at density 1/log n, which lies beyond dense-combinatorics tools.

=== TARGET T1
TYPE: SPECIAL
STATEMENT: If A is valid and consists of squarefree a ≤ n with ω(a) = 3, then |A| ≤ C·n·L/log n. Sharper conjecture: |A| ≤ (1/2 + o(1))·n·L/log n.
BEYOND: Only the trivial count of ω = 3 integers, ~ n·L²/(2 log n), is available. No layer bound is known (unless in ESS95).
VALUE: This is the first layer where the cross-P constraint must be used. It is the template for T5 and for CORE.
SIGNIFICANCE: 2
TEST: Compute the exact maximum for n ≤ 10^4–10^5 by ILP or SAT with bad quadruples from R4 as constraints. Check the ratio against n·L/log n, and the star-at-2 construction {2qP}.
REACH: medium

=== TARGET T2
TYPE: SPECIAL
STATEMENT: Let A be valid with P(a) > √n for every a ∈ A. Then |A| ≤ C·n·L/log n.
BEYOND: The trivial bound is about n·log 2. The cofactor family N(P) ⊆ [√n] must satisfy:
- each N(P) is valid;
- for P ≠ Q, if m1,m2 ∈ N(P), m3,m4 ∈ N(Q) and m1m2m3m4 is a square, then m1m4 = m2m3 or m1m3 = m2m4.

No bound exploiting this is known.
VALUE: It covers a positive proportion of all integers and isolates the alternating-C4 mechanism in a bipartite setting.
SIGNIFICANCE: 2
TEST: Run the ILP over pairs (m,P) with m ≤ √n. Fit the harmonic mass Σ_P |N(P)|·(log P)/n.
REACH: medium

=== TARGET T3
TYPE: STRUCTURE
STATEMENT: Every valid A ⊆ [n] has at most C·n/log n elements with ω(a) ≥ 3 and second-largest prime factor P₂(a) ≥ n^{δ}, where C = C(δ).
BEYOND: Integers with this property have positive density. No structural restriction on valid sets is known beyond R1.
VALUE: It shows the mass lives on "one large prime times a small cofactor". This reduces CORE to the cofactor-graph regime of T2/T1.
SIGNIFICANCE: 2
TEST: Run the ILP restricted to these integers for n ≤ 10^5.
REACH: medium

=== TARGET T4
TYPE: QUANT
STATEMENT: F(n) ≤ n/(log n)^{c} for some explicit c > 0.
BEYOND: The trivial bound is (6/π²)n. ESS-type o(N) results, if they apply, carry no polylog saving.
VALUE: Proof route:
- Use 3-partite Pasch supersaturation from R4 in factorisation grids a = xyz with x, y, z in dyadic ranges.
- Apply a density increment to obtain a polylog saving.

This is a first quantitative foothold.
SIGNIFICANCE: 1
TEST: Exact maxima for small n show the decay rate.
REACH: high

=== TARGET T5
TYPE: SPECIAL
STATEMENT: For each fixed k, valid A consisting of squarefree a with ω(a) ≤ k satisfies |A| ≤ C_k·n·L/log n. Ideally C_k is bounded independently of k.
BEYOND: This extends T1. Trivially the size is ≍ n·L^{k−1}/log n.
VALUE: With C_k uniform up to k ≈ 10L, together with the facts that ω > 10L is negligible and smooth numbers are negligible, this gives CORE.
SIGNIFICANCE: 2
TEST: ILP on layer-restricted universes.
REACH: medium

=== TARGET T6
TYPE: NEGATIVE
STATEMENT: Decide the natural strengthening F(n) ~ n·L/log n. Either construct valid A with |A| ≥ (1+δ)·n·L/log n, or prove F(n) ≤ (1+o(1))·n·L/log n within the class ω ≤ 3.
BEYOND: Only the ω ≤ 2 construction (constant 1) is known. Adding 2qP-type elements conflicts with semiprimes through alternating C4s, a degree-3 support, so the constant is genuinely unclear.
VALUE: This identifies the true constant and the extremal structure that guides the upper-bound proof.
SIGNIFICANCE: 2
TEST: Run a local search (simulated annealing or ILP) seeded with {ω ≤ 2}, allowing removal of edges pq for small p in exchange for triples.
REACH: medium

=== TARGET T7
TYPE: ANALOGUE
STATEMENT: For fixed q, the largest set of monic squarefree polynomials of degree ≤ n over F_q satisfying the condition has size Θ(q^n·log n/n). The integer order is replaced by degree plus lexicographic order, or the condition is used in the ordering-free form R2.
BEYOND: Unstudied. The irreducible-factorisation statistics are exact there, removing the analytic error terms.
VALUE: It tests the weighted alternating-C4 lemma cleanly, and the proof should transfer.
SIGNIFICANCE: 1
TEST: Exact search for q = 2, n ≤ 14.
REACH: medium

=== TARGET T8
TYPE: CONDITIONAL
STATEMENT: No standard arithmetic conjecture (GRH, Elliott–Halberstam, Hypothesis H, abc) is relevant, since all number-theoretic inputs needed are unconditional. Conditional version: assume hypothesis WZ, stated below. Then the full Θ statement holds, and the implication is proved.

Hypothesis WZ: let (G_P), indexed by primes P, be families of squarefree cofactors m ≤ n/P satisfying the T2 cross-consistency and per-P validity. Then Σ_P Σ_{m∈G_P} 1 ≤ C·(n/log n)·Σ_{p≤n} 1/p.
BEYOND: There is no conditional result at all.
VALUE: It isolates the single combinatorial input, a weighted Zarankiewicz-type statement, and delivers the full statement modulo it.
SIGNIFICANCE: 2
TEST: Verify WZ numerically on ILP optima.
REACH: medium

=== TARGET T9
TYPE: REDUCTION
STATEMENT: Prove the implication: CORE follows from the per-scale statement X below.

X: for every valid A and every y ∈ [2, n], #{a ∈ A : P(a) ∈ (y, 2y]} ≤ C·n/(log 2y · log(2n/y)).

Summing over dyadic y gives O(n·L/log n): the sum Σ_k 1/(k(log n − k)) ~ 2L/log n. Each element is counted once.
BEYOND: X is not equivalent to CORE; it is a stronger, local statement. It lets each scale y be attacked separately: for y near n the cofactors are tiny, and for y ≤ √n Pasch-type tools apply.
VALUE: It splits CORE into independent single-scale problems for different sub-teams.
SIGNIFICANCE: 2
TEST: Check X on ILP optima for each dyadic y.
REACH: high

=== TARGET T10
TYPE: QUANT
STATEMENT: F(n) ≤ n·(log log n)^{C}/log n for some absolute C.
BEYOND: Nothing better than o(n), or than T4, is known.
VALUE: This brings the bound within polyloglog of the truth, the first bound of the correct log-shape. Only constant- and loglog-level losses would remain.
SIGNIFICANCE: 3
TEST: none
REACH: low

=== ANGLE A1
TECHNIQUE: Largest-prime decomposition plus harmonic-weighted alternating-C4 Zarankiewicz bound (Erdős's graph method, reweighted).
IDEA:
- Write a = mP and form the bipartite structure (m, P).
- Classify each "cherry" (P; m1, m2) by the class κ = ker(m1m2) and the ratio ρ = m1/m2.
- Cross-consistency says: if a class κ occurs under two different P, then all those occurrences have the same ρ up to inversion.
- Count cherries with weights 1/m via Cauchy–Schwarz against the number of (κ, ρ) classes, giving Σ_P |N(P)| ≪ (n/log n)·Σ 1/p.

BARRIERS: It beats the weight-concentration barrier by weighting by 1/m. It is immune to the abundant-relations barrier because only cross-P inconsistent cherries are charged.
FIRST STEP: Ω = 3 lemma. Let G_P be graphs on primes such that no 4-cycle alternates between G_P and G_Q for P ≠ Q. Then Σ_P Σ_{pq∈G_P, pqP≤n} 1 ≤ (1/2 + o(1))·n·L/log n.

=== ANGLE A2
TECHNIQUE: Sparse hypergraph supersaturation for the Pasch configuration, with transference to the Kubilius random-factorisation model. Not used in KNOWN.
IDEA:
- By R4, valid A contains no bad support: no Pasch pattern {x1y1z1, x1y2z2, x2y1z2, x2y2z1} and no star or triangle pattern.
- Model integers in [n] as random multisets of primes (Kubilius model), which is pseudorandom.
- Prove a relative Pasch-removal / containers statement: a subset of density ε relative to the "≥ 3-factor" host forces many Pasch copies, unless it concentrates on ω ≤ 2 elements.

BARRIERS: It must beat the sparse-regime barrier. Transference (Green–Tao dense model, or Conlon–Fox–Zhao relative removal) is exactly designed for that.
FIRST STEP: Dense case: for squarefree 𝒳, 𝒴, 𝒵 in fixed dyadic ranges and pairwise coprime, any set S of δ|𝒳||𝒴||𝒵| products xyz contains ≫ δ^{C}|𝒳|²|𝒴|²|𝒵|² 3-partite Pasch copies. Then compute the host's linear-forms conditions.

=== ANGLE A3
TECHNIQUE: Quadratic large sieve (Heath-Brown) comparing mod-squares energy with multiplicative energy. Not used in KNOWN.
IDEA:
- Let Q(A) = #{(a,b,c,d) ∈ A⁴ : abcd a square} = Σ_κ R(κ)², and E(A) = #{ab = cd}.
- Validity forces Q(A) ≤ 3E(A).
- Expand 1_{square} via Jacobi symbols χ_m and bound Q(A) − E(A) from below, using the fact that kernel collisions ker(ab) = ker(cd) with ab ≠ cd come from gcd structure.
- Show the inequality fails once |A| ≫ n·L/log n.

BARRIERS: It sidesteps the abundant-relations barrier by counting relations exactly, with no existence argument. It must control E(A) for sets denser than almost-primes.
FIRST STEP: For squarefree A, prove the identity Q(A) − E(A) = Σ #{(a,b,c,d) : ab/gcd(a,b)² = cd/gcd(c,d)², ab ≠ cd}. Lower-bound it in terms of Σ_g |A ∩ gℕ|², which tends to be large when many elements share a factor g, as for ω ≥ 3 sets.

=== ANGLE A4
TECHNIQUE: Entropy / Shearer inequalities on a uniformly random element of A. Not used in KNOWN.
IDEA:
- Take a uniform random a ∈ A, so H(a) = log|A|.
- Decompose a into its ordered prime factors and the cofactor m = a/P(a).
- The absence of alternating C4s gives an entropy inequality, as in the entropy proof of Kővári–Sós–Turán, between H(P | m) and H(m).
- Compare with the maximum-entropy factor distribution of [n], where H(P | m) ≤ log(n/m) − log log(n/m) + O(1). This forces H(m) ≤ log L + O(1).

BARRIERS: Entropy is natively weighted, which beats the weight-concentration barrier. It is layer-uniform, which beats the layer-count barrier.
FIRST STEP: Prove the entropy form of T1. For a uniformly random element pqP of a valid ω = 3 set, show I(pq ; P) ≥ H(pq) − log(L) − O(1).

=== ANGLE A5
TECHNIQUE: Scale-by-scale induction with ratio-class bookkeeping, implementing the reduction T9.
IDEA:
- At scale y, the elements with P(a) ∈ (y, 2y] give cofactor sets N(P) ⊆ [n/y].
- Prove X by induction on n/y, feeding in the bound for the cofactor sets.
- Pay for the overlap between different P only through ratio classes. Each class κ is charged once globally, not once per P, which removes the loglog loss of F(n) ≤ Σ_P F(n/P).

BARRIERS: Its sole purpose is to beat the recursion barrier, using cross-consistency as the saving.
FIRST STEP: For y ≥ n^{1−ε}, so cofactors m ≤ n^{ε}, prove #{a : P(a) ∈ (y, 2y]} ≤ (1+o(1))·(y/log y)·#{valid cofactor sets}-weight. Then show it is ≤ C·n/(log y·log(n/y)).

=== ANGLE A6
TECHNIQUE: Computer-assisted extremal discovery plus an LP/flag-style relaxation over "configuration densities" in the random-factorisation model. Not used in KNOWN.
IDEA:
- Compute exact optima (ILP with R4 constraints) for n ≤ 10^5 to discover the extremal structure, which resolves T6 empirically.
- Then write an LP whose variables are the weighted densities of local cofactor patterns, with constraints from the bad supports. Solve it to certify a constant C.
- Convert the dual certificate into a proof.

BARRIERS: A dual certificate is a weighted counting argument and is not subject to the abundant-relations barrier. The sparse-regime barrier is avoided because constraints are imposed on weighted local densities directly, not via dense regularity.
FIRST STEP: Run the ILP for n = 2000, 5000, 20000 on squarefree universes. Record the optimum, its ω-profile and its P₂-profile. Test the conjecture that the ω ≥ 3 part of an optimum has harmonic mass ≤ 1/2·L.

## Deep dive

GOAL: **Primary target.** Prove the scale-uniform window bound X̃.

Notation:
- P(a) is the largest prime factor of a.
- N_y(A) = #{a∈A : P(a)∈(y,2y]}.
- L = ln ln n.

**(X̃)** There is an absolute constant C such that for every n, every valid squarefree A ⊆ [1,n] and every y ∈ [2,n]:

  N_y(A) ≤ C·n / ( ln(2y) · min(ln 2y, ln(2n/y)) ).

So for y ≥ √n it is the team's hypothesis X, and for y ≤ √n it only asks for C·n/(ln y)². That is weaker than X by the factor ln n/ln y.

**X̃ implies CORE.** Split A by the size of P(a):
- **Elements with P(a) ≤ n^{1/(3L)}.** These are smooth, so there are at most n/(log n)^{3+o(1)} of them.
- **Windows with y ∈ [n^{1/(3L)}, √n].** Summing over dyadic y gives Σ_{j ≥ log₂n/(3L)} C·n/(j ln 2)² = O(n·L/log n).
- **Windows with y ≥ √n.** Summing over dyadic y gives Σ C·n/(ln y·ln(n/y)) = O(n·L/log n).

R3 transfers the bound to all valid A. With R5 this gives the full Θ statement in the Lean theorem, i.e. significance 3.

**Equivalent form.** X̃ is the same as proving X on y ≥ n^δ with constant C(δ) = O(1/δ). Each block δ ∈ [2^{-k-1}, 2^{-k}] then costs O(2^k·n/log n), and the blocks sum to O(n·L/log n).

**Graded fallbacks.**
- **C(δ) = O(δ^{-c}) for some fixed c.** This gives F(n) = O(n·L^{max(1,c)}/log n), a near-optimal upper bound. That is significance 2, provided step 0 confirms the published bound is weaker.
- **Fixed δ.** This gives: for every fixed δ, at most O_δ(n·L/log n) elements of any valid A have P(a) > n^δ. Add the sharp top range: at most (1+o(1))·n·L/log n elements have P(a) > √n·(log n)^4.

## Research program

1 cycle(s), $2.7426; stopped: every lemma established.

TARGET (TRUE): The formal statement `erdos_41635` holds. Write

- f(n) := Nat.findGreatest (p n) n,
- g(n) := n·ln ln n / ln n.

Then f =Θ[atTop] g as real functions. Explicitly, there exist constants 0 < c ≤ C and N₀ such that c·g(n) ≤ f(n) ≤ C·g(n) for all n ≥ N₀.

- **L1** [established] There is an absolute constant C such that every A ⊆ [1,n] satisfying RequiredCondition has
|A| ≤ C·n·loglog n/log n (n ≥ 16). Together with R5: max|A| = Θ(n loglog n/log n).
- **L2** [established] For n ≥ 1, let S_n := {pq ≤ n : p < q primes}. Then S_n satisfies RequiredCondition S_n n. That is:
- S_n ⊆ Ioc 0 n;
- for all a, b, c, d ∈ S_n (repetitions allowed) with a ≤ b ≤ c ≤ d and abcd a perfect square, ad = bc.
- **L3** [established] There is N₀ such that for all n ≥ N₀,
|S_n| ≥ (1/2)·n·ln ln n / ln n.

GLUE:

**Step 0: f(n) is the maximum valid cardinality.**
- p n 0 holds, witnessed by A = ∅.
- Any A with RequiredCondition A n satisfies A ⊆ Ioc 0 n, so |A| ≤ n.

Hence Nat.findGreatest (p n) n is the largest k with p n k. Two consequences follow:
- By Nat.findGreatest_spec, there is a valid A with |A| = f(n).
- By Nat.le_findGreatest, f(n) ≥ k for every k ≤ n with p n k.

**Upper bound.** Let A be the valid set with |A| = f(n). By L1, for n ≥ 16,
f(n) = |A| ≤ C·g(n).

**Lower bound.**
- By L2, S_n is valid, so p n |S_n| holds.
- |S_n| ≤ n, since S_n ⊆ Ioc 0 n.
- Therefore f(n) ≥ |S_n|.
- By L3, |S_n| ≥ (1/2)·g(n) for n ≥ N₀.

**Positivity.** For n ≥ 16 we have ln n > 0 and ln ln n ≥ ln ln 16 > 0. So g(n) > 0 and f(n) ≥ 0, and the norms in IsBigO are just f and g.

**Conclusion.** For all n ≥ max(16, N₀), (1/2)·g(n) ≤ f(n) ≤ C·g(n). This gives:
- f =O[atTop] g, with constant C;
- g =O[atTop] f, with constant 2.

That is f =Θ[atTop] g, which is the formal statement.
