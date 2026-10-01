# Literature library (papers dated before 2025-08-25; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## The distribution of integers with a divisor in a given interval (2008)
https://doi.org/10.4007/annals.2008.168.367; full text: yes

**Verdict: the paper is essentially not relevant.** It studies how often integers n ≤ x have a divisor in an interval (y, z]. That is, it gives order-of-magnitude estimates for H(x,y,z) and H_r(x,y,z). It never considers sums of 1/(d_j − d_i) over pairs of divisors, or over consecutive divisors. It gives no deterministic inequality valid for every n. Its results are averages over n. At most, the following tools about the spacing of divisors might be peripheral ingredients.

**Possibly useful statements (quoted)**

1. **Lemma 7.1 (consecutive divisors).** "Let n have prime factorization n = p_1^{e_1}⋯p_f^{e_f}, where p_1 < ⋯ < p_f. Let N = τ(n), 1 ≤ ℓ ≤ N−1 and define v uniquely by (e_1+1)⋯(e_{v−1}+1) | ℓ, (e_1+1)⋯(e_v+1) ∤ ℓ. Then d_{ℓ+1}(n)/d_ℓ(n) ≤ p_v."
   - Proof: induction on f. The divisors are split according to the exact power of p_{m+1} they contain, and the induction hypothesis is applied to h = n/p_{m+1}^{e_{m+1}}.
   - The paper's remark says this is nearly sharp when p_i > p_{i−1}^4, which gives d_{ℓ+1}/d_ℓ ≥ p_v^{2/3}.
   - This is a deterministic bound on ratios, not differences, of consecutive divisors.

2. **Lemma 7.2.** "Fix ℓ ≥ 1. Uniformly in x ≥ 1, y ≥ 4, Σ_{P⁺(n)≤y, n≥x, τ(n)≥ℓ+1} log(d_{ℓ+1}(n)/d_ℓ(n))/n ≪_ℓ (log y)(log log y)^{ν(ℓ)+1} exp(−log x/(4 log y))."
   - Proof: Lemma 7.1, combined with Lemmas 2.2 and 2.5 (Rankin-type bounds).

3. **Close-pair and isolated-divisor counts.**
   - "W(a;σ) = |{(d_1,d_2) : d_1|a, d_2|a, |log(d_1/d_2)| ≤ σ}|" (Hall).
   - "I(n;σ) = |{d|n : τ(n, de^{−σ}, de^{σ}) = 1}|".
   - **Lemma 4.5:** "I(a;σ)^r ≥ 2^{−r}τ(a)^{r−1}(3τ(a) − 2W(a;σ))." Proof: elementary counting of pairs of divisors.
   - **Lemma 4.7** bounds Σ_{a∈A(b)} W(a;σ)/a. Proof: case analysis on the largest index where the two divisors differ, using Lemma 2.1 (Brun–Titchmarsh) and Lemma 2.2 (Mertens).
   - These count pairs of divisors at multiplicative distance at most σ. That is loosely analogous to controlling a pair sum by a near-neighbour sum, but only on average over a, and on a logarithmic scale.

4. **Lemma 3.1 (deterministic).** It concerns L(a;σ) = meas{x : τ(a, e^x, e^{x+σ}) ≥ 1}. Examples:
   - "L(a;σ) ≤ min(στ(a), σ + log a)".
   - "If (a,b)=1, then L(ab;σ) ≤ τ(b)L(a;σ)".
   - "If γ ≤ σ, L(a;σ) ≤ (σ/γ)L(a;γ)".
   - "L(p_1⋯p_k;σ) ≤ min_{0≤j≤k} 2^{k−j}(log(p_1⋯p_j)+σ)."
   - Proof: L(a;σ) is a union of intervals [log d − σ, log d) over d | a.

5. **Constants.** δ = 1 − (1+log log 2)/log 2 = 0.086071…; β = log 4 − 1 + ξ/√(log log y); G(β) as in (1.3). None of these bears on the problem.

**Open questions stated in the paper** (none is close to the problem):
- (i) Strengthen Theorem 1 to an asymptotic formula.
- (ii) Determine the order of H_r for r ≥ 2 and z ≥ y^C.
- (iii) Establish the order of H_r when yz ≥ x^{1−c}.
- (iv) Make the dependence on r explicit in Theorem 5 and Corollary 7; the Hall–Tenenbaum conjecture lim ε_r(y,2y)/ε(y,2y) = d_r > 0.
- (v) Lower bounds for H(x,y,z;P_λ) of the expected order.
- End of §5: H_r/x ≍ Q_r(log log y, log log z)/log z for y^{10} ≤ z ≤ x^{1/2}, for some polynomial Q_r.

**Bottom line:** none of these addresses the asked inequality directly. Lemma 7.1 is the only deterministic structural fact about gaps between consecutive divisors that might be adapted.

## Equal sums in random sets and the concentration of divisors (2023)
https://doi.org/10.1007/s00222-022-01177-y; full text: abstract only

**Source limitation.** Only the abstract was supplied, so no theorem numbers, lemma statements, proofs or open-question lists are available. Everything below comes from the abstract alone.

**Relevance verdict.** Probably not directly relevant. The problem is a deterministic statement for *every* n. It compares the sum of 1/(d_j − d_i) over all pairs of divisors with the same sum over *consecutive* divisor gaps. The paper studies how divisors of a *typical* n cluster on a logarithmic scale. It gives no statement about additive gaps d_{i+1} − d_i and no inequality of the problem's shape. At most it gives background on how many divisors can crowd into a short log-interval, which bears on how many pairs (i, j) have d_j/d_i close to 1.

**Statements quoted from the abstract**

1. **Definition.** Δ(n) := max_t #{d | n : log d ∈ [t, t+1]}. This is the Hooley-type divisor concentration function.

2. **Main theorem (almost all n).** "Δ(n) ⩾ (log log n)^{0.35332277…} for almost all n."
   - The authors call this bound "we believe to be sharp".
   - It "disproves a conjecture of Maier and Tenenbaum".
   - Method, as far as the abstract says: a reduction to a random-set combinatorial problem (item 4), solved by an optimisation over measures. The details of the reduction are not given.

3. **Analogues.** The paper proves corresponding concentration results for:
   - the divisors of a random permutation;
   - the divisors of a random polynomial over a finite field.

4. **Combinatorial core ("equal sums in random sets").**
   - Choose a random set **A** ⊂ ℕ, with each i included independently with probability 1/i.
   - β_k is the supremum of exponents such that, almost surely as D → ∞, some integer is a sum of elements of **A** ∩ [D^{β_k}, D] in k different ways.
   - **Result:** β_k is characterised as "the solution to a certain optimisation problem over measures on the discrete cube {0,1}^k".
   - **Result:** lower bounds for β_k are obtained, which the authors "believe to be asymptotically sharp".
   - Method: probabilistic and combinatorial, via that optimisation problem. The precise formulation and the constants for each k are not in the abstract.

**Constants.** The only explicit constant is the exponent 0.35332277… in the bound for Δ(n). Its defining formula is not given in the abstract.

**Open questions close to the problem.** None are stated in the abstract. It contains only two belief claims:
- the 0.35332277… exponent is sharp;
- the lower bounds for β_k are asymptotically sharp.

Neither concerns all n, or sums of reciprocal divisor differences.

**Possible tangential use.** Δ(n) controls how many divisors lie within a constant factor of each other. If you split the pair sum by the size of d_j/d_i, the pairs with d_j ≤ e·d_i are counted by quantities like Δ(n). However:
- the paper's results concern typical n, not worst-case n;
- they give lower bounds on concentration, whereas a proof of the inequality would need upper-bound control relative to the consecutive-gap sum.

So it is unlikely to supply a usable ingredient. The full text would need checking for any deterministic lemmas on divisor clustering.

## PRACTICAL NUMBERS AND THE DISTRIBUTION OF DIVISORS (2015)
arXiv 1405.2585 (version 1); full text: yes

**Verdict: essentially not relevant.** The problem asks for a pointwise inequality, for every single $n$, about the sum of $1/(d_j-d_i)$ over all pairs of divisors versus consecutive pairs. The paper works with ratios $d_{i+1}/d_i$, not differences. Its results are counting statements: how many $n\le x$ have maximal consecutive-divisor ratio at most $t$. Nothing in it bounds sums of reciprocal divisor gaps.

**Possibly usable structural facts:**

1. **Tenenbaum [12, Lemma 2.2]**, quoted in the paper:
   $$\max_{1\le i<\tau(n)} \frac{d_{i+1}(n)}{d_i(n)} = \frac{F(n)}{n}\quad (n\ge2),\qquad F(n)=\max\{d\,P^-(d): d\mid n,\ d>1\}.$$
   Equivalently, for $n=p_1^{\alpha_1}\cdots p_k^{\alpha_k}$ with $p_1<\dots<p_k$:
   $$\frac{F(n)}{n}=\max_{1\le j\le k}\frac{p_j}{\prod_{1\le i\le j-1}p_i^{\alpha_i}}.$$
   So the maximal ratio is at most $t$ if and only if $p_j\le t\prod_{i<j}p_i^{\alpha_i}$ for all $j$. The paper cites this; it does not prove it. This is the only pointwise fact about divisor spacing in the paper. It might help to split $n$ into a "dense-divisor" part and a remaining part, but that use is mine, not the paper's.

2. **Image set** (Section 4): $\{F(n)/n: n\ge2\}=S:=\{p/m: p \text{ prime},\ m\ge1,\ F(m)\le p\}$. The proof is elementary, by direct manipulation of the formula above. The paper also shows that if $p/m\in S$ then $F(mp)=p^2$.

3. **Lemma 3** (unique factorisation, elementary). If $\theta(n)\ge P^+(n)$, every $m\le x$ factors uniquely as $m=nr$ with $n\in\mathcal B$ and $P^-(r)>\theta(n)$. This gives
   $$[x]=\sum_{n\le x}\chi(n)\,\Phi(x/n,\theta(n)).$$

**Counting results** (irrelevant to a pointwise bound, listed for completeness):

- **Saias, eq. (2):** $D(x,t)\asymp x\log t/\log xt$ for $x\ge1$, $t\ge2$.
- **Theorem 3:** $D(x,t)=x\big(\alpha(t)d(v)+\frac{C\beta(t)}{v+1}\big)\big(1+O(1/\log 2x)\big)$, where $v=\log x/\log t$.
  - Constants: $C=(1-e^{-\gamma})^{-1}=2.280291\ldots$; $\alpha(t)=1+O(1/\log t)$; $\beta(t)=O(1/\log t)$.
  - Method: the functional equation of Lemma 3, Buchstab-function estimates (Lemmas 1–2), partial summation, and Laplace transforms of a renewal-type integral equation.
- **Theorems 1, 2, 4:** practical numbers satisfy $P(x)=\frac{cx}{\log x}\big(1+O(\frac{\log\log x}{\log x})\big)$. Theorems 2 and 4 generalise this to a broader $\theta$. Same method.
- **Corollary 4:** $M(x,p/m)\asymp x/(pm\log x)$ for $p^{3+\varepsilon}m\le x$. Consequently $C(t)$ is discontinuous at every point of the dense set $S$.

**Open questions stated:** none. The paper says it settles Margenstern's conjecture and a conjecture from [18], and confirms a speculation from [17]. It poses no new problems, and none concerns divisor differences or reciprocal-gap sums.

**Bottom line:** at most, item 1 gives a combinatorial description of when consecutive divisors are multiplicatively close. There are no tools here for comparing $\sum_{i<j}1/(d_j-d_i)$ with $\sum_i 1/(d_{i+1}-d_i)$.

## The number of prime factors of integers with dense divisors (2021)
arXiv 2101.11585 (version 1); full text: yes

**Verdict: essentially not relevant.**

The problem asks for a deterministic inequality, valid for every $n$, comparing the sum of reciprocal differences over all pairs of divisors with the sum over consecutive divisors. The paper is about something else. It studies the average and normal order of $\omega(n)$, $\Omega(n)$ and $\tau(n)$ on sets of integers with dense divisors. It contains no result on reciprocal gaps $1/(d_j-d_i)$, on sums over pairs of divisors, or on any pointwise inequality for all $n$.

**Only tangential material**

- **Definition.** "$n$ is $t$-dense if the ratios of consecutive divisors of $n$ do not exceed $t$." This is a condition on consecutive-divisor ratios, not differences.
- **Structural criterion, from (3) with $\theta(n)=nt$.** $n=p_1^{\alpha_1}\cdots p_k^{\alpha_k}$ is $t$-dense iff $p_i \le t\,p_1^{\alpha_1}\cdots p_{i-1}^{\alpha_{i-1}}$ for $1\le i\le k$.
- **Equivalent criterion (proof of Lemma 8).** "$n\in D_m(x,t)$ if and only if $n\le x$, $m\mid n$ and $F(n)\le nt$", where for $n=p_1\cdots p_k$ with $p_1\le\dots\le p_k$,
  $F(n):=\max_{1\le j\le k} p_j^2 p_{j+1}\cdots p_k$.
  The paper also notes that $m\mid n$ implies $F(m)\le F(n)$. Method: elementary.
- **Lemma 9.** "If $F(n)\le x$, then $p_{k-j+1}\cdots p_k\le x^{1-2^{-j}}$ for $1\le j\le k$." Method: induction on $j$.
- **Lemma 6.** $D(x,t)\asymp x\log t/\log xt$, and $D(x/q,t)-D(q/t,t)\le D_q(x,t)\le D(x/q,qt)$. The first estimate is cited from Saias; the second is elementary.

These describe when consecutive divisor ratios are bounded. They give no control on additive gaps $d_{i+1}-d_i$, so I see no direct route from them to the problem.

**Main results, listed only for completeness**

- **Theorem 1.** For $t$-dense $n\le x$, the mean of $\omega(n)$ is $E(x,t)=C\log_2x-(C-1)\log_2 t+O(1)$, with $C=(1-e^{-\gamma})^{-1}=2.280\ldots$. There is also a Turán–Kubilius type variance bound. The method is a second-moment computation.
- **Theorem 2.** $D_q(x,t)=x\,d(v)\,\eta_{q,t}(1+\dots)$, with $q^{-1}\ll\eta_{q,t}\ll_k q^{-1}$. This uses:
  - the counting identities (27)–(28) for multiples of $q$ (Lemma 2, proved by induction and telescoping);
  - the Dirichlet-series identities (30)–(31), (33)–(34) (Lemmas 3–4);
  - Buchstab-function estimates for $\Phi(x,y)$ (Lemma 5);
  - the integral-equation machinery of Lemma 7, built on the delay-differential function $d(v)$ in (11).
- **Theorem 3.** Asymptotics for the constants $c_q$ and $c_{pq}$, obtained via the identity (34) and limits as $s\to1^+$.
- **Corollaries 1–5.** Applications to practical numbers: Margenstern's Conjecture 5 is disproved, the exponent $\delta$ in his Conjecture 4 is placed in $[0.580\ldots,0.884\ldots]$, and lower bounds are improved for practical shifted primes ($(\log x)^{-3.01712}$) and twin practical numbers ($(\log x)^{-8.32231}$).
- **Lemma 1.** A bound for $\sum_{n\le x,\ \Omega(n)\ge\alpha\log_2x}\tau(n)$, proved by Rankin's trick.

**Open questions stated in the paper close to the problem:** none. The only conjectures mentioned are Margenstern's Conjectures 4 and 5 on practical numbers. The paper disproves Conjecture 5 and constrains Conjecture 4; neither concerns divisor differences.

## Erdős and the Integers (1999)
https://doi.org/10.1006/jnth.1999.2395; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## An introduction to the theory of numbers (1929)
https://doi.org/10.1090/s0002-9904-1929-04793-1; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)
