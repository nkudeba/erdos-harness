# Literature library (papers dated before 2026-03-27; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## Sumsets of Sidon sets (1996)
https://doi.org/10.4064/aa-77-4-353-359; full text: yes

# What Ruzsa, "Sumsets of Sidon sets" (Acta Arith. 77.4, 1996) offers for the isolated-sums problem

**Relevance: indirect.** The paper studies two features of A+A for a Sidon set A ⊂ [1,N]: the longest interval it contains, and its largest gaps. It never counts isolated elements of A+A, meaning a with a±1 ∉ A+A. Its constructions are mainly useful as test cases: Sidon sets whose sumsets are very "clustered" or "dense", against which a proof of the problem must hold.

**Prior results quoted from Erdős–Sárközy–Sós, refs [1, 2]:**
- A+A cannot contain an interval longer than C√N.
- An interval of length N^{1/3} is possible.
- A+A contains gaps longer than c log N.
- The maximal gap may be of size O(√N).

**Lemma 2.1 (the common Erdős–Turán ingredient).** "If p is a prime and i, j, k, l are integers such that i+j ≡ k+l (mod p) and i²+j² ≡ k²+l² (mod p), then either i ≡ k and j ≡ l, or i ≡ l and j ≡ k."

**Theorem 2.2.** "Let c be a positive number, c < 1/√54. For sufficiently large N there is a Sidon set A ⊂ [1,N] of integers such that A+A contains an interval of length c√N."
- Construction: p is the largest prime below √(2N/3) − 4, a_i ≡ i² (mod p), and q = 2[p/4]+1.
  - s_i = 2i + q a_i and t_i = N − i − q a_i, for p/6 < i < p/3.
  - A = A₁ ∪ A₂, with A₁ = {s_i} and A₂ = {t_i}.
  - Then s_i + t_i = N + i gives the interval.
- Method: case analysis on how a solution of x+y=u+v is split between A₁ and A₂. Size comparisons and reduction mod q bring each case back to Lemma 2.1.

**Theorem 3.1.** "For all sufficiently large N there is a Sidon set A ⊂ [0,N] with the property that A+A forms a CN^{1/3}-chain in the interval [0,2N]."
- Definition: a d-chain means every subinterval of length d meets the set.
- Construction: p is the smallest prime with 2p³ > 3N, and s_i = a_i + 2ip + 2b_i p², for 0 ≤ i ≤ p−1.
  - The set is Sidon for *any* choice of integers b_i, by comparing residues mod 2p and then applying Lemma 2.1.
  - The b_i are chosen according to i mod 3 so that the sums i+j+p(b_i+b_j) form an 18-chain.

**Construction behind Theorem 4.1.** q = p(p−1) and g is a primitive root. a_i is defined by a_i ≡ i (mod p−1), a_i ≡ g^i (mod p), 1 ≤ a_i ≤ q. B = {a_i} is a Sidon set mod q (cited from [4, Thm 4.4]).
- Each u with p ∤ u and (p−1) ∤ u is ≡ a_i − a_j (mod q) for exactly one pair (i, j). This is a counting argument.

**Lemma 4.2.** "For a suitable choice of g no interval of length M = φ(p−1)^{1/3} contains more than two numbers whose residues modulo q are elements of B."
- Method: three such elements force u(g^u − 1) ≡ v(g^v − 1) (mod p). Counting roots of this polynomial in g gives fewer than M³ bad g, out of φ(p−1) = M³ primitive roots.

**Theorem 4.1.** "For all c < 1/5 and sufficiently large N there is a Sidon set A ⊂ [0,N] with the property that A+A forms a C log N-chain in the interval [N,(1+c)N]."
- Construction: A = B₁ ∪ (B₂+q) ∪ (5q − B₃), where B is split into three parts uniformly at random and p is the largest prime with 5p(p−1) ≤ N.
- Method:
  - Sidon property: case analysis, with the mixed case reduced to the Sidon property mod q.
  - Each 5q+u lies in A+A with probability 1/9.
  - Lemma 4.2 bounds dependencies: at most 8 other numbers can spoil independence.
  - Greedy selection of ≈ t/9 independent candidates, then a union bound.

**Potential ingredients for the problem.**
- Lemma 2.1 and the "free parameter" family s_i = a_i + 2ip + 2b_i p², which stays Sidon for every b_i, are flexible tools for building Sidon sets with prescribed sumset structure. They could be used to probe how few isolated sums are possible.
- The ESS bound (no interval in A+A longer than C√N) constrains how much of A+A can sit in long runs.
- The exact-representation property of differences a_i − a_j mod q may help count sums with neighbours.

**Open questions stated in the paper.**
- After Lemma 4.2: "it is likely that other dense Sidon sets, constructed via finite fields, also have a similar property, we were unable to establish it."
- Implicitly, the gap question (between c log N and the N^{1/3} or local log N constructions) remains open over the whole interval [0,2N].
- None of these concerns isolated elements of A+A directly.

## Gaps in Dense Sidon Sets (2000)
https://doi.org/10.5281/zenodo.7554448; full text: abstract only

**Summary of "Gaps in Dense Sidon Sets" (2000-08-24) for the isolated-sums problem**

Only the abstract is available. This summary uses nothing beyond it.

**Relevance: low, at most indirect.**
- The problem is about every sufficiently large finite Sidon set. It asks for many sums $a \in A+A$ with both neighbours $a \pm 1 \notin A+A$.
- The paper only treats *dense* Sidon sets, those with $|A|$ close to $N^{1/2}$ inside $[1,N]$.
- Its results are about how $A$ itself is distributed in intervals. They say nothing directly about the structure of $A+A$ or about isolated elements of the sumset.
- An arbitrary large Sidon set need not be dense in $[1,\max A]$, so the paper's results do not apply in general.

**Statements quoted from the abstract**

1. **Interval distribution theorem.** "If $A \subset [1, N]$ is a Sidon set with $N^{1/2} - L$ elements, then any interval $I \subset [1, N]$ of length $cN$ contains $c|A| + E_I$ elements of $A$, with
$$|E_I| \le 52\,N^{1/4}\,(1 + c^{1/2} N^{1/8})\,(1 + (L^+)^{1/2} N^{-1/8}),\qquad L^+ = \max\{0, L\}."$$
   - The explicit constant is 52.
   - $L$ may be negative, which is why only $L^+$ enters the bound.

2. **Gap corollary.** "If $|A| = N^{1/2} + O(N^{1/4})$, and $g(A)$ is the maximum gap in $A$, we deduce that $g(A) \ll N^{3/4}$."
   - Method: this is deduced from statement 1.

3. **Sharpness.** "Under this condition, the exponent 3/4 is sharp."
   - Presumably this is shown by an explicit construction of dense Sidon sets with gaps of order $N^{3/4}$. The abstract does not describe the construction.

**Methods.** The abstract does not say how statement 1 or the sharpness claim is proved. I will not guess at the technique.

**Possible ingredients for a mathematician (heuristic only)**
- In the extremal regime $|A| \approx N^{1/2}$, statement 1 gives equidistribution of $A$ across intervals of length $cN$, with error about $N^{1/4}$.
- This could help control the local density of $A+A$ in dense cases. For example, one might use it to find regions where sums are sparse, and hence where isolated sums are likely.
- Any such use would cover only the dense sub-case. A separate argument would be needed for sparse or general Sidon sets.

**Open questions:** none are stated in the abstract. Since the full text is unavailable, I cannot list any open questions close to the problem.

## Additive Combinatorics: A Menu of Research Problems (2017)
arXiv 1705.07444 (version 1); full text: yes

# Relevance of Bajnok, *Additive Combinatorics: A Menu of Research Problems* (arXiv 1705.07444, May 2017) to the isolated-sums problem for Sidon sets

**Verdict: the supplied text is not relevant to this problem.**

## What the supplied text covers

The excerpt contains only:
- the front matter, preface and notation list;
- Chapter 1 (number theory);
- the start of Chapter 2 (combinatorics), cut off mid-exercise.

Chapter C ("Sidon sets", pp. 153–174) and its proofs (Propositions C.33, C.47, C.48) appear only as entries in the table of contents. None of their statements are in the supplied text, so I cannot quote them.

## Scope of the book

The book's stated scope rules out the problem's setting. The preface says: "In this book we interpret additive combinatorics, somewhat narrowly, as the study of sumsets in finite abelian groups. (A second volume, focusing on the set of integers and other infinite groups, is in the planning phase.)"

The problem concerns finite Sidon sets $A \subset \mathbb{N}$ and the local structure of $A+A$: elements $a$ with $a \pm 1 \notin A+A$. That is a question about integers, so it lies outside the book's declared scope.

## The only Sidon-related material present

The notation list defines the Sidon-type extremal function for unrestricted sums in a finite abelian group $G$:

$$\sigma(G,h) = \max\Big\{|A| : A \subseteq G,\ |hA| = |\mathbb{N}_0^m(h)| = \binom{m+h-1}{h}\Big\}.$$

- For $h=2$, the condition says that all sums $a_i + a_j$ ($i \le j$) are distinct, i.e. $|A+A| = m(m+1)/2$. This is the Sidon property, but inside a finite group $G$.
- Analogous functions are defined for:
  - interval sumsets: $\sigma(G,[0,s])$;
  - signed sumsets: $\sigma_\pm$;
  - restricted sumsets: $\hat\sigma$, including $\hat\sigma(G,\mathbb{N}_0)$ with $|\Sigma A| = 2^m$;
  - restricted signed sumsets: $\sigma^{\hat\pm}$.

These definitions only record that $|A+A|$ is maximal. They say nothing about gaps or isolated elements in $A+A$.

## Chapter 1 material

Chapter 1 gives exact results on the following arithmetic functions:
- $v_g(n,h)$: Theorem 1.4 (Bajnok–Butterworth), Corollary 1.5 ($\lfloor (n-1)/h\rfloor \le v_g(n,h) \le n/2$), and Theorems 1.6 and 1.7;
- $v_\pm(n,h)$: Propositions 1.12, 1.13 and 1.15;
- the Hopf–Stiefel variant $u(n,m,h)$: Proposition 1.18 ($m \le u(n,m,h) \le \min\{n, hm-h+1\}$);
- the restricted variant $\hat u(n,m,h)$: Propositions 1.25, 1.26, 1.32 and 1.34.

These quantities feed into minimum and maximum sumset sizes in cyclic groups $\mathbb{Z}_n$. The method is elementary divisor analysis; for example, Theorem 1.20 shows that the $h$-critical number of $n$ equals $v_1(n,h)+1$. None of this bears on isolated elements of $A+A$ for Sidon $A \subset \mathbb{N}$.

## Open questions stated in the supplied text

The stated open problems are Problems 1.8, 1.9, 1.14, 1.16, 1.21–1.24, 1.27, 1.33, 1.36 and 1.37. All concern the arithmetic functions $v_g$, $v_\pm$, $u$ and $\hat u$. None is close to the problem.

## Recommendation

If the full Chapter C text becomes available, it should be checked for Sidon results stated in $\mathbb{Z}_n$. Even then, those would at best transfer to $\mathbb{N}$ by embedding $A \subset [1,N]$ into $\mathbb{Z}_n$ with $n > 2N$. They would also concern $|A+A|$ or $|A|$ rather than the adjacency structure of $A+A$, so the problem would still need its own argument.

## On suprema of autoconvolutions with an application to Sidon sets (2017)
https://doi.org/10.1090/proc/13690; full text: abstract only

# Summary: "On suprema of autoconvolutions with an application to Sidon sets" (2017-02-23)

**Source limitation.** Only the abstract is available, so no lemma statements, constructions or proofs beyond it can be quoted.

## Main result (quoted from the abstract)

> Let $f$ be a nonnegative function supported on $(-1/4, 1/4)$. We show that
> $$\sup_{x\in\mathbb{R}}\int_{\mathbb{R}} f(t)f(x-t)\,dt \;\ge\; 1.28\left(\int_{-1/4}^{1/4} f(x)\,dx\right)^2,$$
> where 1.28 improves on a series of earlier results.

- **Constant:** $1.28$, a lower bound for the sup-norm of the autoconvolution $f*f$, normalised by $\|f\|_1^2$ with support length $1/2$.
- **Method (from the abstract):** a relaxation of the continuous problem that "reduces to a finite number of cases" and is settled by computer search. This relaxation "yields slightly stronger results" than the displayed inequality, but the abstract does not state them.
- The authors claim the approach "should be able to prove lower bounds that are arbitrary close to the sharp result." The bottleneck is runtime.

## Stated connection to Sidon sets

The abstract says only that "the inequality arises naturally in additive combinatorics in the study of Sidon sets." It does not say which Sidon-set statement is derived. Typically such inequalities give upper bounds on the size of generalised Sidon ($B_2[g]$-type) sets in $\{1,\dots,N\}$, but that is not stated here.

## Open questions stated

The abstract poses only the following, all about the analytic constant:
- What is the sharp constant in the autoconvolution inequality?
- Can new ideas significantly speed up the computation, so the method gets close to that sharp value?

It states no open question about the structure of $A+A$, gaps in sumsets, or isolated sums.

## Relevance to the problem

**Plainly: this paper appears not relevant**, or at best only tangentially so.

- The problem asks for a combinatorial fact about the fine structure of $A+A$ for a large finite Sidon set $A$: there are many sums $a$ with neither $a-1$ nor $a+1$ in $A+A$.
- The paper's result is an extremal bound on $\|f*f\|_\infty$. It concerns the maximum multiplicity of representations, and hence the size of sets with bounded representation counts.
- It says nothing, at least in the abstract, about the local distribution of elements of $A+A$ or about adjacency of sums.

**Possible indirect use.** A mathematician might borrow the general idea that a Sidon set cannot have its sumset "too concentrated." Continuous autoconvolution bounds encode that, but only for the supremum, not for local gap structure. Nothing quoted here gives a usable ingredient for counting isolated elements of $A+A$.

## Recommendation

Do not rely on this paper for the problem unless the full text turns out to contain discrete lemmas about the structure of $A+A$. The abstract gives no evidence that it does.

## Well Distribution of Sidon Sets in Residue Classes (1998)
https://doi.org/10.1006/jnth.1997.2217; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## Erdős and the Integers (1999)
https://doi.org/10.1006/jnth.1999.2395; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)
