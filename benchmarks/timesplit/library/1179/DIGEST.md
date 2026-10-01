# Literature library (papers dated before 2026-01-19; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## Expander graphs and their applications (2006)
https://doi.org/10.1090/s0273-0979-06-01126-8; full text: abstract only

**Summary for the subset-sum equidistribution problem ($g_\epsilon(N)$)**

**What text was available.** Only the abstract (introduction) of the survey "Expander graphs and their applications" (2006-08-07) was supplied. It contains no theorems, lemmas, constructions, constants, proof methods or open questions. Nothing can therefore be quoted as an ingredient, and I will not fill the gap from memory of the full survey.

**What the abstract says.** The excerpt is purely motivational:

- The survey aims to be "accessible to mathematicians as well as computer scientists."
- It includes "a glossary of some basic terms and facts from computer science."
- Graphs model structures in the sciences, computer science and mathematics. In particular: "In Mathematics, Cayley graphs are useful in Group Theory."
- "The property of being an expander seems significant in many of these mathematical, computational and physical contexts."
- Expanders are useful "in the design and analysis of communication networks."

**Relevance to the problem.**

- **Direct relevance: none.** The problem asks how large a random $k$-subset $A$ of an abelian group $G$ with $|G| = N$ must be for all subset-sum counts $F_A(g)$ to be within a factor $1 \pm \epsilon$ of $2^k/N$. In particular, it asks whether $g_\epsilon(N) = (1+o(1))\log_2 N$. The abstract states nothing about:
  - abelian groups;
  - random subsets;
  - subset sums;
  - characters or Fourier analysis;
  - any thresholds of the form $\log_2 N$.
- **Tangential link only.** The abstract mentions Cayley graphs and expansion. Subset-sum equidistribution is closely tied to how fast a random walk on the Cayley graph $\mathrm{Cay}(G, A)$ mixes, which is controlled by spectral expansion. But the supplied text contains:
  - no statement about random Cayley graphs;
  - no bounds on the number of generators needed for expansion;
  - no eigenvalue estimates for abelian groups;
  - no mixing-time results that could be adapted to $F_A$.

  Whether the full survey contains such results cannot be determined from the provided text.

**Theorems, lemmas, constructions, constants:** none in the supplied text.

**Proof methods:** none in the supplied text.

**Open questions stated that are close to the problem:** none in the supplied text.

**Recommendation.** Treat this entry as **not relevant** on the basis of the available text. If the full text becomes available, look for:

- statements on random Cayley graphs of (abelian) groups with about $\log |G|$ random generators;
- the spectral gap and mixing-time bounds attached to those statements, and their proof method (e.g. trace or moment method, or matrix concentration).

Then check whether those bounds are sharp enough to give multiplicative $(1 \pm \epsilon)$ control of every $F_A(g)$. That is a much stronger requirement than spectral expansion, which typically only controls $\ell_2$ or total-variation distance after a walk of many steps.

## Analysis of Boolean Functions (2014)
arXiv 2105.10386 (version 1); full text: yes

## Relevance

The book is only marginally relevant. The supplied text covers Chapters 1 and part of 2. It is generic Fourier analysis on $\mathbb{F}_2^n$: no random subsets, no subset sums, and no general abelian groups. Section 8.5, "Abelian groups", is listed in the table of contents but its text is not included. No result here bears directly on $g_\epsilon(N)$, and the excerpt states no open questions close to the problem.

## Possibly usable ingredients (all on $\mathbb{F}_2^n$)

**Densities (Def. 1.20).** A density is $\varphi:\mathbb{F}_2^n\to\mathbb{R}_{\ge0}$ with $\mathbb{E}[\varphi]=1$, and $\Pr_{y\sim\varphi}[y=y]=\varphi(y)/2^n$. The uniform density on $A$ is $\varphi_A=1_A/\mathbb{E}[1_A]$.

**Convolution as distribution of sums (Prop. 1.26).** "If $g=\psi$ is itself a probability density function then so is $\varphi*\psi$; it represents the distribution on $x\in\mathbb{F}_2^n$ given by choosing $y\sim\varphi$ and $z\sim\psi$ independently and setting $x=y+z$." The proof is direct from the definitions.

**Convolution theorem (Thm. 1.27).** "Let $f,g:\mathbb{F}_2^n\to\mathbb{R}$. Then for all $S\subseteq[n]$, $\widehat{f*g}(S)=\hat f(S)\,\hat g(S)$." The proof is a direct computation using $\chi_S(y+z)=\chi_S(y)\chi_S(z)$ and the independence of $y,z$.

**Link to the problem (my observation, not a statement in the text).** $F_A(g)/2^k$ is the law of $\sum_{x\in S}x$ for a uniformly random $S\subseteq A$. This is a $k$-fold convolution of the densities $\varphi_{\{0,a\}}$. Exercise 1.1(e) asks for the Fourier expansion of $\varphi_{\{a,a+e_i\}}$, but no answer is given.

**Point mass (Fact 1.23).** "Every Fourier coefficient of $\varphi_{\{0\}}$ is 1."

**Plancherel and Parseval.** $\langle f,g\rangle=\sum_S\hat f(S)\hat g(S)$. These follow from orthonormality of the characters (Thm. 1.5).

**Distances to uniform (Exercise 1.23, unproved exercises).**
- (a) $d_{TV}(\varphi,\psi)=\tfrac12\|\varphi-\psi\|_1$.
- (b) The collision probability equals $\|\varphi\|_2^2/2^n$.
- (c) The $\chi^2$-distance of $\varphi$ from uniform equals $\mathrm{Var}[\varphi]$, which is $\sum_{S\neq\emptyset}\hat\varphi(S)^2$ by Prop. 1.13.
- (d) $d_{TV}(\varphi,\text{uniform})\le\tfrac12\sqrt{\mathrm{Var}[\varphi]}$.

These give $L^1$ and $L^2$ control only. The problem needs a uniform pointwise relative bound $\epsilon\,2^k/N$. That would require an $L^\infty$ bound such as $|\varphi(g)-1|\le\sum_{S\ne\emptyset}|\hat\varphi(S)|$, by Fourier inversion. The text implies this bound but does not state it.

**Random function coefficients (Exercise 1.7).** For a random $f$, each $\hat f(S)$ has mean 0 and variance $2^{-n}$, by Parseval. This is a model for second-moment computations.

**Distance to linear functions (Prop. 1.9).** For Boolean $f,g$, $\langle f,g\rangle=1-2\,\mathrm{dist}(f,g)$.

## Constants and quantitative statements

None in the excerpt concern subset sums. Theorem 2.39 ($2\alpha\log(1/\alpha)\le I[f]$) and the noise-stability formulas (Thm. 2.49) are unrelated to the problem.

## Open questions

None are stated in the supplied text that relate to this problem.

## An Introduction to Matrix Concentration Inequalities (2015)
arXiv 1501.01571 (version 1); full text: yes

**Verdict: not relevant.** This monograph (Tropp, *An Introduction to Matrix Concentration Inequalities*, arXiv 1501.01571; the supplied text covers Ch. 1–3 and part of the Ch. 3 notes) is about spectral-norm and eigenvalue concentration for sums of independent random matrices. It contains nothing on:

- abelian groups,
- subset sums,
- random subsets of fixed size, or
- the quantity $g_\epsilon(N)$.

It also states no open question close to the problem. At most, a few generic concentration tools could be borrowed.

**Possibly usable generic tools (exact statements from the text)**

1. **Theorem 1.6.1 (Bernstein Inequality).** "Let $S_1,\dots,S_n$ be independent, centered, real random variables, and assume that each one is uniformly bounded: $\mathbb E S_k=0$ and $|S_k|\le L$ for each $k$. Introduce the sum $Z=\sum_k S_k$, and let $v(Z)=\mathbb E Z^2=\sum_k \mathbb E S_k^2$. Then $\mathbb P\{|Z|\ge t\}\le 2\exp\!\big(\frac{-t^2/2}{v(Z)+Lt/3}\big)$ for all $t\ge0$."
   - The paper gives no proof; it cites [BLM13, §2.8].
   - Caveat: the problem's $A$ is a uniform $k$-subset, so the indicators are not independent. Nothing in the text addresses sampling without replacement.

2. **Theorem 1.6.2 (Matrix Bernstein).** For independent centered $d_1\times d_2$ random matrices with $\|S_k\|\le L$, and $v(Z)=\max\{\|\sum\mathbb E S_kS_k^*\|,\|\sum \mathbb E S_k^*S_k\|\}$:
   - $\mathbb P\{\|Z\|\ge t\}\le (d_1+d_2)\exp\!\big(\frac{-t^2/2}{v(Z)+Lt/3}\big)$;
   - $\mathbb E\|Z\|\le\sqrt{2v(Z)\log(d_1+d_2)}+\tfrac13 L\log(d_1+d_2)$.
   - Method: matrix Laplace transform plus Lieb's theorem. The full proof is in Ch. 6, which is not in the supplied text.

3. **Proposition 3.2.1 (matrix Laplace transform / Markov).** $\mathbb P\{\lambda_{\max}(Y)\ge t\}\le\inf_{\theta>0}e^{-\theta t}\,\mathbb E\,\mathrm{tr}\,e^{\theta Y}$.
   - Proof: Markov's inequality, then bounding $\lambda_{\max}$ of $e^{\theta Y}$ by its trace.

4. **Theorem 3.4.1 (Lieb).** $A\mapsto \mathrm{tr}\exp(H+\log A)$ is concave on positive-definite matrices.
   - **Corollary 3.4.2:** $\mathbb E\,\mathrm{tr}\exp(H+X)\le \mathrm{tr}\exp(H+\log\mathbb E e^X)$, which follows from Lieb plus Jensen.
   - **Lemma 3.5.1:** $\mathbb E\,\mathrm{tr}\exp(\sum\theta X_k)\le\mathrm{tr}\exp(\sum\log\mathbb E e^{\theta X_k})$, by iterating Corollary 3.4.2.
   - **Theorem 3.6.1 (master bounds):** obtained by combining Lemma 3.5.1 with Propositions 3.2.1–3.2.2.

5. **Golden–Thompson (3.3.3).** $\mathrm{tr}\,e^{A+H}\le\mathrm{tr}\,e^Ae^H$. This can fail for three matrices.

None of these is specific to the problem. The scalar Bernstein bound with a union bound over $N$ group elements is the standard generic route. The paper does not discuss it, nor the multiplicative (non-additive) structure of $F_A(g)$.

**Open questions stated in the text**

- In §1.6.5, the paper notes a gap between the bounds const·$[v(Z)+L_\star^2]$ and Const·$[v(Z)\log(d_1+d_2)+L_\star^2\log^2(d_1+d_2)]$ on $\mathbb E\|Z\|^2$. It says "there is no method known for distinguishing between these two extremes."
- This concerns the sharpness of dimensional factors in matrix concentration. It is not close to the subset-sum equidistribution problem.

**Bottom line:** the paper offers generic concentration machinery only. It gives no constructions, constants or results bearing on $g_\epsilon(N)$ or on whether $g_\epsilon(N)=(1+o(1))\log_2 N$.

## Randomness-efficient low degree tests and short PCPs via epsilon-biased sets (2003)
https://doi.org/10.1145/780542.780631; full text: abstract only

**Relevance: essentially none, as far as the available text shows.** Only the abstract is available. It contains no theorem statements, lemmas, explicit constants or open questions, so there is nothing exact to quote beyond the abstract.

**What the abstract claims (quoted where possible):**

- **Main result.** "the first explicit construction of Probabilistically Checkable Proofs (PCPs) and Locally Testable Codes (LTCs) of fixed constant query complexity which have almost-linear (= n · 2^{Õ(√log n)}) size." Earlier explicit constructions "required size n^{1+Ω(ε)} with 1/ε queries." Goldreich–Sudan had shown such objects exist nonconstructively.
- **Key ingredient 1.** "a nearly optimal randomness-efficient version of the low degree test."
- **Key ingredient 2.** "a randomness-efficient version of the BLR linearity test," used for instance to locally test the Hadamard code.
- **Method.** "The derandomizations are obtained through ε-biased sets for vector spaces over finite fields."
  - For the low degree test, ε-biased sets are viewed "as generating sets of Cayley expander graphs."
  - For the linearity test, they are viewed "as defining linear error-correcting codes."

**Connection to the problem (weak, conceptual only):**

- The problem asks when the subset-sum counts F_A(g) of a random k-subset A of an abelian group G of order N are uniform within relative error ε. Expanding F_A in characters of G gives

  F_A(g) = (1/N) Σ_χ χ(g)^{-1} ∏_{x∈A} (1 + χ(x)).

  So uniformity amounts to Σ_{χ≠1} ∏_{x∈A} |1 + χ(x)| ≤ ε·2^k.
- This is a character-sum "bias" condition, which is the same flavour as the defining property of ε-biased sets. The Cayley-expander view of ε-biased sets mentioned in the abstract is also a Fourier/spectral statement.
- However, the paper as described:
  - works only over vector spaces 𝔽_q^m, not general abelian groups;
  - concerns explicit derandomization of tests, not random subsets or subset sums;
  - states no result about random sets, about subset sums, or about thresholds of the form log₂ N.

**Methods named:**

- Spectral analysis of Cayley graphs generated by ε-biased sets (for the low degree test).
- A coding-theoretic analysis of ε-biased sets as linear codes (for the linearity test).

No precise lemma or bound is given in the available text, so none can be quoted as an ingredient.

**Open questions:** none are stated in the available text. Nothing close to estimating g_ε(N), or to whether g_ε(N) = (1+o(1)) log₂ N, appears.

**Recommendation:** treat this paper as not relevant to the problem. At most it supplies background terminology (ε-biased sets, the expander and code viewpoints). Any useful quantitative lemma would have to come from the full text, which is not provided here, or from other sources.

## Uniform expansion bounds for Cayley graphs of SL 2 (𝔽 p ) (2008)
https://doi.org/10.4007/annals.2008.167.625; full text: yes

**Verdict: essentially not relevant.** The paper is about spectral expansion of Cayley graphs of the non-abelian group SL₂(𝔽_p). It contains nothing about abelian groups, subset sums $\sum_{x\in S}x$, sharp $\log_2 N$ thresholds, or $(1\pm\epsilon)$ uniformity of counts. Every key ingredient uses structure special to SL₂(𝔽_p) that abelian groups do not have:

- **Frobenius bound.** Every nontrivial irreducible representation has dimension $d_\rho \ge \frac{p-1}{2}$. For abelian $G$ all irreducible representations have dimension 1, so the multiplicity trick fails.
- **Helfgott's product theorem.** Abelian groups have no analogue.
- **Dickson's subgroup classification.**

**Results stated, with methods (only possible loose analogies):**

1. **Theorem 3.** "Fix $k\ge2$ and suppose that $S_p=\{g_1,g_1^{-1},\dots,g_k,g_k^{-1}\}$ is a symmetric generating set for SL₂(𝔽_p) such that girth$(G(\mathrm{SL}_2(\mathbb F_p),S_p))\ge\tau\log_{2k}p$… Then the $G(\mathrm{SL}_2(\mathbb F_p),S_p)$ form a family of expanders."
   - Method: the Sarnak–Xue argument.
   - It combines the high multiplicity of nontrivial eigenvalues with the trace formula $\sum_j\lambda_j^{2m}=NW_{2m}$.
   - It also uses the return-probability bound $W_{2l}<(2k)^{2l}/p^{3-2\varepsilon}$, which comes from Proposition 1.

2. **Proposition 1.** Under the girth condition, "for any ε>0 there is C(ε,τ) such that for $l>C(\varepsilon,\tau)\log_{2k}p$, $\|\mu_{S_p}^{(l)}\|_2<p^{-3/2+\varepsilon}$."
   - Method: iterate Proposition 2, starting from tree-like behaviour up to length $l_0$.
   - The starting point uses Kesten's bound $\tilde p^{(l)}(x,y)\le\left(\frac{\sqrt{2k-1}}{k}\right)^l$.
   - It also uses a free-group counting result, Proposition 8: a set in $\tilde W_k(2l_0)$ with trivial second commutators has size $<l_0^6$.

3. **Proposition 2 ($L^2$-flattening).** Take a symmetric $\nu$ with $\|\nu\|_\infty<p^{-\gamma}$, $\|\nu\|_2>p^{-3/2+\gamma}$, and $\nu^{(2)}[G_0]<p^{-\gamma}$ for every proper subgroup $G_0$. Then "$\|\nu*\nu\|_2<p^{-\varepsilon}\|\nu\|_2$."
   - Method, step 1: dyadic level-set decomposition $A_j=\{2^{-j}<\nu(x)\le2^{-j+1}\}$ with $J=10\log p$, then pigeonhole to get the energy bound $E(A,B)\ge p^{-4\varepsilon}|A|^{3/2}|B|^{3/2}$.
   - Step 2: Tao's non-commutative Balog–Szemerédi–Gowers theorem (Theorem 4) and the Ruzsa-distance/approximate-group equivalence (Theorem 5).
   - Step 3: Helfgott's theorem (Theorem 6), $|H\cdot H\cdot H|>c|H|^{1+\kappa}$ if $|H|<p^{3-\delta}$ and $H$ is not contained in a proper subgroup.

   The level-set and energy reduction is generic additive combinatorics. In an abelian group, however, the conclusion of the analogous argument would be "the measure concentrates on a coset of an approximate subgroup". That is a structural statement, not a sharp-constant estimate of the kind your problem needs.

4. **Supporting facts.**
   - Proposition 5 (from [8]): random $d$-regular Cayley graphs of SL₂(𝔽_p) have girth $\ge(1/3-o(1))\log_{d-1}|G|$ asymptotically almost surely. This is a non-abelian phenomenon; abelian Cayley graphs have girth at most 4.
   - Proposition 6: logarithmic girth implies generation for $p>d^{17/\tau}$.
   - Lemmas 1–2 on free groups: $u^k=v^k\Rightarrow u=v$, and commuting elements are powers of a common element.

**Constants.** None of the explicit constants is relevant to a sharp $(1+o(1))\log_2N$ threshold. They include $\gamma_1=\frac{\tau}{2}\log_{2k}(2k-1)$, $\gamma<3\tau/16$, and the girth exponent $1/3$. The expansion constant $\kappa(k)$ is ineffective.

**Open questions.** The paper states no open questions related to random subset sums or abelian groups. The only question it mentions is Lubotzky's 1-2-3 question, which concerns non-abelian Cayley graphs and is resolved by Theorem 1.

**Bottom line.** For estimating $g_\epsilon(N)$, at most the generic template "high-moment / $L^2$ return-probability bounds imply uniformity" carries over. The paper offers no ingredients specific to the subset-sum problem.

## Introduction to the non-asymptotic analysis of random matrices (2012)
arXiv 1011.3027 (version 1); full text: yes

**Verdict: essentially not relevant.** This is a tutorial on extreme singular values of random matrices: independent rows or columns, covariance estimation, and restricted isometries. It contains nothing on abelian groups, subset sums, or the counting function $F_A(g)$ for random subsets. Only generic probabilistic tools appear, and none is tailored to the problem.

**Generic tools that might conceivably be used (exact statements as given):**

- **Proposition 10 (Hoeffding-type inequality).** "Let $X_1,\dots,X_N$ be independent centered sub-gaussian random variables, and let $K=\max_i\|X_i\|_{\psi_2}$. Then for every $a\in\mathbb R^N$ and every $t\ge0$,
 $P\{|\sum_i a_iX_i|\ge t\}\le e\cdot\exp(-ct^2/(K^2\|a\|_2^2))$."
 - Proof method: moment generating function bounds (Lemma 9, "rotation invariance") plus the tail property (10).

- **Proposition 16 (Bernstein-type inequality).** For independent centered sub-exponential $X_i$ with $K=\max_i\|X_i\|_{\psi_1}$,
 $P\{|\sum a_iX_i|\ge t\}\le 2\exp[-c\min(t^2/(K^2\|a\|_2^2),\ t/(K\|a\|_\infty))]$.
 - Proof method: exponential Markov inequality with the mgf bound of Lemma 15.

- **Corollary 17.** This is the case $a_i=1$, $t=\varepsilon N$ of Proposition 16.

- **Theorem 29 (non-commutative Bernstein, quoted from [77]).** For independent centered self-adjoint $n\times n$ matrices with $\|X_i\|\le K$ a.s. and $\|\sum_i EX_i^2\|\le\sigma^2$:
 $P\{\|\sum X_i\|\ge t\}\le n\exp(-\tfrac{t^2/2}{\sigma^2+Kt/3})$.
 - Quoted without proof; the text says the approach is based on trace inequalities such as Golden–Thompson.

- **Lemma 46 (Symmetrization).** $E\|\sum(X_i-EX_i)\|\le 2E\|\sum\varepsilon_iX_i\|$.
 - Proof method: an independent copy, Jensen's inequality and symmetry.

- **Lemma 59 (Decoupling).** For a double array $(a_{ij})$ with $a_{ii}=0$:
 $\sum_{i,j}a_{ij}=4E\sum_{i\in T,j\in T^c}a_{ij}$, where $T$ is a random subset with average size $n/2$.
 - Proof method: independent selectors $\delta_i$ with $E\delta_i(1-\delta_j)=1/4$ for $i\neq j$.

- **Covering and union-bound template.** Lemma 2 states $N(S^{n-1},\varepsilon)\le(1+2/\varepsilon)^n$; Theorems 39 and 57 follow the scheme "approximation (net) → concentration → union bound."
 - A union bound over the $N$ elements $g\in G$, combined with a concentration estimate for each fixed $g$, is the only structurally analogous idea. The paper does not apply it to anything resembling $F_A$.

- **Remark 43 (coupon collector).** Sampling coordinate vectors needs $N\ge Cn\log n$ trials so that every coordinate is hit. This is a thresholding example, but in a different setting.

**What is missing:**

- No constants relevant to $\log_2 N$ thresholds appear.
- There are no Fourier-analytic or additive-combinatorial results on random subset sums.
- The text cites surveys [76, 69] for "connections to other problems of random matrix theory and additive combinatorics" (in the context of the hard edge), but gives no content from them.

**Open questions stated in the paper:** none close to the problem. The supplied text states no explicit open problems at all, and it is truncated partway through Section 6 on restricted isometries.

Anyone attacking the problem should not expect usable ingredients here beyond standard concentration inequalities and union-bound methodology.
