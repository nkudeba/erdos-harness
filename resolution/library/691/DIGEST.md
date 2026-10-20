# erdosproblems.com #691: problem page and forum thread (fetched 2026-10-20T08:39:09Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Given $A\subseteq \mathbb{N}$ let $M_A=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}$ be the set of multiples of $A$. Find a necessary and sufficient condition on $A$ for $M_A$ to have density $1$.
#691: [Er79e,p.77]
number theory
A sequence $A$ for which $M_A$ has density $1$ is called a Behrend sequence.
If $A$ is a set of prime numbers (or, more generally, a set of pairwise coprime integers without $1$) then a necessary and sufficient condition is that $\sum_{p\in A}\frac{1}{p}=\infty$.
The general situation is more complicated. For example suppose $A$ is the union of $(n_k,(1+\eta_k)n_k)\cap \mathbb{Z}$ where $1\leq n_1<n_2<\cdots$ is a lacunary sequence. (This construction is sometimes called a block sequence.) If $\sum \eta_k<\infty$ then the density of $M_A$ exists and is $<1$. If $\eta_k=1/k$, so $\sum \eta_k=\infty$, then the density exists and is $<1$.
Erdős writes it 'seems certain' that there is some threshold $\alpha\in (0,1)$ such that, if $\eta_k=k^{-\beta}$, then the density of $M_A$ is $1$ if $\beta <\alpha$ and the density is $<1$ if $\beta >\alpha$.
Tenenbaum notes in [Te96] that this is certainly not true as written since if the $n_j$ grow sufficiently quickly then this sequence is never Behrend, for any choice of $\eta_k$. He then writes 'we understand from subsequent discussions with Erdős that he had actually in mind a two-sided condition on' $n_{j+1}/n_j$.
Tenenbaum [Te96] proves this conjecture: if there are constants $1<C_1<C_2$ such that $C_1<n_{i+1}/n_i<C_2$ for all $i$ and $\eta_k=k^{-\beta}$ then $A$ is Behrend if $\beta<\log 2$ and not Behrend if $\beta>\log 2$.
Additional thanks to: Alfaiz and Desmond Weisenberg

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I would like to share a short note and a Lean 4 formalization related to Erdős problem #691, both produced using GPT-5.4 Pro (which carried out the natural-language proof and its Lean formalization).
The main statement proved is that for $A \subseteq \mathbb N$, the set $M_A$ has natural density $1$ if and only if $\lim_{N\to\infty} d(M_{A\cap[1,N]}) = 1$, equivalently if and only if $\sup_{F\subseteq A,\ F\text{ finite}} d(M_F)=1$.
It seems quite plausible to me that the mathematics surrounding Problem #691 is already largely present in the existing literature on sets of multiples and Behrend sequences. At the same time, the relevant references appear to be spread across several sources, and I do not yet feel that I have completed a sufficiently comprehensive literature review to make a definitive priority claim. I would therefore especially welcome corrections concerning references, priority, and the exact relation of these notes to earlier work.
* Main note: [PDF]
* Lean file / repository: [GitHub]
* typecheck information: [Lean 4 web]
 YutaOriike
 — 06:55 on 17 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Thanks! This is well known. See Hall and Tenenbaum, equation 1.3. Credit to GPT-5.4 Thinking for discussion.
 Nat Sothanaphan
 — 11:27 on 17 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 Thanks for the reference. I have now checked Hall–Tenenbaum, and you are right that equation (1.3), cited there as a result of Davenport and Erdős, already contains the finite-approximation statement. I will revise the note to cite this reference explicitly and to frame the contribution as an expository write-up together with a Lean 4 formalization of this classical fact.
 YutaOriike
 — 13:53 on 18 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 [Post deleted]
 Unknown
 — 22:30 on 31 Aug 2025
 👍
 0
 📝
 0
 🤖
 0
 I think you might have misread the $n_k$ as $\eta_k$?
 Thomas Bloom
 — 22:49 on 31 Aug 2025
 👍
 0
 📝
 0
 🤖
 0