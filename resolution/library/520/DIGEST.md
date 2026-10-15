# erdosproblems.com #520: problem page and forum thread (fetched 2026-10-10T10:55:46Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $f$ be a Rademacher multiplicative function: a random $\{-1,0,1\}$-valued multiplicative function, where for each prime $p$ we independently choose $f(p)\in \{-1,1\}$ uniformly at random, and for square-free integers $n$ we extend $f(p_1\cdots p_r)=f(p_1)\cdots f(p_r)$ (and $f(n)=0$ if $n$ is not squarefree). Does there exist some constant $c>0$ such that, almost surely,\[\limsup_{N\to \infty}\frac{\sum_{m\leq N}f(m)}{\sqrt{N\log\log N}}=c?\]
#520: [Er61,p.251]
number theory | 
probability
Note that if we drop the multiplicative assumption, and simply assign $f(m)=\pm 1$ at random, then this statement is true (with $c=\sqrt{2}$), the law of the iterated logarithm.
 Wintner [Wi44] proved that, almost surely,\[\sum_{m\leq N}f(m)\ll N^{1/2+o(1)},\]and Erdős improved the right-hand side to $N^{1/2}(\log N)^{O(1)}$. Lau, Tenenbaum, and Wu [LTW13] have shown that, almost surely,\[\sum_{m\leq N}f(m)\ll N^{1/2}(\log\log N)^{2+o(1)}.\]Caich [Ca24b] has improved this to\[\sum_{m\leq N}f(m)\ll N^{1/2}(\log\log N)^{3/4+o(1)}.\]Harper [Ha13] has shown that the sum is almost surely not $O(N^{1/2}/(\log\log N)^{5/2+o(1)})$, and conjectured that in fact Erdős' conjecture is false, and almost surely\[\sum_{m\leq N}f(m) \ll N^{1/2}(\log\log N)^{1/4+o(1)}.\]
Additional thanks to: Mehtaab Sawhney

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 [Post deleted]
 Unknown
 — 03:45 on 28 Jul 2026
 👍
 0
 📝
 0
 🤖
 0
 Please resubmit this as a proof claim (and then delete this comment).
 Thomas Bloom
 — 11:46 on 29 Jul 2026
 👍
 0
 📝
 0
 🤖
 0

## Proof claims page
There are 2 proof claims (partial or full) for this problem.
 Appearing on this page is no guarantee of proof correctness, and does not mean that anyone associated with this site has examined any part of the proof.
 Submit your own proof claim
A proof 
claimed by Sigurd William Rachlew Høystad (using GPT 5.6 Sol Pro, Fable 5).
 Summary:
 The Lean development linked below appears to answer Problem #520 in the negative. 
It proves, for the squarefree Rademacher random multiplicative function and every η > 0, that almost surely |M_f(N)| ≪_{ω,η} √N (log log N)^(1/4+η); taking η = 1/8, the ratio M_f(N)/√(N log log N) tends to 0 almost surely, so the limsup in the problem is 0 rather than a positive constant. 
This is the same bound recently proved by Durkan and Pearce-Crump (arXiv:2607.29429) and announced on this site by Korsky and Reis, via essentially the same modification of Caich's argument: a conditional high-moment estimate on each thin prime block, using Doob's inequality and hypercontractivity, in place of a first-moment bound and union bound.
The development is self-contained: Harper's low-moment estimate, the prime number theorem input, and Brun–Titchmarsh are proved within it.
The proofs were largely drafted by AI (GPT 5.6 pro / Fable 5) under my direction.
| 
 External link to proof
 |
 External link to formalisation
 |
 Submitted 2026-08-04 10:47:56 by 
 Sigurd Høystad
 ▶
 Comments (0)
A proof 
claimed by Samuel Korsky (using GPT 5.6-Pro).
 Summary:
 GPT 5.6 Pro claims to resolve Problem #520 in the negative, in particular Harper's conjectured $1/4 + o(1)$ exponent is sharp. 
In Caich’s argument, the loss from exponent $1/4+\varepsilon$ to $3/4+\varepsilon$ appears to come from applying a first-moment bound and union bound over prime blocks. For the Rademacher model, one can instead prove a conditional high-moment estimate\[
\left(\mathbb E[U_j^q\mid\mathcal F_{y_{j-1}}]\right)^{1/q}\ll_q I_{j-1}
\]using ordinary Doob $L^{2q}$, Bonami–Halász hypercontractivity, Minkowski, and the fact that each prime block has reciprocal-prime mass $O(1/\ell)$. Taking fixed $q$ large enough removes the union-bound loss
This work was performed with no human input at all (I just thought the contrast between Harper's conjecture and the Law of the Iterated Logarithm was surprising, so asked GPT to opine and it came up with this), although I attempted to (prompt GPT to) rewrite the proof to make it more readable.
 Notes:
 Victor Reis and I also attempted to (partially) formalize the results in Lean here: https://drive.google.com/file/d/1GAbArk0C1HFFJtrgi8bY_oicpJ5GZ-xq/view. Note that this formalization is not self-contained; we use five inputs from Caich's paper as black box hypotheses, and also the proof of Proposition 3.1 (which is the critical patch to Caich's argument) relies on some standard analytic tools not yet in Mathlib. Neither of us have the technical expertise to verify the proof ourselves; however, we have sent the manuscript to experts familiar with this problem, and initial impressions seem favorable.
We wanted to post in case those more familiar with the problem found the idea interesting/plausible.
| 
 External link to proof
 |
 External link to formalisation
 |
 Submitted 2026-07-29 18:14:10 by 
 SamKorsky
 ▶
 Comments (0)