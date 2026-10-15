# erdosproblems.com #769: problem page and forum thread (fetched 2026-10-14T23:49:08Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $c(n)$ be minimal such that if $k\geq c(n)$ then the $n$-dimensional unit cube can be decomposed into $k$ homothetic $n$-dimensional cubes. Give good bounds for $c(n)$ - in particular, is it true that $c(n) \gg n^n$?
#769: [Er74b]
number theory | 
geometry
A problem first investigated by Hadwiger, who proved the lower bound\[c(n) \geq 2^n+2^{n-1}.\]It is easy to see that $c(2)=6$. Meier conjectured $c(3)=48$. Burgess and Erdős [Er74b] proved\[c(n) \ll n^{n+1}.\]Erdős wrote 'I am certain that if $n+1$ is a prime then $c(n)>n^n$.'
Hudelson [Hu98] proved that if $(2^n-1,3^n-1)=1$ then $c(n) < 6^n$, and in general $c(n) \ll (2n)^{n-1}$. Connor and Marmorino [CoMa18] proved that\[c(n) \geq 2^{n+1}-1\]for all $n\geq 3$,\[c(n) \leq 1.8n^{n+1}\]if $n+1$ is prime, and\[c(n) \leq e^2n^n\]otherwise. 
Additional thanks to: Alfaiz

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 The best currently known lower and upper bounds for $c(n)$ are due to Connor and Marmorino from their paper: Connor, P., Marmorino, P. Decomposing cubes into smaller cubes. J. Geom. 109, 19 (2018). https://doi.org/10.1007/s00022-018-0424-4
Lower bound: For $n \geq 3$,\[
 c(n) \;\geq\; 2^{\,n+1} - 1,
 \]so the lower bound is only exponential in $n$.
Upper bound: If n+1 is composite, then,\[
 c(n) \;\leq\; e^{2}\,n^{\,n}, \\[6pt]
 \]If n+1 is prime, then,\[ c(n) \;\leq\; 1.8\,n^{\,n+1}.
 \]
 Alfaiz
 — 03:22 on 01 Oct 2025
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
claimed by Samuel Korsky (using GPT-5.6 Pro).
 Summary:
 We prove for odd $n$ that for every $\varepsilon>0$\[
c(n)\le \bigl(C_\varepsilon n^{1/(4\sqrt e) + \varepsilon}\bigr)^n,
\]with $n^{1/(4\sqrt e)+\varepsilon}$ replaced by $C(\log n)^2$ under GRH.
For even $n$, we prove that\[
c(n)\ge\left(\left(1-\frac1{\log_2 3}\right)n-\log_2 n-O(1)\right)2^n.
\]The upper bounds combine a numerical-semigroup reduction with character-nonresidue estimates and a product amplification inside the subgroup ${x^n=1}\subset\mathbb F_q^\times$. The lower bound uses a $p$-adic congruence obstruction preserved by doubling and deleting unit cubes. Much of the work for the upper bound and all of the work for the lower bound was performed by GPT - I think the lower bound argument is especially interesting!
 Notes:
 There is application to Erdős Problem 770; if $P(n)=\max\{p\text{ prime},\,p-1\mid n\}$ and\[
h(n)=\min\left\{M>2:\gcd_{2\le m\le M}(m^n-1)=1\right\},
\]the argument gives, for every $\varepsilon>0$ and all sufficiently large $n$,\[
P(n)\le h(n)\le\max\{P(n),n^{1/(4\sqrt e)+\varepsilon}\},
\]and under GRH,\[
h(n)\le\max\{P(n),C(\log n)^2\}.
\]Consequently $h(n)=P(n)$ whenever $P(n)$ exceeds the corresponding scale; this answers the large-$P(n)$ part of Problem 770 unconditionally above the Burgess exponent and, under GRH, for every fixed positive-power threshold. The density and liminf questions remain open.
| 
 External link to proof
 |
 Submitted 2026-08-05 22:46:47 by 
 SamKorsky
 ▶
 Comments (1)
A proof 
claimed by Jeffrey Zeng (using an OpenAI internal model).
 Summary:
 AI-assisted, Lean-formalized partial result for #769/#770. All gcds are collective, not pairwise. Let \(P(n)=\max\{p\text{ prime}:p-1\mid n\}\) and \(S(n)=\lfloor\sqrt{4n}\rfloor+1\). For all \(n\ge1\),\[
P(n)\le h(n)\le\max\{P(n),S(n)\},\quad P(n)>2\sqrt n\Rightarrow h(n)=P(n).
\]For odd \(n\), \(h(n)\le S(n)\) and\[
c(n)\le(S(n)-1)(2^n-2)(S(n)^n-1)+1=o(n^n).
\]Thus #769’s proposed uniform lower bound \(c(n)\gg n^n\) is false. This is only a partial result for #770: its density, liminf, and general \(\varepsilon>0\) questions remain unresolved. Novelty and priority have not been determined. AI disclosure: an OpenAI internal model. The central claims have a sorry-free Lean formalization.
 Notes:
 Let \(G(n,M)=\gcd_{2\le a\le M}(a^n-1)\), with \(M=\max\{P(n),S(n)\}\). If \(q\mid G(n,M)\), then \(q>M\), and \(H=\{x\in\mathbf F_q^*:x^n=1\}\) has at most \(n\) elements. If \(q>M^2\), reduced fractions \(a/b\), \(1\le a,b\le M\), inject into \(H\), but their number is at least \(M^2/4+M>n\). If \(q\le M^2\) and \(n\) is even, Dirichlet approximation gives \(x=a/k\), \(1\le k\le M\), \(0<|a|<M\); hence every \(x\ne0\) satisfies \(x^n=1\), forcing \(q-1\mid n\), impossible since \(q>P(n)\). If \(n\) is odd, \(H\) consists of squares and the least quadratic nonresidue is at most \(\lceil\sqrt q\rceil\), forcing \(q>M^2\). Fermat gives \(P(n)\le h(n)\). Cube refinements add \(a^n-1\), so the gcd-one numerical-semigroup argument yields the stated cutoff.
 Submitted 2026-07-24 17:04:43 by 
 jeffzeng
 ▶
 Comments (0)