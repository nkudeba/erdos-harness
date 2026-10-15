# erdosproblems.com #1110: problem page and forum thread (fetched 2026-10-14T22:12:05Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $p>q\geq 2$ be two coprime integers. We call $n$ representable if it is the sum of integers of the form $p^kq^l$, none of which divide each other. 
If $\{p,q\}\neq \{2,3\}$ then what can be said about the density of non-representable numbers? Are there infinitely many coprime non-representable numbers?
#1110: [ErLe96]
number theory
A problem of Erdős and Lewin [ErLe96], who proved that there are finitely many non-representable numbers if and only if $\{p,q\}=\{2,3\}$.
Indeed, in [Er92b] Erdős wrote 'last year I made the following silly conjecture': every integer $n$ can be written as the sum of distinct integers of the form $2^k3^l$, none of which divide any other. He wrote 'I mistakenly thought that this was a nice and difficult conjecture but Jansen and several others found a simple proof by induction.' 
This simple proof is as follows: one proves the stronger fact that such a representation always exists, and moreover if $n$ is even then all the summands can be taken to be even: if $n=2m$ we are done applying the inductive hypothesis to $m$. Otherwise if $n$ is odd then let $3^k$ be the largest power of $3$ which is $\leq n$ and apply the inductive hypothesis to $n-3^k$ (which is even).
Yu and Chen [YuCh22] prove that the set of representable numbers has density zero whenever $q>3$ or $q=3$ and $p>6$ or $q=2$ and $p>10$. They also prove that there are infinitely many coprime non-representable numbers if $q>3$ or $q=3$ and $p\neq 5$ or $q=2$ and $p\not\in \{3,5,9\}$.
Erdős and Lewin [ErLe96] also asked whether all large integers $n$ can be written as a sum of $2^k3^l$, none of which divide another, each of which is $>f(n)$ for some $f(n)\to \infty$. Let $f(n)$ be the fastest growing such $f(n)$. Yu and Chen [YuCh22] proved\[\frac{n}{(\log n)^{\log_23}}\ll f(n) \ll \frac{n}{\log n}.\]Yang and Zhao [YaZh25] improved the lower bound to $f(n)\gg n/\log n$. van Doorn has observed in the comments that a result of Blecksmith, McCallum, and Selfridge [BMS98] already implies\[f(n)\sim \frac{\log 2\log 3}{2}\frac{n}{\log n}.\]The case of three powers is the subject of [123], and see also [845] for more on the case $\{p,q\}=\{2,3\}$. The problem [246] addresses the topic without the non-divisibility condition.
Additional thanks to: Sarosh Adenwalla, Alfaiz, Stijn Cambie, and Wouter van Doorn

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Let $f(n)$ be the largest integer such that every integer $N \ge n$ can be written as a sum of distinct $3$-smooth integers, all larger than $f(n)$, and such that no two distinct elements divide each other. Then the remarks mention somewhat recent bounds on $f(n)$ by Yu-Chen and Yang-Zhao. However, essentially optimal bounds were already obtained back in $1998$ by Blecksmith, McCallum and Selfridge. 
R. Blecksmith, M. McCallum, J.L. Selfridge, 3-smooth representations of integers. The American Mathematical Monthly, Volume 105, No. 6, 529–543, 1998.
You can find their paper here. In particular, their Theorem $2$ states that every integer larger than or equal to $$2 \sum_{2^a3^b \le m} 2^a 3^b$$can be written as a sum of distinct $3$-smooth integers, all larger than $m$, and such that no two distinct elements divide each other. On the other hand, every such way of writing the integer $$2 \sum_{2^a3^b \le m} 2^a 3^b - 1$$contains an element smaller than or equal to $m$.
If I'm not mistaken, this gives $$f(n) = \left(\frac{\log 2 \log 3}{2} + o(1) \right) \frac{n}{\log n}.$$
(The site has been updated to address this comment.)
 Woett
 — 15:15 on 10 Mar 2026
 👍
 0
 📝
 2
 🤖
 0
 The statement should be 'Yu and Chen [YuCh22] prove that the set of representable numbers has density zero...'
instead of 'non-representable numbers'.
(The site has been updated to address this comment.)
 Adenwalla
 — 19:49 on 08 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 There is a paper 'A conjecture of Yu and Chen related to the Erdős–Lewin theorem' by Quan-Hui Yang and Lilu Zhao in Acta Arithmetica 217 (2025) which proves that there is a constant $c>0$ such that one can take $f(n)\gg\frac{cn}{\log n}$. A result in Yu and Chen's paper shows that this optimal up to the constant.
The Yu and Chen paper also proves that there are infinitely many coprime non-representable numbers when $\{p,q\}\neq \{2,3\},\{2,5\},\{2,9\},\{3,5\}$.
(The site has been updated to address this comment.)
 Adenwalla
 — 17:14 on 07 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 who proved that there are infinitely many non-representable numbers if and only if ...
probably should be
who proved that there are finitely many non-representable numbers if and only if
(The site has been updated to address this comment.)
 StijnC
 — 14:03 on 07 Dec 2025
 👍
 0
 📝
 0
 🤖
 0

## Proof claims page
There are 3 proof claims (partial or full) for this problem.
 Appearing on this page is no guarantee of proof correctness, and does not mean that anyone associated with this site has examined any part of the proof.
 Submit your own proof claim
A proof 
claimed by Jean-Roch Bécart (using Opus 5.5).
 Summary:
 We show that for (p,q) = (7,2) the representable integers have positive lower density.
This pair is not covered by Yu and Chen's density-zero result, which requires p > 10 when q = 2.
Method. We extend the finite-certificate approach of Ding, Li, Liu and Zhang for (2,5).
1. Encoding. A residue $y$ mod $2^{sN}$ is encoded block by block, with $s = 11$ bits per block. Each block gets a chain $\{(\alpha,\gamma)\}$, strictly increasing in both coordinates, with $\sum 2^{\alpha}7^{-\gamma} \equiv$ (current block) mod $2^{s}$.
2. Antichain. The blocks are stacked so that the terms $2^{st+\alpha}\,7^{A-G_t-\gamma}$ form a divisibility antichain. The resulting integer satisfies $n \equiv 7^{A}y \pmod{2^{sN}}$, so the map $y \mapsto n$ is injective.
3. Look-ahead certificate. The chain chosen for each block depends on the next two blocks. A potential function $V$ on the $2^{22}$ states gives an average height increment of $\hat g = 3.904698\ldots$ per block. This is below $11\cdo
 Notes:
 Computer-assisted.
The finite certificate (the table $V$ and the drift inequality over $2^{22}$ states) is checked by two independently written C programs. Both give the exact integer bound $\hat g\cdot 2^{31} = 8385274094$. We also check that $7^{26} < 2^{73}$.
The reduction "certificate ⇒ positive lower density" is formalized in Lean 4 / Mathlib. It uses the formal-conjectures definition of Representable verbatim. It has no sorry and depends only on the standard axioms. Only the certificate check itself is trusted to the C code.
The implied density constant is astronomically small. Numerically, about 22% of the integers up to $2^{27}$ are representable.
The same method does not reach (9,2) or (5,3) at feasible sizes.
The proof, programs and Lean code were produced by the AI under my direction.
They have not yet been reviewed by a human expert, and feedback is welcome.
| 
 External link to proof
 |
 External link to formalisation
 |
 Submitted 2026-09-29 14:37:10 by 
 jbecart
 ▶
 Comments (0)
A proof 
claimed by Yuchen Ding, Huixi Li, Honghu Liu, Zihan Zhang (using GPT 5.6 Sol).
 Summary:
 If $\{p,q\}\ne\{2,3\}$, Erdős and Lewin asked what can be said about the density of the nonrepresentable integers. Yu and Chen made some progress as described above. 
We show that for $(p,q)=(2,5)$, the representable integers have positive lower density.
Let $\mathcal R$ denote the set of representable integers for $2$ and $5$, and let $\mathcal R(x)$ be its counting function. Set $P=2^{12}$. For every positive integer $N$, we define a suitable class of admissible words $$
\mathbf r=(r_0,\ldots,r_{N-1})\in\{0,1,\ldots,P-1\}^N.
$$
We construct an injective map $\Phi$ from the admissible words to $\mathcal R$ such that $\Phi(\mathbf r)\leq 10546\,P^{N}$. Using the cycle lemma and a double counting argument, we show that the number of admissible words is at least $57\,P^{N-1}$. Hence $\mathcal R(10546\,P^{N})\gg P^{N},$ which implies the required conclusion.
 Notes:
 The key finite input is a family of sets
$C(r)=\{(\alpha_{r,i},\gamma_{r,i}):1\leq i\leq t_r\}$,
$0\leq r<P$, with $C(0)=\varnothing$, such that
$$\sum_{(\alpha,\gamma)\in C(r)}2^\alpha(5^\gamma)^{-1}\equiv r\pmod P,$$
where $$0\leq \alpha_{r,1}<\alpha_{r,2}<\ldots<\alpha_{r,t_{r}}\leq 11\quad\text{and}\quad
0\leq \gamma_{r,1}<\gamma_{r,2}<\ldots<\gamma_{r,t_{r}}\leq 7.
$$ Moreover, if $H(0)=0$ and
$$H(r)=1+\max\{\gamma:(\alpha,\gamma)\in C(r)\}
\qquad(r\ne0),$$
then the average value of \(H(r)\) over $0\leq r<P$ is less than \(5\).
| 
 External link to proof
 |
 Submitted 2026-08-24 10:18:38 by 
 Honghu_Liu
 ▶
 Comments (0)
A proof 
claimed by Apiros3 (using GPT-5.6 Sol, GPT-5.5).
 Summary:
 GPT-5.6 Sol and GPT-5.5 were used in the proof formalization.
There are infinitely many coprime non-representable numbers. Yu and Chen reduced this problem to three cases (p,q) = (5,2), (9,2), (5,3), and we give a proof for these three.
The proof is by picking a small seed c < p and then repeatedly forming larger coprime non-representable numbers of the form p^a + c q^M. The proof sketch is as follows:
- Any representation is just a finite antichain of grid points (as no terms divide each other)
- If an antichain sum in the rectangle 0 <= i <= a, 0 <= j < M is congruent to p^a mod q^M, then it is exactly p^a.
- If N = p^a + c q^M has a representation, then c q^M < (p-1)p^a forces (a,0) to be a grid point. Removing this and dividing by q^M implies c is representable, a contradiction.
The cases are each proven by seeds:
- (5,2): c = 3
- (9,2): c = 5
- (5,3): c = 2
| 
 External link to proof
 |
 External link to formalisation
 |
 Submitted 2026-08-05 16:07:35 by 
 apiros3
 ▶
 Comments (1)