# erdosproblems.com #536: problem page and forum thread (fetched 2026-10-06T16:07:33Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I have pushed the elementary fibre argument (Kitamura's $\frac{5}{6}$, Logsdon's $0.813$ further by computing the exact extremal numbers of the smooth-number boxes, which gives $f(N) \leq (0.791 + o(1))N$ with the primes $\{2, 3, 5, 7\}$, and $f(N) \leq (0.7845 + o(1))N$ with $\{2, 3, 5, 7, 11, 13\}$. Both are computer-assisted, but neither is Lean-verified.
For the reduction, fix a finite set $P$ of primes, and define $Q = \prod\limits_{p \in P} p$. Write $n = ms$ with $s$ $P$-smooth and $\gcd(m, Q) = 1$. For fixed $m$ the smooth parts with $ms \leq N$ are the box $B_P(T) = \{e \in \mathbb{N}^P: \prod\limits_{p \in P} p^{e_p} \leq T\}$, $T = \left \lfloor \frac{N}{m}\right \rfloor$, and three elements of one class form an lcm triangle exactly when their exponent vectors $u, v, w$ satisfy $u \vee v = v \vee w = w \vee u$ (coordinate-wise max). Let $\mathrm{ex}_P(T)$ be the largest subset of $B_P(T)$ with no such triple. Then
$$f(N) \leq \sum_{\substack{m \leq N\\ \gcd(m, Q)=1}} \mathrm{ex}_P \left (\left \lfloor \frac{N}{m}\right \rfloor \right ) = \left (c_P + o(1) \right )N,$$
where
$$c_P=\left (\prod\limits_{p \in P} \left (1 - \frac{1}{p}\right ) \right ) \left (\sum_{T \geq 1}\frac{\mathrm{ex}_P(T)}{T(T + 1)} \right ).$$This is the same statement as the finite-prime envelope in Shouqiao Wang's manuscript (his Proposition 2.5, also in his Lean development as f_le_finitePrimeEnvelope). For $P = \{2, 3\}$ it is Kitamura's argument with $\mathrm{ex}_{\{2, 3\}}(T) = \lfloor \log_2(T) \rfloor + \lfloor \log_3(T) \rfloor + 1$, which gives $c = \frac{5}{6}$ exactly, and Logsdon's $0.813$ is the $\{2, 3, 5\}$ box analysed through adjacent $5$-adic slices. Note that only triangles inside one core class are used, so the bound is monotone in $P$ (i.e. a $P \cup \{p\}$-box is a union of $p$-adic slices that are $P$-boxes), and it never sees triangles whose three elements have different cores.
This does lead to me getting the explicit form 
$$f(N) \leq c_P N + \left (1 + 2^{|P| + 1}\right )(1 + \log_2(N))^{|P|} N^{\frac{1}{2}}$$I proceeded to find upper bound $U(T) \geq \mathrm{ex}_P(T)$ to bound $c_P$. I observed
$$U(T) \leq \min_{p \in P} \left (U_{P \setminus p}(T)+U \left (\left \lfloor \frac{T}{p} \right \rfloor \right ) \right ),$$which I combined with some computation on small $T$ to get my aforementioned results.
*AI disclosure: the computations and the Lean formalisation of the reduction were produced with Claude, but the mathematical choices and the checks described are mine.*
 Sharvil Kesarwani
 — 14:28 on 07 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 I made a Lean formalization attempt for the following upper bound in Erdos Problems #536: $|A| \le N-\lfloor N/6 \rfloor$
Equivalently, this is $|A| \le \lceil 5N/6\rceil$; asymptotically, the coefficient is $5/6 \approx 0.833333$, i.e. about $0.833333N$.
Here $A \subseteq \{1,\ldots,N\}$ has no three distinct elements $a,b,c$ such that $\operatorname{lcm}(a,b)=\operatorname{lcm}(a,c)=\operatorname{lcm}(b,c)$.
Lean4Web: https://live.lean-lang.org/#url=https://raw.githubusercontent.com/KitaKen1/erdos536-lean-five-six-bound/main/Erdos536_lean4web.lean
Github: https://github.com/KitaKen1/erdos536-lean-five-six-bound
Verification: the GitHub repository builds with 'lake build'; the checked 'Erdos536/' sources contain no 'sorry', 'axiom', or 'admit'; and the target theorem's axiom printout lists only the usual Lean foundations: '[propext, Classical.choice, Quot.sound]'.
AI usage: this Lean formalization and forum comment were prepared with assistance from Codex 5.5 using xhigh reasoning and ChatGPT 5.5 Pro.
 KentaKitamura
 — 01:47 on 22 Jun 2026
 👍
 1
 📝
 0
 🤖
 0
 I have run a screening check and the Lean is correct.
This is the strongest upper bound so far, and the argument is surprisingly simple given the efforts already spent by others.
Write an integer $n = m 2^i 3^j$ where $(m, 6) = 1$. For a fixed $m$, identify $n$ with a point $(i, j)$ in a lattice.
The condition on $A$ implies that the 3 points which form a "corner": $\{ (i, j), (i - a, j), (i, j - b) \}$, $a, b > 0$, cannot all be in $A$.
Define a projection to the axes
$$ \pi(i, j) = \begin{cases} (i, j), & i = 0\text{ or }j = 0, \\
(i, 0), & \text{some point of }A\text{ lies to its left}, \\
(0, j), & \text{otherwise}.
\end{cases}$$
It is easy to check that the projection $\pi$ is injective by the corner observation above.
It immediately follows:
$$ |A| \le \#\{\text{axis points}\} = \{ n \le N: 6 \nmid n \} = N - \lfloor N/6 \rfloor. $$
This kind of forbidden pattern is known in literature as $\Gamma$-free $0$-$1$ matrices. See e.g. this 2018 paper by Bényi and Nagy. It is known that such a matrix of size $n \times k$ has at most $n + k - 1$ $1$'s, which also follows from the above projection argument.
Nevertheless, the consideration of this specific lattice for this problem could be novel.
 Nat Sothanaphan
 — 17:01 on 22 Jun 2026
 👍
 1
 📝
 0
 🤖
 0
 Although this is superseded asymptotically by Shouqiao Wang’s subsequent proposed proof that $f(N)=o(N)$, I found that the elementary lattice argument above can itself be refined from $5/6$ to $813/1000.$ I formalized this refinement completely in Lean: Lean repository. The completed asymptotic result appears in the final Lean theorem. This may be of some independent interest as an explicit quantitative strengthening of the elementary argument.
The idea is to refine the decomposition to\[
n=m2^i3^j5^k,\qquad (m,30)=1.
\]For fixed $m$ and $k$, the selected integers again form a $\Gamma$-free subset of\[
D(T)=\{(i,j):2^i3^j\le T\},
\]with the usual projection bound\[
L(T)=\lfloor\log_2T\rfloor+\lfloor\log_3T\rfloor+1.
\]The improvement comes from the fact that adjacent 5-adic slices cannot attain these bounds independently.
More precisely, suppose an upper slice $F\subseteq D(S)$ is extremal, so $|F|=L(S)$. Then every nontrivial $2,3$-smooth integer $c\le S$ is forbidden in the slice immediately below it. Indeed, $1\in F.$ If $c\in F$, then\[
\{5,5c,c\}
\]has equal pairwise LCMs. If $c\notin F$, maximality implies that adding $c$ creates a corner with some $u,v\in F$, and then\[
\{5u,5v,c\}
\]has equal pairwise LCMs.
Thus the lower slice is forced into\[
\{1\}\cup R(T),\qquad
R(T)=\{2^i3^j:T/5<2^i3^j\le T\}.
\]If $h(T)$ is the largest size of a $\Gamma$-free subset of $R(T)$, the needed annulus estimate is\[
h(T)\le L(T)-3\qquad(T\ge120).
\]For large $T$, this follows from a row-counting argument. The remaining finite range is handled exactly.
Writing\[
d_k=L(T_k)-|F_k|
\]for the deficit in the $k$-th 5-adic slice, this gives\[
T_k\ge120,\quad d_{k+1}=0
\quad\Longrightarrow\quad
d_k\ge2.
\]There is also the finite two-slice strengthening\[
d_k+d_{k+1}\ge2
\]when\[
45\le T_k\le71
\qquad\text{or}\qquad
80\le T_k\le119.
\]The finite verification reduces to the ten states\[
45,48,54,60,64,80,81,90,96,108.
\]These states are proved inside Lean and were also checked independently by two exact Python programs: one directly enumerates the relevant $\Gamma$-free families, while the other constructs the complete two-layer LCM hypergraph and computes its exact minimum hitting set.
Summing the forced deficits over the 5-adic tower gives total weighted deficit\[
\frac{61}{800}.
\]The cores coprime to $30$ have density $4/15$, so the saving from the original $5/6$ coefficient is\[
\frac4{15}\frac{61}{800}=\frac{61}{3000}.
\]Therefore\[
\frac56-\frac{61}{3000}
=\frac{813}{1000},
\]giving\[
\boxed{f(N)\le(813/1000+o(1))N}.
\]The repository’s GitHub Actions build the complete Lean proof. I would still greatly appreciate independent mathematical and Lean review.
AI disclosure: the mathematical exploration, verification code, write-up, and Lean formalization were prepared with substantial assistance from ChatGPT/Codex.
 Sara Logsdon
 — 18:17 on 17 Aug 2026
 👍
 1
 📝
 0
 🤖
 0
 I plan to post a note to arxiv later showing that $f(N) \ge \frac{N}{(\log N)^{0.059... + o(1)}}$ with a more involved argument, but for now here's a quick sketch that $f(N) \ge \frac{N}{(\log N)^{1 - 1/e + o(1)}}$:
Let\[
L=\log\log N,
\qquad
k=\left\lfloor \frac{L}{e}\right\rfloor.
\]Let $X$ be the set of squarefree $n\in(N/2,N]$ with $\omega(n)=k$ and let $J(\alpha) = 1 - \alpha + \alpha\log\alpha$. The squarefree version of the Sathe--Selberg theorem gives, uniformly for fixed $0<\alpha<1$,\[
\#\{n\in(N/2,N]:n\text{ squarefree},\ \omega(n)=\lfloor \alpha\log\log N\rfloor\}
=\frac{N}{(\log N)^{J(\alpha)+o(1)}}.
\]Taking $\alpha=1/e$ gives\[
|X|=\frac{N}{(\log N)^{J(1/e)+o(1)}}.
\]Color every prime independently and uniformly with one of $k$ colors. For a coloring $\chi$, let $A_\chi\subseteq X$ consist of those $n$ whose $k$ prime factors receive all $k$ colors exactly once. For fixed $n\in X$,\[
\mathbb{P}(n\in A_\chi)=\frac{k!}{k^k}=\exp(-k+o(k))=(\log N)^{-1/e+o(1)}.
\]Hence\[
\mathbb{E}_\chi \left[|A_\chi|\right]=\frac{N}{(\log N)^{J(1/