# erdosproblems.com #657: problem page and forum thread (fetched 2026-10-19T18:06:10Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Is it true that if $A\subset \mathbb{R}^2$ is a set of $n$ points such that every subset of $3$ points determines $3$ distinct distances (i.e. $A$ has no isosceles triangles) then $A$ must determine at least $f(n)n$ distinct distances, for some $f(n)\to \infty$?
#657: [Er73][Er75f,p.101][ErPa90][Er97e]
geometry | 
distances
In [Er73] Erdős attributes this problem (more generally in $\mathbb{R}^k$) to himself and Davies. In [Er97e] he does not mention Davis, but says this problem was investigated by himself, Füredi, Ruzsa, and Pach.
In [Er73] Erdős says it is not even known in $\mathbb{R}$ whether $f(n)\to \infty$. Sarosh Adenwalla has observed that this is equivalent to minimising the number of distinct differences in a set $A\subset \mathbb{R}$ of size $n$ without three-term arithmetic progressions. Dumitrescu [Du08] proved that, in these terms,\[(\log n)^c \leq f(n) \leq 2^{O(\sqrt{\log n})}\]for some constant $c>0$.
Hunter observed in the comments that a result of Ruzsa coupled with standard tools of additive combinatorics (with details given by Alfaiz and Tang) allow recent progress on the size of subsets without three-term arithmetic progression (see [BlSi23] which improves slightly on the bounds due to Kelley and Meka [KeMe23]) yield\[2^{c(\log n)^{1/9}}\leq f(n)\]for some constant $c>0$.
Straus has observed that if $2^k\geq n$ then there exist $n$ points in $\mathbb{R}^k$ which contain no isosceles triangle and determine at most $n-1$ distances.
See also [135].
Additional thanks to: Sarosh Adenwalla, Alfaiz, Zach Hunter, and Quanyu Tang

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 It seems that a new bound $f(n)\geq2^{\Omega({\frac{(\log n)^{1/6}}{\log\log n}})}$ follows from [Ra26] by R. Raghavan (following the same reduction used in the previous $1/9$ exponent bound).
 Alfaiz
 — 06:20 on 06 Aug 2026
 👍
 0
 📝
 1
 🤖
 0
 For positive integers $k,\ell$, we consider planar point sets where every $k$ points determine at least $\ell$ distinct distances. Let $\phi(n,k,\ell)$ denote the minimum number of distinct distances spanned by such a set of $n$ points. Then $\phi(n,3,3)$ is exactly the $n f(n)$ in this problem.
I checked the literature, including Fox–Pach–Suk, Fish–Lund–Sheffer, Pohoata–Sheffer, and Sheffer’s survey. They all record only the trivial lower bound $\phi(n,3,3)\ge n-1$, usually explained by: “Since no isosceles triangles are allowed, a point $p\in P$ determines $n-1$ distinct distances to $P\setminus\{p\}$.”
Here is a small sharpening of the trivial bound, which seems worth recording:\[
\phi(n,3,3)\ \ge\ 
\begin{cases}
n, & n\ \text{odd},\\[2mm]
n-1, & n\ \text{even}.
\end{cases}
\]This bound is tight for $n=3$ (any scalene triangle) and for $n=4$ (any non-square rectangle).
Proof. Let $A\subset\mathbb{R}^2$ be an $n$–point set that has no isosceles triangles. Consider the complete graph $K_n$ on the vertex set $A$. Color every edge of $K_n$ by its Euclidean length; thus two edges receive the same color if and only if they have the same length. Let the number of colors (i.e., the number of distinct distances) be $m$. If two edges of the same color met at a vertex, they would form an isosceles triangle, contradicting the hypothesis. Hence, for each color $c$, the set $E_c$ of edges of color $c$ is a matching in $K_n$. Because $E_c$ is a matching, it contains at most $\lfloor n/2\rfloor$ edges. Summing over all colors and using that the edges of $K_n$ are partitioned by the color classes, we get\[
\binom{n}{2}
\;=\;
\sum_{c} |E_c|
\;\le\;
m\cdot \big\lfloor\tfrac{n}{2}\big\rfloor.
\]Rearranging yields\[
m\ \ge\ \frac{\binom{n}{2}}{\lfloor n/2\rfloor}
=
\begin{cases}
n, & \text{if } n \text{ is odd} ,\\
n-1, & \text{if } n \text{ is even}.
\end{cases}
\]This proves the stated small sharpening.
 Quanyu Tang
 — 05:42 on 02 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 I have tried to so some improvement based on Zach's idea given above in the comments of the problem, I would be glad, if someone points out any mistakes or corrections in my understanding of the problem.
Let $A \subset \mathbb{R}^2$ be a set of $n$ points such that no three points of $A$ form an isosceles triangle.
Equivalently, if we project $A$ onto the real line, the image is a set of $n$ real numbers containing no nontrivial $3$-term arithmetic progressions.
Define $f(n)$ by\[
|A-A| \;\ge\; f(n)\,n.
\]Erdos asked whether $f(n)\to\infty$ as $n\to\infty$. Dumitrescu (2008) showed\[
(\log n)^c \;\le f(n) \;\le 2^{O(\sqrt{\log n})}
\]for some constant $c>0$.
We improve the lower bound as follows.
Let $A$ be a finite subset of a torsion-free abelian group with $|A|=n$.
Set\[
S := A+A, \quad H := |S|, \quad D := |A-A|.
\](1) Ruzsa (2009) proved: if $A$ contains no nontrivial $3$-term arithmetic progression, then
\begin{equation}\
H \;\ge\; c_0\,n \left( \frac{n}{r_3(H)} \right)^{1/4},
\end{equation}
where $r_3(N)$ denotes the maximal size of a progression-free subset of $\{1,\dots,N\}$, and $c_0>0$ is absolute.
Also,
(2) Kelley--Meka (2023) proved that
\begin{equation}\
r_3(N) \;\le\; N \exp\!\big( -c_1 (\log N)^\beta \big),
\end{equation}
with an absolute $c_1>0$ and some $\beta>0$. Bloom--Sisask (2020) showed that $\beta=\tfrac{1}{9}$ is admissible.
Substituting (2) into (1) gives\[
H \;\ge\; c_0\,n \,\Big(\tfrac{n}{H}\Big)^{1/4}
\exp\!\Big( \tfrac{c_1}{4}\, (\log H)^\beta \Big).
\](3) Equivalently,
\begin{equation}\
H^{5/4} \;\ge\; c\, n^{5/4} \exp\!\Big( \tfrac{c_1}{4}\,(\log H)^\beta \Big).
\end{equation}
Note that $H \ge n$ trivially. Thus $\log H \ge \log n$.
From (3), one may apply a standard iteration/bootstrapping argument:
if $H \ll n \exp( C (\log n)^\beta)$, then the exponential factor on the right-hand side strictly dominates, leading to a contradiction for large $n$. Therefore, the inequality (3) forces: (4)
\begin{equation}\
H \;\ge\; n \exp\!\Big( c_2 (\log n)^\beta \Big),
\end{equation}
for some absolute constant $c_2>0$ and all sufficiently large $n$.
This step requires care since the exponential factor contains $\log H$, not $\log n$. A standard way to resolve this is to observe that if $H \le n \exp(C(\log n)^\beta)$, then $\log H \le \log n + O((\log n)^\beta)$, so $(\log H)^\beta = (\log n)^\beta (1+o(1))$, hence the factor $\exp(c_1(\log H)^\beta/4)$ still gives the desired contradiction. Iterating yields (4).
By a standard Plunnecke inequality, if $|A-A| \le K n$, then $|A+A| \le K^2 n$.
Equivalently,\[
D \;=\; |A-A| \;\ge\; \sqrt{Hn}.
\]Applying (4), we obtain\[
D \;\ge\; \sqrt{Hn}
\;\;\ge\;\; n \,\exp\!\Big( \tfrac{c_2}{2} (\log n)^\beta \Big).
\]Thus\[
f(n) \;=\; \frac{D}{n} \;\ge\; \exp\!\Big( c (\log n)^\beta \Big),
\]for some absolute constant $c>0$ and $\beta=\tfrac{1}{9}$ possible.
Hence $f(n)$ grows quasipolynomially, substantially improving the earlier polylogarithmic lower bound of Dumitrescu.
References can be found here:
Ruzsa, Sumsets and structure, in: Combinatorial Number Theory and Additive Group Theory, Birkh\"auser, 2009.
S. Kelley and R. Meka, Strong bounds for 3-term arithmetic progressions, Ann. of Math. 197 (2023) no. 1.
T. Bloom and O. Sisask, Breaking the logarithmic barrier in Roth’s theorem, Ann. of Math. 192 (2020).
A. Dumitrescu, On distinct distances with no isosceles triangles, Discrete Comput. Geom. 39 (2008), no. 4–5.
 Alfaiz
 — 12:41 on 01 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 It seems one can get (4) in a slightly simpler (and a bit stronger) way, without passing to \(r_3(H)\) or doing a bootstrap on \(\log H\). By Ruzsa’s original bound (Eq. (9.4) in Ruzsa, Sumsets and Structure, 2009),\[
|A+A|\ge cn\Big(\frac{n}{r_3(n)}\Big)^{1/4}.
\]Combining this with the Kelley–Meka bound (2),\[
r_3(n) \le n\exp \big(-c_1(\log n)^{\beta}\big),
\]we get immediately\[
H=|A+A| \ge cn\exp\Big(\frac{c_1}{4}(\log n)^{\beta}\Big),
\]which is exactly of the form (4) and avoids any iteration. Then, by Ruzsa’s twin to the triangle inequality \(|A+A||A|\le |A-A|^2\), one also gets \(|A-A|\ge n\exp\big(\tfrac{c_1}{8}(\log n)^{\beta}\big)\) and hence \(|A-A|/n\ge \exp\big(\tfrac{c_1}{8}(\log n)^{\beta}\big)\).
 Quanyu Tang
 — 15:52 on 01 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 I think I have found a gap in your argument. 
The reduction from the planar problem ($A \subset \mathbb{R}^2$ with no isosceles triangles) to the one-dimensional case ($A \subset \mathbb{R}$ with no nontrivial 3-term arithmetic progression) is not valid: projecting to the real line does not preserve the “no isosceles triangle” property, so the two formulations are not equivalent. 
That said, your improvement on Dumitrescu’s lower bound in the one-dimensional setting is entirely correct, since in fact Dumitrescu’s result itself only concerns the case $A \subset \mathbb{R}$. For sets on the line we do have $nf(n)=\Theta(|A-A|)$, so applying recent additive combinatorics results gives a genuine strengthening. In fact, your detailed proof appears to be an expanded version of the approach already pointed out earlier by zach hunter in his comments. However, for $A \subset \mathbb{R}^k$ with $k \geq 2$, no such strengthening is currently known.
 Quanyu Tang
 — 19:34 on 01 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 Indeed, you are correct. The improvement is valid for the one-dimensional/torsion free abelian group problem. For \(A \subset \mathbb{R}^2\), the question remains open.
And yes, I tried to do some improvement, based on Zach's idea.
 Alfaiz
 — 01:56 on 02 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 A result of Ruzsa shows that if $A$ is $3$-AP-free with $n$ elements (inside a torsion-free group), then $|A+A|\ge (1/2)n (n/r_3(n))^{1/4}$. Thus by Plunnecke-Ruzsa and Kelley-Meka, one can improve the bounds of Dumitrescu to be quasipolynomial.
(The site has been updated to address this comment.)
 zach hunter
 — 06:16 on 19 Aug 2025
 👍
 0
 📝
 0
 🤖
 0