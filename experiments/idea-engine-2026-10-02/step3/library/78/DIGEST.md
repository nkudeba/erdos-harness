# erdosproblems.com #78: problem page and forum thread (fetched 2026-10-08T01:42:11Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Quick clarification question: my colleague has mentioned that Erdos's probabilistic bound $R(k)\gg 2^{k/2}$ can be derandomized via the method of conditional expectations, yielding a deterministic construction of a 2-coloring of $K_n$ with no monochromatic $K_k$ for $n\approx 2^{k/2}$.
Is such a derandomization considered "constructive" for the purposes of this problem, or would it make sense to clarify the question to ask for a substantially more explicit/efficient/algebraic construction (e.g. a fixed family of graphs)?
 Neel Somani
 — 02:24 on 15 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 Explicit. 
The derandomization here only gives an existence proof. For $n$ large it would indeed not be efficient either.
An algebraic construction would be good, but other ways of constructing would be allowed as well.
 StijnC
 — 08:16 on 15 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 The term "constructive" is somewhat subjective in mathematics, but perhaps one concrete question would be to exhibit a deterministic algorithm that, for a given $k$, produces a graph on exponentially many vertices with Ramsey number at least $k$, in time that is guaranteed to be less than double exponential in $k$.
 TerenceTao
 — 15:40 on 15 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 Gpt 5.5 pro seems to have found a solution to this formulation
Given \(k\), there is a deterministic algorithm running in
\(2^{O(k^2)}\) time which outputs a graph on \(2^{\Omega(k)}\) vertices with
no clique or independent set of size \(k\).
Let\[
N=\lfloor 2^{k/3}\rfloor,\qquad r=\binom{k}{2}.
\]Fix once and for all a lexicographic ordering of the edges of \(K_N\). For a
partial red/blue colouring \(P\) of the edges of \(K_N\), define\[
\Phi(P)=\sum_{S\in\binom{[N]}{k}}
\Pr(S\text{ becomes monochromatic after completing }P\text{ uniformly at random}).
\]This quantity is exactly computable by enumerating all \(k\)-sets \(S\). For
a given \(S\), the summand is \(0\) if \(S\) already contains both a red and
a blue edge; it is \(2^{-u}\) if \(S\) has at least one already-coloured edge,
all already-coloured edges of \(S\) have the same colour, and \(u\) edges of
\(S\) remain uncoloured; and it is \(2^{1-r}\) if all \(r\) edges of \(S\)
remain uncoloured.
Initially\[
\Phi(\varnothing)
=
\binom{N}{k}2^{1-r}
\leq
\frac{N^k}{k!}2^{1-k(k-1)/2}
\leq
\frac{2^{k^2/3+1-k(k-1)/2}}{k!}
=
\frac{2^{1-k^2/6+k/2}}{k!}
<1
\]for all sufficiently large \(k\).
Now colour the edges one at a time in the fixed order. Suppose \(e\) is the
next uncoloured edge. Then\[
\Phi(P)=\frac12\Phi(P\cup\{e=\mathrm{red}\})
 +\frac12\Phi(P\cup\{e=\mathrm{blue}\}),
\]so at least one of the two choices keeps \(\Phi\) from increasing. Choose such
a colour, breaking ties by choosing red. This is the standard method of
conditional expectations.
After all edges have been coloured, \(\Phi(P)\) is exactly the number of
monochromatic \(K_k\)'s in the final colouring. Since \(\Phi\) never increased
and \(\Phi(\varnothing)<1\), this final number is a nonnegative integer less
than \(1\), hence it is \(0\). Thus the red graph has neither a \(k\)-clique
nor a \(k\)-independent set.
The running time is \(2^{O(k^2)}\). There are \(O(N^2)=2^{O(k)}\) edge decisions,
and for each decision one may recompute \(\Phi\) by enumerating\[
\binom{N}{k}\leq N^k=2^{O(k^2)}
\]\(k\)-sets and inspecting \(O(k^2)\) edges. All probabilities can be handled
exactly, for instance by scaling \(\Phi\) by \(2^r\) and working with integers.
Finally, since\[
N=\lfloor 2^{k/3}\rfloor\geq 2^{k/4}
\]for all sufficiently large \(k\), this deterministic algorithm outputs a graph
on at least \(2^{k/4}\) vertices with no clique or independent set of size
\(k\). Hence it proves \(R(k)>2^{k/4}\) for all sufficiently large \(k\), in
the concrete algorithmic sense, with running time well below double-exponential
in \(k\). Equivalently, after decreasing the base constant if desired, this
gives \(R(k)>C^k\) for some absolute constant \(C>1\).
 aditya
 — 13:21 on 04 May 2026
 👍
 0
 📝
 0
 🤖
 0
 Yes, this is the well-known method of conditional expectations. (The method is detailed for example in the book of Alon and Spencer, and I'm sure that applying it to $R(k)$ like this has been written up explicitly a number of times before.)
What is usually meant by 'explicit' nowadays (see for example the introduction of [Co15], cited in the comments) is that there is an algorithm which, given any two vertices, determines whether the edge between them is present, which runs in time polynomial in $\log n$ (if the graph has $n$ vertices).
 Thomas Bloom
 — 15:59 on 04 May 2026
 👍
 0
 📝
 0
 🤖
 0