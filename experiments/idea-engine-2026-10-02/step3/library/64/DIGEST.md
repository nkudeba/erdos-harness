# erdosproblems.com #64: problem page and forum thread (fetched 2026-10-08T01:42:09Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Exhaustive search: no cubic bipartite counterexample on at most $62$ vertices.
Alfaiz's comment cites Markström [Ma04] (a cubic counterexample needs $\ge 30$ vertices) and Nowbandegani-Esfandiari [NoEs11] (a bipartite one needs $\ge 32$). For the cubic bipartite subclass there is a newer published bound not yet on this page: Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite Counterexamples to the Erdős-Gyárfás Conjecture", arXiv:2608.02675, which covers $n \le 58$ and so gives $\ge 60$. I have covered $n \le 62$, which gives $\ge 64$.
Every even $n$ from $4$ to $62$ was searched with no gaps, $1.85 \times 10^{10}$ search-tree nodes in total, $1.22 \times 10^{10}$ of them at $n = 62$ alone. Nothing in the range survived even the weaker filter of avoiding all of $C_4$, $C_8$ and $C_{16}$, so the $C_{32}$ test was never reached.
Tranquilli's proof opens with a Moore-bound observation he states as valid below $62$ vertices, so $n = 62$ falls just outside the range that observation covers. This reaches past it by brute force rather than by extending the structure theory.
The search generates connected cubic (bipartite) graphs in BFS-canonical labelling and prunes any partial graph already containing a $C_4$, $C_8$ or $C_{16}$, which is sound because a partial graph is a subgraph of every completion. It performs no isomorph rejection, so it over-generates; for a non-existence claim that is the safe direction, since duplicates only cost time whereas missed graphs would manufacture a false negative.
As an independent check, nauty's 'geng' reproduces the connected cubic bipartite counts (A006823) for every even $n$ up to $20$, and, restricted to the $C_4$-free graphs that alone could survive, up to $n = 28$; a separate cycle routine finds no survivor anywhere in that range. Beyond $n = 28$ no independent regeneration is feasible, so for $n$ from $30$ to $62$ exhaustiveness rests on the original generator being correct. That is the weakest point in the claim and I would treat it as such.
Two further limits. This covers only the cubic bipartite subclass and does not improve [NoEs11], since a bipartite counterexample need not be cubic. And my general cubic search reached only $n \le 34$, so I claim no advance there.
Code, certificates, the validation suite and step-by-step reproduction instructions:
https://github.com/sallerk/erdos-notes/tree/main/p64
Disclosure: the searches and computations herein were done with AI assistance.
Edits: compacted wording, added Github repo, added AI disclosure.
 sallerk
 — 06:10 on 31 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 A small improvement building on the work of A. Carr: any minimal counterexample has strictly more than \(2/3\) (up from \(4/7\)) of its vertices of degree exactly \(3\). Found by ChatGPT 5.6 Sol High, not verified.
Let \(G\) be a counterexample to the Erdős--Gyárfás conjecture of minimum order and, subject to that, minimum size. Define\[ V_3=\{v\in V(G):d(v)=3\}, \qquad V_{\ge4}=\{v\in V(G):d(v)\ge4\}. \]Then\[ |V_3|\ge 2|V_{\ge4}|+1, \]and consequently\[ |V_3|>\frac23|V(G)|. \]Carr proved that \(V_{\ge4}\) is independent and that every vertex of \(G\) has a neighbor of degree \(3\). Hence every edge incident with \(V_{\ge4}\) joins \(V_{\ge4}\) to \(V_3\), while every vertex of \(V_3\) has at most two neighbors in \(V_{\ge4}\). Therefore\[ 4|V_{\ge4}| \le \sum_{v\in V_{\ge4}}d(v) =e(V_{\ge4},V_3) \le 2|V_3|, \]so\[ |V_3|\ge2|V_{\ge4}|. \]It remains to exclude equality. Suppose that\[ |V_3|=2|V_{\ge4}|. \]Equality must then hold throughout the preceding inequalities. Thus every vertex of \(V_{\ge4}\) has degree \(4\), and every vertex of \(V_3\) has exactly two neighbors in \(V_{\ge4}\) and one neighbor in \(V_3\). Construct a graph \(H\) with vertex set \(V_{\ge4}\) by replacing each \(x\in V_3\), whose two neighbors in \(V_{\ge4}\) are \(u_x\) and \(v_x\), with the edge \(u_xv_x\). The graph \(H\) is simple: two distinct vertices of \(V_3\) with the same two neighbors in \(V_{\ge4}\) would form a \(4\)-cycle in \(G\). Moreover, every vertex of \(H\) has degree \(4\). Since\[ |V(H)|=|V_{\ge4}|<|V(G)|, \]the minimality of \(G\) implies that \(H\) contains a cycle of length \(2^k\) for some \(k\ge2\). Replacing each edge of this cycle by its corresponding two-edge path through \(V_3\) produces a cycle in \(G\) of length\[ 2^{k+1}, \]a contradiction. Hence equality is impossible, and\[ |V_3|\ge2|V_{\ge4}|+1. \]Finally,\[ 3|V_3| >2\bigl(|V_3|+|V_{\ge4}|\bigr) =2|V(G)|, \]and therefore\[ |V_3|>\frac23|V(G)|. \]
 jul059
 — 16:32 on 26 Jul 2026
 👍
 0
 📝
 0
 🤖
 0
 The conjecture is confirmed for these cases:
(i) $K_{1,m}$-free graphs with minimum degree at least $m+1$ or maximum degree at least $2m-1$ by S. E. Shauger in [Sh98].
(ii) Planar claw-free graphs by D. Daniel and S. E. Shauger in [DaSh01].
(iii) 3-connected cubic planar graphs by C. C. Heckman and R. Krakovski in [HeKr13].
(iv) Cayley graphs on generalized quaternion groups, dihedral groups, semidihedral groups and groups of order $p^3$ in M. H. Ghaffari and Z. Mostaghim [GhMo18].
(v) Cayley graphs of order $2p^2$ and $4p$ by M. Ghasemi and R. Varmazyar in [GhVa21].
(vi) $P_8$-free graphs by Y. Gao and S. Shan in [GaSh22].
(vii) $P_{10}$-free graphs by Z. Hu and C. Shen in [HuSh24].
(viii) Diameter-2 graphs by A. Carr in [Ca26].
Additionally:
(I) K. Markstrom in [Ma04] has shown that any cubic counterexample to this conjecture must have at least 30 vertices.
(ii) Nowbandegani and H. Esfandiari in [NoEs11] has shown that any bipartite counterexample must have at least 32 vertices.
(iii) Nowbandegani, H. Esfandiari, M. H. S. Haghighi and K. Bibak in [NEHB14] has shown that any cubic claw-free counterexample must have 114 vertices and every claw-free graph with minimum degree at least 3 has a cycle whose length is $2^k$ or $3\times2^k$, for some positive integer $k$.
(iv) A. Carr in [Ca26b] has shown that in any minimal counterexample, every vertex is adjacent to a vertex of degree exactly $3$, and at least $4/7$ of its vertices have degree exactly $3$.
[Sh98]: S. E. Shauger, Results on the Erd˝os-Gy´arf´as conjecture in K1,m-free graphs, Congr. Numer. 134 (1998) 61-65.
[DaSh01]: D. Daniel, S. E. Shauger, A result on the Erd˝os-Gy´arf´as conjecture in planar graphs, Congr. vol. 153 (2001) 129-139
[HeKr13]: C. C. Heckman, R. Krakovski, Erd˝os-Gy´arf´as conjecture for cubic planar graphs, Electron. J. Comb. 20(2) (2013) 7-43.
(The site has been updated to address this comment.)
 Alfaiz
 — 19:00 on 06 Dec 2025
 👍
 1
 📝
 1
 🤖
 0