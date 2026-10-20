# erdosproblems.com #810: problem page and forum thread (fetched 2026-10-20T07:31:12Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Does there exist some $\epsilon>0$ such that, for all sufficiently large $n$, there exists a graph $G$ on $n$ vertices with at least $\epsilon n^2$ many edges such that the edges can be coloured with $n$ colours so that every $C_4$ receives $4$ distinct colours?
#810: [BEGS8,p.273][Er91,p.399]
graph theory | 
ramsey theory
A problem of Burr, Erdős, Graham, and Sós [BEGS89], who believed the answer is no.
Equivalently, if $\chi_S(n,e,G)$ is the anti-Ramsey number, the smallest $r$ such that there is a graph with $n$ vertices and $e$ edges with an $r$-colouring of its edges in which every copy of $G$ has entirely distinct edge colours, then this asks whether there exists an $\epsilon>0$ such that\[\chi_S(n,\epsilon n^2,C_4)\leq n\]for all large $n$. In [BEGS89] they prove there does not exist such $\epsilon$ if we replace $C_4$ with $P_4$.
In [BEGS89] they ask the stronger question as to whether, for fixed $\epsilon>0$,\[\chi_S(n,\epsilon n^2,G)/n\to \infty\]as $n\to \infty$ for all connected bipartite $G$ which is not a star. This was proved for all such $G$ except complete bipartite graphs by Sárközy and Selkow [SaSe06]. It remains open in particular for $C_4$.
In [BEGS89] they also observe that, for some constant $c>0$,\[\chi_S(n, cg(n;7,4),C_4)\leq n,\]where $g(n;7,4)$ is the maximum number of edges in a $3$-uniform hypergraph on $n$ vertices in which no $7$ vertices contain $4$ edges. It is unknown whether (but likely) that $g(n;7,4)=o(n^2)$ (see [1178]).
See also [809].

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A negative answer to this problem implies the (finite field) Ajtai-Szemeredi theorem that for $d$ large, every dense subset of $F_2^d \times F_2^d$ contains a square $\{ (a,b), (a,b+r), (a+r,b), (a+r,b+r)\}$.. Indeed, if one could find a dense set $A \subset F_2^d \times F_2^d$ without squares, then one can form the bipartite graph joining $a \in F_2^d $ to $b \in F_2^d$ if $(a,b) \in A$, and color it by $a+b$; as no rectangle in $A$ is a square and we are in characteristic 2, this bipartite graph has all $C_4$s polychromatic and is dense, thus positively answering this problem.
By considering other coloring schemes than $a+b$, we see that a negative answer to this problem actually implies quite a lot of Ajtai-Szemeredi type theorems; only one of these has to fail in order to positively answer the question.
EDIT: the problem seems vaguely reminiscent of the recently popular topic of skew-corner-free sets. The problem is close to that of asking for $\gg n^2$ points in $\{1,\dots,n\}^3$ that do not contain a pattern of the form $(a,b,c), (a,b',c'), (a',b',c), (a',b,c'')$ (here the third component should be thought of as the "color" of the edge connecting the first two components).
 TerenceTao
 — 06:23 on 07 Dec 2025
 👍
 2
 📝
 0
 🤖
 0
 Consider the set $S = \{(a,b,a): a,b,\in [N]\}$. Note that is one contains a pattern of the form shown we have that $a = c$ and $a' = c$. This forces $a = a'$ so we don't get a genuine $4$ cycle in the base as $(a,b) = (a',b)$ in this example. 
This counterexample was given by ChatGPT 5.1 Pro. (This seems to be a ''mistaken'' version of the $(7,4)$ problem presumably?)
 msawhney
 — 22:10 on 07 Dec 2025
 👍
 0
 📝
 0
 🤖
 0
 But this is not a counterexample to the original problem. Terry's reformulation is not literal. The exact (obvious) reformulation reads: does there exist a set $A\subseteq[n]^2$ with $\gg n^2$ elements and a function $f\colon A\to[n]$ such that the graph of $f$ does not contain any of the following $6$ patterns:\[ (a,b), (a,b',c'), (a',b,c''), (a',b',c''') \]with $a\neq a'$, $b\neq b'$ and $c=c'$ or $c=c''$ or $c=c'''$ or $c'=c''$ or $c'=c'''$ or $c''=c'''$.
What you wrote doesn't prevent all of them.
 Vjeko_Kovac
 — 22:35 on 07 Dec 2025
 👍
 1
 📝
 0
 🤖
 0
 Thanks for clarifying my post! (This does seem very close to the $(7,4)$ problem; see https://yufeizhao.com/gtacbook/gtacbook.pdf.) Note that the $(7,4)$ problem with loss of generality can be assumed to be on linear hyper graphs; if four hyperedges intersect at an edges this given a $(6,4)$ configuration so an easy pruning argument reduces to a linear hyper graph. Given this linear hypergraph, one may take a random tripartition which preserves a positive density of the edges. It is then a question of how to divide the seven vertices among the three parts. Every part obvious has at least $1$ vertex; however any $(5,1,1)$, $(4,2,1)$ or $(3,3,1)$ would force the hypergraph not to be linear. The $(3,2,2)$ split is then almost exactly the problem mentioned except that we have a ''designated'' part for the $3$ instead of having the freedom where it is placed. Given this connection I expect the problem not to be particularly easy.
 msawhney
 — 01:56 on 08 Dec 2025
 👍
 1
 📝
 0
 🤖
 0
 Is this a formal implication? i.e. does a negative answer to this problem #810 imply a positive answer to the (7,4) problem?
 TerenceTao
 — 16:05 on 08 Dec 2025
 👍
 0
 📝
 0
 🤖
 0
 I believe so? To see this, consider a hypergraph $\mathcal{H}$ with $n$ vertices and $\ge \varepsilon n^2$ hyperedges and suppose that is has no $(7,4)$ configuration. By reducing $\ \varepsilon \to \varepsilon/6$ (say) we may assume $\mathcal{H}$ is linear; this is due to the fact that if $4$ hyperedges all share a common pair of vertices this gives a $(6,4)$ configuration. Once $\mathcal{H}$ is linear we may then apply a random tripartition and get a $\mathcal{H}'$ which is tripartite with parts $A_1,A_2,A_3$ such that $|A_i| = n/3$ and $\mathcal{H}'$ has $\gg \varepsilon n^2$ edges. Define $G$ to be the $2$-graph between $(A_1,A_2)$ and define the coloring of $G$ by identifying by how a given edge extends into third part. A $3$-coloured $C_4$ in $G$ corresponds to a $(7,4)$ configuration in $\mathcal{H}'$ and hence in $\mathcal{H}$ as desired.
 msawhney
 — 16:32 on 08 Dec 2025
 👍
 5
 📝
 0
 🤖
 0
 In fact this implication is already mentioned in the original paper of Burr, Erdős, Graham, and Sós.
 mbucic
 — 13:37 on 01 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 Thanks! This prompted me to revisit that original paper and add more details and references.
 Thomas Bloom
 — 15:03 on 01 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 For anyone who wants to work with explicit examples, I got AlphaEvolve to find the densest n-colored graphs it could on $\{0,\dots,n-1\})$ with all $C_4$'s polychromatic for $n=4,\dots,25$. Here is the list (given as triples $(a,b,c)$ of edges $\{a,b\}$ colored by $c$, together with edge densities). The edge counts are
$$ (4,5), (5,7), (6,11), (7,14), (8,17), (9,23), (10,30), (11,34), (12,40), (13,47), (14,54), (15,62), (16,69), (17,77), (18,85), (19,94), (20,103), (21,112), (22,123), (23,133), (24,143), (25,155)$$
(e.g., for $n=25$ the example has 155 edges, for an edge density of $0.5167$. So if the edge density goes to zero, it does so rather slowly (but this is to be expected, given the connection to the Ajtai-Szemeredi theorem).
AlphaEvolve gives no guarantee of optimality. Perhaps some SAT-solver experts could work out the optimal edge counts for enough values of $n$ that an OEIS submission could be made.
 TerenceTao
 — 01:05 on 11 Dec 2025
 👍
 0
 📝
 0
 🤖
 0