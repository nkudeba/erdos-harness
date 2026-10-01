# Literature library (papers dated before 2026-06-02; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## On the non-(p-1)-partite K_{p}-free graphs (2012)
https://doi.org/10.7151/dmgt.1654; full text: abstract only

**Summary for the $h_4$ problem**

**Source text available.** Only a truncated abstract was supplied. There is no full text, so no theorem statements, constants or proofs can be quoted beyond the following.

**What the abstract states (verbatim):**
> "We say that a graph G is maximal K p -free if G does not contain K p but if we add any new edge e ∈ E(G) to G, then the graph G + e contains K p. We study the minimum and maximum size of non-(p -1)-partite maximal K p -free graphs with n vertices. We also answer the interpolation question: 10"

The abstract cuts off there. The interpolation question itself, and its answer, are not given.

**Content and method.**
- The topic is extremal and saturation-type size bounds for maximal $K_p$-free graphs that are not $(p-1)$-partite.
- For $p=3$, these are maximal triangle-free graphs that are non-bipartite.
- No specific results, constructions, constants or proof methods are stated in the provided text.
- The phrase "interpolation question" suggests the paper determines which edge counts between the minimum and maximum are attained. The text does not state this, and I cannot confirm it.

**Relation to the problem.**
- The problem asks about adding edges to a connected triangle-free graph while staying triangle-free, so as to reach diameter exactly 4.
- The paper's objects (maximal triangle-free graphs) are the endpoint of adding edges while staying triangle-free. Such graphs are saturated: adding any edge creates a triangle.
- The paper's case concerns non-bipartite such graphs on $n$ vertices and their edge counts.
- Edge-count bounds for maximal triangle-free graphs could at most give crude bounds on how many edges one can add in total. The problem, however, asks for the minimum number of additions to hit a specific diameter (4), with a bound of $(1-c)n$.
- Nothing in the abstract addresses diameter, distances, or the number of added edges needed to reach a prescribed diameter.

**Open questions stated.** None are visible in the provided text. The interpolation question is mentioned as answered, not open, and its statement is truncated.

**Verdict.** As far as the supplied text shows, the paper is essentially not relevant to the $h_4(G)<(1-c)n$ question. It is at most tangentially related, through the general theme of saturating triangle-free graphs. A full text would be needed to check whether any construction of sparse non-bipartite maximal triangle-free graphs could serve as an example or ingredient. Nothing usable can be extracted from the abstract alone.

## Minimizing the Diameter of a Network Using Shortcut Edges (2010)
https://doi.org/10.1007/978-3-642-13731-0_39; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## Improved approximability and non-approximability results for graph diameter decreasing problems (2011)
https://doi.org/10.1016/j.tcs.2011.05.014; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## $C_4$-saturated graphs of minimum size (1989)
W3179424942; full text: abstract only

**Verdict: essentially not relevant.** Only the abstract is available, and it contains no statement that bears directly on adding edges to a triangle-free graph to reach diameter 4.

**What the abstract actually contains**

- **Definition (F-saturated).** "Call a graph G F-saturated if F is not a subgraph of G, but a subgraph isomorphic to F appears whenever a new edge is added to G."
- **sat(n, F).** This is "the minimum number of edges in an F-saturated graph on n vertices." The stated problem is to determine sat(n, F), possibly for large n, and to describe the extremal graphs.
- **Small n.** "for n < |V(F)| the complete graph is the unique F-saturated one."
- **History.**
  - The first result is due to Erdős, Hajnal and Moon (1964).
  - The first general upper bound on sat(n, F) is due to Kászonyi and Tuza.
  - A survey [5] also covers hypergraphs and weakened conditions.
- **Open question stated.** "the value of sat(n, C₅) is not known. Perhaps it is 3n/2 + O(1) as n tends to infinity."
- **Main result.** The abstract announces that Ollman [4] proved a result for C₄, but it is cut off before the statement. So:
  - The exact value or formula for sat(n, C₄) is not given in the text.
  - No constants are given.
  - No methods or proofs are given.

**Possible tangential link to the problem**

- A triangle-free graph to which no edge can be added without creating a triangle is exactly a K₃-saturated graph.
- Triangle-free graphs of diameter 2 are exactly the maximal triangle-free graphs, so this is the h₂ setting.
- The problem asks about diameter 4, not saturation. The abstract offers no lemma, construction or bound about:
  - completing a graph to diameter r while staying triangle-free, or
  - linear-in-n edge counts for such completions.
- The only conceptual link is the general framework of minimum edge counts under "adding an edge creates F." The abstract states no sat(n, K₃) result.

**Open questions near the problem**

- None directly. The only stated open question is the conjectured value of sat(n, C₅) quoted above, which is unrelated to h₄.

**Recommendation.** The full paper, describing the C₄-saturated graphs of minimum size, might contain structural constructions, such as tree-like or sparse graphs of small diameter. Nothing of that kind can be extracted from the provided text.

## Independent domination in graphs: A survey and recent results (2013)
https://doi.org/10.1016/j.disc.2012.11.031; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## Improved approximation for tree augmentation: saving by rewiring (2018)
arXiv 1804.02242 (version 1); full text: yes

## Verdict

**This paper is essentially not relevant to the problem.**

The paper studies the Tree Augmentation Problem (TAP). You are given a tree $T=(V,E)$ and a set of candidate links $L$. The task is to add the fewest links so that the result is **2-edge-connected**. This is approximation algorithmics: LP and SDP rounding.

The problem asks something different in three ways:

- **Goal:** adding edges to a connected triangle-free graph to reach **diameter 4**, while keeping it **triangle-free**.
- **Question:** whether $h_4(G)<(1-c)n$.
- **Mismatch:** none of diameter, triangle-freeness, or extremal bounds in $n$ appears in the paper.

## Items with at most a loose structural connection

None of these is a direct ingredient.

1. **Theorem 1:** "There exists a 1.458-approximation algorithm for TAP."
   - The bound $\sqrt{34}/4<1.458$ is Theorem 4, for O(1)-wide instances.
   - Method: a $k$-wide LP made of {0,½}-Chvátal–Gomory cuts plus "local convex decomposition constraints", followed by "rewiring" (replacing pairs of cross-links by one link).

2. **Definition 2 (k-wide):** "there exists a vertex r … Any subtree of T consisting of r, one of its children u, and all descendants of u has at most k leaves."
   - **Lemma 17** decomposes any tree into subtrees $T_i$ with $T_i/H_i$ $k$-wide, at extra cost $O(1/\sqrt k)\cdot x(L)$.
   - Method: splitting at γ-light edges with $\gamma=1/\sqrt k$ and contracting ζ-heavy edges with $\zeta=\sqrt k/4$, following Adjiashvili.
   - This is a tree-decomposition idea that a tree-based argument might conceivably borrow.

3. **Lemma 13 (matching lemma):** "Let G=(V,E) be an undirected graph, let $x\in\mathbb R^E_{\ge0}$ such that for any v∈V we have $x(\delta(v))\le1$, and let A be a random subset of V with … (i) $\Pr[v\in A]=x(\delta(v))$ … (ii) $\Pr[v\in A \text{ and } u\in A]=\Pr[u\in A]\Pr[v\in A]$ ∀{u,v}∈E. Then there exists a matching M⊆E in G such that $E|M\cap\binom A2|\ge x(E)^2/|V|$."
   - Method: take a vertex of the polytope $Q$ (whose support has size at most $|V|$), run the greedy weighted matching, then apply Cauchy–Schwarz.
   - The paper notes this is essentially tight via a star example.
   - **Lemma 24** refines it to $\ge z(E_1)^2/|E_1|+z(E_2)^2/|E_2|$.

4. **Counting fact used in Lemma 15:** in a tree with $K$ leaves, the number of vertices of degree ≠ 2 (excluding the root) satisfies $|V_{crit}|<2K$. This follows from the average-degree argument.

5. **Lemma 9:** in a shadow-minimal link set on a $k$-wide tree, each principal subtree has at most $k$ cross-links with an endpoint in it. Method: pigeonhole over leaves.

## Open questions stated in the paper

None of these is close to the problem.

- The integrality gap of the cut-LP is known to be at most $2-2/15$ (Nutov) and at least 1.5.
- It is unknown "whether the stronger LPs introduced in [1] and [9] are any stronger than the canonical cut-LP."
- For weighted TAP, the authors make "no effort to obtain the best possible function $g(\Delta)$."

## Recommendation

Do not rely on this paper for the diameter/triangle-free augmentation problem. At most, the $k$-wide tree decomposition (Lemma 17) and the leaf/degree counting might inspire handling a spanning tree of $G$. The paper itself makes no such connection.
