# erdosproblems.com #103: problem page and forum thread (fetched 2026-10-11T17:47:23Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimise the diameter subject to the constraint that $d(x,y)\geq 1$ for all points $x\neq y$. Is it true that $h(n)\to \infty$?
#103: [Er94b]
geometry | 
distances
It is not even known whether $h(n)\geq 2$ for all large $n$.
See also [99].

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 What does "which minimize the diameter" mean? Is it the diameter of the set of $n$ points, or something directly about each of the incongruent sets?
 marinov
 — 15:38 on 27 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 Let $F$ be the family of all sets of $n$ points that satisfy $d(x,y)\geq 1$ for every pair of distinct points. If $$k=\min_{P\in F}diam(P),$$ then let $$F'=\{P\in F | diam(P)=k\}.$$
We can partition $F'$ into disjoint blocks such that two point sets belong to the same block if and only the point sets are congruent. Then $h(n)$ is the number of distinct blocks in the partition.
 Adenwalla
 — 15:58 on 27 Sep 2026
 👍
 0
 📝
 0
 🤖
 0