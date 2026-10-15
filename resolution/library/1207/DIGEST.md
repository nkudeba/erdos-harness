# erdosproblems.com #1207: problem page and forum thread (fetched 2026-10-15T06:40:21Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $P_d(n)$ be such that in any set of $n$ points in $\mathbb{R}^d$ there exist at least $P_d(n)$ many points which do not contain an isosceles triangle. Estimate $P_d(n)$ - in particular, is it true that\[P_2(n)<n^{1-c}\]for some constant $c>0$?
#1207: [Er80,p.110]
geometry | 
distances
Erdős [Er80] attributes this problem to Riddell, and states it is not hard to prove that $P_d(n)>n^{\epsilon_d}$ where $\epsilon_d\to 0$ as $d\to \infty$. Indeed, one can take any subset of points with all distinct distances, whence\[P_d(n)\geq f_d(n) \geq n^{\frac{1}{3d-3}-o(1)}\]with $f_d(n)$ defined as in [1208].
Erdős suggested that perhaps the worst set of points is the set of lattice points in a sphere of suitable radius.
The case $d=1$ is equivalent to finding sets with no three-term arithmetic progressions, and is the $k=3$ case of [201]. 
The bound of Pach and Tardos [PaTa02] on the maximum number of isosceles triangles in a point set, together with a random deletion argument, shows that $P_2(n) \gg n^{0.432}$. In Section 5.3 of [BMP05] they claim that the regular polygon shows that $P_2(n) \ll n^{1/2}$ but give no details. This seems to be incorrect, since an isosceles triangle from the vertices of a regular polygon correspond to three points whose angles form an arithmetic progression. This shows that $P_2(n)\ll r_3(n)$, where $r_3(n)$ is the maximum size of a subset of $\{1,\ldots,n\}$ without a non-trivial three-term arithmetic progression (see [140]).
A better construction, which proves that $P_2(n)<n^{1-c}$ for some absolute constant $c>0$, was found by Lee, Pohoata, and Zhu (assisted by ChatGPT) [LPZ26]. (This construction is similar to that used for the unit distance problem [90]). 
Although this answers the main question of Erdős, I leave this open as a general challenge to estimate $P_d(n)$ more generally.
See [1208] (and also [657]) for a variant in which we ask for all sets of three points to have distinct distances.
Additional thanks to: KentaKitamura

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I would like to mention the recent preprint of Lee--Pohoata--Zhu, “The Minkowski grid has robustly many repeated distances”. 
It appears to settle the conjectural part of Problem #1207.
The authors explicitly say in the abstract that their first result “confirms a conjecture of Erdős from 1980”, and after Corollary 3 they again write that “the first result confirms a conjecture by Erdős from 1980”.
(The site has been updated to address this comment.)
 KentaKitamura
 — 23:43 on 08 Jul 2026
 👍
 2
 📝
 1
 🤖
 0