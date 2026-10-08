# erdosproblems.com #458: problem page and forum thread (fetched 2026-10-08T01:42:19Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I extended the verification from $10^{12}$ to $10^{20}$, using the prime gap records that already exist rather than any new large search.
By the product criterion above, a counterexample gap must contain prime powers $q^a$ ($a \geq 2$) whose distinct bases multiply to at least $p_k$. A single square plus a single higher power is never enough, since $p_{k+1}^{1/2+1/3} < p_k$ in the relevant range. So a counterexample needs either two squares in one gap, which forces $p_{k+1}-p_k > 2\sqrt{p_k}$, or two higher powers in one gap.
Both are ruled out below $10^{20}$. Every prime gap up to $10^{20}$ has length at most $1854$ (exhaustive to $4\times 10^{18}$ by Oliveira e Silva, Herzog and Pardi, Math. Comp. 83 (2014), and to $10^{20}$ by the community prime gap search as of
May 2026; see A005250), while $2\sqrt{p_k} > 1854$ once $p_k > 859329$. I also checked all $341805$ prime powers $q^a$, $a \geq 3$, below $1.05 \times 10^{20}$: the only two lying within $1854$ of each other are $73^3 = 389017$ and $5^8 =
390625$. The small range I checked directly (exact lcm to $3\times 10^5$, the product criterion to $10^9$); the worst case is still $(7,11)$ with $6 < 7$.
So any counterexample has $p_{k+1} > 10^{20}$. Caveats: above $4\times 10^{18}$ the gap bound rests on the distributed search rather than refereed work, and this is verification only; it says nothing about the Legendre-type obstruction in the remarks.
 bhowerton
 — 21:22 on 12 Jun 2026
 👍
 1
 📝
 0
 🤖
 0
 I ran a computational check of this conjecture up to $p_{k+1} \leq 10^{12}$ and found no counterexample.
Using the identity
$\operatorname{lcm}(1,\ldots,n)=\prod_{q \leq n,\ q\ \mathrm{prime}} q^{\lfloor \log_q n \rfloor}$,
for two consecutive primes $p<r$, the quotient
$\operatorname{lcm}(1,\ldots,r-1)/\operatorname{lcm}(1,\ldots,p)$
is equal to
$\prod q$,
where $q$ runs over prime bases such that some prime power $q^a$ lies strictly between $p$ and $r$. More precisely, $q$ is counted with multiplicity equal to the number of powers $q^a$ in $(p,r)$, though in the tested range no repeated base occurred in one gap.
Thus the desired inequality for the gap $(p,r)$ is equivalent to checking
$\prod_{q^a \in (p,r)} q < p$.
Algorithm used:
1. Generate all prime powers $q^a < 10^{12}$ with $a \geq 2$.
2. For each such prime power $m=q^a$, find the previous prime $p<m$ and next prime $r>m$ using deterministic Miller--Rabin primality testing.
3. Group all such $m$ by the prime gap $(p,r)$.
4. For each gap with $r \leq 10^{12}$, multiply the corresponding prime bases $q$.
5. Check whether this product is ever $\geq p$.
No failing gap was found. The closest case was the small gap $(7,11)$, where the powers $8=2^3$ and $9=3^2$ occur, giving product $2\cdot 3=6<7$.
This is only a computational verification, not a proof, and I do not know whether this computation has already appeared elsewhere in the literature.
 Zeraoulia Rafik
 — 22:59 on 27 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 This question is equivalent to asking whether for all $k \geq 1$, the prime $p_k$ is greater than the product of all primes with powers in between $p_k$ and $p_{k+1}$.
 DesmondWeisenberg
 — 20:07 on 19 Aug 2025
 👍
 1
 📝
 0
 🤖
 0