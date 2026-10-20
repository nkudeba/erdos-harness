# erdosproblems.com #663: problem page and forum thread (fetched 2026-10-20T08:51:26Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $k\geq 2$ and $q(n,k)$ denote the least prime which does not divide $\prod_{1\leq i\leq k}(n+i)$. Is it true that, if $k$ is fixed and $n$ is sufficiently large, we have\[q(n,k)<(1+o(1))\log n?\]
#663: [BEGL96][Er97e]
number theory
A problem of Erdős and Pomerance.
The bound $q(n,k)<(1+o(1))k\log n$ is easy. It may be true this improved bound holds even up to $k=o(\log n)$. 
A heuristic argument in favour of this is provided by Tao in the comments. 
See also [457].
Additional thanks to: Terence Tao

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Here is a heuristic argument to suggest that the answer should be "yes". Fix $k$, take a random number $n \in [x,2x]$ and heuristically compute the probability that $q(n,k) \geq (1+\varepsilon) \log x$ for some fixed $\varepsilon > 0$. All the primes up to $(1+o(1)) \log x$ will have to divide one of $n+1,\dots,n+k$, so there are $k^{(1+o(1))(\log x/\log\log x)}=x^{(\log k+o(1))/\log\log x}$ ways to allocate these factors. By the Chinese remainder theorem and prime number theorem, this will determine $n$ uniquely. The "probability" that the primes from $(1+o(1)) \log x$ up to $(1+\varepsilon) \log x$ also divide one of $n+1,\dots,n+k$ is heuristically of the shape $(k /(1+O(\varepsilon))\log x)^{(1+o(1))\varepsilon \log x /\log\log x} = x^{-\varepsilon+o(1)}$, which should eventually overwhelm the $x^{(\log k+o(1))/\log\log x}$ factor and suggests that there are only finitely many $n$ with this property. But it looks quite hard to turn this into a rigorous argument!
Another trivial remark: the difficulty of this problem is monotone in $k$, so one can focus initially on the $k=2$ case if one is angling for a proof.
(The site has been updated to address this comment.)
 TerenceTao
 — 05:56 on 06 Sep 2025
 👍
 1
 📝
 1
 🤖
 0