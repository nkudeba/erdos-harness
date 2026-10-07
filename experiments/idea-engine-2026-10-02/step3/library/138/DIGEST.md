# erdosproblems.com #138: problem page and forum thread (fetched 2026-10-06T16:06:57Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A new general lower bound by GPT:
https://arxiv.org/abs/2608.20824
 Xiao Hu
 — 03:28 on 24 Aug 2026
 👍
 0
 📝
 1
 🤖
 0
 The DeepMind prover agent has found a Lean proof for the difference variant as formalised in Formal Conjectures. Formal proof here.
An informal description of the proof is as follows. The argument is rather simple, once one knows what the right thing to prove is.
$Claim$: $W(k+1) \geq W(k) + k$
$Proof$: Given a 2-coloring of the first $W(k)-1$ integers without a monochromatic $k$-AP, we can extend it by $k$ further elements without creating a monochromatic $(k+1)$-AP by proceeding greedily. Adding new elements one by one, suppose we have validly colored up to $M$ (where $M < W(k)-1+k$); we simply color $M+1$ red if doing so doesn't create a red $(k+1)$-AP, and blue otherwise. The only way this algorithm could result in an invalid coloring is if both choices are blocked, meaning there is already a red $k$-AP with some step size $d_R$ and a blue $k$-AP with some step size $d_B$ such that the $(k+1)$-th element for both progressions lands exactly on $M+1$. But this is impossible. Because our original interval up to $W(k)-1$ has no monochromatic $k$-APs, these progressions must contain at least one newly added element, which bounds their step sizes to $d_R, d_B \le k-1$. Hence, if we step backward $d_B$ times along the red progression and $d_R$ times along the blue progression, both calculations land exactly on the positive integer $M + 1 - d_R d_B$, meaning this single point would have to be simultaneously colored red and blue, which is a contradiction.
 Adam Zsolt Wagner
 — 09:30 on 10 Apr 2026
 👍
 5
 📝
 0
 🤖
 0
 Nice, thanks! This is quite a fun argument; it's interesting to compare this to the difference of consecutive Ramsey numbers (see [1030]).
Here you're taking advantage of the fact (which has no graph theoretic analogue as far as I can see) that any two arithmetic progressions of length $k$ and step size $<k$ with the same start/end point must have at least one other point in common. I don't recall seeing this nice fact used before, but I'm sure I'm wrong, and would be interested to see other applications.
EDIT: The obvious generalisation proves that\[W(k+1,l+1) \geq W(k,l)+\min(k,l).\]It's interesting to explore what this kind of argument can prove for the $r$-colour variant $W_r(k)$ (in which we want to $r$-colour the integers without any monochromatic $k$-AP). A naive first attempt proves\[W_r(k+1)-W_r(k)\geq k+r-1.\]
 Thomas Bloom
 — 09:51 on 10 Apr 2026
 👍
 3
 📝
 0
 🤖
 0
 GPT-5.4 Thinking and I in these notes have refined the difference bound to:
$$ W_r(k+1) - W_r(k) \ge k + \min(k, F(r)) + 1, $$
where $F(r) = \Theta(r \log \log r)$ is an explicit function. So for large $r$ and large $k$ depending on $r$, the difference is at least $k + \Theta(r \log \log r)$.
 Nat Sothanaphan
 — 18:59 on 10 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 Szabó in An Application of Lovász' Local Lemma-A New Lower Bound for the van der Waerden Number (1990) showed that for all $\varepsilon > 0$, there exists $k_0(\varepsilon)$ such that for all $k \geq k_0(\varepsilon)$, $W(k) \geq \frac{2^k}{k^\varepsilon}$.
EDIT: Kozik and Shabanov in Improved algorithms for colorings of simple hypergraphs and applications (2016)
showed that $W(n,r)>cr^{n−1}$ for some constant $c > 0$ (so in particular $W(k,2) = W(k) >c2^{k-1} = (c/2) 2^k$). This is the current best lower bound for $W(k)$. Thanks to Zach Hunter for pointing out this result!
(The site has been updated to address this comment.)
 JakeMallen
 — 00:23 on 28 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 false. Kozik and Shabanov get a lower bound of $W(k) > c2^k$.
(The site has been updated to address this comment.)
 zach hunter
 — 01:20 on 28 Dec 2025
 👍
 1
 📝
 2
 🤖
 0
 In Van der waerden and ramsey type games(by Jozsef Beck, 1980), it is given that:
"Erdos and Lovasz (unpublished), asserts that $W(p)>p2^p$ if $p$ is a prime and $W(n)>c2^n$ for all $n$."
They obviously don't give any references for the intended paper. Perhaps, some search would confirm this fact...
 Alfaiz
 — 18:12 on 01 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 Note that the first assertion contains a typo; it should be Berlekamp's result, $W(p+1)≥p2^p$. Beck explicitly cites the Berlekamp 1968 paper as reference [4], which is [Be68] in this problem's description. If $W(p)>p2^p$ were true, then for $p=3$ we would have $W(3)>24$. However, we know the exact value of $W(3)$ is $9$, which is a contradiction.
 JakeMallen
 — 23:16 on 27 Dec 2025
 👍
 1
 📝
 0
 🤖
 0