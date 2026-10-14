# erdosproblems.com #695: problem page and forum thread (fetched 2026-10-10T18:59:21Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $p_1<p_2<\cdots$ be a sequence of primes such that $p_{i+1}\equiv 1\pmod{p_i}$. Is it true that\[\lim_k p_k^{1/k}=\infty?\]Does there exist such a sequence with\[p_k \leq \exp(k(\log k)^{1+o(1)})?\]
#695: [Er79e]
number theory
Such a sequence is sometimes called a prime chain. 
If we take the obvious 'greedy' chain with $2=p_1$ and $p_{i+1}$ is the smallest prime $\equiv 1\pmod{p_i}$ then Linnik's theorem implies that this sequence grows like\[p_k \leq e^{e^{O(k)}}.\]It is conjectured that, for any prime $p$, there is a prime $p'\leq p(\log p)^{O(1)}$ which is congruent to $1\pmod{p}$, which would imply this sequence grows like\[p_k\leq \exp(k(\log k)^{1+o(1)}).\]An extensive study of the growth of finite prime chains was carried out by Ford, Konyagin, and Luca [FKL10].
See also [696].

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 My guess for the first question is yes.
Since the $q$'s are prime, there are no excluded prime divisors of $kq+1$ and thus the various $k$ can be expected to grow on average at least like $\log(q)$.
The greedy sequence, [oeis/A061092], is the natural candidate for the second question.
 StijnC
 — 21:02 on 10 Aug 2025
 👍
 0
 📝
 0
 🤖
 0