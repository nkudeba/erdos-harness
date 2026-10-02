# erdosproblems.com #156: problem page and forum thread (fetched 2026-10-02T01:25:16Z)

Comments are unverified; several withdraw earlier claims.

## Page
OPEN
This is open, and cannot be resolved with a finite computation.
Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?
#156: [ESS94]
sidon sets
A question of Erdős, Sárközy, and Sós [ESS94]. It is easy to prove that the greedy construction of a maximal Sidon set in $\{1,\ldots,N\}$ has size $\gg N^{1/3}$. Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N\log N)^{1/3}$.
See also [340].

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Some exact small-case data for the cyclic analogue of this problem.
Let $c(k)$ be the largest $n$ such that $\mathbb{Z}_n$ contains an inclusion-maximal Sidon set of size $k$ (Sidon in the group sense: $a+b=c+d$ implies ${a,b}={c,d}$).
Exhaustive search over all $n$ up to the trivial bound $(k^3+k^2+2k)/2$ gives $c(3),\ldots,c(7) = 14, 30, 50, 84, 126$, with witnesses ${0,2,3}$, ${0,19,21,22}$, ${0,7,19,20,22}$, ${0,7,55,56,58,67}$, ${0,21,50,103,104,119,121}$.
For comparison, the largest $n$ such that ${1,\ldots,n}$ contains an inclusion-maximal $k$-set is $10, 22, 42, 67, 101$ for $k=3,\ldots,7$ (from the data of OEIS A382397/A399118) and $144$ for $k=8$ (Huber, 2026). For $k=7$, maximal sets exist in $\mathbb{Z}_n$ for all $48 \le n \le 118$ and then only for $n = 120, 122, 124, 126$; for even $n$ every $a + n/2$ is blocked automatically.
Code, logs and an independent brute-force verification: https://github.com/veljjanoski/erdos156.
AI-usage disclosure: Claude (Anthropic) was used as a coding assistant.
 veljjanoski
 — 12:55 on 16 Sep 2026
 👍
 0
 📝
 0
 🤖
 0