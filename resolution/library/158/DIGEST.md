# erdosproblems.com #158: problem page and forum thread (fetched 2026-10-15T07:43:47Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $A\subset \mathbb{N}$ be an infinite set such that, for any $n$, there are most $2$ solutions to $a+b=n$ with $a\leq b$. Must\[\liminf_{N\to\infty}\frac{\lvert A\cap \{1,\ldots,N\}\rvert}{N^{1/2}}=0?\]
#158: [ESS94]
sidon sets
If we replace $2$ by $1$ then $A$ is a Sidon set, for which Erdős proved this is true.

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I posted a computational note on greedy $B_2[2]$ sets here: https://zenodo.org/records/18452185. 
Let $A\subset\mathbb{N}$ be constructed by the greedy rule: at step $k+1$, choose the smallest $m>a_k$ such that every sum $n$ has at most two representations $n=a+b$ with $a\le b$ and $a,b\in A\cup\{m\}$. The computation reaches $a_{2000}=7{,}445{,}662$, and the normalized count $|A\cap[1,N]|/\sqrt{N}$ stays around $0.7$ in this range (e.g. $\approx 0.733$ at $N=a_{2000}$). This supports the possibility that $\liminf_{N\to\infty}|A\cap[1,N]|/\sqrt{N}>0$, i.e. a counterexample to Problem 158 may exist.
 Zeraoulia Rafik
 — 23:05 on 01 Feb 2026
 👍
 0
 📝
 0
 🤖
 0