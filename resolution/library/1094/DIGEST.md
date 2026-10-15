# erdosproblems.com #1094: problem page and forum thread (fetched 2026-10-15T05:52:18Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
For all $n\geq 2k$ the least prime factor of $\binom{n}{k}$ is $\leq \max(n/k,k)$, with only finitely many exceptions.
#1094: [ELS88][ELS93]
number theory | 
binomial coefficients
A stronger form of [384] that appears in a paper of Erdős, Lacampagne, and Selfridge [ELS88]. Erdős observed that the least prime factor is always $\leq n/k$ provided $n$ is sufficiently large depending on $k$. Selfridge [Se77] further conjectured that this always happens if $n\geq k^2-1$, except $\binom{62}{6}$.
The threshold $g(k)$ below which $\binom{n}{k}$ is guaranteed to be divisible by a prime $\leq k$ is the subject of [1095].
More precisely, in [ELS88] they conjecture that if $n\geq 2k$ then the least prime factor of $\binom{n}{k}$ is $\leq \max(n/k,k)$ with the following $14$ exceptions:\[\binom{7}{3},\binom{13}{4},\binom{23}{5},\binom{14}{4},\binom{44}{8},\binom{46}{10},\binom{47}{10},\]\[\binom{47}{11},\binom{62}{6},\binom{74}{10},\binom{94}{10},\binom{95}{10},\binom{241}{16},\binom{284}{28}.\]They also suggest the stronger conjecture that, with a finite number of exceptions, the least prime factor is $\leq \max(n/k,\sqrt{k})$, or perhaps even $\leq \max(n/k,O(\log k))$. Indeed, in [ELS93] they provide some further computational evidence, and point out it is consistent with what they know that in fact this holds with $\leq \max(n/k,13)$, with only $12$ exceptions.
Discussed in problem B31 and B33 of Guy's collection [Gu04] - there Guy credits Selfridge with the conjecture that if $n> 17.125k$ then $\binom{n}{k}$ has a prime factor $p\leq n/k$. 
This is related to [1093], in that the only counterexamples to this conjecture can occur from $\binom{n}{k}$ with deficiency $\geq 1$.
There is an interesting discussion about this problem on MathOverflow.
Additional thanks to: Alfaiz

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A part of this problem has been discussed on MathOverflow.
(The site has been updated to address this comment.)
 Alfaiz
 — 12:45 on 18 Oct 2025
 👍
 2
 📝
 2
 🤖
 0