# erdosproblems.com #902: problem page and forum thread (fetched 2026-10-19T22:34:51Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Let $f(n)$ be minimal such that there is a tournament (a complete directed graph) on $f(n)$ vertices such that every set of $n$ vertices is dominated by at least one other vertex. Estimate $f(n)$.
#902: [Er63c][Er82e]
graph theory
Schütte asked Erdős this in the early 1960s.
It is easy to check that $f(1)=3$ and $f(2)=7$. Erdős [Er63c] proved\[2^{n+1}-1 \leq f(n) \ll n^22^n.\]Szekeres and Szekeres [SzSz65] proved that $f(3)=19$ and\[n2^n \ll f(n).\]

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 The classical bounds are formalised in Lean 4 (Mathlib): 2^{n+1}−1 ≤ f(n) and f(n) ≤ n+3n²·2ⁿ as a single kernel-checked sandwich theorem, plus f(1)=3 and f(2)=7 by decision procedure. Axioms: propext, Classical.choice, Quot.sound. Source: https://github.com/jaredwilder/erdos902 - posted so nobody duplicates the effort.
 epassports
 — 16:53 on 26 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 A constructive proof for a weaker bound has been given by R. L. Graham and J. H. Spencer in [GrSp71].
Edit: Thanks to Stijn for clarifying!
 Alfaiz
 — 15:11 on 14 Dec 2025
 👍
 0
 📝
 0
 🤖
 0
 It is not solved there at all. It gives a constructive proof for a weaker bound.
(one could consider it solved once the order of the solution is known, where now upper and lower bound are a factor $n$ off)
 StijnC
 — 15:24 on 14 Dec 2025
 👍
 1
 📝
 0
 🤖
 0
 Correct. In fact, starting with "It seems" was an indicator of this underlying thought.
 Alfaiz
 — 15:28 on 14 Dec 2025
 👍
 0
 📝
 0
 🤖
 0