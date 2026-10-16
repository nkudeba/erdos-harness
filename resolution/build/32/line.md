=== GOAL

**No settling line is plausible. This line aims at major progress (significance 3), not at settling.**

The formal `erdos_32` asks for a complement with $B(N)=o(\log^2N)$. It can be settled in only two ways, and both are blocked:

- **Disproof.** This needs $\limsup B/\log^2>0$ for every complement. By T2 that implies Cramér-scale prime gaps, far beyond FGKMT.
- **Proof.** This needs a complement adapted to the actual primes that beats the random ceiling and the Jensen/local-structure barrier. In other words, the primes would have to be markedly less random than every model predicts.

The statement is purely asymptotic, so no PARI/SAT computation can decide it. I see no exploitable convention: $0\in A$ is harmless and finite $A$ is impossible.

**Target (Erdős's \$50 question, question 2 negative):** prove that every $A$ with $P+A\supseteq[n_0,\infty)$ satisfies $B(X)/\log X\to\infty$.

The route goes through a covering lemma, CL(K):

> For every $K$ and every $\varepsilon>0$ there is $y_0$ such that every finite $H\subset\mathbb Z$ with $|H|\le Ky$ and $y\ge y_0$ admits residues $r_p \bmod p$ for all $p\le y$ with $\#\{h\in H: h\not\equiv r_p \ \forall p\le y\}\le \varepsilon\, y/\log y$.

How the pieces combine:

- CL(K) for all $K$ plus the CRT/Brun–Titchmarsh transfer gives $B(X)/\log X\to\infty$. An expert would rate that 3.
- CL(K₀) for one explicit $K_0$ above Ruzsa's threshold beats $e^\gamma$. That is a fallback rated 2.
- If CL turns out false for adversarial $H$, a proof of that is also valuable: it would be a barrier showing that CRT/Erdős–Rankin methods cannot answer the \$50 question.

=== WHY THIS LINE
**It is legal under the barriers.**
- T2 allows lower bounds up to the FGKMT rate, and $G/\log\to\infty$ is classical, so the target creates no gap-record contradiction.
- It avoids the parity/overlap problem behind the first-moment ceiling. It never needs lower bounds on prime pairs. It only needs to make $n-a$ composite by small-factor certificates (A2/A4) and then use a union bound with Brun–Titchmarsh upper bounds.
- The almost-all barrier is respected: the uncovered $n$ are CRT-chosen and have density zero.

**The reduction is sound and elementary.** I checked this sketch:
- Take $y=\theta\log X$ with $\theta<1$ and $Q=P(y)\approx X^{\theta}$.
- Cover $H=A\cap[0,X]$ with residues $r_p$. Every $n\equiv r \pmod Q$ then has $n-a$ divisible by some $p\le y$ for each covered $a$.
- The class has about $X^{1-\theta}$ representatives in $[X/2,X]$. Each $a$ blocks at most one representative through $n-a\le y$, so some $n$ dodges $A\cap[n-y,n)$.
- Survivors are handled by $\sum_{a\in S}\#\{n\equiv r\ (Q),\ n\le X:\ n-a\text{ prime}\}\le |S|\cdot 2X/(\varphi(Q)\log(X/Q))$, together with $Q/\varphi(Q)\sim e^\gamma\log y$.

**The covering problem is the real crux, and it is genuinely open.**
- For intervals, CL is Rankin. For random $H$, a first-moment count ($e^{y}$ residue systems against a miss probability of $e^{-Ke^{-\gamma}y/\log y}$) predicts covers up to $K\approx e^\gamma\log y$.
- The difficulty is adversarial $H$. Once survivors number fewer than $p$, pigeonhole forces no collisions mod $p$. So the gain must come from structure versus pseudorandomness, which suggests a hypergraph-covering (Pippenger–Spencer, as in FGKMT) plus dichotomy argument.

**No team results exist yet.** Everything here rests on standard theorems: Mertens, Brun–Titchmarsh, Ruzsa's argument, and the FGKMT covering lemma.

=== PLAN
1. **Referee the 2026 arXiv claim (≤1 day).** Locate the error the red flags predict: the $B=\{0\}$ specialisation and the T2 consequence. Stop if it fails. If it survives, it answers question 2, and the line becomes verifying it.
2. **Write the transfer lemma rigorously.** State: CL-type covering of $A\cap[0,X]$ with $\le\varepsilon\log X/\log\log X$ survivors implies an uncovered $n\in[X/2,X]$.
   - Include the window argument for $n-a\le y$, and the case $a=n$.
   - Sanity-check it by recovering a bound of order $\log X$ and comparing the constant with Ruzsa's $e^\gamma$.
   - Not established by the team.
3. **Compute (the PARI/SAT role).** For $y\le 60$–$100$, use ILP/MaxSAT (variables $x_{p,r}$, maximise covered elements) to estimate $m^*(y)$, the largest $m$ such that every tested $H$ of size $m$ is fully coverable.
   - Run an adversarial search over $H$: random sets, primes in a window, sets with bounded load mod every $p\in(\sqrt y,y]$, and sets equidistributed mod small $Q$.
   - Decision rule: if $m^*(y)/y$ grows, pursue step 4. If the hardest sets stay at $m^*=O(y)$, pivot to step 6.
4. **Prove CL(K) by dichotomy.**
   - (a) Random residues for $p\le z$.
   - (b) For $p\in(z,y]$, form the hypergraph whose edges are survivor classes mod $p$. If many surviving pairs differ by a multiple of a large $p$ (the "structured" case), apply the FGKMT/Pippenger–Spencer covering lemma.
   - (c) If survivor collisions are rare (the "pseudorandom" case), use a second-moment count over residue systems.
   - First prove CL(K₀) for one explicit $K_0$; that already beats $e^\gamma$.
5. **Combine steps 2 and 4** to get $B(X)/\log X\to\infty$, or $B\ge(e^\gamma+c)\log X$ from CL(K₀).
6. **Fallback if CL fails:** construct adversarial $H$ of size $Ky$ that cannot be covered, and prove that all CRT-certificate arguments cap at $O(\log X)$. That is a barrier result rated 2.

=== PITFALLS
- **No referee findings exist yet.** The team has produced nothing, so there is no catalogue of past errors to avoid.
- **The 2026 claim.** Do not use it until step 1 clears it.
- **T2 sanity check.** Any covering lemma with $K(y)\gg\log y\cdot L_4/L_3$ applies to intervals and would beat the FGKMT Jacobsthal bound. Treat it as suspect.
- **Pigeonhole failure.** Survivor sets smaller than $p$ have no forced collisions. Odd differences never survive mod 2, so collision counts must be restricted to same-parity (singular-series-compatible) pairs.
- **No averaged results.** Do not use averaged Hardy–Littlewood or Bombieri–Vinogradov with exceptional sets, because an adversarial $A$ may sit inside them. Use only Brun–Titchmarsh upper bounds, and track its factor $2/(1-\theta)$ and the requirement $Q\le X^{\theta}$.
- **Random-$A$ reasoning.** It says nothing about the lower bound for every $A$. Do not claim the formal `erdos_32` is settled: neither its negation (needs Cramér-scale gaps) nor the statement itself is reachable by this line.
