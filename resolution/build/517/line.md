=== GOAL

No line is likely to settle the true mathematical question. Erdős #517 is open, and the CORE reduction (no $Pe^g$ with $g$ transcendental has Fabry-gap Taylor support) is exactly the open problem. Almost all of the 0.03 comes from Step 0, a cheap audit of the Lean conventions. The main line is therefore a **major-progress line**, aimed at significance 3.

**Theorem (target).** Let $P\not\equiv 0$ be a polynomial and $g$ a transcendental entire function of **finite order** $\rho$. Then the Taylor support of $Pe^{g}$ does not satisfy $n_k/k\to\infty$.

**Corollary.** If $f$ has Fabry gaps and $c\in\mathbb C$ is any value, then $f-c\ne Pe^{g}$ for every $g$ of finite order. Equivalently, every Fabry-gap entire function whose iterated order $\limsup \log\log\log M/\log r$ is finite takes every value infinitely often.

This class contains infinite-order functions that Pólya's theorem cannot reach (it needs $f$ of finite order). It also contains every growth rate that Biernacki's gap condition excludes, so it is new on both axes. Such functions sit squarely in the CORE regime: infinite lower order, $\sum 1/n_k=\infty$ allowed, and $s(r)\log s(r)\gtrsim\psi$ allowed. An expert would rate it 3: it is the first Fabry-only result past the Fejér/Biernacki convergence threshold in infinite order.

=== WHY THIS LINE
The barriers that kill one-circle methods are the gap-versus-growth trade-off, block functions and recurrence length. This line does not fight them on a single circle. It uses one extra global rigidity, finite order of $g$, which is exactly what the **thin-tracts** barrier lacks.

- **The tract of 0 is a set of $\operatorname{Re} g$.** A Picard-exceptional $c$ is an asymptotic value, and $\{|f-c|<\varepsilon\}$ is essentially $\{\operatorname{Re} g<-K\}$. Here $g$ has finite order, and $\operatorname{Re} g$ is a harmonic function of finite order. So Carleman–Tsuji / Ahlfors distortion bound the number of tracts of $\operatorname{Re} g$ by about $2\rho$. They also force $\int^{R}\frac{dr}{r\,\theta(r)}\le \rho\log R+O(1)$ for the angular measure $\theta(r)$ of the tract, so tracts cannot be super-thin on most scales.
- **Block functions are not of this type.** Their transitions $D\to D'$ require $g$ to change "degree" across scales without bound, so they do not contradict this line.
- **The other ingredient is Fabry's arc-locality.** The barriers list explicitly says thin tracts "do not rule out arc-local Fabry theorems". Pólya's local form of Fabry says the singularities are dense on every arc.
- **The contradiction.** A fixed-width angular region along which $f\to c$ at the rate $|f-c|\le e^{-\text{huge}}$ should contradict Fabry arc-locality when $f$ is rescaled to a circle of convergence.

The team has no validated results yet. The line builds only on the KNOWN entries: Picard/Iversen factorization, shift invariance, Fabry/Pólya arc-local, Nazarov, and Fuchs's finite-order method as a template.

=== PLAN
0. **Convention audit (do first, at most an hour).**
   - Read the exact definition of `HasFabryGaps`.
   - If it does **not** force `n` to be injective or StrictMono, disprove the statement directly:
     - Take $n_{2j}=n_{2j+1}=2^{j}$ (for $j\ge 1$), which satisfies $n_k/k\to\infty$.
     - Take $a_{2j}=1/(2^j)!$ and $a_{2j+1}=-1/(2^j)!$. These are all nonzero.
     - The series is absolutely summable everywhere and $f\equiv 0$, so $\{x\mid f x=1\}=\emptyset$, which is a counterexample with $z=1$.
     - Check how $n\,0/0=0$ is handled in the definition.
   - If StrictMono is required, record that the statement matches the informal problem. With $z=0$, the convention `0^0=1` is harmless.
   - Not yet done.
1. **Reduction (standard, write it out).**
   - Let $f$ be Fabry-gap with $f-c=Pe^g$.
   - Then $g$ is transcendental, because $f$ has infinitely many nonzero coefficients.
   - $f-c$ is Fabry-gap by shift invariance.
   - The tract $T_K=\{\operatorname{Re} g<-K\}$ contains an asymptotic path to $c$, and $\log|f-c|=\operatorname{Re} g+O(\log r)$.
2. **Tract geometry.**
   - For finite-order $g$, prove there are a set $E\subset[1,\infty)$ of positive upper logarithmic density and $\delta>0$ such that, for every $r\in E$, $T_K\cap\{|z|=r\}$ contains an arc of length $\ge\delta r$ on which $\operatorname{Re} g\le -\eta\log M(r,f)$.
   - The tools are Ahlfors distortion and a Harnack argument inside the tract.
3. **Arc-local lower bound.**
   - For Fabry-gap $F$, show that for $r$ in a set of positive logarithmic density, every arc of length $\delta r$ on $|z|=r$ contains a point with $\log|F|\ge(1-\eta/2)\log M(r)$.
   - Route: rescale $F(rz)$ and apply Pólya's arc-local Fabry theorem in quantitative form (Pólya's "Lückenreihen" estimates).
   - Alternative route: Nazarov on an arc, using that the set from Step 2 has *fixed* angular size $\delta$, not $1/s$. This is where finite order of $g$ beats the one-scale barrier.
4. **Make the density sets intersect.** Steps 2 and 3 give sets of positive density, which need not meet. Upgrade one of them to density 1, e.g. Step 3 via a Fuchs-type exceptional-set argument. Steps 3 and 4 are the real risk.
5. **Conclude.** For $r\in E$, Steps 2 and 3 contradict each other on the same arc.
6. **Stretch goal.** Replace "finite order of $g$" by finite lower order of $g$, or by finitely many tracts of $\operatorname{Re} g$.

=== PITFALLS
- **No referee findings yet.** Main risks for this line:
  - **Step 3 must not be a one-circle "most of the circle" estimate.** Block functions defeat any claim that $\log|f|\approx\log M$ on most of each circle. Use only "somewhere on every arc of fixed width", and check it against the block functions. If block functions violate the Step 3 claim on arcs of width $\delta$, the claim is false as stated and must use finite order of $g$ explicitly.
  - **Do not lose the $1/s$-versus-$\delta$ distinction.** Harnack+Jensen only give tract width about $1/s$. If Step 2 degrades to that, you are back in the trade-off barrier.
  - **Do not cite Pólya's sectorial theorem for infinite-order $f$** unless the precise statement is located. Its classical form uses the Borel transform and needs finite order of $f$. Here $f$ has infinite order, since $g$ is transcendental.
- **Density-zero use.** $e^{z^q}$ shows the argument must use $K(N)=o(N)$ somewhere. Identify exactly where, presumably in Step 3.
- **Exceptional sets.** Positive-density sets need not intersect. Step 4 cannot be skipped.
- **Novelty.** Before claiming novelty, search Hayman–Rossi, Sons, Murai and Sixsmith for the "$g$ finite order" case, per the memory rule "check claims before calling anything new".
- **Lean.** The informal theorem is not the formal statement. Only Step 0 can settle the formal statement cheaply.
