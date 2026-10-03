# r2s3 notebook — improved lower bound via Fourier zeros

## Result
PROVED (C1): every maximal Sidon set A ⊆ [N] has |A| ≥ (1.2679 − o(1))·N^{1/3}.
Equivalently, liminf minMaximalSidonSet(N)/N^{1/3} ≥ (2/0.981)^{1/3} > 1.2679. The constant in KNOWN is 2^{1/3} = 1.2599.
The proof reduces to a continuum problem, c* := sup{α : ∃μ with law(X+Y−Z) ≥ α·Leb on [0,1]}, by compactness.
It then kills α near 1 using the zero at ξ = 2π of the characteristic function of Uniform[0,1]: |φ_μ(2π)|³ ≤ 1−α,
but a variance bound forces |φ_μ(2π)| ≥ cos(2π·√Var) ≈ 0.28. The method's limit is (2/c*)^{1/3}, with
0.6746 ≤ c* ≤ 0.981 (the lower end is numerical, see Data). So the true constant from this relaxation could be as large as about 1.44.
New: the constant improves on (2N)^{1/3}. It is a lower-bound result and does not touch CORE (the construction side).

## Claims
### C1
STATEMENT: Let m(N) = minMaximalSidonSet(N). Then liminf_{N→∞} m(N)³/N ≥ 2/0.981, so m(N) ≥ (1.2679 − o(1)) N^{1/3}.
STATUS: PROVED (all steps checked by hand. The single numerical inequality, cos(2π√s0) > ε0^{1/3}, was checked in s1.py
and by hand: s0 = 0.0420415, √s0 = 0.20504, cos(1.28831) = 0.2787 > 0.2668 = 0.019^{1/3}.)
TYPE: QUANT
BEYOND: improves KNOWN "(1−o(1))(2N)^{1/3}" (constant 1.2599) to 1.2679. It also identifies the exact continuum constant (2/c*)^{1/3}
of the triple-counting method, which no linear (single test function) argument can improve; see Dead ends.
PROOF.
Step 0 (blocking). Let A ⊆ [N] be maximal Sidon with |A| = k, and let x ∈ [N]∖A. Then A∪{x} has a nontrivial
relation involving x. Either x+a = b+c, giving x = b+c−a (an ordered triple in A³), or 2x = b+c with b ≠ c.
(The cases x+x = x+a and x+a = x+b are trivial or force x ∈ A.)
Step 1 (discrete inequality). Put μ_N = (1/k)Σ_{a∈A} δ_{a/N}, and let ν_N be the law of (a+b−c)/N with (a,b,c) uniform in A³,
so ν_N = μ_N*μ_N*μ̃_N. Fix a closed interval J = [s,t] ⊆ [0,1]. The integers x ∈ [1,N] with x/N ∈ J number at least N|J| − 2.
Each such x lies in A (at most k of them), or is a midpoint (at most k² of them), or equals b+c−a. The number of distinct
values b+c−a is at most the number of triples ({b,c} unordered, a), which is ≤ (k³ν_N(J) + k²)/2.
Hence ν_N(J) ≥ (2N|J| − 4 − 2k − 3k²)/k³.
Step 2 (compactness). Suppose L := liminf m(N)³/N < 2/0.981. L ≥ 2 by KNOWN, so k → ∞. Take N_i with k_i³/N_i → L,
where A_i is a minimum maximal set. Then ν_i(J) ≥ (2/L)|J| − o(1) for each fixed closed J. Pass to a further subsequence
with μ_i → μ weakly (Prokhorov; everything is supported on [0,1]). Characteristic functions converge pointwise, so
ν_i → ν := μ*μ*μ̃ weakly (Lévy). Portmanteau for closed J gives ν(J) ≥ limsup ν_i(J) ≥ α|J| with α = 2/L > 0.981.
This holds for every closed interval J ⊆ [0,1]. By inner approximation it also holds for open intervals, hence (countable
disjoint unions) for open sets U ⊆ (0,1), hence by outer regularity for every Borel E ⊆ [0,1]. Indeed ν(E) = inf ν(U) ≥ λ(E).
So ρ := ν − α·λ|_[0,1] is a nonnegative measure of mass ε := 1−α < 0.019. Here λ is Lebesgue measure.
Step 3 (Fourier zero). Let X,Y,Z be iid with law μ, S = X+Y−Z ~ ν, and φ(ξ) = E e^{iξX}. Then E e^{iξS} = φ(ξ)² conj(φ(ξ)),
so |ν̂(ξ)| = |φ(ξ)|³. The transform of λ|_[0,1] is (e^{iξ}−1)/(iξ), which vanishes at ξ = 2π. Hence |φ(2π)|³ = |ρ̂(2π)| ≤ ε.
Step 4 (variance). S ∈ [−1,2], so |S−½| ≤ 3/2. We have E(S−½)² = α/12 + ∫(t−½)²dρ ≤ α/12 + 9ε/4 =: B, and
|τ| := |ES − ½| = |∫(t−½)dρ| ≤ 3ε/2. Put σ² = Var X and W = X − ½ ∈ [−½,½]. Then E(S−½)² = 3σ² + τ² (ES = EX), so
EW² = σ² + τ² ≤ (B−τ²)/3 + τ² ≤ α/36 + 3ε/4 + 1.5ε² =: s(ε). This is increasing in ε on [0, 0.019], so s(ε) ≤ s0 := s(0.019) = 0.0420415.
Step 5 (convexity). g(u) = cos(2π√u) is convex on [0,¼]. Proof: g''(u) = −(2π/(4u^{3/2}))·(t cos t − sin t) with t = 2π√u ∈ [0,π],
and t cos t − sin t ≤ 0 there. g is also decreasing there. Since W² ∈ [0,¼], Jensen gives
|φ(2π)| ≥ Re(e^{−iπ}φ(2π)) = E cos(2πW) = E g(W²) ≥ g(EW²) ≥ g(s0) = cos(2π·0.205040) = 0.2787.
Step 6. Then 0.2787 ≤ |φ(2π)| ≤ ε^{1/3} < 0.019^{1/3} = 0.2668, a contradiction. Hence L ≥ 2/0.981, i.e. m(N) ≥ ((2/0.981)^{1/3} − o(1))N^{1/3}
and (2/0.981)^{1/3} = 1.26800. ∎
(The threshold of this exact argument is ε* ≈ 0.01974. We use 0.019 for margin.)

### C2
STATEMENT: For every N, m(N)³ ≥ (2/c* − o(1))N, where c* is the continuum constant above. Moreover c* ≥ 0.6746: the histogram
density on 40 cells found in s1.py gives law(X+Y−Z) ≥ 0.6746·Leb on [0,1]. It has an atom-like spike of mass ≈ 0.44 at x ≈ 0.49.
STATUS: the first sentence is PROVED (Steps 0–2 of C1 with 0.981 replaced by c*; c* is attained by compactness). The numerical value of c* is CONJECTURED to be ≈ 0.68–0.70.
TYPE: REDUCTION
BEYOND: makes the triple-counting lower bound an explicit extremal problem. If c* ≈ 0.675, the method gives about 1.436·N^{1/3}.
PROOF/EVIDENCE: see C1. The histogram μ is a genuine measure, and its bin masses are computed exactly from the kernel (1/6, 2/3, 1/6) of
U1+U2−U3. So 0.6746 is a rigorous lower bound on c*, up to floating point. This means C1's method can never exceed (2/0.6746)^{1/3} ≈ 1.436.

## Data
- s1.py: the contradiction threshold of Steps 4–6 is ε* = 0.019740. The constant (2/(1−ε))^{1/3} is 1.2680 at ε = 0.019.
- Optimiser (n = 40 cells, exponentiated-gradient softmin, 6 restarts): α = 0.6746. Profile (density ×n): roughly flat at 0.2–1.3, with a spike
  of 10.95 + 6.8 (mass ≈ 0.44) at cells 19–20. This matches r1s4's "atom ≈ 0.46 at ½".

## Dead ends
- A single linear test functional W ≥ 0 can never beat α ≤ 1. For μ = δ_t, E W(S) = W(t), and max W ≥ mean W.
  So any improvement must be nonlinear in μ (here, the cubic structure φ²·conj(φ) at a zero of the target transform).
- Using D = X−X′ (symmetrised, |φ|²) instead of a centred W loses: 1−4π²/36 < 0. The bound n²(1−ψ(2π/n)) → π²/9 > 1 also fails.
- The weak point of C1 is the crude bound ∫(t−½)²dρ ≤ 9ε/4 on the waste mass. Bounding it better (or using more zeros 2πj) should
  push ε well beyond 0.02. Not done (budget).
