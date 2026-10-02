## Result
NEW (computer-assisted, PROVED modulo the standard game reduction re-derived in C1): every convex prime sequence has
liminf q_n/n^2 >= 1/rho_17 = 0.86429, i.e. d_n >= (1.7286 - o(1)) n. This beats the blackboard's best, 0.80024 (z = 13).
The z = 17 game value is EXACT: G_17 = 295318 per period M = 255255, certified by a max-plus eigenvector. So 0.86429 is
the best the z <= 17 congruence game can give. The full target (rho_z -> 1) is NOT proved. Data: rho_z - 1 = 0.392,
0.250, 0.157 for z = 11, 13, 17, shrinking by a factor of about 0.63 per added prime. That is much faster than the
blackboard's conjectured ≍ 1/log z ((rho-1)·log z = 0.94, 0.64, 0.45), though no asymptotic claim follows. Also proved:
rho_z is nonincreasing (C2), so rho_inf = lim rho_z exists and lies in [1, 1.15702].

## Claims
### C1
STATEMENT: Let q_1 < q_2 < ... be primes with q_{n+1}-q_n >= q_n-q_{n-1}. Then liminf q_n/n^2 >= 1/rho_17 >= 0.86429.
Here rho_17 = G_17/M + tau_17 with M = 3·5·7·11·13·17 = 255255, G_17 = 295318 and
tau_z = sum_{p>z} (p-2)(1-1/p)/prod_{3<=l<p} l, so tau_17 = 0.0000675 and rho_17 = 1.157020.
Equivalently d_n >= (2/rho_17 - o(1)) n.
STATUS: PROVED (computer-assisted: game2.py gives the upper bound, game3.py gives exactness; the code reproduces the
blackboard values for z <= 13)
TYPE: QUANT
BEYOND: the blackboard bound 0.80024 (z = 13, informally refereed). Richter has 0.352 and AP-multiplicity 0.543.
PROOF:
Game. S = odd primes <= z, M = prod S. State s in (Z/M)^*. A period is v = 0, 1, ..., M-1 (v read mod M).
At step v with M ∤ v, choose m >= 0 such that s + 2vj is a unit mod M for j = 1..m; gain m; then s <- s + 2vm.
At v ≡ 0 (mod M) set m := 0 (s is unchanged anyway). T is the one-period Bellman operator on functions of s:
(T h)(s) = max over one period of (gain + h(end state)).
(a) Reduction. Discard the finitely many terms <= max(z, ...). Gaps are even, d = 2v, and by monotonicity each value v
is used in one consecutive block of m_v >= 0 gaps. The terms are primes > z, hence units mod M, so a block with M ∤ v
is a legal game move from s = (current term mod M). A block with M | v leaves s mod M unchanged. For it, m_v <= p(d)-2,
where p(d) is the least odd prime not dividing d (necessarily > z): the m_v + 1 terms form an AP with difference prime
to p, so if m_v + 1 >= p one term is ≡ 0 (mod p) and so equals p. That is impossible for large terms, since
p(d) = O(log d) = O(log q).
(b) Game bound. If T h = h + G (an eigenvector), then by induction any path over j periods gains
<= jG + max h - min h. Extending a path by m = 0 moves only increases the window, so any window of v-values of length
V gains <= G·V/M + O_z(1).
(c) Tail. Sum_{w<=W} (p(2Mw)-2) = W·M·tau_z + o(W). Here p(2Mw) is the least prime > z not dividing w, its law
(density (1-1/p)/prod_{z<l<p} l) is periodic, and p(2Mw) = O(log w).
(d) So N(V) := #{k : d_k <= 2V} <= rho_z V + o(V). Since n <= N(d_n/2), we get d_n >= (2/rho_z - o(1)) n and
q_n >= sum_{k<n} d_k >= (1/rho_z - o(1)) n^2.
(e) Computation for z = 17. Value iteration on the full residue array, with nonunits set to -inf (float32; all values
are integers < 2^24, so the arithmetic is exact). The step at v takes p(v)-2 Jacobi sweeps of
C(x) = max(W(x), 1 + C(x+2v)), restricted to units, where p(v) is the least prime of S not dividing v. This covers all
chains, because m+1 consecutive units along step 2v force m <= p(v)-2. The first period gives max T(0) = 295318, so
already G <= 295318: T is monotone and commutes with constants, hence T^j 0 <= j·max T0. The second period, with
V = T0 - max, gives T V - V = 295318 on EVERY unit state. So V is an exact eigenvector and G_17 = 295318 exactly
(runtime 88 s).
Check: the same code gives G = 2, 20, 156, 1596, 18748 for z = 3, 5, 7, 11, 13, which are exactly the blackboard
values (and 1/rho = 0.54345 = 1/kappa at z = 3).

### C2
STATEMENT: rho_z is nonincreasing in z. Hence rho_inf := lim rho_z exists, and 1 <= rho_inf <= rho_17 = 1.157020.
STATUS: PROVED
TYPE: STRUCTURE
BEYOND: Not on the blackboard. It makes "rho_z -> 1" a statement about one limit.
PROOF: Let z < z', S ⊂ S', R = M'/M. Take a z'-game path over j periods of length M' and reduce its states mod M.
Steps with M ∤ v are legal z-moves. Steps with M | v, M' ∤ v leave s mod M unchanged and satisfy m_v <= p(2v)-2,
because m+1 consecutive units along step 2v mod p(v) ∈ S' are impossible once m+1 >= p(v). So
jG_{z'} <= (jR·G_z + O(1)) + j·sum_{w mod R, w≢0} (p(2Mw)-2).
In that last sum, p(2Mw) depends only on w mod R (the least prime of S'\S not dividing w). Averaging over all w gives
M·tau_z = (1/R)·[sum_{w≢0} + M'·tau_{z'}], so sum_{w≢0} = M'(tau_z - tau_{z'}). Divide by jM' and let j -> ∞:
G_{z'}/M' <= G_z/M + tau_z - tau_{z'}, i.e. rho_{z'} <= rho_z.
Lower bound: the Euler/Rabinowitsch quadratic path (m = 1 at every step, discriminant a nonresidue mod every p in S)
gives G_z >= M-1, so rho_z >= 1 - 1/M + tau_z > 1.

### C3
STATEMENT (conjecture): rho_z -> 1. Quantitatively, rho_z - 1 decays at least geometrically in pi(z) over the
computable range (ratio about 0.63 per prime), not like c/log z.
STATUS: CONJECTURED
TYPE: QUANT
BEYOND: It replaces the blackboard's guess rho_z - 1 ≍ 1/log z, which the data contradicts in the computable range.
PROOF/EVIDENCE: e_z = rho_z - 1 = 0.840, 0.707, 0.573, 0.392, 0.2496, 0.1570 for z = 3, 5, 7, 11, 13, 17.
Successive ratios: 0.84, 0.81, 0.68, 0.64, 0.63. e_z·log z = 0.94, 0.64, 0.445 at z = 11, 13, 17.
Mechanism (trace.py, optimal cycles at z = 11, 13): the excess does not come from rare perturbations of an Euler
quadratic, since about 40% of steps have m ≠ 1. It comes from large multiplicities at steps with 3|v: the mean m at
p(v) = 5, 7, 11, 13 is 1.89, 3.20, 6.05, 9.5 at z = 13. This is paid for by zeros on the 3∤v steps, whose mean m is
0.803 at z = 11 and 0.753 at z = 13. Each new prime p cuts the high multiplicities at the classes p(v) < p, and the
mean at p(v) = 5 fell from 2.30 to 1.89 between z = 11 and z = 13. Caveat: these are 6 points with z <= 17, so
geometric decay may not persist.

## Data
z : M : G : G/M : tau_z : rho_z : 1/rho_z
3 : 3 : 2 : 0.666667 : 1.173435 : 1.840102 : 0.54345
5 : 15 : 20 : 1.333333 : 0.373435 : 1.706769 : 0.58590
7 : 105 : 156 : 1.485714 : 0.087721 : 1.573435 : 0.63555
11 : 1155 : 1596 : 1.381818 : 0.009799 : 1.391617 : 0.71859
13 : 15015 : 18748 : 1.248618 : 0.0010077 : 1.249626 : 0.80024
17 : 255255 : 295318 (exact) : 1.156953 : 0.0000675 : 1.157020 : 0.86429
Optimal-cycle structure. Mean m by class p(v) = least prime of S not dividing v:
 z=11: p(v)=3: 0.803 (152 zeros/770) | 5: 2.299 | 7: 3.061 | 11: 6.80 ; glitch fraction 0.40
 z=13: p(v)=3: 0.753 (2468 zeros/10010) | 5: 1.888 | 7: 3.20 | 11: 6.05 | 13: 9.5 ; glitch fraction 0.39
 m distribution at z=13: m=0: 2613, 1: 9148, 2: 1140, 3: 1618, 4: 246, 5: 156, 6+: 94.
Periodic patterns (periodic.py): every multiplicity pattern of period T <= 12 with mean > 1 (entries <= 4 for T <= 4,
<= 3 for T <= 8, <= 2 for T <= 12) fails mod 3 or mod 5, for every phase. This is consistent with C1/C2, which bound
every periodic Ẑ-good pattern by rho_17 anyway.

## Dead ends
- Exact z = 19 (and higher): M = 4.85e6 would cost about 361x the z = 17 run (about 10^4 s). Files are not allowed,
  so work cannot be checkpointed across runs. z = 17 is the computational limit here.
- Separable per-prime potentials (LP relaxation): heuristically weak. Each prime alone permits big m at v ≡ 0 mod p,
  and the relaxation decouples these, so I expect a value >= 4/3. Not computed, not proved.
- Block-separable potentials Phi(s mod M_17) + psi(s mod 19): with Phi the optimal z = 17 potential, both m = 0 and
  m = 1 are tight in the first block, which forces lambda >= lambda_17, so this gives no gain. A general Phi was not
  analysed.
- Proving rho_z -> 1: no argument found. The Ẑ-good formulation (for every p, the positions P_k mod p miss a class)
  plus Weil handles primes p >> 4^T for period-T patterns but not p <= T, and optimal strategies have period M_z.
