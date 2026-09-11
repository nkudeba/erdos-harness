# Erdős #677 — analysis produced in this session (operator-supplied to the run)

Statement (formal-conjectures): `∀ m n k : ℕ, k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k`,
where `lcmInterval n k = lcm{n+1, …, n+k}`. Write `M(n,k)` for it and `P_k(n) = ∏_{i=1}^{k} (n+i)`.

## 1. The bounded-divisor reduction

Put `d_k(n) = P_k(n) / M(n,k)`. **`d_k(n)` takes only finitely many values for fixed `k`.**
Reason: if two of `n+1,…,n+k` are both divisible by `p^t` then `p^t` divides their difference, which is
`< k`, so `p^t < k`. Hence for every prime `p`, all but at most one of the `k` terms have
`v_p < log_p k`, and the excess `Σ_i v_p(n+i) − max_i v_p(n+i)` is bounded by a function of `k` alone.
Only primes `p ≤ k` contribute.

Measured value sets (exhaustive over `n < 200000`):

| k | d values |
|---|---|
| 1 | {1} |
| 2 | {1} |
| 3 | {1, 2} |
| 4 | {2, 6} |
| 5 | {2,4,6,8,12,24} |
| 6 | {12,24,60,120} |
| 7 | {12,24,36,48,60,72,120,144,180,240,360,720} |
| 8 | {48,144,240,336,720,1008,1680,5040} |

`M(n,k) = M(m,k)` is therefore equivalent to `P_k(m)/P_k(n) = d_k(m)/d_k(n)`, a ratio from an explicit
finite set. Since `m > n` makes the left side `> 1`, only the ratios `> 1` can occur:

| k | ratios a counterexample must realise |
|---|---|
| 2 | none |
| 3 | 2 |
| 4 | 3 |
| 5 | 4/3, 3/2, 2, 3, 4, 6, 12 |
| 6 | 2, 5/2, 5, 10 |


## 1a. `d_k` is periodic, so the value sets above are complete (not just sampled)

For a prime `p`, if two of the `k` terms are both divisible by `p^t` then `p^t | (i−j)` with `|i−j| < k`,
so `p^t ≤ k−1`. Hence every term except the one of maximal valuation has `v_p ≤ t_p := ⌊log_p(k−1)⌋`,
and which term is maximal plus all the smaller valuations are decided by `n mod p^{t_p+1}`. So
`d_k(n)` is **periodic in n** with period dividing `Π_{p ≤ k} p^{t_p+1}`:

| k | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| period | 12 | 36 | 360 | 1800 | 12600 | 88200 | 176400 |

Verified over three full periods for each `k`, and the `d`-set computed from one period equals the one
computed from `n < 200000`. The value sets in the table above are therefore **exhaustive**, which is what
makes the ratio lists exhaustive and the searches below conclusive rather than heuristic.

## 3a. Ruling out EVERY m, not just m in a window

Because the admissible ratios are a finite exhaustive list, for each `n` the possible `P_k(m)` are a
finite explicit list, and `m` is then pinned by the k-th root. So a clean sweep over `n < N` rules out
**all** `m ≥ n+k`, unbounded:

| k | n range swept | m range | counterexamples |
|---|---|---|---|
| 3 | n < 10^9 | all m | 0 |
| 4 | n < 10^8 | all m | 0 |
| 5 | n < 5·10^6 | all m | 0 |
| 6 | n < 5·10^6 | all m | 0 |
| 7 | n < 2·10^6 | all m | 0 |
| 8 | n < 2·10^6 | all m | 0 |
| 9 | n < 10^6 | all m | 0 |
| 10 | n < 10^6 | all m | 0 |

(For k = 3 the sole solution of `P_3(m) = 2P_3(n)` in range is `(n,m) = (2,3)`, with `m−n = 1 < 3`.
For k = 4 the two solutions of `P_4(m) = 3P_4(n)` are `(1,2)` — `m−n = 1 < 4` — and `(4,6)`, which
fails the `d`-ratio since `d_4(4) = d_4(6) = 2`.)

## 2. What this proves outright

**k = 1 and k = 2: the conjecture is TRUE, unconditionally.** `d_k ≡ 1`, so `M(n,k) = P_k(n)` is strictly
increasing in `n`; `m ≥ n+k > n` gives `M(m,k) > M(n,k)`. (For k = 2 the input is that `n+1` and `n+2`
are coprime, so `lcm(n+1,n+2) = (n+1)(n+2)`.) These are the two lemmas most worth certifying in Lean.

## 3. What this reduces

- **k = 3**: needs `P_3(m) = 2·P_3(n)`, i.e. `(x−1)x(x+1) = 2(y−1)y(y+1)` with `x = m+2 > y = n+2`
  (and then necessarily `n` even, `m` odd). Exhaustive search over `y < 10^8`: the **only** solution is
  `(y,x) = (4,5)`, i.e. `(n,m) = (2,3)`, and `m − n = 1 < 3`, so it is **not** a counterexample.
  Hence no counterexample for `k = 3` with `n < 10^8`.
- **k = 4**: needs `P_4(m) = 3·P_4(n)`. Search over `n < 5·10^6` finds `(1,2)` (`m−n = 1 < 4`) and
  `(4,6)` (fails the `d`-ratio: `d_4(4) = d_4(6) = 2`, not `6/2`). No counterexample for `k = 4` in range.

## 4. A smoothness obstruction (general k)

**Lemma.** If `M(n,k) = M(m,k)` with `m ≥ n+k`, then every prime `p > k` dividing any of
`m+1,…,m+k` satisfies `p ≤ (m−n) + (k−1)`.

*Proof.* `p | m+j` and `p | M(m,k) = M(n,k)` force `p | n+i` for some `1 ≤ i ≤ k`. Since `m ≥ n+k`,
`m+j > n+i`, so `0 < (m+j)−(n+i) = (m−n)+(j−i) ≤ (m−n)+(k−1)` and `p` divides it. ∎

So all of `m+1,…,m+k` are `max(k, m−n+k−1)`-smooth. Combined with `P_k(m) ≤ D_k · P_k(n)`
(from `d_k ≤ D_k`), which bounds `m` in terms of `n`, this is a genuine constraint for small `k`;
it weakens as `k` grows because `D_k^{1/k}` grows.

## 5. Direct search (independent of the reduction)

Exhaustive same-`k` scan for `M(n,k) = M(m,k)` with `m ≥ n+k`: **none** for `n,m < 4·10^5` (k ≤ 3),
`< 2·10^5` (k ≤ 6), `< 8·10^4` (7 ≤ k ≤ 20). Same-`k` collisions *do* occur but always with overlapping
intervals and a tiny gap — the largest `m−n` seen is 1 (k=3,4,5,7), 2 (k=6,8), 3 (k=10,12,16), 4 (k=20),
always at small `n` (`n ≤ 16`), against the `m−n ≥ k` a counterexample needs.
