# #699 at i=3: the units-digit system, a sharper localization, and where the difficulty actually sits

**Date:** 2026-09-16. **Outcome: no proof, no counterexample; claim eligible: false.**
Operator-assisted assessment (Claude Fable 5.1 in a Claude Code session, no paid harness run; session cost
unavailable). Everything below is a *written* argument with exact-integer checks of each step. **Nothing in this
report is Lean-certified.** The Lucas units-digit step is published mathematics (Kummer/Lucas); no novelty is claimed
for it. Live forum refreshed 2026-09-16: no comment since 25 Jul 2026, status still FALSIFIABLE/open.

## 1. What a counterexample at i=3 must satisfy, and the part that needs no Lucas digits beyond the low ones

A counterexample (n,3,j), 4 ≤ j ≤ n/2, means every prime p ≥ 3 dividing C(n,3) = n(n−1)(n−2)/6 fails to divide
C(n,j). Those primes are: every odd prime p ≥ 5 dividing n(n−1)(n−2), and p=3 exactly when 9 | n(n−1)(n−2).

**Units-digit consequence.** If p^e ∥ (n−t) with t ∈ {0,1,2}, t < p, and p ∤ C(n,j), then j mod p^e ≤ t.
(n ≡ t mod p^e, so the base-p digits 0..e−1 of n are t,0,…,0; Lucas forces j's digits 0..e−1 to be ≤ those,
i.e. j mod p^e ∈ {0,…,t}.) The library has the e=1 case (`small_index_carry`); e ≥ 2 is a short induction on
top of `digit_carry` and is not yet certified.

Define A′, B′, C′ = the odd parts of n, n−1, n−2 with a single factor 3 removed when 3 exactly divides
(3^e with e ≥ 2 is kept; those 3-powers ARE constraint primes). Then a counterexample satisfies

    (U3)   A′ | j,     B′ | j(j−1),     C′ | j(j−1)(j−2).

(For p^e ∥ n−1: j ≡ 0 or 1 mod p^e ⇔ p^e | j(j−1) since gcd(j,j−1)=1; for n−2 likewise with three factors, p odd.)

**Conjecture U(3).** No n ≥ 8, 4 ≤ j ≤ n/2 satisfy (U3). *U(3) ⇒ #699 holds for i=3.* U(3) mentions neither
binomial coefficients nor Lucas digits: it is a statement about the block {n, n−1, n−2} and the block {j, j−1, j−2}.

## 2. Reduction of U(3) (written proof; every non-vacuous step checked exactly, see §4)

**(a) n odd: no solution.** If 3 ∤ n or 9 | n then A′ = n | j ≤ n/2, impossible. So 3 ∥ n, A′ = n/3, j = n/3.
C′ = n−2 (odd, coprime to 3). 27·j(j−1)(j−2) = n(n−3)(n−6) ≡ 2·(−1)·(−4) = 8 (mod n−2) and gcd(n−2,27)=1, so
(n−2) | 8, n = 3 < 8.

**(b) n ≡ 2 (mod 4): no solution.** n = 2a, a odd, A′ ∈ {a, a/3}, h := n/(2A′) ∈ {1,3}, j = kA′, 1 ≤ k ≤ h.
(E1) below gives B′ | k(2h−k). h=1: k=1, B′ | 1, n ≤ 4. h=3 (3 ∥ a, so 3 ∤ B′ = n−1): k(6−k) ∈ {5,8,9},
B′ | 5 ⇒ n = 6 < 8. So **4 | n.**

**(c) Notation for 4 | n.** n = 2^r a, r ≥ 2, a odd. A′ = a/3 if 3 ∥ a else a. h := n/(2A′) ∈ {2^{r−1}, 3·2^{r−1}}
(even). j = kA′, 1 ≤ k ≤ h. B′ = (n−1)/e with e = 3 iff 3 ∥ n−1; C′ = (n/2 − 1)/e′ with e′ = 3 iff 3 ∥ n/2−1
(v₂(n−2)=1). gcd(B′,C′) = gcd(2h,B′) = gcd(h,C′) = 1.

  (E1) B′ | j(j−1) ⇔ B′ | k(2h−k).   [n = 2hA′ ≡ 1 (B′); multiply j(j−1) by (2h)².]
  (E2) C′ | j(j−1)(j−2) ⇔ C′ | k(h−k)(2h−k).   [n ≡ 2 (C′) ⇒ hA′ ≡ 1; multiply by h³.]
  (E4) k = h is impossible: B′ | h² = 4^{r−1}·{1,9} ⇒ B′ | 9 ⇒ B′ ∈ {1,3,9} ⇒ n ∈ {2,4,10}, none has 4 | n.
       **So j < n/2 in any solution** (equality j = n/2 is the only pattern the strict-variant near-misses show).
  (E5) Put d = h−k ∈ [1,h−1]. k(2h−k) = h²−d² = B′ℓ with ℓ ≥ 1, ℓ ≤ (h²−1)/B′; k(h−k)(2h−k) = d·B′ℓ, so
       C′ | k(h−k)(2h−k) ⇔ **C′ | dℓ**.

**(d) Bound.** C′ ≤ dℓ ≤ (h−1)(h²−1)/B′, so B′C′ < h³. With B′ ≥ (2hA′−1)/3, C′ ≥ (hA′−1)/3:
(2hA′−1)(hA′−1) < 9h³ ⇒ **A′² < 4.5h + 2.25**. Since A′h = n/2 this is **A′³ < 2.25n + 2.25A′**, i.e.
A′ ≲ 1.31·n^{1/3}, a ≤ 3A′, and therefore

    2^r = v₂-part of n  ≳  n^{2/3}/3.93 .

The 2026-09-12 report had n ≤ (9/4)4^r + 1, i.e. 2^r ≳ (2/3)√n. Bringing n−2 in correctly raises the exponent
from 1/2 to 2/3. It is still not an absolute cutoff: n = 2^r (a=1) satisfies every size bound for all r.

**(e) The residual system, in its cleanest form.** For fixed (r,a) a solution is a pair (d,ℓ) with
    h² − d² = B′ℓ,   C′ | dℓ,   1 ≤ d ≤ h−1,   where eB′ = 2e′C′ + 1.
For a = 1 (n = 2^r, the family no size bound kills) this reads, with k = j:
    (2^r − 1)/e | k(k−1)   and   (2^{r−1} − 1)/e′ | (k(k−1)·e/(2^r−1))·(k−2),   4 ≤ k ≤ 2^{r−1} − 1.
Since gcd(2^r−1, 2^{r−1}−1) = 1 and their prime factors have unrelated orders of 2, no algebraic identity forces or
forbids the second divisibility given the first. This is the honest obstruction: an exponential-Diophantine
coincidence, not a Lucas-digit issue. A heuristic count of solutions is Σ_{r,a} polylog/(2^r a²), dominated by
small n — exactly the range verified below — with tail ≲ 10⁻⁴ beyond 3·10⁵.

## 3. Results

| check | range | result | script |
|---|---|---|---|
| (U3) by direct enumeration, all n (odd/even), all j | n ≤ 300,000 | **0 solutions** | `i3_units.py` |
| (U3) parametrised (every odd a with A′² < 4.5h+2.25) | r = 2..30 ⇒ all n with 2 ≤ v₂(n) ≤ 30, hence **all n < 2^31 ≈ 2.1·10^9**; largest candidate 2.7·10^14 | **0 solutions** | `i3_param2.py` |
| (U3) parametrised, extension | r = 31..38 ⇒ all n with v₂(n) ≤ 38, hence **all n < 2^39 ≈ 5.5·10^11**; largest candidate 1.1·10^18 | **0 solutions** (`i3_param_31_38.log`) | `i3_param2.py` |
| (E1),(E2),(E4),(E5),(d) exact check on every (n,k), 4 | n | n ≤ 6000, 22,986 pairs; 49 satisfy the B′ condition, 0 the C′ condition | all pass | `verify_algebra.py` |
| U(i) (general-i units-digit system, §5) | i = 4..8, n ≤ 60,000 | **0 survivors** | `ui_general.py` |
| U(i) extension | i = 4..10, n ≤ 10^6 | **0 survivors** (`ui_general_1e6.log`) | `ui_general.py` |

**Conditional consequence.** Granting the written reduction (§1–2), *no counterexample to #699 with i=3 has
v₂(n) ≤ 38*; in particular none with n < 2^39 ≈ 5.5·10^11. This subsumes the published n ≤ 10^7 check for i=3 only. It is
**not** recorded as an Atlas `search_floor`: the floor covers all i and this is conditional on an uncertified
argument.

## 4. What is and is not established

- Mechanically verified (library): Lucas units digit (`digit_carry`, `small_index_carry`), block-prime, smoothness.
- Written and exactly checked, not certified: the prime-power units-digit lemma (e ≥ 2); (U3) as a consequence of
  a counterexample; (a)–(d) above.
- Conjecture, not proved: U(3). Empirically true to 2^31 (and beyond for small a).
- Not touched: i ≥ 4 in general (Van Doorn/Rocca manuscript, unverified, ineffective, heavy machinery).

## 5. The same picture for i ≥ 4

For general i the units-digit consequence of a counterexample is: for every t < i and every p^e ∥ (n−t) with
p ≥ i (and, when p = i is prime, e ≥ 2), j mod p^e ≤ t. Call the system U(i). `ui_general.py` finds **no
solutions of U(i) for i = 4..10 up to n = 10^6** (and none of the full Lucas condition either, as expected). So for every i tested, the
identity-level/units-digit constraints alone are never simultaneously satisfiable; the higher Lucas digits were
never needed. #699 ⇐ ∀i U(i), and U(i) is a pure statement about a block of i consecutive integers ending at n
and one ending at j (equivalently, by symmetry, one ending at n−j).

## 6. Strategic reading

1. **Disproof is not a target.** Heuristic solution count beyond the verified range is ≲ 10⁻⁴; the published
   floor stands; the negative direction should stay skipped.
2. **The difficulty is concentrated in U(3).** Van Doorn/Rocca leave i=3 open; U(3) is elementary to state and
   the (d,ℓ) form above is the sharpest known necessary condition. Nobody — here or on the forum — has a route to
   a contradiction uniform in r. A proof run aimed at "#699 for i=3" would burn budget re-deriving §2.
3. **What the harness can certify now** (research-mode target, Lean, elementary): the e ≥ 2 units-digit lemma;
   counterexample ⇒ (U3); (a) odd n; (b) 4 | n; (E4) j < n/2; (d) A′² < 4.5h+2.25. That supersedes the
   guidance's step 1 (formalising the weaker √n bound) and step 2 (bringing in n−2).
4. **What needs a human/forum.** U(3) itself, especially the a=1 family in §2(e). Posting the reformulation, the
   n^{2/3} localization and the verified range is the highest-leverage move: it hands the people already working
   on #699 (Del Pin, Van Doorn, Rocca) a cleaner target.
5. **A useful negative to remember.** The units-digit route is *sufficient* to prove #699 (given U(i)) and,
   empirically, never needs higher digits — the opposite of what the refuted Conjecture D tried, which was to
   find a *witness* prime by units digits alone. Existence of a witness may need p = i and higher carries
   (e.g. (10,3,5)); non-existence of a counterexample apparently does not.
