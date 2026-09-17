# Erdős 699 — second attempt, full resolution. 2026-09-11

## Objective and assistance

Operator requests a full resolution: a complete proof of the frozen target, or a counterexample to it.
A partial lemma is not success on the main objective. This is operator-assisted: the reduction chain
below was assembled and numerically checked by the operator from PUBLIC forum sources before this run.
No resolution claim without independent human review.

Exact target, both directions: for all natural n, i, j with 1 <= i, i < j, 2*j <= n, there is a prime p
with i <= p and p dividing gcd(C(n,i), C(n,j)).

## THE ONE FATAL CONFUSION: p >= i, never p > i

The non-strict `i <= p` is the target. The strict `i < p` variant is a DIFFERENT and FALSE statement.
Its nine known failures were recomputed in exact integer arithmetic; in every one the largest shared
prime is EXACTLY i, so each SATISFIES this target and refutes only the strict variant:

    (n,i,j) = (10,3,5) (16,2,6) (28,3,14) (28,5,14) (244,3,122)
              (512,2,147) (2048,2,713) (2188,3,1094) (1594324,3,797162)

If an attempt "refutes" #699 by producing one of these, it has formalized the wrong statement. Any
claimed counterexample must be checked against this list FIRST.

## Do not run a counterexample search

Cong's published Rust search covered every n <= 10^7 (4.17e19 candidate triples), plus n = 2^k for
k <= 27 and n = 3^m + 1 for m <= 17. That is 4.2e10 times the bounded-search reach. The triage gate
already skips the search stage on this basis. Spend nothing re-deriving it.

## The reduction chain — status of each link

V_i(n) denotes the part of C(n,i) supported on primes >= i; U_i(n) the part on primes < i.

(F1) IDENTITY. C(n,i)*C(n-i,j-i) = C(n,j)*C(j,i). Hence if d divides C(n,i) and is coprime to C(n,j)
     then d divides C(j,i). Applied to V_i(n): a counterexample forces V_i(n) | C(j,i).
     STATUS: checked exhaustively for all i<j<=n/2, n<=160. Public (Bloom's exposition).

(F2) EEES78. V_i(n)^2 > C(n,i) outside 12 explicit exceptions. STATUS: published, not reproved here.

(F3) KUMMER BOUND. U_i(n) <= n^pi(i-1), so V_i(n) >= C(n,i)/n^pi(i-1). Proof: by Kummer the exponent
     v_q(C(n,i)) counts carries adding i and n-i in base q, so q^v_q <= n for each of the pi(i-1) primes
     below i. STATUS: checked for all 2<=i<=n/2, n<=900. Public (forum comment, 25 Jul 2026).

(F4) SINGLE-DIGIT KUMMER. If p is prime, i < p, and n mod p < i, then p divides C(n,i).
     STATUS: checked for all primes p in (n/2,n] and all k<=n/2, n<=1200. A DRAFT LEAN PROOF EXISTS but
     never compiled (see the previous run's partial attempts). CERTIFYING THIS IS THE FIRST CONCRETE GOAL.

(F5) SMOOTHNESS REDUCTION (the sharp form of the obstruction). Let p be a prime with p > j dividing any
     one of n, n-1, ..., n-i+1, say p | n-t with 0 <= t < i. Then n mod p = t (since p > j > i > t), so
     n mod p = t < i < j, and F4 applies twice: p divides C(n,i) AND p divides C(n,j). Also p > j > i.
     THEREFORE: in any counterexample, every prime factor of the descending product
     n(n-1)...(n-i+1) is at most j — the product is j-SMOOTH.
     STATUS: derived from F4; numerically confirmed. This is strictly stronger than the weaker and
     better-known "a counterexample needs no prime in the interval (n-i, n]", which is the special case
     where n-t is itself prime.

(F6) SIZE BOUND. From F1 and F3 with C(n,i)/C(j,i) >= (n/j)^i (valid for n >= j), a counterexample
     satisfies n <= j^(i/(i-pi(i-1))). STATUS: public (same forum comment).

## The remaining open region, precisely

Combining 2*j <= n with F5 and F6, a counterexample (n,i,j) must satisfy ALL of:

  (a) 2*j <= n <= j^(i/(i-pi(i-1)))      [empty unless j is large enough that j^(e-1) >= 2]
  (b) n(n-1)...(n-i+1) is j-smooth
  (c) j > J1(i), where J1(i) ~ 3i/2 + log2(i)/4 is the endpoint of the accepted size argument
      (j <= 3i/2 and n = 2j are settled on the site; reproving them resolves nothing)

Note (a) alone does NOT close for any fixed i: since n <= j^e and n >= 2j, we get j >= n^(1/e), so (b)
is the demand that a product of i consecutive integers near n be n^(1/e)-smooth. For i = 3 (pi(2)=1,
e = 3/2) this is: n(n-1)(n-2) is n^(2/3)-smooth with n >= 2j. Products of consecutive integers being
smooth is exactly the Bugeaud-Evertse-Gyory territory the Van Doorn/Rocca manuscript invokes
INEFFECTIVELY; an effective version is what the problem actually needs. i = 3 with the gcd a power of 2
is the case that manuscript explicitly cannot rule out.

## What to do, in priority order

1. ATTEMPT THE FULL THEOREM. The most promising route is to make (b) effective: derive a contradiction
   between "n(n-1)...(n-i+1) is j-smooth" and the size/valuation constraints, without appealing to an
   ineffective finiteness theorem. Use exact valuation reasoning (Kummer/Lucas), not magnitude alone.
2. If the full theorem does not close, CERTIFY THE CHAIN as reusable partial value, in this order:
   F4 first (the draft is close), then F5 as a standalone statement about the descending product, then
   the combination "counterexample implies j-smooth descending product". A certified F4+F5 is a genuine
   reduction of #699 to an effective smoothness statement and is worth more than scattered lemmas.
3. Prefer a cheap necessary condition to a search. Ask what the structure forces before enumerating.

## Honesty constraints

No axioms for the target, no native_decide, no sorry in a claimed result. A compiling proof certifies
the FROZEN statement, not the problem. Do not silently strengthen (p > i) or weaken (dropping 2*j <= n,
or fixing i or j) the quantifiers. Every numerical check is a check of a proposed reduction, never a
new search floor.
