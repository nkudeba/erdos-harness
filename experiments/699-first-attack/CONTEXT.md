# Erdős 699: first full-resolution attempt, 2026-09-11

## Objective and assistance

User explicitly requests tackling the genuinely open problem, with a full proof or a counterexample as the objective. This is an operator-assisted attempt: Codex selected and read public sources, supplied this mathematical route, and disabled generic enumeration. A partial lemma is not success on the main objective. No resolution claim without independent review.

Exact target: for integers 1 <= i < j and 2*j <= n, a prime p >= i divides both C(n,i) and C(n,j). Preserve >=, not >. A counterexample must refute this exact target. Do not replace the full statement with a special case.

## Live sources read

- https://www.erdosproblems.com/forum/thread/699
- https://www.erdosproblems.com/forum/thread/699/proof-claims
- Van Doorn/Rocca manuscript, read-only Overleaf https://www.overleaf.com/read/ywsndhgyrzsx, file `Binomial coefficients sharing a large prime divisor.tex`, read in full on 2026-09-11.

The catalogue remains open. The April full proof was rejected by Bloom (11 May): its Lean code did not formalize the target. Price's partial proof for j <= 3i/2 or n=2j is accepted by the site. Cong reports testing all n <= 10^7 plus targeted families near 1.3e8; not rerun here. Small brute-force exploration can only test a proposed lemma, not establish new coverage.

IMPORTANT UPDATE: the current Overleaf manuscript differs materially from the claims-page summary (which mentions i<=1475 and an orbit polynomial). The current manuscript uses a binomial determinant, proves an asymptotic large-i result, states without details an effective i>=1000 cutoff, and uses an ineffective S-part argument for fixed i>=4. Neither the asymptotic theorem nor ineffective finiteness settles the full problem. Treat the manuscript as an external proposed proof, not as a verified assumption.

## Current manuscript's route, for audit

Write G=gcd(C(n,i),C(n,j)). It proposes, for 4<=i<j<=n/2,

    G > exp(-2*i) * (n/i)^(i/4).

For k=ceil(i/2), take the (k+1)-square Toeplitz matrix

    A[r,s] = C(n-i, j-i+k-r+s), 0<=r,s<=k.
    Delta = product_{r=0}^k (n-i+r)! r! / ((j-i+k+r)! (n-j-k+r)!).

Let L=lcm(1,...,i), B=C(n,j)/G and jstar=(j+1)^(2*k-i). The binomial identity

    C(n,j) C(j,i-h) C(n-j,h) = C(n,i) C(i,h) C(n-i,j-i+h)

shows B divides C(i,h) C(n-i,j-i+h), and C(i,h) divides L. Consequently B divides all entries of L*A except possibly the upper-right entry for odd i; multiplying its row by j+1 fixes that entry. Thus B^(k+1) divides L^(k+1)*jstar*Delta. Product estimates give the displayed lower bound.

The large-i argument combines this with G <= n^pi(y) if all prime factors are below y, taking y=(i log i)/10, and a prime in (n-i,n] when i>=n^(21/40), for sufficiently large n. The manuscript's explicit i>=1000 statement is asserted with references but the calculation is omitted. Do not assume it is certified.

For each fixed i>=5, Bugeaud-Evertse-Gyory 2018, Theorem 2.1, is invoked to bound the part of n(n-1)...(n-i+1) supported on primes <=i by n^1.1 for sufficiently large n. Contradicts G >> n^(i/4). This is ineffective and not a finite executable search limit. The i=4 case uses a separate weighted product of linear factors and a conic. The manuscript explicitly says it cannot rule out infinitely many cases with i=3 and G a power of 2.

## Productive attack priorities

1. The full theorem remains the frozen target. Investigate whether the small-prime obstruction can be eliminated uniformly, especially i=3 (G a power of 2). Do not spend the run reconstructing accepted j<=3i/2 cases.
2. For any p>=i dividing C(n,i), no common large prime means C(n,j) is nonzero mod p. Kummer/Lucas constraints on j must then hold simultaneously for all such p. Use exact congruence/valuation reasoning, not magnitude alone.
3. The standard identity implies that the >=i-prime part V of C(n,i) must divide C(j,i) in a counterexample; the symmetric identity also gives V | C(n-j,i). Exploit both simultaneously. A size estimate alone cannot generally solve the unbalanced range.
4. At i=3, C(n,3)=n(n-1)(n-2)/6. For p>=5 and p^a dividing one of n,n-1,n-2, no carries in base p forces j mod p^a <= n mod p^a (at that power), with n mod p^a in {0,1,2}. This creates a finite list of residue placements per n. Also handle p=3 exactly, including the denominator's factor 3; ignoring p=3 proves only the wrong strong variant.
5. For i=3, binomial gcd lower bounds and the exact 2-part may force n close to a high power of two. Explore that structural reduction and empirically refute overstrong intermediate claims before using them.

All numerical lemma checks must state that they are checks of a proposed reduction, not a new search floor. Every executed model-written Python script goes through sandbox_argv. No axioms for the target, no native_decide, no silent stronger or weaker quantifiers.
