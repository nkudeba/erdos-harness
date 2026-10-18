# Review packet: new terms of OEIS A082449 (Erdős #695)

This packet is for the person deciding whether the values below are right, and whether to submit them to OEIS or first ask
for an independent check. Written 2026-10-17. The evidence is in this folder; `README.md` lists it.

## The claim

| Term | Value | What OEIS has now |
|---|---|---|
| A082449(21) | 866,284,735,109,723 | Only as an upper bound, in D. A. Corneth's comment |
| A082449(22) | 2,957,807,053,316,399 | Nothing; the comment's upper bound is 11,407,852,252,734,739 |
| A082449(23) | more than 9·10¹⁵, at most 94,649,825,706,124,769 | The comment's upper bound is 115,504,631,269,039,577 |

A082449(n) is the least prime that needs at least n steps to reach 2 when you repeatedly replace p by the greatest prime
factor of p − 1.

The same computation bears on Jianing Song's conjecture in the entry, that a(n) is also the least prime whose Pratt tree
has height n + 1. The entry says it is verified for n ≤ 13; it would now hold for n ≤ 22.

## Check 1: the upper bounds, in two minutes

Run `python3 verify.py`. It checks each witness chain:

- every number is prime;
- each step is one more than an even multiple of the previous prime;
- the previous prime is always the greatest prime factor of the next number minus 1.

A chain like that proves its last prime takes at least that many steps, so a(n) is at most that prime. The upper bounds
need no trust in any search program.

## Check 2: the lower bounds, and what you would be trusting

The exact values also need minimality: no smaller prime takes as many steps. That comes from exhaustive computer
searches.

**Why the search cannot miss a prime**
- Let R_t be the primes with a chain of t primes ending at them. An odd prime p is in R_t exactly when p − 1 has a prime
  factor in R_{t−1} (Lemma 1). That factor is at most (p − 1)/2.
- So to find every member of R_t up to Y, you need R_{t−1} only up to Y/2. The search builds the levels bottom-up, each
  from the one below: a "pyramid".
- **Lemma R** halves those ranges again. In a chain p_t, p_{t+1}, …, p_T, write each step as p_{i+1} = m_i·p_i + 1, so
  that p_T > p_t·m_t·…·m_{T−1}.
  - If any m_i is at least 4, then p_t is below Y/2^{T−t+1}: it lies in the lower half of the plain range.
  - If every m_i is 2, the tail is forced: p_T = 2^{T−t}(p_t + 1) − 1. Those few candidates are tested directly.
- **Primality tests.** The test used (BPSW) has no failures below 2⁶⁴, and every number here is below 2⁵⁷.

**Why A082449 and the search agree.** A082449 follows one particular chain, the greatest prime factor at each step. The
search allows any chain. So every prime A082449 counts is also found by the search, which gives A082449(n) ≥ P(n+1).
Each minimizing prime's own chain follows the greatest prime factor at every step, so the two are equal.

**What guards against a bug**
- Two separately written implementations agree on P(22), and two on P(23).
- Each reproduces every term OEIS lists, a(0) to a(20), and the other's intermediate counts.
- A plainer method without Lemma R found nothing below 4.33·10¹⁴ for P(22), as it should.
- `verify.py`'s plain pyramid shares no code with the searches and reproduces a(1) to a(14).

**What has not been checked**
- No person has read the large searches' code.
- The second P(22) run uses the same method, written afresh.
- Nothing is Lean-checked.

## Before an OEIS submission

OEIS's [policy on AI use](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions) requires:
- a human author who has checked the terms and understands any program submitted;
- no AI-written comments.

In practice:

1. **Decide whether you can vouch for the values**, using checks 1 and 2.
2. **Get an independent computation first** (recommended), by someone with their own program.
   - The entry's recent extenders are Jud McCranie, who added a(17) to a(20) in April 2026, and David A. Corneth, who
     wrote the bounds comment.
   - The SeqFan mailing list is where OEIS contributors discuss checks like this.
3. **Make the edit.** If it holds up, it is small:
   - append the two terms to the DATA and the b-file;
   - add an EXTENSIONS line with your name.

   Any comment, for example on a(23)'s bounds, should be in your own words.

## Facts for an independent check

- a(21) = 866284735109723: exhaustive over all primes up to 866284735109723, that number's own chain giving the bound.
- a(22) = 2957807053316399: exhaustive over all primes up to 3465138940438892.
- a(23) > 9·10¹⁵: exhaustive over all primes up to 9·10¹⁵. a(23) ≤ 94649825706124769 = 32·a(22) + 1.
- The chains are listed in `README.md`.
- Method: a bottom-up pyramid of the level sets (primes with a chain of t primes), halved again by Lemma R. Run times were
  29–61 minutes per run on an Apple M1 Pro.
