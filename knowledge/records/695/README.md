# Erdős #695: new terms of OEIS A082449 (computed 2026-10-16 and 17)

**Status: computed, not yet reviewed by a person.** Each exact value comes from two independent exhaustive computer
searches that agree. Each witness chain was checked independently. Minimality rests on the searches' correctness, not on
a proof, and nothing here is Lean-checked.

## What is computed

- **P(k)** is the least prime p that ends a chain of primes 2 = p₁ < p₂ < … < p_k = p in which each p_{i+1} ≡ 1
  (mod p_i). Equivalently, it is the least prime whose Pratt tree has height k (H(2) = 1, H(p) = 1 + max H(q) over the
  primes q dividing p − 1).
  - Erdős #695 asks how fast such chains must grow: is lim p_k^{1/k} = ∞?
- **A082449(n)** is the least prime that needs at least n steps to reach 2 when you repeatedly take the greatest prime
  factor of p − 1.
  - That iteration is one particular chain, so A082449(n) ≥ P(n+1).
  - When the minimizing prime's chain follows the greatest prime factor at every step, the two are equal. That holds for
    every value below.

## Results

| Quantity | Value | How it was obtained |
|---|---|---|
| P(21) = A082449(20) | 64,750,853,277,599 | Already OEIS's last listed term; reproduced exactly (`long/deep-long_pyr21`). |
| P(22) = A082449(21) | 866,284,735,109,723 | Exhaustive over all primes ≤ 8.66·10¹⁴ by two runs (`long/marathon-1-long_p22`, `long/marathon-2-long_p22`). OEIS had this value only as an upper bound, in D. A. Corneth's comment. |
| P(23) = A082449(22) | 2,957,807,053,316,399 | Exhaustive over all primes ≤ 3.465·10¹⁵ by two independent implementations (`long/marathon-2-long_p23`, `long/marathon-3-long_p23i`). OEIS's comment gave the upper bound 11,407,852,252,734,739. |
| P(24) = A082449(23) | 9·10¹⁵ < P(24) ≤ 94,649,825,706,124,769 | The lower bound: one exhaustive run over primes ≤ 9·10¹⁵ (`long/marathon-3-long_p24`). The upper bound: an explicit chain, 32·P(23) + 1. OEIS's comment gave 115,504,631,269,039,577. |

The marathon-3 run also re-derived P(14) through P(22), each matching.

Witness chains (each element prime; each step is 1 more than a small multiple of the previous prime, which is therefore
the greatest prime factor):

- P(22): 2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637, 716174549, 1432349099,
  25782283783, 1082855918887, 10828559188871, 21657118377743, 433142367554861, 866284735109723
- P(23): 2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907, 4457536189,
  106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549, 739451763329099, 1478903526658199,
  2957807053316399
- P(24) ≤: the P(23) chain, then 94649825706124769

## Evidence in this folder

- `long/<job>/`: each computation, with the script (`case-0001/script.py`), its sha256 (`manifest.json`) and its output
  (`case-0001/attempt-1.log`, `RESULTS.md`).
- `notebooks/marathon-{1,2,3}.md`: the research sessions' notebooks. They hold the "refined pyramid" search and the
  pruning lemma (Lemma R) that the exhaustive runs rely on.
- `check_chains.py`: the session's checker for the witness chains. It prints CERTIFIED in the harness sandbox.
- An operator-side check, 2026-10-17, independent of the session's code: all three chains, every element prime (sympy,
  deterministic below 2⁶⁴), every step ≡ 1 mod the previous, the previous always the greatest prime factor.

## Caveats

- Minimality depends on the searches being correct, the refined pyramid and Lemma R in particular.
  - Both P(22) runs use the refined method. The plain-method cross-check (`long/marathon-2-long_p22b`) covered only
    primes ≤ 4.33·10¹⁴, where it found none, as it should.
  - P(23)'s two runs are separate implementations of the refined method.
- Not Lean-checked. The chains (the upper bounds) are within reach of a Lean proof by Pratt certificates; the minimality
  is not.
- A person should review this before anyone calls it new or submits it to OEIS.

## Assistance (the honesty rule)

- The engine's research sessions designed and requested every computation (their `LONG:` lines). The campaign ran them
  with no model calls.
- The operator session intervened on infrastructure and scheduling only, with no mathematical input:
  - it added the OEIS lookup after P(21) turned out to be a known term;
  - it routed record problems to the deep tier;
  - it queued one certification pass by hand, after two automatic follow-ups had done nothing (a bug, since fixed).
- The job manifests say "Operator selected scripts and attack order". That was the long-computation tool's default
  label. For these jobs the engine's sessions selected the scripts, and the label is now recorded correctly for new jobs.

## Reproducing a run

Copy a job folder elsewhere and run its case through the harness sandbox, for example:

```bash
python3 -c "import harness as H, subprocess, sys; subprocess.run(H.sandbox_argv(sys.argv[1]))" path/to/case-0001/script.py
```

The full P(23) runs took 48–61 minutes each on this machine, an Apple M1 Pro.
