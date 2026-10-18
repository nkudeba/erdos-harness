"""Checks for knowledge/records/695 that anyone can read and run: numpy and sympy, about a minute.

Written separately from the engine's search programs, so it shares no code with them.

1. The witness chains. Every element is prime, each step is one more than an even multiple of the previous prime, and
   the previous prime is always the GREATEST prime factor of (next - 1). This proves the upper bounds
       A082449(21) <= 866284735109723,  A082449(22) <= 2957807053316399,  A082449(23) <= 94649825706124769.
2. The search method, on the terms OEIS already lists. A plain pyramid (Lemma 1 only, without the Lemma R refinement the
   large runs used) recomputes P(t) for t <= 15 and compares them with A082449(t - 1). This checks the method's logic,
   not the large runs themselves.

P(t) is the least prime p with Pratt height H(p) >= t, where H(2) = 1 and H(p) = 1 + max H(q) over the primes q | p - 1.
Lemma 1: an odd prime p has H(p) >= t (t >= 3) exactly when p - 1 has a prime factor r with H(r) >= t - 1. Such an r is
odd, so p = m*r + 1 with m even, which gives p ≡ 1 (mod 2r) and r <= (p - 1)/2.
"""
import numpy as np
from sympy import factorint, isprime

CHAINS = {
    "A082449(21) = P(22)": [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637,
                            716174549, 1432349099, 25782283783, 1082855918887, 10828559188871, 21657118377743,
                            433142367554861, 866284735109723],
    "A082449(22) = P(23)": [2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907,
                            4457536189, 106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549,
                            739451763329099, 1478903526658199, 2957807053316399],
}
CHAINS["A082449(23) <= upper bound"] = CHAINS["A082449(22) = P(23)"] + [32 * 2957807053316399 + 1]

# A082449(0..20), from the OEIS entry (October 2026)
OEIS = [2, 3, 7, 23, 47, 283, 719, 1439, 2879, 34549, 138197, 1266767, 14619833, 36449279, 377982107, 1432349099,
        22111003847, 54560052479, 619108107719, 7242080052479, 64750853277599]


def check_chain(chain: list[int]) -> bool:
    """sympy's isprime is deterministic below 2^64, and every value here is far below that."""
    ok = all(isprime(p) for p in chain)
    for a, b in zip(chain, chain[1:]):
        ok = ok and (b - 1) % a == 0 and max(factorint(b - 1)) == a
    return ok


def gpf_steps(p: int) -> int:
    """How many times "take the greatest prime factor of p - 1" is applied before reaching 2 (the A082449 count)."""
    steps = 0
    while p != 2:
        p, steps = max(factorint(p - 1)), steps + 1
    return steps


def primes_up_to(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return sieve


def plain_pyramid(T: int, Y: int) -> dict[int, int]:
    """min R_t for t = 2..T, where level t holds R_t ∩ (0, Y // 2^(T - t)]: a witness for a prime at level t lies at
    level t - 1 and is at most half as large, so each level's range is half the next one's (Lemma 1)."""
    is_prime = primes_up_to(Y)
    level = np.flatnonzero(is_prime[: Y // 2 ** (T - 2) + 1])
    level = level[level > 2]                                  # R_2 = the odd primes
    best = {2: int(level.min())}
    for t in range(3, T + 1):
        top = Y // 2 ** (T - t)
        marked = np.zeros(top + 1, dtype=bool)
        for r in level:                                       # p = m*r + 1 with m even: p ≡ 1 (mod 2r)
            marked[2 * r + 1::2 * r] = True
        level = np.flatnonzero(marked & is_prime[: top + 1])
        if level.size == 0:
            break
        best[t] = int(level.min())
    return best


if __name__ == "__main__":
    print("1. Witness chains")
    for name, chain in CHAINS.items():
        print(f"   {name}: {chain[-1]} — {len(chain)} primes, {gpf_steps(chain[-1])} greatest-prime-factor steps, "
              f"valid: {check_chain(chain)}")
    print("2. Plain pyramid against the terms OEIS lists (T = 15, Y = 4*10^8)")
    best = plain_pyramid(15, 400_000_000)
    for t, p in sorted(best.items()):
        print(f"   P({t}) = {p}: equals A082449({t - 1}) = {OEIS[t - 1]}: {p == OEIS[t - 1]}, "
              f"its greatest-prime-factor steps = {gpf_steps(p)}")
