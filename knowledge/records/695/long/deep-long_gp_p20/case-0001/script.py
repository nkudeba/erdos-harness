# LONG: independent PARI/GP confirmation of P(20) (no numpy, no sieve marking): candidate pyramid,
# R_t exact on (0, Y_t], Y_t = floor(Ytop/2^(20-t)), Ytop = 7.36e12 (same ranges as check_c2.py).
# Decides whether min R_20(7.36e12) = 7242080052479.
import time
from cypari2 import Pari
pari = Pari(); pari.allocatemem(4 * 10**9)
TEST = False
T, Ytop = (18, 80_000_000_000) if TEST else (20, 7_360_000_000_000)
t0 = time.time()
pari(r"""
lvl(Rp, Y) = {
  my(L = List());
  foreach (Rp, q, if (2*q+1 > Y, break);
    forstep (n = 2*q+1, Y, 2*q, if (isprime(n), listput(L, n))));
  Set(L);
}
""")
LVL = pari("lvl")
Y = [None, None] + [Ytop >> (T - t) for t in range(2, T + 1)]
R = pari(f"primes([3, {Y[2]}])")
print("t=2", len(R), flush=True)
mins = {}
for t in range(3, T + 1):
    R = LVL(R, Y[t])
    mins[t] = int(R[0]) if len(R) else None
    print(f"t={t} Y_t={Y[t]} |R_t|={len(R)} min={mins[t]} time={time.time()-t0:.0f}", flush=True)
print(f"RESULT: GP pyramid: min R_{T}(Y_{T}={Y[T]}) = {mins[T]}; min R_{T-1}(Y_{T-1}={Y[T-1]}) = {mins[T-1]}"
      + (" (agrees with P(20)=7242080052479)" if mins[T] == 7242080052479 else ""))
