# Wide GP beam (deep/check_c3 algorithm, B nodes per level, m <= max(M0, C log q)); every link of every reported
# chain is then PROVED prime in pure Python by Pocklington (p_i prime, p_i^2 > p_{i+1}) or trial division.
import time, math
from cypari2 import Pari
pari = Pari(); pari.allocatemem(4 * 10**9)
TEST = False
B, M0, C, K = (400, 60, 3.0, 100) if TEST else (16000, 60, 3.0, 100)
t0 = time.time()
pari(r"""
bt(B, M0, C, K) = {
  my(par = List([0]), val = List([2]), mul = List([0]), lev = [1], bestL = List([1]), cand, s, w, Mq);
  for (k = 2, K,
    cand = List();
    foreach (lev, i, my(q = val[i]); Mq = max(M0, floor(C * log(q)));
      for (m = 1, Mq, my(n = m*q + 1); if (n % 2 == 1 && ispseudoprime(n), listput(cand, [n, i, m]))));
    cand = vecsort(Vec(cand), 1);
    s = List(); w = 0;
    for (j = 1, #cand, if (w == 0 || cand[j][1] != val[w],
        listput(val, cand[j][1]); listput(par, cand[j][2]); listput(mul, cand[j][3]); w = #val; listput(s, w);
        if (#s >= B, break)));
    if (#s == 0, return(0));
    listput(bestL, s[1]);
    print("level ", k, " best ", val[s[1]], " time ", gettime());
    lev = Vec(s));
  [Vec(par), Vec(mul), Vec(bestL)];
}
""")
out = pari(f"bt({B},{M0},{C},{K})")
par = [int(x) for x in out[0]]; mul = [int(x) for x in out[1]]; best = [int(x) for x in out[2]]
def word(k):
    i = best[k - 1]; ws = []
    while par[i - 1]:
        ws.append(mul[i - 1]); i = par[i - 1]
    return ws[::-1]
def prime_link(q, m):
    N = m * q + 1
    if q * q <= N:
        return N > 1 and all(N % d for d in range(2, math.isqrt(N) + 1))
    for a in range(2, 200):
        if pow(a, N - 1, N) != 1: return False
        if math.gcd(pow(a, m, N) - 1, N) == 1: return True
    return False
DEEP = [10411,10736,11816,13158,14059,14937,16057,17062,17840,19078,20224,21180,22817,23516,24839,26040,26987,27765,29313,29915,31870,33017,34163,35418,37238,37840,39358,40885,41881,43027,44442,46499,48057,49127,51200,52407,53982,55341,56130,58033,58871,61159,62530,63433,64911,66464,67765,69218,71110,73063,74552,76532,77432,78878,80781,82479,83772,85246,86246,88566,90487,91566,92911,94327,95977,96669,98313,100267,102300,104395,106056,108139,108999,110476,111476,113772,115396,117497,119275,120783,122198,124215,126788,128157]
ok = True; tab = []
for k in range(1, K + 1):
    ws = word(k); p = 2
    for m in ws:
        if not prime_link(p, m): ok = False; print("link fails", k); break
        p = m * p + 1
    tab.append((k, p, ws))
improved = []
for k, p, ws in tab:
    if k >= 17:
        lg = math.floor(1000 * math.log10(p))
        if lg < DEEP[k - 17]:
            improved.append(k)
            if k <= 40 or k % 10 == 0:
                print("W", k, p if k <= 30 else lg, ",".join(str(m // 2 if m > 1 else 0) for m in ws))
print("all links Pocklington-proved:", ok, "time", round(time.time() - t0))
print("RESULT: beam B=%d: improved over deep/C3 at %d of 84 k in 17..100: %s; floor(1000 log10 P_k bound) k=17..100: %s"
      % (B, len(improved), improved, [math.floor(1000 * math.log10(p)) for k, p, ws in tab if k >= 17]))
