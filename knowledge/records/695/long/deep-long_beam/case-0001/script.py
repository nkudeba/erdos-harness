# LONG: wider beam (B=8000) version of check_c3.py, to sharpen the C3 upper bounds P(k) <= p_k for k <= 100.
# Chains found with ispseudoprime (search only); every link then PROVED prime in pure Python by Pocklington
# (p_{i+1} = m p_i + 1, p_i proven prime, p_i^2 > p_{i+1}; a^(N-1)=1, gcd(a^m-1,N)=1) or trial division if tiny.
# Prints a progress line per level, the multiplier word of each best chain (k=17..100) and one RESULT line.
import time, math
from cypari2 import Pari
pari = Pari(); pari.allocatemem(3 * 10**9)
TEST = False
B, M0, C, K = (400, 60, 3.0, 40) if TEST else (20000, 60, 3.0, 100)
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
    printf("k=%d log10best=%.3f beam=%d\n", k, log(val[s[1]])/log(10), #s);
    lev = Vec(s));
  [Vec(par), Vec(mul), Vec(bestL)];
}
""")
out = pari(f"bt({B},{M0},{C},{K})")
par = [int(x) for x in out[0]]; mul = [int(x) for x in out[1]]; best = [int(x) for x in out[2]]
print("beam time", round(time.time() - t0, 1), flush=True)
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
        if pow(a, N - 1, N) == 1:
            if math.gcd(pow(a, m, N) - 1, N) == 1:
                return True
        else:
            return False
    return False
ok = True; table = []
for k in range(1, K + 1):
    ws = word(k)
    if len(ws) != k - 1: ok = False; print("bad length", k); continue
    p = 2
    for m in ws:
        if not prime_link(p, m): ok = False; print("link fails", k, p, m); break
        p = m * p + 1
    table.append((k, p, ws))
for k, p, ws in table:
    if k >= 17: print("word", k, ",".join(map(str, ws)))
print("exact bounds k=17..30:", [(k, p) for k, p, ws in table if 17 <= k <= 30])
print("time", round(time.time() - t0, 1))
print("RESULT: B=%d beam, all links Pocklington-proved=%s; floor(1000*log10 P(k) bound) k=17..%d: %s"
      % (B, ok, K, [math.floor(1000 * math.log10(p)) for k, p, ws in table if k >= 17]))
