"""Is the masked #397 run's family new?  Exact comparison against every published solution family.

Sources read 2026-09-24: erdosproblems.com/397 + its forum thread (30 comments), MathOverflow 138209
(Elkies 2013, Krachun 2026, Taylor 2026), AoPS China TST 2012 Quiz 1 Day 1 P3 thread (2012-2023 posts).
"""
from fractions import Fraction
from math import comb

def ratio(S, T):
    """prod C(2s,s) / prod C(2t,t), exact. Pads with 0 (C(0,0)=1), pairs sorted elements, multiplies the
    short interval products C(2x,x)/C(2y,y) = prod_{m=y+1}^{x} 2(2m-1)/m. Any bijection is valid; sorted keeps
    the intervals short for 'local' solutions."""
    S, T = sorted(S), sorted(T)
    n = max(len(S), len(T))
    S, T = [0] * (n - len(S)) + S, [0] * (n - len(T)) + T
    r = Fraction(1)
    for x, y in zip(S, T):
        lo, hi, sign = (y, x, 1) if x > y else (x, y, -1)
        seg = Fraction(1)
        for m in range(lo + 1, hi + 1):
            seg *= Fraction(2 * (2 * m - 1), m)
        r *= seg if sign == 1 else 1 / seg
    return r

def ok(S, T):
    S, T = list(S), list(T)
    return (len(set(S)) == len(S) and len(set(T)) == len(T) and not set(S) & set(T)
            and all(v > 0 for v in S + T) and ratio(S, T) == 1)

key = lambda S, T: frozenset([frozenset(S), frozenset(T)])   # orientation-free

# ---------------- the harness family (masked #397 run, runs/20260923-213808-216117-bench-erdos39851) ----------------
def H(t):
    return ([2*t*t + 13*t + 21, 2*t + 8, 2*t + 5, 8*t**3 + 82*t*t + 277*t + 307],
            [2*t*t + 13*t + 20, 2*t + 7, 2*t + 6, 8*t**3 + 82*t*t + 277*t + 308])

# closed form: n = B = 2t+6, A = n(n+1)/2, C = n+2, D = (2n-1)(n+1)(n+2)/2  -- valid for EVERY n >= 4
def N(n):
    A, D = n * (n + 1) // 2, (2*n - 1) * (n + 1) * (n + 2) // 2
    return ([A, n + 2, n - 1, D - 1], [A - 1, n + 1, n, D])

# the slice it lives in: f(A)f(C) = f(B)f(D), f(X)=(2X-1)/X, with B(A+C-1) = AC  <=>  (A-B)(C-B) = B(B-1),
# D = (2B-1)(A+C-1).  x = A-B, y = C-B any factorisation of B(B-1).
def slice_sol(B, x, y):
    A, C = B + x, B + y
    D = (2*B - 1) * (A + C - 1)
    return [A, C, B - 1, D - 1], [A - 1, C - 1, B, D]

# ---------------- published families ----------------
def P1(a):   # Somani (site, Jan 2026) = veyron (AoPS, 2012) = Peter Taylor (MO, Jan 2026)
    c = 8*a*a + 8*a + 1
    return [a, 2*a + 2, c], [a + 1, 2*a, c + 1]
def P2(k):   # yunxiu, AoPS 2012
    return [4*k + 1, 6*k, 12*k - 1, 8*k*k + 3*k - 1], [4*k + 2, 6*k - 1, 12*k - 2, 8*k*k + 3*k]
def P3(k):   # yunxiu, AoPS 2012
    return [2*k + 1, 3*k - 1, 6*k - 2, 4*k*k + k], [2*k, 3*k, 6*k - 1, 4*k*k + k - 1]
def P4(a, b):   # SharkyKesa family 1 (forum, 11 Jan 2026); needs (2b+1) | (2a+1)(4a+3), b <= 2a
    K, r = divmod((2*a + 1) * (4*a + 3), 2*b + 1)
    if r or b < 0 or b > 2*a:
        return None
    return [a, 2*a - b + 1, 2*a + 2, K - (2*a + 2)], [a + 1, 2*a - b, 2*a + 1, K - (2*a + 1)]
def P5(a, b):   # SharkyKesa family 2 (forum, 11 Jan 2026); needs (3b-2) | (2ab-1)
    if b < 1 or 3*b - 2 <= 0:
        return None
    L, r = divmod(2*a*b - 1, 3*b - 2)
    if r:
        return None
    return [a - 1, 2*a - 2, a*b, L], [a, 2*a - 1, a*b - 1, L - 1]
def P6(t):   # octonion (forum, 12 Jan 2026), Simon's factoring trick  (= P4(3t, 1), per BorisAlexeev)
    return [3*t + 1, 24*t*t + 4*t, 6*t + 1, 6*t - 1], [3*t, 24*t*t + 4*t - 1, 6*t + 2, 6*t]
def P7(t):   # old-bielefelder via ChatGPT-5.2 (forum, 12 Jan 2026)
    return [5*t + 3, 40*t*t + 32*t + 6, 10*t + 2, 10*t + 5], [5*t + 2, 40*t*t + 32*t + 5, 10*t + 3, 10*t + 6]
SPECIFIC = {   # individual published solutions
    "Elkies-5 (MO 2013)": ([2, 5, 8, 13, 19], [3, 4, 6, 14, 20]),
    "Elkies-6 (MO 2013)": ([3, 6, 8, 11, 13, 17], [4, 5, 7, 10, 14, 18]),
    "Kesarwani heterogeneous": ([5, 7, 19], [1, 2, 3, 6, 20]),
    "Kesarwani dense": ([1, 4, 6, 8, 10, 13, 14, 16, 20, 23, 25, 27, 31, 35],
                        [2, 3, 5, 7, 9, 12, 15, 17, 19, 22, 26, 29, 33, 34]),
}

def section(s):
    print("\n== " + s)

section("1. sanity: every transcribed published family really is a solution")
assert all(ok(*P1(a)) for a in range(2, 200))
assert all(ok(*P2(k)) for k in range(2, 200))   # k=1 gives S = T
assert all(ok(*P3(k)) for k in range(3, 200))   # k<=2 collide
assert all(ok(*P6(t)) for t in range(1, 200))
assert all(ok(*P7(t)) for t in range(1, 200))
n4 = sum(1 for a in range(1, 150) for b in range(0, 2*a + 1) if P4(a, b) and ok(*P4(a, b)))
n5 = sum(1 for a in range(2, 150) for b in range(1, 150) if P5(a, b) and ok(*P5(a, b)))
bad4 = [(a, b) for a in range(1, 150) for b in range(0, 2*a + 1) if P4(a, b) and not ok(*P4(a, b))]
print(f"P1,P2,P3,P6,P7 verified on 200 parameters each; P4 valid instances {n4}, P5 valid instances {n5}")
print(f"P4 instances failing distinctness (e.g. Kesarwani's own a=1,b=0 note): {len(bad4)}  first: {bad4[:3]}")
for name, (S, T) in SPECIFIC.items():
    assert ok(S, T), name
print("specific published solutions verified:", ", ".join(SPECIFIC))
assert all(key(*P6(t)) == key(*P4(3*t, 1)) for t in range(1, 200))
assert all(key(*P7(t)) == key(*P4(5*t + 2, 2)) for t in range(1, 200))
assert all(key(*P1(a)) == key(*[[v for v in P4(a, 0)[0] if v != 2*a + 1], [v for v in P4(a, 0)[1] if v != 2*a + 1]]) for a in range(2, 200))
print("P6 = P4(3t,1), P7 = P4(5t+2,2), P1 = P4(a,0) with the shared 2a+1 cancelled: all confirmed")

section("2. the harness family is a solution, and its closed form")
assert all(ok(*H(t)) for t in range(0, 400))
assert all(key(*H(t)) == key(*N(2*t + 6)) for t in range(0, 400))
assert all(ok(*N(n)) for n in range(4, 1500))
print("H(t) verified for t = 0..399; H(t) = N(2t+6); N(n) verified for EVERY n = 4..1499 (odd n too)")
for t in range(0, 4):   # independent check with full big-integer central binomials
    S, T = H(t)
    ps = 1
    for v in S: ps *= comb(2*v, v)
    pt = 1
    for v in T: pt *= comb(2*v, v)
    assert ps == pt
print("big-integer check of the full products for t = 0..3: equal (t=3 product has",
      len(str(ps)), "digits)")
print("N(4) =", N(4), " N(5) =", N(5), " (smallest members; the harness's own parametrisation starts at N(6))")

section("3. is any H(t) or N(n) an instance of a published family?  (exact, exhaustive per candidate)")
def published_matches(S, T):
    """Every published instance that could equal (S,T): parameters are forced by the elements."""
    els = S + T
    target = key(S, T)
    hits = []
    for a in els:                       # P1: a is an element; also P4 with a = element
        if a >= 2 and len(S) == 3 and key(*P1(a)) == target: hits.append(("P1", a))
        for e in els:                   # P4: element 2a-b+1 = e  =>  b = 2a+1-e
            b = 2*a + 1 - e
            inst = P4(a, b) if 0 <= b <= 2*a else None
            if inst and key(*inst) == target: hits.append(("P4", a, b))
    for e1 in els:                      # P5: a-1 = e1, ab = e2
        a = e1 + 1
        for e2 in els:
            if e2 % a == 0:
                inst = P5(a, e2 // a)
                if inst and key(*inst) == target: hits.append(("P5", a, e2 // a))
    for e in els:                       # 1-parameter families: parameter forced by any one element
        for fam, forms in (("P2", [(4, 1), (4, 2)]), ("P3", [(2, 0), (2, 1)]), ("P6", [(3, 0), (3, 1)]),
                           ("P7", [(5, 2), (5, 3)])):
            for (m, c) in forms:
                if (e - c) % m == 0 and (e - c) // m >= 1:
                    k = (e - c) // m
                    if key(*{"P2": P2, "P3": P3, "P6": P6, "P7": P7}[fam](k)) == target: hits.append((fam, k))
    for name, st in SPECIFIC.items():
        if key(*st) == target: hits.append((name,))
    return hits

hitsH = {t: published_matches(*H(t)) for t in range(0, 3000)}
hitsN = {n: published_matches(*N(n)) for n in range(4, 3000)}
print("H(t), t=0..2999, instances coinciding with a published one:", sum(bool(v) for v in hitsH.values()))
print("N(n), n=4..2999, instances coinciding with a published one:", sum(bool(v) for v in hitsN.values()),
      [ (n, v) for n, v in hitsN.items() if v][:5])

section("4. structural reason (not just a finite check): the invariants that define P4 and P5")
# Each 4-vs-4 solution here is 4 consecutive pairs (x-1, x); group the pairs by which side holds the upper element.
def groups(S, T):
    Ss, Ts = set(S), set(T)
    up_S = sorted(x - 1 for x in S if x - 1 in Ts)      # pairs whose upper element is in S (lower end listed)
    up_T = sorted(x - 1 for x in T if x - 1 in Ss)
    return up_S, up_T
print("H(t) groups (lower ends):", groups(*H(1)), "at t=1;  symbolic: {2t+7, A-1} | {2t+5, D-1}")
print("P4 needs a lower end y in one group and 2y+1 in the other (a and 2a+1);")
print("P5 needs a lower end y and 2y in the SAME group (a-1 and 2a-2).")
def has_P4_shape(g1, g2):
    return any(2*y + 1 in g2 for y in g1) or any(2*y + 1 in g1 for y in g2)
def has_P5_shape(g1, g2):
    return any(2*y in g1 for y in g1) or any(2*y in g2 for y in g2)
print("H(t) with P4 shape for some t < 3000:", [t for t in range(3000) if has_P4_shape(*groups(*H(t)))][:5])
print("H(t) with P5 shape for some t < 3000:", [t for t in range(3000) if has_P5_shape(*groups(*H(t)))][:5])
print("(as polynomials: 2(2t+5)+1=4t+11, 2(2t+7)+1=4t+15 are never 2t+7, A-1, 2t+5 or D-1 for t>=0,")
print(" and no doubling 2(2t+5), 2(2t+7) hits D-1 or A-1: no polynomial reparametrisation can land in P4 or P5)")

section("5. the slice (A-B)(C-B) = B(B-1): which published families does it contain?")
def divisors(n):
    ds, i = [], 1
    while i * i <= n:
        if n % i == 0:
            ds += [i, n // i] if i * i != n else [i]
        i += 1
    return ds
count = somani = inP4 = inP5 = other = 0
for B in range(2, 400):
    for x in divisors(B * (B - 1)):
        y = B * (B - 1) // x
        if x > y:
            continue
        S, T = slice_sol(B, x, y)
        Sc, Tc = set(S) - set(T), set(T) - set(S)          # cancel shared elements (the chained case)
        if not Sc or len(Sc) != len(S) - len(set(S) & set(T)) or not ok(sorted(Sc), sorted(Tc)):
            continue
        count += 1
        if y == x + 1: somani += 1                          # x = B-1, y = B  is exactly Somani's family
        h = published_matches(sorted(Sc), sorted(Tc))
        if any(m[0] == "P4" for m in h): inP4 += 1
        elif any(m[0] == "P5" for m in h): inP5 += 1
        elif h: other += 1
print(f"B = 2..399: {count} valid slice solutions; {somani} are Somani's (the factorisation x=B-1, y=B, 3-vs-3 after")
print(f"cancelling 2a+1 -- same as P4 with b=0); coincide with P4: {inP4}, with P5: {inP5}, other published: {other}")
assert all(key(*[sorted(set(slice_sol(a+1, a, a+1)[0]) - set(slice_sol(a+1, a, a+1)[1])),
                 sorted(set(slice_sol(a+1, a, a+1)[1]) - set(slice_sol(a+1, a, a+1)[0]))]) == key(*P1(a))
           for a in range(2, 300))
print("confirmed: slice(B=a+1, x=a, y=a+1) = Somani's P1(a) for a = 2..299")
