"""
Erdős #201 construction search (iteration 2).

Object: an N-element set A ⊂ ℕ (min 0) whose Roth number roth(A) := size of the largest
3-AP-free subset of A is strictly smaller than R_3(N) = rothNumberNat N.  Such an A witnesses
    G_3(N) ≤ roth(A) < R_3(N),
i.e. the strict gap between the two quantities the problem compares.

Ideas (all structured, then a short hill climb):
  * AP-saturated greedy growth: start from a seed with small Roth number (the classical {0,1,2,3,6},
    a short interval, a dilated interval 2·{0..k}) and repeatedly add the integer that keeps roth(A)
    minimal, breaking ties by the NUMBER of maximum 3-AP-free subsets (fewer = more "saturated").
    Since roth is monotone in A while R_3(N) jumps at N = 9, 11, 13, 14, growing without raising roth
    produces the gap.
  * "dilate_plus": 2·{0..k} plus a few odd elements (the iteration-1 record [0,2,..,18] ∪ {9} has
    this shape) — the odd elements act as midpoints that kill all large AP-free subsets.
  * two/three short blocks, and random sets as a control.
Exact Roth numbers are computed by a bitmask branch-and-bound (N ≤ 14, instant).

Score = (R_3(N) - roth(A)) + N/1000   [unit: gap between R_3(N) and the G_3-witness; known best gap = 1].
Certificate (by `decide`, `decide +kernel` for N ≥ 12): (i) every (roth(A)+1)-subset of A contains a
3-AP (so roth(A) ≤ m); (ii) an explicit 3-AP-free subset of {0,…,N-1} of size r (so R_3(N) ≥ r).
Together: R_3(N) - G_3(N) ≥ r - m.
"""
from functools import lru_cache

PARAM_SPACE = {
    "N": [5, 9, 10, 11, 12, 13, 14],
    "style": ["grow_seed", "grow_interval", "grow_dilate", "dilate_plus", "blocks", "random", "record"],
    "span": [1, 2, 3],
    "steps": [0, 10, 25],
}

MAX_N = 14
KNOWN_RECORD = [0, 2, 4, 6, 8, 9, 10, 12, 14, 16, 18]   # roth 5 < 6 = R_3(11)


# ---------------------------------------------------------------- exact Roth number solver
@lru_cache(maxsize=None)
def _solve(A_tuple, want_all):
    """A_tuple sorted, distinct.  Returns (m, sols): m = max size of a 3-AP-free subset,
    sols = tuple of index-bitmasks of such subsets (all of them if want_all, else one)."""
    a = list(A_tuple)
    n = len(a)
    idx = {v: i for i, v in enumerate(a)}
    conf = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i):
            z = 2 * a[j] - a[i]                    # z < a[j] < a[i] is an AP
            if z in idx:
                conf[i].append((1 << j) | (1 << idx[z]))
            s = a[i] + a[j]
            if not (s & 1):                        # a[j] < mid < a[i] is an AP
                h = s >> 1
                if h in idx:
                    conf[i].append((1 << j) | (1 << idx[h]))
    best = [0]
    sols = []

    def rec(i, mask, cnt):
        if i == n:
            if cnt > best[0]:
                best[0] = cnt
                sols[:] = [mask]
            elif cnt == best[0] and want_all:
                sols.append(mask)
            return
        rem = cnt + (n - i)
        if want_all:
            if rem < best[0]:
                return
        elif rem <= best[0]:
            return
        ok = True
        for p in conf[i]:
            if mask & p == p:
                ok = False
                break
        if ok:
            rec(i + 1, mask | (1 << i), cnt + 1)
        rec(i + 1, mask, cnt)

    rec(0, 0, 0)
    return best[0], tuple(sols)


def _mask_to_vals(a, mask):
    return tuple(a[i] for i in range(len(a)) if (mask >> i) & 1)


def roth(A):
    return _solve(tuple(sorted(set(A))), False)[0]


def _num_max_sets(A):
    return len(_solve(tuple(sorted(set(A))), True)[1])


@lru_cache(maxsize=None)
def R3(N):
    """rothNumberNat N with an explicit witness, computed exactly."""
    a = tuple(range(N))
    m, sols = _solve(a, False)
    return m, _mask_to_vals(a, sols[0])


# ---------------------------------------------------------------- helpers
def _normalize(s):
    s = sorted(set(int(x) for x in s))
    if not s:
        return s
    m = s[0]
    return [x - m for x in s]


def _make(N, A):
    return {"N": int(N), "A": _normalize(A)}


def _fill_to(N, s, rng, hi):
    s = set(s)
    while len(s) < N:
        s.add(rng.randrange(0, hi + 1))
    while len(s) > N:
        s.discard(rng.choice(sorted(s)))
    return s


def _grow(B, N, rng, window=6, max_cands=18):
    """AP-saturated greedy growth: add elements keeping roth minimal, tie-break by fewest maximum
    AP-free subsets.  Works with negative values, normalized at the end."""
    s = set(B)
    while len(s) < N:
        lo, hi = min(s) - window, max(s) + window
        cands = [x for x in range(lo, hi + 1) if x not in s]
        if len(cands) > max_cands:
            cands = rng.sample(cands, max_cands)
        rv = {x: roth(s | {x}) for x in cands}
        mn = min(rv.values())
        ties = [x for x in cands if rv[x] == mn]
        if len(ties) > 1 and len(ties) <= 8:
            cnt = {x: _num_max_sets(s | {x}) for x in ties}
            mc = min(cnt.values())
            ties = [x for x in ties if cnt[x] == mc]
        s.add(rng.choice(ties))
    while len(s) > N:
        s.discard(rng.choice(sorted(s)))
    return _normalize(s)


# ---------------------------------------------------------------- generate / mutate
def generate(params, rng):
    N = int(params.get("N", 11))
    N = max(3, min(MAX_N, N))
    style = params.get("style", "grow_seed")
    span = int(params.get("span", 2))
    steps = int(params.get("steps", 10))

    if style == "record":
        base = [x for x in KNOWN_RECORD]
        if N <= len(base):
            s = set(base[:N])
            s = _grow(s, N, rng) if len(s) < N else s
        else:
            s = _grow(set(base), N, rng)
    elif style == "grow_seed":
        s = _grow({0, 1, 2, 3, 6}, N, rng)
    elif style == "grow_interval":
        k = max(2, min(N, rng.choice([3, 4, 5, N // 2 + 1])))
        s = _grow(set(range(k)), N, rng)
    elif style == "grow_dilate":
        k = max(2, min(N, N - rng.randrange(1, max(2, N // 3 + 1))))
        s = _grow(set(2 * x for x in range(k)), N, rng)
    elif style == "dilate_plus":
        k = max(2, N - rng.randrange(1, max(2, N // 3 + 1)))
        s = set(2 * x for x in range(k))
        odds = list(range(1, 2 * k - 1, 2))
        rng.shuffle(odds)
        # prefer central odd elements (midpoints of many even pairs)
        odds.sort(key=lambda o: abs(o - (k - 1)) + rng.random() * span)
        for o in odds:
            if len(s) >= N:
                break
            s.add(o)
        s = _fill_to(N, s, rng, 2 * k + 2)
    elif style == "blocks":
        nb = rng.choice([2, 3])
        s = set()
        pos = 0
        left = N
        for b in range(nb):
            ln = max(1, left // (nb - b)) if b < nb - 1 else left
            ln = min(ln, left)
            s.update(range(pos, pos + ln))
            left -= ln
            pos += ln + rng.randrange(1, span * ln + 2)
        s = _fill_to(N, s, rng, pos)
    else:  # random
        L = N + rng.randrange(0, span * N + 1)
        s = set(rng.sample(range(L), N))

    obj = _make(N, s)
    # cheap hill climb: accept non-increasing roth(A)
    cur = roth(obj["A"])
    for _ in range(steps):
        cand = mutate(obj, rng)
        if not valid(cand):
            continue
        r = roth(cand["A"])
        if r <= cur:
            obj, cur = cand, r
    return obj


def mutate(obj, rng):
    A = list(obj["A"])
    N = obj["N"]
    if not A:
        return _make(N, range(N))
    hi = max(A) + 3
    s = set(A)
    r = rng.random()
    if r < 0.55:
        # replace one element by a random one
        x = rng.choice(A)
        s.discard(x)
        tries = 0
        while tries < 50:
            y = rng.randrange(0, hi + 1)
            if y not in s:
                s.add(y)
                break
            tries += 1
        if len(s) < N:
            s.add(x)
    elif r < 0.8:
        # remove one element, re-add greedily (roth-minimizing) from a small window
        x = rng.choice(A)
        s.discard(x)
        cands = [y for y in range(-3, hi + 1) if y not in s]
        cands = rng.sample(cands, min(8, len(cands)))
        best_y, best_r = None, None
        for y in cands:
            ry = roth(s | {y})
            if best_r is None or ry < best_r:
                best_y, best_r = y, ry
        s.add(best_y if best_y is not None else x)
    elif r < 0.92:
        # shift a suffix by ±1
        i = rng.randrange(1, len(A))
        d = rng.choice([-1, 1])
        B = A[:i] + [x + d for x in A[i:]]
        if len(set(B)) == N and min(B) >= 0:
            s = set(B)
    else:
        # reflect (AP-structure preserving)
        mx = max(A)
        s = set(mx - x for x in A)
    return _make(N, s)


# ---------------------------------------------------------------- valid / score / describe
def valid(obj):
    try:
        N = int(obj["N"])
        A = obj["A"]
    except Exception:
        return False
    if not (3 <= N <= MAX_N):
        return False
    if not isinstance(A, list) or len(A) != N:
        return False
    if any((not isinstance(x, int)) or isinstance(x, bool) or x < 0 for x in A):
        return False
    if len(set(A)) != N:
        return False
    if max(A) > 400:
        return False
    return True


def score(obj):
    if not valid(obj):
        return -1e9
    N = obj["N"]
    r = R3(N)[0]
    m = roth(obj["A"])
    return float(r - m) + N / 1000.0


def describe(obj):
    if not valid(obj):
        return "invalid object"
    N = obj["N"]
    A = obj["A"]
    r, _ = R3(N)
    m = roth(A)
    return (f"N={N}, A={A}: roth(A)={m}, R_3(N)={r}, gap={r - m} "
            f"(score unit: R_3(N)-roth(A); known best gap 1). Certifies G_3({N}) <= {m} and R_3({N}) >= {r}.")


# ---------------------------------------------------------------- Lean certificate
def _finset_lit(xs):
    return "({" + ", ".join(str(x) for x in sorted(xs)) + "} : Finset ℕ)"


def lean_certificate(obj):
    N = obj["N"]
    A = sorted(obj["A"])
    m = roth(A)
    r, W = R3(N)
    k = m + 1
    Alit = _finset_lit(A)
    Wlit = _finset_lit(W)
    tactic = "decide" if N <= 11 else "decide +kernel"
    return f"""-- IMPORTS: Mathlib.Data.Finset.Powerset
-- IMPORTS: Mathlib.Data.Finset.Card
-- Object: A = {A} (N = {N}).  Claims: (i) every {k}-subset of A contains a 3-term AP,
-- hence addRothNumber A ≤ {m} and G_3({N}) ≤ {m};  (ii) W = {list(W)} ⊆ {{0,…,{N-1}}} is 3-AP-free
-- with |W| = {r}, hence rothNumberNat {N} ≥ {r}.  Together: R_3({N}) - G_3({N}) ≥ {r - m}.
set_option maxRecDepth 8192 in
theorem construct_cert :
    ({Alit}.card = {N} ∧
      ∀ t ∈ {Alit}.powersetCard {k},
        ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, a < b ∧ b < c ∧ a + c = b + b) ∧
    ((∀ x ∈ {Wlit}, x < {N}) ∧ {Wlit}.card = {r} ∧
      ∀ a ∈ {Wlit}, ∀ b ∈ {Wlit}, ∀ c ∈ {Wlit},
        a < b → b < c → a + c ≠ b + b) := by
  {tactic}
"""
