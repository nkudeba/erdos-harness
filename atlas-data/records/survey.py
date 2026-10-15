"""Records and explicit-threshold survey: where a computation could produce a NEW certified result. No model calls.

Two kinds of target, both certified by computation rather than found by insight alone:
- RECORD: an open problem tied to a finite quantity, through its OEIS sequences or its own page: a new value, the next
  term, a better explicit construction or bound, or a counterexample. A certificate (the explicit object, or an
  exhaustive search's log) is checked independently, and a small one is proved in Lean.
- EXPLICIT: an open problem whose page says the answer is known for sufficiently large n, or with finitely many
  exceptions. Making the threshold explicit and checking the range below it by computer settles the problem outright.

Why: the campaign's settle attempts compete with a wave of AI-assisted proof claims (145 of 633 open problems carry
one, 2026-10-15), and #769, its only complete answer judged new, was a weaker form of two of them. Both kinds here reward
patient, checkable computation, where a harness that can run for days has an edge.

    python3 atlas-data/records/survey.py            # rank from the caches, fetching OEIS entries not yet cached
    python3 atlas-data/records/survey.py --refresh  # refetch every OEIS entry

Writes `atlas-data/records/survey.json`; `resolution.queue` reads it for the record and explicit tracks.
"""
import argparse, json, math, re, sys, time, urllib.error, urllib.request
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "atlas-data"))
from atomic import atomic_write_json          # noqa: E402

OEIS = HERE / "oeis"
OUT = HERE / "survey.json"
UA = "Mozilla/5.0 (erdos-harness research survey)"
OPENISH = ("open", "open (Lean)", "falsifiable", "decidable", "verifiable")
CLAIMS_RE = re.compile(r"There (?:are|is) (\d+) proof claims?")
TABLE_RE = re.compile(r"Table of n, a\(n\) for n = (-?\d+)\.\.(\d+)")
# A result known for large n with the rest unchecked: the explicit track. Each pattern names what it signals.
EXPLICIT = [
    (r"sufficiently large", "known for sufficiently large n"),
    (r"for all large", "known for all large n"),
    (r"all but finitely many", "known with finitely many exceptions"),
    (r"finitely many exceptions", "known with finitely many exceptions"),
    (r"only finitely many", "finitely many cases"),
    (r"for (?:all )?\$?n\s*(?:\\geq|\\ge|>|≥)\s*\d", "known beyond an explicit n"),
    (r"(?:verified|checked|confirmed) (?:for|up to|below)", "verified up to a bound"),
    (r"ineffective", "an ineffective bound"),
    (r"\bn_0\b|N_0", "an unspecified threshold"),
]
# A finite quantity with a stated record: the records track.
RECORD_PHRASES = [
    (r"(?:best|currently) known (?:lower|upper)? ?bounds?", "best known bounds stated"),
    (r"(?:is known|are known) for (?:all )?\$?n\s*(?:\\leq|\\le|<|≤)", "values known for small n"),
    (r"computer search|computation|computed|exhaustive", "computational results cited"),
    (r"\b[A-Z]\(\d+(?:,\s*\d+)*\)\s*(?:=|\\geq|\\leq|≥|≤)", "explicit small values cited"),
]


def fetch_oeis(a: str, refresh: bool) -> dict | None:
    f = OEIS / f"{a}.json"
    if f.exists() and not refresh:
        try:
            return json.loads(f.read_text())
        except ValueError:
            pass
    req = urllib.request.Request(f"https://oeis.org/search?q=id:{a}&fmt=json", headers={"User-Agent": UA})
    for k in range(3):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                data = json.loads(r.read().decode(errors="replace"))
            break
        except (urllib.error.URLError, TimeoutError, OSError, ValueError):
            time.sleep(5 * (k + 1))
    else:
        return None
    rec = data[0] if isinstance(data, list) and data else (data.get("results") or [None])[0] if isinstance(data, dict) else None
    if rec is None:
        return None
    OEIS.mkdir(parents=True, exist_ok=True)
    f.write_text(json.dumps(rec, ensure_ascii=False))
    time.sleep(1.0)                                   # one request a second: the OEIS is a shared resource
    return rec


def oeis_summary(a: str, rec: dict) -> dict:
    terms = [t for t in (rec.get("data") or "").split(",") if t.strip()]
    kw = set((rec.get("keyword") or "").split(","))
    links = rec.get("link") or []
    table = [(int(m.group(1)), int(m.group(2))) for l in links for m in [TABLE_RE.search(str(l))] if m]
    known = max((hi - lo + 1 for lo, hi in table), default=len(terms))
    last = terms[-1].strip() if terms else ""
    return {"id": a, "name": (rec.get("name") or "")[:200], "terms_in_entry": len(terms), "known_terms": known,
            "last_term_digits": len(last.lstrip("-")), "keywords": sorted(kw), "more": "more" in kw, "hard": "hard" in kw,
            "complete": bool(kw & {"fini", "full", "done"}), "revised": (rec.get("time") or "")[:10],
            "revision": int(rec.get("revision") or 0)}


def record_score(seqs: list[dict]) -> tuple[float, list[str]]:
    """A heuristic order, never a probability: wanted terms, few known, no completeness keyword."""
    best, why = 0.0, []
    for s in seqs:
        if s["complete"]:
            continue
        sc = 1.0
        w = []
        if s["more"]:
            sc += 2.0
            w.append(f"{s['id']} wants more terms")
        if s["hard"]:
            sc += 0.5                                   # a new term is an achievement there, and rarely attempted
            w.append(f"{s['id']} is marked hard")
        if s["known_terms"] <= 15:
            sc += 1.5
            w.append(f"{s['id']} has only {s['known_terms']} known terms")
        elif s["known_terms"] <= 40:
            sc += 0.75
        if s["last_term_digits"] > 30:
            sc -= 1.0                                   # astronomically large values: a search will not reach the next
        if sc > best:
            best, why = sc, w
    return round(best, 3), why


def page_text(d: dict) -> str:
    t = d.get("thread") or ""
    end = t.find("Proof expositions")
    nav = t.rfind("Random", 0, end) if end >= 0 else -1
    head = t[(nav + len("Random")) if nav >= 0 else 0:end] if end >= 0 else ""
    i = t.find("Order by")
    body = (t[i:] if i >= 0 else "").split("All comments are the responsibility of the user")[0]
    return head + "\n" + body


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--refresh", action="store_true", help="refetch every OEIS entry")
    ap.add_argument("--problems", help="the problem database (default: the newest resolution/fresh/problems-*.yaml)")
    a = ap.parse_args()
    import yaml
    db = Path(a.problems) if a.problems else max((ROOT / "resolution" / "fresh").glob("problems-*.yaml"), default=None)
    if db is None:
        db = ROOT / "benchmarks" / "timesplit" / "cache" / "teorth-problems.yaml"
    probs = {str(p["number"]): p for p in yaml.safe_load(db.read_text())}
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    records, explicit = [], []
    for n, p in sorted(probs.items(), key=lambda kv: int(kv[0])):
        state = (p.get("status") or {}).get("state")
        if state not in OPENISH:
            continue
        f = ROOT / "atlas-data" / "forum" / f"{n}.json"
        forum = json.loads(f.read_text()) if f.exists() else {}
        m = CLAIMS_RE.search(forum.get("claims") or "")
        claims = int(m.group(1)) if m else 0
        text = page_text(forum) if forum else ranks.get(n, {}).get("statement", "")
        base = {"problem": int(n), "state": state, "claims": claims, "formalized": (p.get("formalized") or {}).get("state"),
                "statement": (ranks.get(n, {}).get("statement") or "")[:300], "forum_cached": bool(forum)}
        seqs = []
        for oid in [x for x in (p.get("oeis") or []) if str(x).startswith("A")]:
            rec = fetch_oeis(oid, a.refresh)
            if rec:
                seqs.append(oeis_summary(oid, rec))
        hits = sorted({label for pat, label in RECORD_PHRASES if re.search(pat, text, re.I)})
        sc, why = record_score(seqs)
        if seqs or hits:
            records.append({**base, "kind": "record", "score": round(sc + 0.5 * len(hits), 3),
                            "why": why + hits, "oeis": seqs})
        ex = sorted({label for pat, label in EXPLICIT if re.search(pat, text, re.I)})
        if ex:
            explicit.append({**base, "kind": "explicit", "score": float(len(ex)), "why": ex,
                             "excerpt": next((text[max(0, mm.start() - 160): mm.end() + 160].replace("\n", " ")
                                              for pat, _ in EXPLICIT for mm in [re.search(pat, text, re.I)] if mm), "")})
    records.sort(key=lambda r: (-r["score"], r["claims"], r["problem"]))
    explicit.sort(key=lambda r: (-r["score"], r["claims"], r["problem"]))
    out = {"at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "problems_db": str(db.relative_to(ROOT)),
           "note": "scores are a heuristic order for the campaign's queue, never probabilities",
           "records": records, "explicit": explicit}
    atomic_write_json(OUT, out, indent=1)
    unclaimed = lambda xs: [x for x in xs if not x["claims"]]
    print(f"records: {len(records)} candidates ({len(unclaimed(records))} unclaimed); "
          f"explicit: {len(explicit)} ({len(unclaimed(explicit))} unclaimed) -> {OUT.relative_to(ROOT)}")
    for x in unclaimed(records)[:12]:
        print(f"  record #{x['problem']} {x['score']}: {'; '.join(x['why'][:3])}")
    for x in unclaimed(explicit)[:12]:
        print(f"  explicit #{x['problem']} {x['score']}: {'; '.join(x['why'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
