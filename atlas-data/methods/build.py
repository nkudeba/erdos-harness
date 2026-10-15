"""Methods library: how sibling Erdős problems were recently resolved or advanced, for the engine to borrow. No model calls.

Two sources, both from the cached erdosproblems.com pages (`atlas-data/forum/<n>.json`):
- every proof claim on a claims page: who, with which model, the summary and the notes (195 on 2026-10-15, mostly
  GPT-5.6 and GPT-6 runs). These are the methods that cracked problems AFTER the model's knowledge cutoff;
- the notes on the pages of solved problems: how the published solution went.

For a target problem, `methods_digest(n)` ranks the entries by shared tags and shared statement words and returns the
closest ones as markdown. The campaign writes it to the problem's library (METHODS.md), which the engine reads beside
the problem's own digest. Why: the engine mapped each problem from its memory and the problem's own page, so a method
that had just cracked a neighbouring problem (#769's numerical-semigroup argument, a Burgess-type character bound)
reached it only if the model happened to know it, and the model's knowledge stops in June 2026.

    python3 atlas-data/methods/build.py               # rebuild methods.json from the caches
    python3 atlas-data/methods/build.py --show 1199   # the digest one problem would get
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "atlas-data"))
from atomic import atomic_write_json          # noqa: E402

OUT = HERE / "methods.json"
SOLVED = ("proved", "disproved", "solved", "proved (Lean)", "disproved (Lean)", "solved (Lean)")
STOP = set("""about above after again against being below between could every first given there these their those
under where which while whose would integer integers number numbers prove proved true false exists exist large largest
small smallest least sufficiently constant function infinitely finite finitely always never other least such
""".split())


def words(text: str) -> set[str]:
    t = re.sub(r"\$[^$]*\$|\\\[.*?\\\]|\\[a-zA-Z]+", " ", text or "", flags=re.S)
    return {w for w in re.findall(r"[a-z]{5,}", t.lower()) if w not in STOP}


def page_parts(d: dict) -> tuple[str, str]:
    """(the problem page's own text, the claims page's claims section)."""
    t = d.get("thread") or ""
    end = t.find("Proof expositions")
    nav = t.rfind("Random", 0, end) if end >= 0 else -1
    head = t[(nav + len("Random")) if nav >= 0 else 0:end] if end >= 0 else ""
    c = d.get("claims") or ""
    m = re.search(r"There (?:are|is) \d+ proof claims?", c)
    return head, (c[m.start():].split("All comments are the responsibility of the user")[0] if m else "")


def parse_claims(section: str) -> list[dict]:
    out = []
    parts = re.split(r"\n\s*A (partial |full )?proof\s*\n", "\n" + section)
    for scope, blk in zip(parts[1::2], parts[2::2]):
        who = re.search(r"claimed by ([^\n]+?)\.?\s*\n", blk)
        summ = re.search(r"Summary:\s*(.*?)(?:\n\s*Notes:|\n\s*\|\s*\n|\n\s*External link|\n\s*Submitted)", blk, re.S)
        notes = re.search(r"Notes:\s*(.*?)(?:\n\s*\|\s*\n|\n\s*External link|\n\s*Submitted)", blk, re.S)
        date = re.search(r"Submitted (\d{4}-\d{2}-\d{2})", blk)
        if not (who and summ):
            continue
        out.append({"by": " ".join(who.group(1).split())[:160], "scope": (scope or "").strip() or "unstated",
                    "summary": " ".join(summ.group(1).split())[:1500],
                    "notes": " ".join(notes.group(1).split())[:1200] if notes else "",
                    "date": date.group(1) if date else ""})
    return out


def build() -> list[dict]:
    import yaml
    db = max((ROOT / "resolution" / "fresh").glob("problems-*.yaml"), default=None) or \
        ROOT / "benchmarks" / "timesplit" / "cache" / "teorth-problems.yaml"
    probs = {str(p["number"]): p for p in yaml.safe_load(db.read_text())}
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    entries = []
    for f in sorted((ROOT / "atlas-data" / "forum").glob("*.json"), key=lambda x: int(x.stem) if x.stem.isdigit() else 0):
        n = f.stem
        try:
            d = json.loads(f.read_text())
        except ValueError:
            continue
        p = probs.get(n) or {}
        state = (p.get("status") or {}).get("state") or ""
        tags = list(p.get("tags") or ranks.get(n, {}).get("tags") or [])
        statement = ranks.get(n, {}).get("statement") or ""
        head, claims = page_parts(d)
        base = {"problem": int(n), "state": state, "tags": tags, "statement": " ".join(statement.split())[:400],
                "words": sorted(words(statement))}
        for c in parse_claims(claims):
            entries.append({**base, "kind": "claim", **c})
        if state in SOLVED and head.strip():
            # the page's notes after the statement: how the published solution went
            notes = head.split(statement[:60])[-1] if statement[:60] and statement[:60] in head else head
            entries.append({**base, "kind": "solution", "summary": " ".join(notes.split())[:1500]})
    return entries


def methods_digest(n: int, entries: list[dict] | None = None, k: int = 8, room: int = 6000) -> str:
    """The `k` entries closest to problem n by shared tags (weight 2) and shared statement words, never n itself."""
    entries = entries if entries is not None else json.loads(OUT.read_text())["entries"]
    me = next((e for e in entries if e["problem"] == int(n)), None)
    if me is None:
        import yaml
        ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
        me = {"tags": ranks.get(str(n), {}).get("tags") or [], "words": sorted(words(ranks.get(str(n), {}).get("statement") or ""))}
    tags, ws = set(me.get("tags") or []), set(me.get("words") or [])

    def score(e):
        return 2 * len(tags & set(e.get("tags") or [])) + len(ws & set(e.get("words") or []))
    ranked = sorted((e for e in entries if e["problem"] != int(n) and score(e) > 0), key=lambda e: (-score(e), -e["problem"]))
    out, used = [], 0
    for e in ranked[:k]:
        head = (f"#{e['problem']} ({', '.join(e.get('tags') or [])}; {e['state']}): {e['statement'][:220]}\n"
                + (f"  A {e.get('scope', 'unstated')} proof claimed by {e['by']}, {e.get('date') or 'undated'}: {e['summary']}"
                   if e["kind"] == "claim"
                   else f"  How it was solved: {e['summary']}")
                + (f"\n  Notes: {e['notes'][:500]}" if e.get("notes") else ""))
        if used + len(head) > room:
            break
        out.append(head)
        used += len(head)
    if not out:
        return ""
    return ("# Methods from neighbouring problems (unverified; proof claims on erdosproblems.com and notes on solved "
            "problems' pages)\nA claim is not a checked result. Use these for ideas, techniques and analogies.\n\n"
            + "\n\n".join(out) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--show", type=int, help="print the digest one problem would get")
    a = ap.parse_args()
    if a.show is not None:
        print(methods_digest(a.show))
        return 0
    entries = build()
    atomic_write_json(OUT, {"entries": entries}, indent=1)
    print(f"{len(entries)} entries ({sum(e['kind'] == 'claim' for e in entries)} claims, "
          f"{sum(e['kind'] == 'solution' for e in entries)} solution notes) -> {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
