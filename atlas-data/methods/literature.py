"""Literature digest for one open problem: the most relevant works OpenAlex finds, with their abstracts. No model calls.

The engine maps a problem from its own memory, which stops in June 2026, and from the problem's page. The paper that
settles #1207 (Lee-Pohoata-Zhu 2026, the "Minkowski grid") reached the engine only because a forum comment named it.
This puts the recent literature in front of every stage: the campaign writes it to the problem's library
(LITERATURE.md), which the engine reads beside the page digest and the methods library.

    python3 atlas-data/methods/literature.py 1207      # print the digest for one problem
"""
import json, re, sys
from datetime import date, timedelta
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STOP = set("""about above after again against being below between could every first given there these their those
under where which while whose would integer integers number numbers prove proved true false exists exist large largest
small smallest least sufficiently constant function infinitely finite finitely always never other such then that this
with from have does many most some what when into only also must each than them they show maximal minimal possible
""".split())


def query_for(statement: str, tags: list[str], k: int = 9) -> str:
    """Distinctive words of the statement, in order, plus the tags: what a paper on the problem would contain."""
    t = re.sub(r"\$[^$]*\$|\\\[.*?\\\]|\\[a-zA-Z]+|\{|\}", " ", statement or "", flags=re.S)
    seen, out = set(), []
    for w in re.findall(r"[A-Za-z][a-z]{3,}", t):
        lw = w.lower()
        if lw in STOP or lw in seen:
            continue
        seen.add(lw)
        out.append(lw)
    return " ".join(out[:k] + [x for x in tags if x.lower() not in seen][:2])


def literature_digest(statement: str, tags: list[str], search=None, k: int = 8, room: int = 6000) -> str:
    if search is None:
        sys.path.insert(0, str(ROOT))
        import library as L

        def search(q):
            return L.search(q, date.today() + timedelta(days=1), per_page=k + 4)
    q = query_for(statement, tags)
    if not q:
        return ""
    try:
        works = search(q) or []
    except Exception as e:                               # noqa: BLE001 - the digest is context, never a reason to stop
        return f"# Literature (OpenAlex)\nThe search for \"{q}\" failed: {type(e).__name__}.\n"
    sys.path.insert(0, str(ROOT))
    import library as L
    out, used = [], 0
    for w in works[:k]:
        title = " ".join(str(w.get("title") or w.get("display_name") or "").split())
        if not title:
            continue
        year = str(w.get("publication_year") or (w.get("publication_date") or "")[:4])
        authors = ", ".join(a.get("author", {}).get("display_name", "") for a in (w.get("authorships") or [])[:3])
        ab = " ".join(L.abstract_of(w).split())[:700]
        item = f"- {title} ({year}{'; ' + authors if authors else ''})" + (f"\n  {ab}" if ab else "")
        if used + len(item) > room:
            break
        out.append(item)
        used += len(item)
    if not out:
        return ""
    return (f"# Literature (OpenAlex, searched {date.today()} for \"{q}\"; unverified, read critically)\n"
            "Recent work may postdate your knowledge. Check whether any of it already settles or advances the problem.\n\n"
            + "\n".join(out) + "\n")


def main() -> int:
    n = sys.argv[1]
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    p = ranks[n]
    print(literature_digest(p.get("statement") or "", p.get("tags") or []))
    return 0


if __name__ == "__main__":
    sys.exit(main())
