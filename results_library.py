"""A cross-problem library of results, so one run can build on another's. No model calls.

openai/math's README says some of its results "build upon earlier results produced by the models", and its trace for
Erdős #3 takes Part I's theorem as Part II's lemma. Here every run started from its own problem's blackboard alone.
The library holds two kinds of entry, each labelled with how far it can be trusted:

- `harness`: claims our own engine runs on CATALOGUE problems got through validation (`validated-new`, `valid-routine`,
  `valid-known`). They passed model referees, an adversary and novelty judges; none is human-reviewed. Benchmark runs
  (synthetic ids) are never read, so no dev or test item's solution can leak into another run.
- `openai/math`: the families of the openai/math release (2026-10-06, Apache-2.0), indexed from its manuscript map:
  family title and description, manuscript titles, links, and whether a Lean formalization exists. Unverified by us;
  the release itself says unformalized results "could have issues".

`select()` ranks entries for a problem by term overlap (TF-IDF), always putting the problem's own harness entries
first, and `render()` turns them into the labelled block an engine run reads. A benchmark run never loads the library:
the release postdates every benchmark cutoff, and it resolves several catalogue problems outright.

    python3 results_library.py --build                     # refresh knowledge/results-library.jsonl
    python3 results_library.py --problem 873 --k 8         # show what a run on #873 would see
"""
from __future__ import annotations

import argparse, collections, json, math, re, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LIBRARY = ROOT / "knowledge" / "results-library.jsonl"
OPENAI_INDEX = ROOT / "knowledge" / "external" / "openai-math" / "families.json"
VALID = ("validated-new", "valid-routine", "valid-known")
# Term overlap needed to show another problem's entry. Real matches scored 0.32-0.47 (#138 with van der Waerden, #3 with
# Erdős-Turán, #89 with distinct distances); unrelated ones reached 0.20 (a harness entry on #20). Noise costs a model
# its attention and can mislead it.
MIN_OVERLAP = 0.2
STOP = set("""the a an of and or to in for with on by is are be that this every each any all some there exists exist such
as at from its it which we let if then than not no has have most least one two first number numbers set sets proves
prove resolves resolving conjecture problem question show shows gives fixed large sufficiently positive integer
integers real constant absolute their they them these those into over under where when while also only both either""".split())


def _tokens(s: str) -> list[str]:
    s = re.sub(r"\$`?|`?\$|\\[a-zA-Z]+|[{}^_]", " ", str(s or "").lower())
    return [w for w in re.findall(r"[a-zőöü][a-zőöü\-]{2,}", s) if w not in STOP]


def time_split_held_out(root: Path = ROOT) -> set[int]:
    """Catalogue numbers of time-split dev and test items: their results never enter the library, even from a run under
    the true number, because anything learned from them would carry their solutions into later evaluations."""
    try:
        items = json.loads((root / "benchmarks" / "timesplit" / "pool.json").read_text())
    except (OSError, ValueError):
        return set()
    items = items.get("items", items) if isinstance(items, dict) else items
    return {int(i["problem"]) for i in items if str(i.get("split")) in ("dev", "test") and str(i.get("problem", "")).isdigit()}


def harness_entries(root: Path = ROOT) -> list[dict]:
    """Validated claims from engine runs on catalogue problems. Benchmark runs (aliases) are skipped."""
    sys.path.insert(0, str(root))
    import atlas_ids
    held_out = time_split_held_out(root)
    out = []
    for ej_path in sorted((root / "runs").glob("*/engine/engine.json")):
        run = ej_path.parent.parent
        m = re.search(r"erdos(\d+)$", run.name)
        if not m or not (1 <= int(m.group(1)) <= 1217):
            continue                                     # synthetic ids: benchmark aliases, never read
        if int(m.group(1)) in atlas_ids.benchmark_aliases(root) or int(m.group(1)) in held_out:
            continue
        try:
            ej = json.loads(ej_path.read_text())
        except (OSError, ValueError):
            continue
        for c in ej.get("ledger") or []:
            v = c.get("validation") or {}
            if v.get("status") not in VALID or c.get("status") not in ("PROVED", "REFUTED"):
                continue
            nov = v.get("novelty") or {}
            out.append({"source": "harness", "problem": int(m.group(1)), "run": run.name,
                        "claim": f"{c.get('session')}/{c.get('id')}", "status": v.get("status"),
                        "significance": nov.get("significance"), "kind": c.get("status"),
                        "statement": " ".join(str(c.get("statement") or "").split())[:1500],
                        "trust": "passed model referee, adversary and novelty judges; not human-reviewed"})
    return out


DIGESTS = ROOT / "knowledge" / "external" / "openai-math" / "digests"
_THM = re.compile(r"\\begin\{(theorem|proposition|corollary|conjecture|maintheorem|mainthm)\*?\}(.*?)\\end\{\1\*?\}", re.S)
_ABS = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.S)
_SEC = re.compile(r"\\(?:sub)?section\*?\{([^}]*)\}")
_HOW = re.compile(r"(?i)\b(overview|strategy|outline|ideas?|approach|sketch|methods?|structure of the proof|plan of the proof|"
                  r"proof plan|roadmap|road map|heuristics?)\b")


def _tex_clean(s: str) -> str:
    s = re.sub(r"(?m)(?<!\\)%.*$", "", s)
    s = re.sub(r"\\(label|cite|ref|eqref)\{[^}]*\}", "", s)
    return " ".join(s.split())


def tex_digest(folder: Path, room: int = 3500) -> str:
    """How a manuscript proves what it proves, from its LaTeX: the abstract, the main statements, and the proof-overview
    section when there is one. No model call: the authors' own words, clipped."""
    texs = sorted(folder.rglob("*.tex"), key=lambda f: (f.name != "main.tex", "figure" in str(f), str(f)))
    src = "\n".join(f.read_text(errors="replace") for f in texs)
    parts = []
    a = _ABS.search(src)
    if a:
        parts.append("ABSTRACT: " + _tex_clean(a.group(1))[:1200])
    thms = [_tex_clean(m.group(2))[:500] for m in _THM.finditer(src)][:3]
    if thms:
        parts.append("MAIN STATEMENTS: " + " | ".join(thms))
    secs = list(_SEC.finditer(src))
    for i, m in enumerate(secs):
        if _HOW.search(m.group(1)):
            end = secs[i + 1].start() if i + 1 < len(secs) else len(src)
            parts.append(f"{m.group(1).upper()}: " + _tex_clean(src[m.end():end])[:1800])
            break
    return "\n".join(parts)[:room]


def build_digests(release: Path, mapping: Path | None = None) -> int:
    """A method digest for every family whose manuscripts are checked out of the openai/math release (a sparse clone),
    written to knowledge/external/openai-math/digests/<family>.md with the release's attribution."""
    import collections as _c
    blocks = {b[2:5]: b for b in re.split(r"(?=\*\*\d{3}\. )", (release / "CONTENTS.md").read_text()) if re.match(r"\*\*\d{3}\. ", b)}
    DIGESTS.mkdir(parents=True, exist_ok=True)
    n = 0
    for fam, b in blocks.items():
        dirs = sorted(set(re.findall(r"\]\((preprints/[^/)]+)/", b)))
        texts = [tex_digest(release / d) for d in dirs if (release / d).exists() and any((release / d).rglob("*.tex"))]
        texts = [x for x in texts if x]
        if not texts:
            continue
        (DIGESTS / f"{fam}.md").write_text(
            f"<!-- openai/math family {fam}: the authors' abstract, main statements and proof overview, from the LaTeX "
            f"sources of the OpenAI Math Release (Apache-2.0, https://github.com/openai/math). Unverified by us. -->\n"
            + "\n\n".join(texts))
        n += 1
    return n


def openai_entries(path: Path = OPENAI_INDEX) -> list[dict]:
    if not path.exists():
        return []
    d = json.loads(path.read_text())
    out = []
    for fam in d.get("families") or []:
        dg = DIGESTS / f"{fam['family']}.md"
        out.append({"source": "openai/math", "family": fam["family"], "title": fam["title"],
                    "statement": (fam.get("description") or "")[:1500],
                    "manuscripts": [m.get("title") for m in fam.get("manuscripts") or []][:6],
                    "url": fam.get("url"), "lean": bool(fam.get("lean")), "erdos": fam.get("erdos") or [],
                    "digest": re.sub(r"(?s)^<!--.*?-->\s*", "", dg.read_text())[:3500] if dg.exists() else "",
                    "trust": ("Lean-formalized in the release, not checked by us" if fam.get("lean")
                              else "unformalized; the release says such results could have issues")})
    return out


def build(root: Path = ROOT) -> list[dict]:
    entries = harness_entries(root) + openai_entries(root / "knowledge" / "external" / "openai-math" / "families.json")
    LIBRARY.parent.mkdir(parents=True, exist_ok=True)
    LIBRARY.write_text("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries))
    return entries


def load(root: Path = ROOT) -> list[dict]:
    if not LIBRARY.exists():
        return build(root)
    return [json.loads(l) for l in LIBRARY.read_text().splitlines() if l.strip()]


def select(statement: str, tags: list[str] | None, entries: list[dict], k: int = 8, problem: int | None = None) -> list[dict]:
    """The `k` entries most relevant to a problem: its own harness results first, then by TF-IDF overlap. An
    openai/math family mapped to this very problem is included too: it is the most important thing to know."""
    own = sorted((e for e in entries if e.get("source") == "harness" and problem is not None and e.get("problem") == problem),
                 key=lambda e: (e.get("status") != "validated-new", -(e.get("significance") or 0)))[: max(1, k - 3)]
    mapped = [e for e in entries if e.get("source") == "openai/math" and problem is not None and problem in (e.get("erdos") or [])]
    rest = [e for e in entries if e not in own and e not in mapped
            and not (e.get("source") == "harness" and e.get("problem") == problem)]
    docs = [_tokens(f"{e.get('title', '')} {e.get('statement', '')} {' '.join(e.get('manuscripts') or [])}") for e in rest]
    q = _tokens(statement + " " + " ".join(tags or []))
    df = collections.Counter(w for d in docs for w in set(d))
    n = len(docs) + 1

    def vec(ws):
        c = collections.Counter(ws)
        v = {w: (1 + math.log(x)) * math.log(n / (1 + df[w])) for w, x in c.items()}
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {w: x / norm for w, x in v.items()}
    qv = vec(q)
    scored = sorted(((sum(qv.get(w, 0.0) * x for w, x in vec(d).items()), i) for i, d in enumerate(docs)), reverse=True)
    picked = [rest[i] for s, i in scored if s > MIN_OVERLAP][: max(0, k - len(own) - len(mapped))]
    return own + mapped + picked


def render(entries: list[dict]) -> str:
    if not entries:
        return ""
    lines = ["RESULTS LIBRARY: results from other work that may be usable here. Each line says how far it can be trusted. "
             "Use a result as a tool, cite it by its label, and never treat an unverified one as proved."]
    shown = 0
    for e in entries:
        if e.get("source") == "harness":
            lines.append(f"- [harness #{e['problem']} {e['claim']}, {e['status']}"
                         f"{', significance ' + str(e['significance']) if e.get('significance') is not None else ''}; "
                         f"{e['trust']}] {e['statement']}")
        else:
            lines.append(f"- [openai/math family {e['family']}, {e['trust']}] {e['title']} {e['statement']}"
                         + (f" ({e['url']})" if e.get("url") else ""))
            if e.get("digest") and shown < 2:              # how it was proved, for the two most relevant families
                lines.append("  HOW IT WAS PROVED (the authors' abstract, statements and overview):\n  "
                             + e["digest"].replace("\n", "\n  "))
                shown += 1
    return "\n".join(lines)


def index_openai(contents_md: Path, out: Path = OPENAI_INDEX, mapping: Path | None = None, commit: str | None = None) -> int:
    """Index the release's manuscript map (CONTENTS.md) as compact family records, with the Erdős mapping if given."""
    t = contents_md.read_text()
    erdos = collections.defaultdict(list)
    if mapping and mapping.exists():
        m = json.loads(mapping.read_text())
        for kind in ("claimed_resolved", "claimed_partial"):
            for r in m.get(kind) or []:
                erdos[r["family"]].append(int(r["problem"]))
    fams = []
    for b in re.split(r"(?=\*\*\d{3}\. )", t):
        h = re.match(r"\*\*(\d{3})\. (.+?)\*\*(.*?)</td>(.*)", b, re.S)
        if not h:
            continue
        desc = " ".join(re.sub(r"<[^>]+>", "", h.group(3)).split())
        manus = [{"title": " ".join(x.split())} for x in re.findall(r"\[([^\]]+)\]\(preprints/", h.group(4))]
        fams.append({"family": h.group(1), "title": re.sub(r"<[^>]+>", "", h.group(2)).strip(),
                     "description": re.sub(r"\s*\(\[Lean\]\([^)]*\)\)\s*$", "", desc)[:1500],
                     "manuscripts": manus, "lean": "lean/docs/" in h.group(3),
                     "url": f"https://github.com/openai/math/blob/main/CONTENTS.md", "erdos": sorted(set(erdos.get(h.group(1), [])))})
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"source": "https://github.com/openai/math", "license": "Apache-2.0",
                               "attribution": "Family titles, descriptions and manuscript titles from openai/math "
                                              "(CONTENTS.md), released 2026-10-06 by OpenAI under the Apache License 2.0.",
                               "commit": commit, "indexed": datetime.now(timezone.utc).strftime("%Y-%m-%d"),
                               "families": fams}, indent=1, ensure_ascii=False))
    return len(fams)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--index-openai", metavar="CONTENTS_MD")
    ap.add_argument("--commit")
    ap.add_argument("--digest-openai", metavar="RELEASE_DIR",
                    help="write method digests from a (sparse) clone of github.com/openai/math")
    ap.add_argument("--problem", type=int)
    ap.add_argument("--k", type=int, default=8)
    a = ap.parse_args()
    if a.index_openai:
        n = index_openai(Path(a.index_openai), mapping=ROOT / "atlas-data" / "openai-math-2026-10-06.json", commit=a.commit)
        print(f"indexed {n} families")
    if a.digest_openai:
        print(f"{build_digests(Path(a.digest_openai))} family digests written")
    if a.build:
        e = build()
        print(f"{len(e)} entries: {sum(1 for x in e if x['source'] == 'harness')} harness, "
              f"{sum(1 for x in e if x['source'] == 'openai/math')} openai/math")
    if a.problem:
        probs = {p["id"]: p for p in json.loads((ROOT / "atlas-data" / "parsed.json").read_text())}
        p = probs[a.problem]
        print(render(select(str(p.get("statement")), p.get("tags"), load(), a.k, a.problem)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
