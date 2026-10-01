"""A dated literature library for one problem: search, choose, read and summarise the papers that existed BEFORE a
cutoff, so that discovery and planning can stand on the published methods (`harness.py --library DIR`).

Why. OpenAI's Navier–Stokes agents read "a cached version of the internet" (2026-09-08), and the route they and
Buckmaster–Alpöge extended was a published programme (Córdoba–Martínez-Zoroa's forced blowup). Every idea stage here
runs with no tools: discovery and plans see a literature memo written from the model's memory, at medium effort, in
under 600 words. A library is the cheapest way to hand a run the literature itself.

Why DATED. On the time-split benchmark the resolution is on the web, so a library is only measurable if it holds
nothing published on or after the item's resolution. `--cutoff` is exclusive and applies to the OpenAlex
publication date; arXiv full texts are always fetched as version 1, never a later version that could cite the
resolution; and `--exclude` drops any document whose title, abstract or text matches (the builder adds the problem's
own number patterns for a benchmark item, so its identity does not reach a masked run). The cutoff, every query,
every candidate and every document's hash are recorded in manifest.json.

    python3 library.py build --statement-file S.md --cutoff 2026-03-27 --out library/timesplit/152 \\
        --exclude 'erdosproblems\\.com/152\\b' --exclude 'Problem\\s*#?\\s*152\\b'

Searching is OpenAlex (free; it indexes arXiv preprints by their posting date). The arXiv export API rate-limits this
machine (HTTP 429). Model calls: one for queries, one to choose papers, one digest per paper; about $1-2 a library,
recorded in the manifest. Nothing here is a verified fact: the digests say what papers claim."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
UA = "erdos-harness-library/0.1 (research use)"
OPENALEX = "https://api.openalex.org/works"
FIELDS = "id,title,publication_date,type,ids,abstract_inverted_index,open_access,best_oa_location,primary_location,cited_by_count"

QUERIES_PROMPT = """You are a research librarian. Propose search queries for finding the published literature most useful
for attacking the problem below: papers about its objects, the classical results about them, partial results on this
or closely related questions, and techniques likely to apply. Do not guess the answer, and do not search for a
solution of this exact problem.

PROBLEM:
{statement}

Give exactly {k} queries, one per line, each 2 to 6 words, plain keywords (no quotes, no boolean operators), and
nothing else."""

CHOOSE_PROMPT = """You are choosing which papers a mathematician should read before attacking the problem below. Prefer
papers whose results or methods could be ingredients of a proof, partial results on the same or a closely related
question, and surveys of the area. Skip papers that merely share words with the problem. Prefer papers marked
[text]: only their contents can be read; a paper marked [title only] can be cited but not summarised.

PROBLEM:
{statement}

CANDIDATES:
{candidates}

Reply with exactly one ```json block: {{"chosen": ["<id>", ...]}} listing at most {k} ids, most useful first."""

DIGEST_PROMPT = """Summarise, for a mathematician about to attack the problem below, what in this paper could help. Quote
the exact statements of the theorems, lemmas, constructions and constants that could be ingredients, say what method
proves each one, and list the open questions the paper states that are close to the problem. Say plainly when the
paper is not relevant. Use ONLY the text below, never your memory of the paper or of later work: this library must
hold only what was published before a cutoff date. Do not speculate about the problem's answer. At most {words} words.

PROBLEM:
{statement}

PAPER: {title} ({when}{venue})

{text}"""


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def get_json(url: str, tries: int = 4) -> dict:
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.loads(r.read().decode("utf-8", "replace"))
        except Exception:                          # noqa: BLE001 - network: back off and retry
            if k == tries - 1:
                raise
            time.sleep(3 * (k + 1))
    return {}


def abstract_of(work: dict) -> str:
    inv = work.get("abstract_inverted_index") or {}
    if not inv:
        return ""
    pos = sorted((i, w) for w, idx in inv.items() for i in idx)
    return " ".join(w for _, w in pos)


def arxiv_id(work: dict) -> str | None:
    for u in [(work.get("best_oa_location") or {}).get("pdf_url"), (work.get("best_oa_location") or {}).get("landing_page_url"),
              (work.get("open_access") or {}).get("oa_url"), (work.get("primary_location") or {}).get("landing_page_url")]:
        m = re.search(r"arxiv\.org/(?:abs|pdf)/([0-9]{4}\.[0-9]{4,5}|[a-z\-]+(?:\.[A-Z]{2})?/[0-9]{7})", u or "")
        if m:
            return m.group(1)
    return None


def search(query: str, cutoff: date, per_page: int = 15) -> list[dict]:
    last = (cutoff - timedelta(days=1)).isoformat()
    url = (f"{OPENALEX}?search={urllib.parse.quote(query)}&filter=to_publication_date:{last}"
           f"&per-page={per_page}&select={FIELDS}")
    return get_json(url).get("results") or []


def excluded(text: str, patterns: list[str]) -> str | None:
    for p in patterns:
        if re.search(p, text or "", re.I):
            return p
    return None


def fetch_text(work: dict, room: int = 120000) -> tuple[str, str]:
    """(text, source). arXiv papers are fetched as VERSION 1 only: a later version may postdate the cutoff and cite
    the resolution. Other open-access PDFs are the published version, dated by its publication date."""
    aid = arxiv_id(work)
    urls = [f"https://arxiv.org/pdf/{aid}v1"] if aid else []
    pdf = (work.get("best_oa_location") or {}).get("pdf_url")
    if pdf and not aid:
        urls.append(pdf)
    for url in urls:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=90) as r:
                data = r.read(25_000_000)
            if not data.startswith(b"%PDF"):
                continue
            with tempfile.TemporaryDirectory() as tmp:
                p = Path(tmp) / "paper.pdf"
                p.write_bytes(data)
                out = subprocess.run(["pdftotext", "-layout", str(p), "-"], capture_output=True, text=True, timeout=120)
            text = re.sub(r"[ \t]+", " ", out.stdout)
            if len(text) > 2000:
                return text[:room], url
        except Exception:                          # noqa: BLE001 - a paper without full text keeps its abstract
            continue
        time.sleep(3)
    return "", ""


def llm(model: str):
    """Text-only calls, no tools, nothing masked: the papers' named results (Erdős–Turán, ...) are the point."""
    sys.path.insert(0, str(ROOT))
    import harness as H
    backend = H.ClaudeCliBackend(model, 1800, 2.0)

    def call(purpose: str, prompt: str, effort: str, budget: float) -> tuple[str, float]:
        before = backend.total_cost_usd
        text = backend.complete(purpose, prompt, effort_override=effort, budget_override=budget)
        return text, round(backend.total_cost_usd - before, 4)
    return call


def ambiguous_date(work: dict, cutoff: date) -> str | None:
    """Why a work's date cannot be trusted against the cutoff, or None. OpenAlex writes January 1 when only the year
    is known, so a "2026-01-01" work may appear months after a March cutoff; an arXiv id carries the month version 1
    was posted, which must fall strictly before the cutoff's month."""
    when = work.get("publication_date") or ""
    if when.endswith("-01-01") and int(when[:4]) >= cutoff.year:
        return f"placeholder date {when}"
    aid = arxiv_id(work) or ""
    m = re.match(r"([0-9]{2})([0-9]{2})\.", aid)
    if m and (2000 + int(m.group(1)), int(m.group(2))) >= (cutoff.year, cutoff.month):
        return f"arXiv {aid} posted in or after the cutoff month"
    return None


def build(args) -> int:
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "papers").mkdir(exist_ok=True)
    statement = Path(args.statement_file).read_text().strip() if args.statement_file else args.statement
    cutoff = date.fromisoformat(args.cutoff)
    excludes = list(args.exclude or [])
    call = llm(args.model)
    cost = 0.0
    manifest = {"built": now(), "cutoff_exclusive": cutoff.isoformat(), "excludes": excludes, "model": args.model,
                "source": "OpenAlex search; arXiv full text as version 1 only", "statement_sha": hashlib.sha256(statement.encode()).hexdigest()[:16]}
    text, c = call("library-queries", QUERIES_PROMPT.format(statement=statement, k=args.queries), "low", 0.3)
    cost += c
    queries = [re.sub(r"^[\s\-*\d.)]+", "", l).strip().strip('"') for l in text.splitlines()]
    queries = [q for q in queries if 2 <= len(q.split()) <= 8][: args.queries]
    manifest["queries"] = queries
    pool: dict[str, dict] = {}
    dropped = []
    for q in queries:
        for w in search(q, cutoff):
            wid = w["id"].rsplit("/", 1)[-1]
            if wid in pool:
                continue
            when = w.get("publication_date") or ""
            if not when or date.fromisoformat(when) >= cutoff:
                dropped.append({"id": wid, "why": f"dated {when}"})
                continue
            vague = ambiguous_date(w, cutoff)
            if vague:
                dropped.append({"id": wid, "why": vague})
                continue
            hit = excluded((w.get("title") or "") + " " + abstract_of(w), excludes)
            if hit:
                dropped.append({"id": wid, "why": f"matches {hit}"})
                continue
            pool[wid] = w
        time.sleep(1)
    manifest["candidates"], manifest["dropped"] = len(pool), dropped
    def has_text(w):
        return bool(arxiv_id(w) or (w.get("best_oa_location") or {}).get("pdf_url") or len(abstract_of(w)) > 200)
    ranked = sorted(pool.items(), key=lambda kv: (not has_text(kv[1]), -(kv[1].get("cited_by_count") or 0)))
    listing = "\n".join(f"[{wid}] {'[text]' if has_text(w) else '[title only]'} {w.get('title')} "
                        f"({(w.get('publication_date') or '')[:4]}; cited {w.get('cited_by_count')}): "
                        f"{abstract_of(w)[:450]}" for wid, w in ranked[:80])
    text, c = call("library-choose", CHOOSE_PROMPT.format(statement=statement, candidates=listing or "(none)", k=args.papers),
                   "medium", 0.6)
    cost += c
    try:
        chosen = json.loads(re.findall(r"```json\s*(\{.*?\})\s*```", text, re.S)[-1]).get("chosen") or []
    except (IndexError, ValueError):
        chosen = []
    chosen = [str(i).strip("[] ") for i in chosen if str(i).strip("[] ") in pool][: args.papers]
    docs, digests = [], []
    for wid in chosen:
        w = pool[wid]
        full, src = fetch_text(w)
        hit = excluded(full, excludes) if full else None
        if hit:
            dropped.append({"id": wid, "why": f"full text matches {hit}"})
            full, src = "", ""
        abstract = abstract_of(w)
        body = full or (("ABSTRACT ONLY: " + abstract) if abstract else "")
        (out / "papers" / f"{wid}.txt").write_text(body)
        when = w.get("publication_date") or ""
        if len(body) < 300:
            # nothing to read: a digest would be the model's memory, which no cutoff can date
            dtext = "(No text or abstract was available, so this paper is cited, not summarised.)"
        else:
            dtext, c = call("library-digest", DIGEST_PROMPT.format(statement=statement, title=w.get("title"), when=when,
                                                                   venue=f"; arXiv {arxiv_id(w)}" if arxiv_id(w) else "",
                                                                   words=args.words, text=body[:100000]), "medium", 0.8)
            cost += c
        digests.append(f"## {w.get('title')} ({when[:4]})\n"
                       f"{'arXiv ' + arxiv_id(w) + ' (version 1)' if arxiv_id(w) else (w.get('ids') or {}).get('doi') or wid}"
                       f"; full text: {'yes' if full else 'abstract only'}\n\n{dtext.strip()}\n")
        docs.append({"id": wid, "title": w.get("title"), "date": when, "arxiv": arxiv_id(w), "doi": (w.get("ids") or {}).get("doi"),
                     "full_text": bool(full), "text_source": src, "sha256": hashlib.sha256(body.encode()).hexdigest()[:16],
                     "chars": len(body)})
        time.sleep(1)
    manifest.update({"chosen": docs, "dropped": dropped, "cost_usd": round(cost, 4)})
    head = (f"# Literature library (papers dated before {cutoff.isoformat()}; {len(docs)} paper(s))\n\n"
            "Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, "
            "and a paper's claim is not a Lean fact.\n\n")
    (out / "DIGEST.md").write_text(head + "\n".join(digests))
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1, ensure_ascii=False))
    print(json.dumps({"out": str(out), "papers": len(docs), "full_text": sum(d["full_text"] for d in docs),
                      "candidates": len(pool), "cost_usd": round(cost, 4)}, indent=1))
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--statement", default="")
    b.add_argument("--statement-file", default=None)
    b.add_argument("--cutoff", required=True, help="exclusive: only works published BEFORE this date (YYYY-MM-DD)")
    b.add_argument("--out", required=True)
    b.add_argument("--exclude", action="append", help="regex; a document matching it is dropped (repeatable)")
    b.add_argument("--queries", type=int, default=8)
    b.add_argument("--papers", type=int, default=6)
    b.add_argument("--words", type=int, default=500)
    b.add_argument("--model", default="claude-opus-5-5")
    args = ap.parse_args(argv)
    return build(args)


if __name__ == "__main__":
    sys.exit(main())
