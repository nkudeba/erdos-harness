#!/usr/bin/env python3
"""Time-split benchmark: Erdős problems resolved after the model's training data, attacked as if still open.

Every earlier benchmark re-derived a problem the model may remember, and the saved-solve pool is used up
(docs/HANDOVER-2026-09-23.md). A problem whose resolution first appeared after the model's knowledge cutoff is,
to the model, an OPEN problem with a known answer. That is the only setting in which "did the harness find a
step nobody told it" has ground truth, so this is the measuring instrument for the self-improvement loop.
README.md next to this file has the protocol, the contamination rules and how a gate should read the numbers.

    python3 benchmarks/timesplit/timesplit.py build     # pool.json from pinned public sources; no model calls
    python3 benchmarks/timesplit/timesplit.py freeze --unprobed   # answer-free Lean statements, compile-checked (free)
    python3 benchmarks/timesplit/timesplit.py probe     # what the model knows about each resolution (~$0.03-0.20 each)
    python3 benchmarks/timesplit/timesplit.py judge     # faithfulness of each kept statement (two model calls each)
    python3 benchmarks/timesplit/timesplit.py status    # the splits, and why each excluded item is out
    python3 benchmarks/timesplit/timesplit.py run --split dev --budget 8 [--detach]
    python3 benchmarks/timesplit/timesplit.py progress --tag <tag>   # dense progress of finished runs (Lean, no model)
    python3 benchmarks/timesplit/timesplit.py score --tag <tag> [--baseline <tag>]
"""
from __future__ import annotations
import argparse, hashlib, json, math, os, re, subprocess, sys, time, urllib.error, urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CACHE, MASKS, PROBES, RESULTS = (HERE / d for d in ("cache", "masks", "probes", "results"))
POOL = HERE / "pool.json"
sys.path.insert(0, str(ROOT / "atlas-data"))
sys.path.insert(0, str(ROOT))

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/128.0 Safari/537.36")          # the site 403s generic fetchers (CLAUDE.md)
SOURCES = {
    "teorth": "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml",
    "wiki": "https://raw.githubusercontent.com/wiki/teorth/erdosproblems/AI-contributions-to-Erd%C5%91s-problems.md",
    "fc_head": "https://api.github.com/repos/google-deepmind/formal-conjectures/commits/main",
    "fc_file": "https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{sha}/FormalConjectures/ErdosProblems/{n}.lean",
    "site": "https://www.erdosproblems.com/{n}",
    "arxiv": "https://export.arxiv.org/api/query?id_list={ids}&max_results={k}",
}
# First day the model cannot have seen. The stated cutoff for Opus 5.5 is June 2026, but a stated cutoff is fuzzy
# (it did not know #90's May 2026 disproof), so for everything BEFORE this date the probe, not the date, decides.
CUTOFFS = {"claude-opus-5-5": "2026-07-01"}
DEFAULT_MODEL, DEFAULT_SINCE = "claude-opus-5-5", "2026-01-01"
RESOLVED = ("proved", "disproved", "solved")
RESOLVE_RE = re.compile(r"\b(solved|resolved|proved|proven|disproved|disproof|answered|settled|counterexample|"
                        r"negative|affirmative|refuted|confirmed)\b", re.I)
AI_RE = re.compile(r"\b(GPT[-\w.]*|ChatGPT|OpenAI|Aristotle|AlphaProof|AlphaEvolve|Aletheia|Gemini|Deep ?Think|Claude|"
                   r"DeepMind|Harmonic|Grok|LLMs?|AI|prover agent|internal model)\b")
KEY_RE = re.compile(r"\[([A-Z][A-Za-z+\-]*\d{2}[a-z]?)\]")
# A sentence that resolves THIS problem, as opposed to background ("Zhao [Zh11] proved it for large n"): only these
# date the resolution. Markdown emphasis is removed first ("has been **disproved**").
STRONG_RE = re.compile(r"\b(?:(?:this|it|the (?:problem|question|conjecture))(?: question| conjecture| problem)?\s+"
                       r"(?:was|has been|is|had been)\s+(?:now\s+|also\s+|since\s+)?(?:solved|resolved|disproved|proved|"
                       r"proven|answered|settled|refuted|confirmed)|(?:solved|resolved|disproved|proved|answered|settled|"
                       r"refuted)\s+(?:this|the (?:problem|question|conjecture))|(?:gave|give|gives|given|giving)\s+an?\s+"
                       r"(?:negative|positive|affirmative|complete|full)\s+(?:answer|solution|resolution)|"
                       r"(?:answer|solution) was given|in the (?:negative|affirmative)|answered (?:negatively|affirmatively))", re.I)
# "trivially true", "has a trivial solution", "is trivial" -- not "the trivial bound" or "non-trivial"
TRIVIAL_RE = re.compile(r"(?<![-\w])(?:trivially (?:true|false|answered|satisfied|solved|resolved|holds)|"
                        r"(?:has|with|admits) a trivial (?:solution|answer|counterexample|construction)|is trivial\b)", re.I)
ARXIV_RE = re.compile(r"(?:arxiv\.org/(?:abs|pdf|html)/|arXiv:\s*)(\d{4}\.\d{4,5})", re.I)


# ---------------------------------------------------------------- fetching (cached, polite) --------------------------

def fetch(url: str, dest: Path, refresh: bool = False, pause: float = 0.0, tries: int = 4) -> str:
    """GET with the browser UA, cached at `dest`. A 404 is cached as an empty file: a miss is an answer.
    Transient failures (timeouts, 429/5xx) are retried with backoff and never cached, so a rerun resumes."""
    if dest.exists() and not refresh:
        return dest.read_text(errors="replace")
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    for k in range(tries):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                text = r.read().decode(errors="replace")
            break
        except urllib.error.HTTPError as e:
            if e.code == 404:
                text = ""
                break
            if e.code not in (429, 500, 502, 503, 504) or k == tries - 1:
                raise
        except (urllib.error.URLError, TimeoutError, OSError):
            if k == tries - 1:
                raise
        finally:
            time.sleep(pause)
        time.sleep(5 * (k + 1))
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(text)
    return text


def text_of(page: str) -> str:
    from fetch_forum import text_of as t   # the Atlas's own HTML-to-text, so both read pages the same way
    return t(page)


# ---------------------------------------------------------------- dates -----------------------------------------------

def parse_date(cell: str | None) -> str | None:
    """'25 Apr, 2026' / '20 May 2026' / '21 May-9 Jun, 2026' -> ISO date of the FIRST day named."""
    if not cell:
        return None
    year = re.findall(r"\b(20\d{2}|19\d{2})\b", cell)
    m = re.search(r"\b(\d{1,2})\s+([A-Za-z]{3,9})\b", cell)
    if not (year and m):
        return None
    for fmt in ("%d %b %Y", "%d %B %Y"):
        try:
            return datetime.strptime(f"{m.group(1)} {m.group(2)} {year[-1]}", fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return None


def key_year(key: str) -> int | None:
    m = re.search(r"(\d{2})[a-z]?$", key)
    if not m:
        return None
    yy = int(m.group(1))
    return 1900 + yy if yy >= 40 else 2000 + yy


# ---------------------------------------------------------------- source parsers --------------------------------------

STATUS_LINE = re.compile(r"^(?:[A-Z][A-Z ()\-]*|This (?:has been|is|was) .*|-?\s*\$[\d,]+.*)$")


def parse_site(page: str, n: int) -> dict:
    """Statement, resolution notes and last-edited date from an erdosproblems.com page."""
    t = text_of(page) if page else ""
    m = re.search(rf"(?m)^#{n}:.*$", t)
    if not m:
        return {}
    start = t.rfind("Random Open", 0, m.start())
    head = t[start + len("Random Open"): m.start()] if start >= 0 else t[: m.start()]
    stmt = [l.strip() for l in head.splitlines() if l.strip() and not STATUS_LINE.match(l.strip())]
    tail = t[m.end():]
    cut = [i for i in (tail.find("Proof expositions"), tail.find("Additional thanks to")) if i >= 0]
    edited = re.search(r"This page was last edited (\d{1,2} \w+ \d{4})", t)
    return {"statement": "\n".join(stmt), "notes": tail[: min(cut) if cut else len(tail)].strip(),
            "edited": parse_date(edited.group(1)) if edited else None}


def parse_wiki(md: str) -> dict[str, list[dict]]:
    """Every row of the teorth AI-contributions wiki, per problem, read through each table's own header."""
    rows: dict[str, list[dict]] = {}
    section = header = None
    for line in md.splitlines():
        h = re.match(r"^###\s+(\d\([a-z]\))", line)
        if h:
            section, header = h.group(1), None
            continue
        if section is None or not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if header is None:
            header = [c.lower() for c in cells]
            continue
        m = re.match(r"\[\[(\d+)\]\]", cells[0])
        if not m:
            continue
        rec = dict(zip(header, cells))
        rows.setdefault(m.group(1), []).append({
            "section": section, "systems": rec.get("ai systems"), "humans": rec.get("humans"),
            "date": parse_date(rec.get("date")), "outcome": rec.get("outcome"), "literature": rec.get("literature")})
    return rows


OPENERS, CLOSERS = "([{⟨", ")]}⟩"


def scan_to(text: str, i: int, stop: str) -> int:
    """Index of the first `stop` at bracket depth 0 from `i`, skipping strings and comments; -1 if none."""
    depth, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j < 0 else j + 2
            continue
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        if depth == 0 and text.startswith(stop, i) and not (stop == ":" and text.startswith(":=", i)):
            return i
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        i += 1
    return -1


def signature_end(rest: str) -> int:
    """The ':=' that ends a theorem signature. A statement may bind inside itself (#38: `let α := ...`), and cutting
    there truncated the statement, so a ':=' that closes a `let`/`have` binder is skipped."""
    i = 0
    while True:
        j = scan_to(rest, i, ":=")
        if j < 0 or not re.search(r"\b(?:let|have|letI|haveI)\s+[^\s:=,()]+(?:\s*:\s*[^:=]+?)?\s*$", rest[:j]):
            return j
        i = j + 2


def strip_comments(text: str) -> str:
    """Docstrings, block and line comments out: a formal-conjectures docstring states the resolution."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"(?m)[ \t]*--.*$", "", text)


def neutralize(text: str, n: int) -> str:
    """No identifier may carry the true number: `Erdos884Prop` would name the problem to every prompt."""
    text = strip_comments(text)
    text = re.sub(rf"\bErdos{n}\.", "", text)
    return re.sub(rf"\b[Ee]rdos_?{n}_?(\w*)", lambda m: "TS" + (m.group(1) or "Main"), text)


def parse_refs(block: str) -> dict:
    refs = {}
    for m in re.finditer(r"\[([A-Za-z][\w+\-]*?\d{2}[a-z]?)\](.*?)(?=\n\s*[-*]\s*\[|\Z)", block, re.S):
        body = m.group(2)
        years = re.findall(r"\b(19\d{2}|20\d{2})\b", body)
        refs[m.group(1)] = {"arxiv": sorted(set(ARXIV_RE.findall(body))), "year": int(years[-1]) if years else None,
                            "text": " ".join(body.split())[:240]}
    return refs


DECL_HEAD = re.compile(r"(?m)^(?:@\[[^\n]*\]\s*\n)?(?:(?:noncomputable|private|protected|scoped)\s+)*"
                       r"(def|abbrev|structure|inductive|class|instance)\s+([^\s:({\[]*)")
BLOCK_END = re.compile(r"(?m)^(?=(?:@\[|/--|/-|theorem\b|lemma\b|example\b|def\b|abbrev\b|noncomputable\b|private\b|"
                       r"protected\b|instance\b|structure\b|inductive\b|class\b|namespace\b|end\b|section\b|open\b|"
                       r"variable\b|notation\b|local\b|scoped\b|set_option\b|attribute\b|#))")


def parse_fc(src: str, n: int) -> dict:
    """The main theorem of a formal-conjectures Erdős file, answer-free.

    Returns the proposition P (the question's YES reading), its truth where the file records it, the file-local
    definitions P depends on (transitively), the `open`s it needs, and the references. Every docstring and
    comment is stripped and every identifier carrying the problem number is renamed: a docstring saying "this
    was disproved" must never reach a benchmark prompt."""
    if not src.strip():
        return {"error": "no formal-conjectures file"}
    mod = re.search(r"/-!(.*?)-/", src, re.S)
    out: dict = {"refs": parse_refs(mod.group(1) if mod else "")}
    m = re.search(rf"(?m)^theorem\s+erdos_{n}(?:_statement)?(?=[\s:({{\[])", src)     # #330 names it erdos_330_statement
    if not m:
        parts = sorted(set(re.findall(rf"(?m)^theorem\s+erdos_{n}\.(\S+)", src)))
        return {**out, "error": "no main theorem" + (f" (parts: {', '.join(parts[:6])})" if parts else "")}
    before = src[: m.start()]
    k = before.rfind("/--")
    doc, lead = "", ""
    if k >= 0 and "-/" in before[k:]:
        e = before.index("-/", k)
        between = before[e + 2:]
        if re.fullmatch(r"\s*(?:(?:@\[.*?\]|open\s[^\n]*\bin)\s*)*", between, re.S):
            doc, lead = before[k + 3: e], between
    out["doc"] = " ".join(doc.split())
    cat = re.search(r"category\s+([\w ]+?)\s*(?:,|\])", lead)
    out["category"] = cat.group(1).strip() if cat else None
    inline_opens = [l.strip() for l in lead.splitlines() if re.match(r"\s*open\s.*\bin\s*$", l)]
    rest = src[m.end():]
    j = signature_end(rest)
    if j < 0:
        return {**out, "error": "main theorem has no ':='"}
    sig = rest[:j].strip()
    c = scan_to(sig, 0, ":")
    if c < 0:
        return {**out, "error": "cannot split binders from the statement"}
    # Layout is kept, not collapsed: `let α := v` ends at a newline, and joining the lines made #38 read `v ∃ b ...`.
    binders, typ = sig[:c].strip(), "\n".join(l.rstrip() for l in strip_comments(sig[c + 1:]).strip().splitlines() if l.strip())
    # `letI A := {...}` may sit in front of the answer (#469): the bindings stay, in front of P.
    ans = re.match(r"((?:(?:let|letI|have|haveI)\b[^\n]*\n\s*)*)answer\((True|False|sorry)\)\s*↔\s*", typ)
    rev = re.search(r"\s*↔\s*answer\((True|False|sorry)\)$", typ)
    if ans or rev:
        out["answer"] = {"True": True, "False": False, "sorry": None}[ans.group(2) if ans else rev.group(1)]
        lets = [l.strip() for l in ans.group(1).splitlines() if l.strip()] if ans else []
        prop, out["form"] = ("\n".join(lets + [typ[ans.end():]]) if ans else typ[: rev.start()]), "answer-iff"
    elif "answer(" in typ:
        return {**out, "error": "non-boolean answer (the question asks for a value)"}
    else:
        prop, out["form"] = typ, "assertion"
        out["answer"] = True if out["category"] == "research solved" else None
        inner = re.fullmatch(r"¬\s*\((.*)\)", prop, re.S)
        if inner and scan_to(inner.group(1) + ")", 0, ")") == len(inner.group(1)):
            prop, out["negation_stripped"] = inner.group(1), True     # keep P the YES reading of the question
            out["answer"] = False if out["answer"] else out["answer"]
    decls = []
    for d in DECL_HEAD.finditer(before):
        end = BLOCK_END.search(before, d.end())
        decls.append({"kind": d.group(1), "name": d.group(2).split(".")[-1], "text": before[d.start(): end.start() if end else len(before)]})
    names = {d["name"] for d in decls if d["name"]}
    need, frontier = set(), binders + " " + prop
    while True:
        plain = re.sub(rf"\bErdos{n}\.", "", frontier)          # `Erdos884.foo` is the local `foo`
        # a preceding dot is allowed: `n.IsSumDivisors` is dot notation for the local `Nat.IsSumDivisors` (#469)
        hit = {x for x in names - need if re.search(rf"(?<![\w]){re.escape(x)}(?![\w'])", plain)}
        if not hit:
            break
        need |= hit
        frontier = " ".join(d["text"] for d in decls if d["name"] in hit)
    out["defs"] = [neutralize(d["text"], n).strip() for d in decls if d["name"] in need or d["kind"] == "instance"
                   and any(re.search(rf"\b{re.escape(x)}\b", d["text"]) for x in need)]
    out["variables"] = [l.strip() for l in before.splitlines() if l.startswith("variable")]
    out["opens"] = [l.strip() for l in before.splitlines() if re.match(r"open\s", l) and not l.rstrip().endswith(" in")]
    out["inline_opens"] = inline_opens
    out["binders"], out["prop"] = neutralize(binders, n).strip(), neutralize(prop, n).strip()
    return out


def frozen_statement(fc: dict, alias: int, extra: list[str] | None = None, classical: bool = False) -> str:
    """Library definitions (if any), opens, the definitions P needs, then `theorem erdos_<alias> : P := by sorry`
    -- the harness's frozen form."""
    head = "\n".join((["open scoped Classical"] if classical else []) + fc.get("opens", []) + fc.get("variables", []))
    body = list(extra or []) + ([head] if head else [])
    body += fc.get("defs", [])
    lead = "".join(f"{o}\n" for o in fc.get("inline_opens", []))
    binders = f" {fc['binders']}" if fc.get("binders") else ""
    first, *more = fc["prop"].split("\n")
    prop = "\n".join(["    " + first.strip()] + [l if l.startswith((" ", "\t")) else "    " + l for l in more])   # never column 0
    body.append(f"{lead}theorem erdos_{alias}{binders} :\n{prop} := by\n  sorry")
    return "\n\n".join(body)


# ---------------------------------------------------------------- building the pool -----------------------------------

def resolution_sentences(*texts: str) -> list[str]:
    out = []
    for t in texts:
        for s in re.split(r"(?<=[.!?])\s+|\n+", t or ""):
            if RESOLVE_RE.search(s):
                out.append(" ".join(s.replace("*", "").split())[:400])
    return out


def strong_sentences(sents: list[str]) -> list[str]:
    return [s for s in sents if STRONG_RE.search(s.replace("_", ""))]


def arxiv_dates(ids: list[str], refresh: bool) -> dict[str, str]:
    """v1 submission dates from the arXiv API, cached; a missing id falls back to its YYMM (first of month)."""
    cache = CACHE / "arxiv.json"
    known = json.loads(cache.read_text()) if cache.exists() else {}
    todo = sorted({i for i in ids if i not in known})
    for k in range(0, len(todo), 40):
        batch = todo[k: k + 40]
        try:
            req = urllib.request.Request(SOURCES["arxiv"].format(ids=",".join(batch), k=len(batch)), headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=60) as r:
                xml = r.read().decode(errors="replace")
        except (urllib.error.URLError, TimeoutError, OSError):
            xml = ""
        for e in re.findall(r"<entry>(.*?)</entry>", xml, re.S):
            i = re.search(r"<id>https?://arxiv\.org/abs/(\d{4}\.\d{4,5})", e)
            p = re.search(r"<published>(\d{4}-\d{2}-\d{2})", e)
            if i and p:
                known[i.group(1)] = p.group(1)
        time.sleep(3)                    # arXiv asks for 3 s between API calls
    for i in ids:
        known.setdefault(i, f"20{i[:2]}-{i[2:4]}-01")
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps(known, indent=1, sort_keys=True))
    return known


def split_of(n: str) -> str:
    """dev or train, fixed by the problem number alone, so the assignment survives every rebuild and pool growth."""
    return "dev" if int(hashlib.sha256(f"timesplit:{n}".encode()).hexdigest(), 16) % 2 == 0 else "train"


def classify(item: dict, cutoff: str) -> tuple[str, str | None]:
    """(split, exclude_reason) before and after the probe; an item leaves only for a stated reason."""
    if item.get("exclude_reason"):
        return "excluded", item["exclude_reason"]
    probe, mask = item.get("probe") or {}, item.get("mask") or {}
    if probe.get("verdict") == "recalled":
        return "excluded", "probe: the model recalls the resolution"
    if probe.get("verdict") == "partial-recall":
        return "excluded", "probe: the model knows it was resolved and names a source"
    if mask and not mask.get("ok"):
        return "excluded", "frozen statement does not compile: " + str(mask.get("error") or "")[:200]
    if mask.get("faithful") is False:
        return "excluded", "judge: the frozen statement is not the question answered yes"
    if item["first_public"] >= cutoff:
        return "test", None
    return (split_of(item["problem"]) if probe.get("verdict") else "unprobed"), None


def build(args) -> int:
    import yaml
    CACHE.mkdir(parents=True, exist_ok=True)
    data = yaml.safe_load(fetch(SOURCES["teorth"], CACHE / "teorth-problems.yaml", args.refresh))
    wiki = parse_wiki(fetch(SOURCES["wiki"], CACHE / "ai-wiki.md", args.refresh))
    head = CACHE / "fc-sha.txt"
    if args.refresh or not head.exists():
        head.write_text(json.loads(fetch(SOURCES["fc_head"], CACHE / "fc-head.json", True))["sha"])
    sha = head.read_text().strip()
    parsed = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "parsed.json").read_text())}
    old = {i["problem"]: i for i in json.loads(POOL.read_text())["items"]} if POOL.exists() else {}
    cutoff = CUTOFFS.get(args.model, args.cutoff)
    cands = []
    for p in data:
        inf = p.get("informal_status") or {}
        st, d = str(inf.get("state", "")).lower(), str(inf.get("last_update", ""))
        if st.startswith(RESOLVED) and d >= args.since:
            cands.append((str(p["number"]), st, d, p))
    print(f"{len(cands)} problems resolved on or after {args.since} (teorth data); fetching sources ...", flush=True)
    items, all_ids = [], []
    for n, st, d, p in cands:
        site = parse_site(fetch(SOURCES["site"].format(n=n), CACHE / "site" / f"{n}.html", args.refresh, pause=1.0), int(n))
        fc = parse_fc(fetch(SOURCES["fc_file"].format(sha=sha, n=n), CACHE / "fc" / f"{n}.lean", args.refresh, pause=0.1), int(n))
        sents = resolution_sentences(fc.get("doc", ""), site.get("notes", ""))
        strong = strong_sentences(sents)
        keys = sorted({k for s in strong for k in KEY_RE.findall(s)})
        ids = sorted({i for s in strong for i in ARXIV_RE.findall(s)}
                     | {i for k in keys for i in fc.get("refs", {}).get(k, {}).get("arxiv", [])})
        all_ids += ids
        items.append({"n": n, "state": st, "site_date": d, "p": p, "site": site, "fc": fc, "sents": sents,
                      "strong": strong, "keys": keys, "ids": ids})
    dates = arxiv_dates(sorted(set(all_ids)), args.refresh)
    out = []
    for it in items:
        n, fc, site = it["n"], it["fc"], it["site"]
        ev = [{"date": it["site_date"], "source": "teorth informal_status.last_update (site recorded the resolution)"}]
        ev += [{"date": dates[i], "source": f"arXiv:{i} v1, cited with the resolution"} for i in it["ids"]]
        site_year = int(it["site_date"][:4])
        for s in it["strong"]:                 # "In September 2025, Tao gave a conditional negative answer" (#884)
            for mon, y in re.findall(r"\b(January|February|March|April|May|June|July|August|September|October|"
                                     r"November|December)\s+(19\d{2}|20\d{2})\b", s):
                ev.append({"date": datetime.strptime(f"1 {mon} {y}", "%d %B %Y").strftime("%Y-%m-%d"),
                           "source": f"'{mon} {y}' in a resolution sentence: {s[:120]}"})
            for y in re.findall(r"\b(?:in|since|by|from) (19\d{2}|20\d{2})\b", s):
                if int(y) < site_year:
                    ev.append({"date": f"{y}-12-31", "source": f"'{y}' in a resolution sentence: {s[:120]}"})
        for k in it["keys"]:
            y = (fc.get("refs", {}).get(k) or {}).get("year") or key_year(k)
            if y and y < site_year:
                ev.append({"date": f"{y}-12-31", "source": f"[{k}] ({y}) cited with the resolution: older literature"})
        wrows = wiki.get(n, [])
        for r in wrows:
            if r["date"] and "🟢" in (r["outcome"] or ""):
                ev.append({"date": r["date"], "source": f"AI wiki {r['section']}: {r['systems']} -- {r['outcome']}"})
            lit = re.search(r"\((\d{4})\)", r.get("literature") or "")
            if lit and "🟢" in (r.get("literature") or ""):
                ev.append({"date": f"{lit.group(1)}-12-31", "source": f"AI wiki {r['section']}: literature {r['literature']}"})
        first = min(ev, key=lambda e: e["date"])
        green = [r for r in wrows if "🟢" in (r["outcome"] or "")]
        prov = sorted({"literature" for e in ev if "older literature" in e["source"] or ": literature " in e["source"]}
                      | {"literature" for r in green if r["section"] == "2(a)"}
                      | {"ai" for r in green if r["section"].startswith("1")}
                      | ({"ai"} if any(AI_RE.search(s) for s in it["strong"]) else set()))
        answer, reason = fc.get("answer"), fc.get("error")
        state_answer = {"proved": True, "disproved": False}.get(it["state"].split()[0])
        if not reason and answer is None:
            answer = state_answer
            if answer is None:
                reason = "truth of the formal statement not recorded (formal-conjectures open/sorry, teorth state 'solved')"
        if not reason and state_answer is not None and fc.get("form") == "answer-iff" and answer != state_answer:
            reason = f"sources disagree: formal-conjectures answer({answer}) vs teorth '{it['state']}'"
        stmt = (parsed.get(n) or {}).get("statement") or site.get("statement", "")
        if not reason and not stmt.strip():
            reason = "no statement text"
        if not reason and (ROOT / "knowledge" / "solved" / f"Erdos{n}.lean").exists():
            reason = "already solved by this harness: its proof is in knowledge/solved/, so no run of it is blind"
        if not reason and TRIVIAL_RE.search(" ".join(it["sents"])):
            reason = "the site calls the resolution trivial (no test, as #280 and #1193 were not)"
        item = {"problem": n, "statement_en": stmt, "tags": list(it["p"].get("tags") or []), "answer": answer,
                "answer_source": ("formal-conjectures " + ("answer(...)" if fc.get("form") == "answer-iff" else
                                  f"assertion, category '{fc.get('category')}'")) if fc.get("answer") is not None else f"teorth '{it['state']}'",
                "informal_state": it["state"], "site_resolved": it["site_date"], "first_public": first["date"],
                "first_public_source": first["source"], "evidence": sorted(ev, key=lambda e: e["date"]),
                "provenance": prov or ["human"], "ai_wiki": wrows, "resolution_sentences": it["strong"][:4],
                "background_sentences": [s for s in it["sents"] if s not in it["strong"]][:4],
                "formal": {k: fc.get(k) for k in ("form", "category", "binders", "prop", "defs", "opens", "inline_opens",
                                                   "variables", "negation_stripped", "error") if fc.get(k)},
                "formal_source": f"google-deepmind/formal-conjectures@{sha[:12]} FormalConjectures/ErdosProblems/{n}.lean",
                "exclude_reason": reason, "probe": (old.get(n) or {}).get("probe"), "mask": (old.get(n) or {}).get("mask")}
        item["split"], item["split_reason"] = classify(item, cutoff)
        out.append(item)
    meta = {"built": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "since": args.since, "cutoff": cutoff,
            "model": args.model, "sources": {"teorth": SOURCES["teorth"], "wiki": SOURCES["wiki"],
                                             "formal_conjectures_sha": sha}, "counts": counts(out)}
    POOL.write_text(json.dumps({"meta": meta, "items": sorted(out, key=lambda i: int(i["problem"]))}, indent=1, ensure_ascii=False))
    print(json.dumps(meta["counts"]))
    return 0


def counts(items: list[dict]) -> dict:
    c: dict = {}
    for i in items:
        c[i["split"]] = c.get(i["split"], 0) + 1
    return c


def load_pool() -> dict:
    return json.loads(POOL.read_text())


def save_pool(pool: dict) -> None:
    for i in pool["items"]:
        i["split"], i["split_reason"] = classify(i, pool["meta"]["cutoff"])
    pool["meta"]["counts"] = counts(pool["items"])
    POOL.write_text(json.dumps(pool, indent=1, ensure_ascii=False))


# ---------------------------------------------------------------- the recall probe ------------------------------------

PROBE = """You are being asked a calibration question before a benchmark. Answer plainly and honestly: "I do not
know" is the useful answer whenever it is true.

Erdős problem #{n} (erdosproblems.com/{n}) asks:

{statement}

1. As far as you know, is this problem still open, or has it been resolved? If you believe it has been resolved,
   say by whom, when, in which direction (the answer to the question: yes or no), and the key idea.
2. If you do not know of a resolution, which answer do you expect, and why? Mark it clearly as a guess.
3. Do you remember a specific paper, preprint, forum post or formal proof that settles it? Name it, or say no.

End with exactly one ```json block:
{{"status_believed": "open" | "resolved" | "unsure", "answer_claimed": "yes" | "no" | null,
  "answer_guess": "yes" | "no" | null, "recalls_method": true | false, "source_recalled": "<short>" | null,
  "confidence": <number between 0 and 1>}}
"answer_claimed" is ONLY for an answer you remember; a guess goes in "answer_guess"."""


def probe_verdict(parsed: dict, yes: bool) -> str:
    """recalled / partial-recall exclude the item; misremembered and unaware keep it.

    Conservative on purpose: a model that says "resolved" and names a source is excluded even without the
    answer, because a long run can turn a half-memory into the route."""
    truth = "yes" if yes else "no"
    status, claimed = parsed.get("status_believed"), parsed.get("answer_claimed")
    if claimed == truth and (status == "resolved" or parsed.get("recalls_method")):
        return "recalled"
    if status == "resolved" and claimed not in (None, truth):
        return "misremembered"
    if status == "resolved" and (parsed.get("recalls_method") or parsed.get("source_recalled")):
        return "partial-recall"
    return "unaware"


def json_tail(text: str) -> dict:
    blocks = re.findall(r"```json\s*(\{.*?\})\s*```", text or "", re.S) or re.findall(r"(\{[^{}]*\"status_believed\"[^{}]*\})", text or "", re.S)
    for b in reversed(blocks):
        try:
            return json.loads(b)
        except ValueError:
            continue
    return {}


def probe(args) -> int:
    import harness as H
    pool = load_pool()
    todo = [i for i in pool["items"] if i["split"] != "excluded" and (args.redo or not i.get("probe"))]
    if args.items:
        todo = [i for i in pool["items"] if i["problem"] in set(args.items)]
    todo = todo[: args.limit] if args.limit else todo
    backend = H.ClaudeCliBackend(args.model, 900, args.call_budget)
    PROBES.mkdir(parents=True, exist_ok=True)
    spent, failures = 0.0, 0
    for i in todo:
        if spent >= args.max_spend:
            print(f"stopping: probe spend ${spent:.2f} reached --max-spend {args.max_spend}")
            break
        prompt = PROBE.format(n=i["problem"], statement=i["statement_en"])
        try:
            answer = backend.complete("probe", prompt)
            failures = 0
        except Exception as e:                                   # provider failure: record nothing, retry later
            failures += 1
            print(f"#{i['problem']}: probe failed ({str(e)[:160]})")
            if failures >= 3:
                print("three provider failures in a row: stopping (usage limit or login?); rerun `probe` to continue")
                break
            continue
        cost = (getattr(backend, "last_meta", {}) or {}).get("cost_usd")
        spent += cost or 0.0
        parsed = json_tail(answer)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
        path = PROBES / f"{i['problem']}-{stamp}.md"
        path.write_text(f"# Time-split recall probe, #{i['problem']} ({stamp}Z)\n\nmodel: {args.model}  cost_usd: {cost}\n\n"
                        f"## Prompt\n\n```\n{prompt}\n```\n\n## Answer\n\n{answer}\n")
        verdict = probe_verdict(parsed, bool(i["answer"])) if parsed else "unparsed"
        guess = parsed.get("answer_claimed") or parsed.get("answer_guess")
        i["probe"] = {"verdict": verdict, "status_believed": parsed.get("status_believed"),
                      "answer_claimed": parsed.get("answer_claimed"), "answer_guess": parsed.get("answer_guess"),
                      "prior_correct": None if guess is None else guess == ("yes" if i["answer"] else "no"),
                      "source_recalled": parsed.get("source_recalled"), "model": args.model, "cost_usd": cost,
                      "file": str(path.relative_to(ROOT)), "at": stamp}
        print(f"#{i['problem']}: {verdict} (believed {parsed.get('status_believed')}, guess {guess}, ${cost})", flush=True)
        save_pool(pool)
    print(f"probe spend ${spent:.2f}; {json.dumps(counts(pool['items']))}")
    return 0


# ---------------------------------------------------------------- freezing statements ---------------------------------

def taken_aliases() -> set[int]:
    taken = set(range(0, 2001))
    for d in (ROOT / "benchmarks").glob("*/masks/*.json"):
        try:
            taken.add(int(json.loads(d.read_text()).get("alias_id", -1)))
        except (ValueError, OSError):
            pass
    for d in [*(ROOT / "benchmarks").glob("*/problems/erdos_*.json"), *(ROOT / "programs").glob("erdos_*")]:
        m = re.search(r"erdos_(\d+)", d.name)
        if m:
            taken.add(int(m.group(1)))
    return taken


def alias_for(n: str, salt: str, taken: set[int]) -> int:
    """A 5-digit synthetic id, deterministic in (problem, salt), never a real id or one already in use."""
    h = int(hashlib.sha256(f"timesplit:{n}:{salt}".encode()).hexdigest(), 16)
    for k in range(80000):
        a = 20000 + (h + 7919 * k) % 80000
        if a not in taken:
            taken.add(a)
            return a
    raise RuntimeError("alias space exhausted")


def freeze(args) -> int:
    import harness as H
    pool = load_pool()
    if args.redo or args.retry_failed:   # a failed mask excludes an item, so clear masks before choosing the work
        for i in pool["items"]:
            failed = (i.get("mask") or {}).get("ok") is False
            if not i.get("exclude_reason") and (args.redo or failed) and (not args.items or i["problem"] in set(args.items)):
                i["mask"] = None
                i["split"], i["split_reason"] = classify(i, pool["meta"]["cutoff"])
    want = {"test", "dev", "train"} | ({"unprobed"} if args.unprobed else set())
    todo = [i for i in pool["items"] if i["split"] in want and (args.redo or not (i.get("mask") or {}).get("ok"))]
    if args.items:
        todo = [i for i in pool["items"] if i["problem"] in set(args.items)]
    try:
        os.nice(10)                      # another lane may be compiling; ours can wait
    except OSError:
        pass
    MASKS.mkdir(parents=True, exist_ok=True)
    taken = taken_aliases()
    checker = H.LeanChecker(H.FORMAL, args.lean_timeout)
    idx = H.decl_index() if args.auto_import else None
    aliases = {i["problem"]: int((i.get("mask") or {}).get("alias_id") or alias_for(i["problem"], "mask", taken)) for i in todo}
    statements = {i["problem"]: frozen_statement(i["formal"], aliases[i["problem"]]) for i in todo}
    imports = {p: list(H.DEFAULT_IMPORTS) for p in statements}
    passed, errors, inlined, classical = set(), {}, {}, set()
    decls = fcm_decls() if (CACHE / "fcm").exists() else []
    items_by = {i["problem"]: i for i in todo}
    pending = set(statements)
    for rnd in range(6):
        # One batch per distinct import set: `Mathlib.Tactic` does not reach SimpleGraph, Nat.nth or the asymptotics
        # notation, and an import per statement (not the union) keeps every later check in a run as light as it was.
        groups: dict[tuple, list[str]] = {}
        for p in pending:
            groups.setdefault(tuple(imports[p]), []).append(p)
        newly = set()
        for imps, ps in groups.items():
            ok, errs = batch_check(H, checker, {p: statements[p] for p in ps}, args.batch, list(imps))
            passed |= ok
            errors.update(errs)
            newly |= set(ps) - ok
        pending = set()
        for p in newly:
            errs = errors.get(p, [])
            mods = modules_for(errs, idx, imports[p])
            if mods:
                imports[p] += mods
                pending.add(p)
                continue
            if "Decidable" in " ".join(errs) and p not in classical:
                # formal-conjectures states Props in a classical environment; decidability never changes a Prop
                classical.add(p)
            elif decls and p not in inlined:
                # imports cannot help; the name may be formal-conjectures' own (`Set.upperDensity`, `≪`)
                blocks, names = fcm_inline(errs, statements[p], decls, idx)
                if not blocks:
                    continue
                inlined[p] = (blocks, names)
            else:
                continue
            statements[p] = frozen_statement(items_by[p]["formal"], aliases[p], extra=(inlined.get(p) or ([], []))[0],
                                             classical=p in classical)
            pending.add(p)
        print(f"round {rnd + 1}: {len(passed)} of {len(statements)} compile; {len(pending)} retry "
              f"(added imports or inlined formal-conjectures definitions)", flush=True)
        if not pending:
            break
    for i in todo:
        p = i["problem"]
        alias, statement = aliases[p], statements[p]
        res = {"ok": p in passed, "errors": [] if p in passed else errors.get(p, ["no error attributed (timeout?)"])}
        imports_p = imports[p]
        mask = {"true_problem": i["problem"], "alias_id": str(alias), "statement_en": i["statement_en"],
                "statement_lean": statement, "imports": imports_p, "tags": i["tags"], "ok": bool(res.get("ok")),
                "errors": [str(e)[:300] for e in res.get("errors", [])][:3],
                "source": i["formal_source"] + " (main theorem; answer stripped; comments removed; identity renamed)",
                "inlined_from_formal_conjectures": (inlined.get(p) or ([], []))[1], "classical": p in classical,
                "checked": datetime.now(timezone.utc).strftime("%Y-%m-%d")}
        (MASKS / f"{i['problem']}.json").write_text(json.dumps(mask, indent=1, ensure_ascii=False))
        i["mask"] = {"alias_id": str(alias), "ok": mask["ok"], "file": str((MASKS / f"{i['problem']}.json").relative_to(ROOT)),
                     "faithful": None, "error": "; ".join(mask["errors"])[:300] if not mask["ok"] else None}
        print(f"#{i['problem']}: {'compiles' if mask['ok'] else 'FAILS: ' + (i['mask']['error'] or '')[:140]}", flush=True)
        save_pool(pool)
    return 0


def judge_cmd(args) -> int:
    """Faithfulness of each frozen statement to the question, for items the probe kept: the harness's own blind
    back-translation, then its open-problem judge for the YES direction. Two model calls per item."""
    import harness as H
    pool = load_pool()
    todo = [i for i in pool["items"] if i["split"] in ("test", "dev", "train") and (i.get("mask") or {}).get("ok")
            and (args.redo or (i["mask"].get("faithful") is None))]
    if args.items:
        todo = [i for i in pool["items"] if i["problem"] in set(args.items) and (i.get("mask") or {}).get("ok")]
    backend = H.MaskedBackend(H.ClaudeCliBackend(DEFAULT_MODEL, 900, 1.0))
    spent = 0.0
    for i in todo:
        if spent >= args.max_spend:
            print(f"stopping: judge spend ${spent:.2f} reached --max-spend {args.max_spend}")
            break
        path = ROOT / i["mask"]["file"]
        mask = json.loads(path.read_text())
        try:
            mask["faithfulness"] = judge(H, i, mask, backend)
        except Exception as e:                                    # provider failure: leave it unjudged
            print(f"#{i['problem']}: judge failed ({str(e)[:140]})")
            continue
        spent += mask["faithfulness"].get("cost_usd") or 0.0
        path.write_text(json.dumps(mask, indent=1, ensure_ascii=False))
        i["mask"]["faithful"] = mask["faithfulness"].get("faithful")
        i["mask"]["issues"] = (mask["faithfulness"].get("issues") or [])[:4]
        print(f"#{i['problem']}: faithful={i['mask']['faithful']}  {str(mask['faithfulness'].get('verdict'))[:150]}", flush=True)
        save_pool(pool)
    return 0


UNKNOWN_RE = re.compile(r"[Uu]nknown (?:identifier|constant|namespace) '?`?([\w.'₀-₉]+)")
FIELD_RE = re.compile(r"Invalid field `([\w'₀-₉]+)`")
MISSING_RE = re.compile(r"environment does not contain `([\w.'₀-₉]+)`")      # dot notation: `G.CliqueFree`


def modules_for(errors: list[str], idx, have: list[str]) -> list[str]:
    """Mathlib modules that would supply the names an error says are missing: a declaration (`Nat.nth`), a dot-
    notation target (`SimpleGraph.CliqueFree`, reported as a missing field), or a whole namespace an `open`
    names (`EuclideanGeometry`), which no single declaration lookup finds."""
    if not idx:
        return []
    text = " ".join(errors)
    mods = set()
    for u in set(UNKNOWN_RE.findall(text)) | set(MISSING_RE.findall(text)):
        hit = idx.lookup(u)
        if hit:
            mods.add(hit[0])
            continue
        if "namespace" in text and re.fullmatch(r"[A-Z][\w]*(?:\.[A-Z][\w]*)*", u):
            inside = sorted((k for k in idx.by_name if k.startswith(u + ".")), key=len)[:1]
            mods |= {idx.by_name[k][0] for k in inside}
    return sorted(m for m in mods if m not in have)
# `scoped[NS]` is Mathlib's scoped-to-a-namespace modifier: formal-conjectures declares `ℝ²` that way (Geometry/2d.lean),
# and without it every statement over the plane failed on its first `ℝ²` (#655, 2026-10-14).
FCM_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|scoped(?:\[[^\]]*\])?|public|nonrec|partial|"
                      r"unsafe)\s+)*"
                      r"(?P<kind>def|abbrev|irreducible_def|structure|class|inductive|instance|notation|infix|infixl|"
                      r"infixr|prefix|postfix)\b\s*(?P<name>[^\s:({\[]*)")


def fcm_decls() -> list[dict]:
    """Top-level declarations of formal-conjectures' Mathlib extension (cached at the pinned commit), each with the
    namespace, `open`s and `variable`s in force where it is declared. A statement written against that library
    names things plain Mathlib lacks (`Set.upperDensity`, the `≪` notation); inlining them keeps the frozen
    statement self-contained on Mathlib imports, which is all the harness admits."""
    out = []
    for path in sorted((CACHE / "fcm").rglob("*.lean")):
        text = strip_comments(path.read_text(errors="replace"))
        raw = re.split(r"\n(?=\S)", text)
        chunks, carry = [], ""
        for ch in raw:                                   # an attribute line belongs to the declaration after it
            if re.fullmatch(r"\s*(?:@\[[^\]]*\]\s*)+", ch):
                carry += ch.strip() + "\n"
                continue
            chunks.append(carry + ch)
            carry = ""
        ns, scopes = [], [{"vars": [], "opens": []}]
        for ch in chunks:
            s = ch.strip()
            first = s.split("\n")[0]
            if re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:namespace|section)\b", first):
                m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?namespace\s+(\S+)", first)
                ns.append(m.group(1) if m else None)
                scopes.append({"vars": [], "opens": []})
            elif first.startswith("end") and ns:
                ns.pop()
                scopes.pop()
            elif first.startswith("variable"):
                scopes[-1]["vars"].append(s)
            elif first.startswith("open ") and not first.rstrip().endswith(" in"):
                scopes[-1]["opens"].append(first.strip())
            elif (m := FCM_DECL.match(s)):
                names = [x for x in ns if x]
                is_notation = m.group("kind") in ("notation", "infix", "infixl", "infixr", "prefix", "postfix")
                name = "" if is_notation else m.group("name")
                full = (name[len("_root_."):] if name.startswith("_root_.") else ".".join(names + [name])) if name else ""
                toks = re.findall(r'"\s*([^"]*?)\s*"', first) if is_notation else []
                lead = toks[0] if toks else ""
                out.append({"kind": m.group("kind"), "name": full, "last": full.split(".")[-1], "ns": ".".join(names),
                            "text": s, "lead": lead if lead.strip("()[]{},. ") else "",   # "χ(" and "≪" lead; ")" never does
                            "vars": [v for sc in scopes for v in sc["vars"]], "opens": [o for sc in scopes for o in sc["opens"]],
                            "file": str(path.relative_to(CACHE / "fcm"))})
    return out


def fcm_inline(errors: list[str], statement: str, decls: list[dict], idx=None, with_decls: bool = False) -> tuple:
    """(blocks to prepend, names inlined) for a statement that fails on names only formal-conjectures defines; with
    `with_decls`, the chosen declarations too, so a caller can check each against another commit's source."""
    by_last: dict[str, list[dict]] = {}
    for d in decls:
        if d["last"]:
            by_last.setdefault(d["last"], []).append(d)
    text = " ".join(errors)
    wanted = [u.split(".")[-1] for u in UNKNOWN_RE.findall(text)] + FIELD_RE.findall(text)
    common = {"=", "+", "-", "*", "/", "<", ">", "≤", "≥", "∣", "^", "∑", "∏", "∫", "|"}
    notations = [d for d in decls if d["lead"] and d["lead"] not in common and d["lead"] in statement]
    chosen: list[dict] = []
    seen: set[tuple] = set()

    def add(d, depth=0):
        key = (d["kind"], d["name"] or d["lead"])
        if key in seen or depth > 6:
            return
        seen.add(key)
        body = d["text"]
        for last, cands in by_last.items():               # dependencies first
            if last != d["last"] and len(last) > 3 and re.search(rf"(?<![\w']){re.escape(last)}(?![\w'])", body):
                for c in cands:
                    if c["kind"] != "instance" and not (idx and idx.lookup(c["name"])):
                        add(c, depth + 1)
        for n in decls:
            if n["lead"] and n["lead"] not in common and n is not d and n["lead"] in body:
                add(n, depth + 1)
        chosen.append(d)

    for w in dict.fromkeys(wanted):
        for c in by_last.get(w, []):
            if c["kind"] != "instance":
                add(c)
    for n in notations:
        add(n)
    blocks = []
    for d in chosen:
        inner = "\n".join(d["opens"] + d["vars"] + [d["text"]])
        blocks.append(f"namespace {d['ns']}\n{inner}\nend {d['ns']}" if d["ns"] else inner)
    names = [d["name"] or f"notation {d['lead']}" for d in chosen]
    return (blocks, names, chosen) if with_decls else (blocks, names)


def batch_check(H, checker, statements: dict[str, str], size: int,
                imports: list[str] | None = None) -> tuple[set[str], dict[str, list[str]]]:
    """(problems whose frozen statement compiles, the errors charged to each failing one), checked many per Lean
    process: the Mathlib import dominates a check (20-60 s) and the machine is shared with a live lane. Each
    statement sits in its own namespace, so its `open`s and definitions stay local; an item passes only if no
    error falls inside its block. An error outside every block passes nothing in that chunk."""
    ok: set[str] = set()
    errors: dict[str, list[str]] = {}
    keys = sorted(statements, key=int)
    for k in range(0, len(keys), size):
        chunk = keys[k: k + size]
        body = "\n\n".join(f"-- TS-BLOCK {p}\nnamespace TSB{p}\n\n{statements[p]}\n\nend TSB{p}" for p in chunk)
        src = H.compose(body, list(imports or H.DEFAULT_IMPORTS))
        starts = sorted((ln, p) for ln, line in enumerate(src.splitlines(), 1)
                        for p in [m.group(1) for m in [re.match(r"-- TS-BLOCK (\d+)$", line)] if m])
        tag = hashlib.sha256("".join(chunk).encode()).hexdigest()[:8]
        res = checker.check(src, ROOT / "runs" / "adhoc" / f"timesplit-batch-{tag}.lean")
        if res.get("timeout"):
            continue
        bad = set()
        for e in res.get("errors", []):
            m = re.match(r"line (\d+):", str(e))
            owner = [p for ln, p in starts if m and ln <= int(m.group(1))]
            who = owner[-1] if owner else "*"
            bad.add(who)
            errors.setdefault(who, []).append(str(e)[:400])
        if "*" not in bad:
            ok |= set(chunk) - bad
    errors.pop("*", None)
    return ok, errors


def freeze_compiling(H, fc: dict, alias: int, checker, idx=None, decls: list[dict] | None = None,
                     rounds: int = 8) -> dict:
    """One frozen statement through the mask builder's repair loop, for a caller with no pool (the resolution
    campaign's Lean tier). It adds:
    - the Mathlib modules its errors name;
    - `open scoped Classical` on a decidability error;
    - the formal-conjectures declarations it uses, inlined verbatim.

    Inlining repeats while it finds something new, because a round sees only what the parser reached: #655's `ℝ²` hid
    `distinctDistances` until the notation was in. The last check compiles the statement exactly as a run will, outside
    the batch namespace. Returns {ok, statement, imports, inlined (names), files (their source files), classical,
    errors, decls (the inlined declarations: name, file, text)}."""
    imports, blocks, names, chosen, classical = list(H.DEFAULT_IMPORTS), [], [], [], False
    statement, errs = frozen_statement(fc, alias), []

    def out(ok: bool) -> dict:
        return {"ok": ok, "statement": statement, "imports": imports, "inlined": names, "classical": classical,
                "files": sorted({d["file"] for d in chosen}), "errors": [] if ok else errs[:3],
                "decls": [{"name": nm, "file": d["file"], "text": d["text"]} for nm, d in zip(names, chosen)]}

    for _ in range(rounds):
        passed, errors = batch_check(H, checker, {str(alias): statement}, 1, imports)
        if str(alias) in passed:
            res = checker.check(H.compose(statement, imports), ROOT / "runs" / "adhoc" / f"freeze-{alias}.lean")
            errs = [str(e)[:400] for e in res.get("errors", [])] or (["timeout"] if res.get("timeout") else [])
            return out(bool(res.get("ok")))
        errs = errors.get(str(alias)) or ["no error attributed (timeout?)"]
        mods = modules_for(errs, idx, imports)
        if mods:
            imports += mods
            continue
        if "Decidable" in " ".join(errs) and not classical:
            classical = True
        else:
            new = fcm_inline(errs, statement, decls, idx, with_decls=True) if decls else ([], [], [])
            fresh = [(b, nm, d) for b, nm, d in zip(*new) if b not in blocks]
            if not fresh:
                break
            blocks += [b for b, _, _ in fresh]
            names += [nm for _, nm, _ in fresh]
            chosen += [d for _, _, d in fresh]
        statement = frozen_statement(fc, alias, extra=blocks, classical=classical)
    return out(False)


def judge(H, item: dict, mask: dict, backend) -> dict:
    """The harness's own blind back-translation, then its open-problem judge for the YES direction."""
    cost = 0.0
    bt = backend.complete("backtranslate", H.backtranslate_prompt(mask["statement_lean"]))
    cost += (getattr(backend, "last_meta", {}) or {}).get("cost_usd") or 0.0
    verdict = json_tail_any(backend.complete("faithful", H.compare_prompt(
        {"id": mask["alias_id"], "statement": item["statement_en"], "notes": "(none)"}, bt, direction="pos")))
    cost += (getattr(backend, "last_meta", {}) or {}).get("cost_usd") or 0.0
    return {"faithful": verdict.get("faithful"), "issues": verdict.get("issues"), "verdict": verdict.get("verdict"),
            "backtranslation": bt, "cost_usd": round(cost, 4), "model": DEFAULT_MODEL}


def json_tail_any(text: str) -> dict:
    for b in reversed(re.findall(r"```json\s*(\{.*?\})\s*```", text or "", re.S)):
        try:
            return json.loads(b)
        except ValueError:
            continue
    return {}


# ---------------------------------------------------------------- candidate: discover-first ---------------------------
#
# Designed from evidence OUTSIDE this benchmark (the #242 and masked #275 research runs), never from dev
# transcripts. The research loop proposes ONE plan per cycle and formalises every idea before it can be judged:
# on #242, 19 plans in six sessions cost $4.73 of $23.59, the rest went to proving their hypotheses in Lean. And
# `--open` splits the budget evenly although the model's prior guess of the answer is right 26 times in 31.
# discover-v1 moves the cheap part first: several independent informal attempts from different angles, a referee
# pass on each, then (if they agree) the whole remaining budget on one direction, with the best route handed to
# every research stage as guidance. Same $8 per item as the baseline.

DISCOVER_FRAMES = (
    "Look for an explicit construction, counterexample or identity first: work out small cases systematically, "
    "find the pattern, and turn it into a general formula you then verify.",
    "Look for a structural argument: reduce to a cleaner special case, choose an extremal object, induct, or split "
    "into cases whose union is exhaustive.",
    "Look for a counting, averaging, probabilistic or analytic argument: pigeonhole, double counting, generating "
    "functions, density or entropy estimates, explicit inequalities.",
)

DISCOVER_PROMPT = """You are attacking a research problem that may still be open. Find out which way it goes, and produce a
proof a referee would accept.

PROBLEM:
{statement}

THE PRECISE STATEMENT (Lean 4). A proof of this, or of its negation, is what will be checked; read it carefully,
including its conventions:
```lean
{lean}
```

APPROACH FOR THIS ATTEMPT: {frame}

1. Decide whether the precise statement is TRUE or FALSE. Test small cases and look for counterexamples before
   committing.
2. Give a complete proof of your answer. State every lemma precisely, give every construction explicitly (formulas,
   not descriptions), and check every inequality and computation. If the statement is FALSE, the proof is an explicit
   counterexample or a proof of the negation.
3. If you cannot complete the proof, give the most promising route and name the exact missing step.

End with exactly one ```json block:
{{"answer": "true" | "false", "confidence": <number between 0 and 1>, "complete": true | false,
  "key_steps": ["<each lemma or construction the proof rests on, one sentence each>"], "gap": "<missing step or null>"}}"""

CRITIC_PROMPT = """Referee the claimed proof below. Check every step, recompute every calculation, and test the key lemmas
on small cases. Do not repair it: find the first real error or gap, if there is one.

STATEMENT (Lean 4):
```lean
{lean}
```

CLAIMED ANSWER: the statement is {answer}.

CLAIMED PROOF:
{proof}

End with exactly one ```json block: {{"valid": true | false, "first_error": "<where and why, or null>", "fixable": true | false}}"""


GAP_PROMPT = """You are proving ONE missing step inside a larger argument. Earlier attempts on the whole problem reduced it to
this step; the rest of the route is believed to be in place.

THE WHOLE PROBLEM (context):
{statement}

THE PRECISE STATEMENT (Lean 4) that the whole argument must establish ({direction}):
```lean
{lean}
```

THE ROUTE SO FAR (unverified):
{route}

THE MISSING STEP:
{gap}

APPROACH FOR THIS ATTEMPT: {frame}

Prove the missing step completely. First state it precisely: you may strengthen or weaken it slightly if the route
still goes through, and say so. Give every construction explicitly and check every computation. If the step is
FALSE, give a counterexample and say what that means for the route.

End with exactly one ```json block:
{{"proved": true | false, "refuted": true | false, "lemma": "<the exact statement you proved or refuted>",
  "confidence": <number between 0 and 1>, "key_steps": ["<one sentence each>"], "remaining_gap": "<or null>"}}"""


def decide_direction(attempts: list[dict], single_confident: float | None = None, floor: float | None = None) -> dict:
    """Which direction to commit to, from the attempts' answers, confidence, completeness and the referee.

    Weight per attempt: confidence x 2 if complete and refereed valid, x 1 if complete and only fixably wrong, x 0.5
    otherwise. Commit when one direction holds at least 75% of the weight AND either an attempt there survived the
    referee or every attempt agrees; otherwise attack both directions, as the baseline does."""
    score = {"true": 0.0, "false": 0.0}
    for a in attempts:
        ans = a.get("answer")
        if ans not in score:
            continue
        conf = min(max(float(a.get("confidence") or 0.5), 0.0), 1.0)
        valid = a.get("complete") and (a.get("critic") or {}).get("valid")
        fixable = a.get("complete") and (a.get("critic") or {}).get("fixable")
        score[ans] += conf * (2.0 if valid else 1.0 if fixable else 0.5)
    total = sum(score.values())
    if not total:
        return {"commit": None, "share": 0.0, "score": score, "best": None}
    ans = max(score, key=score.get)
    share = score[ans] / total
    mine = [a for a in attempts if a.get("answer") == ans]
    survived = any(a.get("complete") and (a.get("critic") or {}).get("valid") for a in mine)
    unanimous = len(mine) == len([a for a in attempts if a.get("answer") in score]) >= 2
    # v2: one confident answer is enough when the others produced nothing (#392 lost its commitment because one of
    # two attempts overran its cap and the survivor alone was not "unanimous")
    confident = single_confident is not None and len(mine) == len([a for a in attempts if a.get("answer") in score]) \
        and any(float(a.get("confidence") or 0) >= single_confident for a in mine)
    best = max(mine, key=lambda a: (bool(a.get("complete") and (a.get("critic") or {}).get("valid")),
                                    bool(a.get("complete")), float(a.get("confidence") or 0)))
    commit = ("pos" if ans == "true" else "neg") if share >= 0.75 and (survived or unanimous or confident) else None
    # --commit-floor (calibrated on train, calibration-train-v2r1): every wrong commit in 45 rounds was a FALSE statement
    # called true at a mean confidence below 0.6; at 0.6, 33 commits and none wrong. A floor only withholds.
    if commit and floor is not None:
        confs = [float(a.get("confidence")) for a in mine if isinstance(a.get("confidence"), (int, float))]
        if not confs or sum(confs) / len(confs) < floor:
            commit = None
    return {"commit": commit, "answer": ans, "share": round(share, 3), "score": score, "best": best}


def negated_statement(statement: str) -> str:
    """The frozen statement's negation, for committing to the NO direction: binders become a leading ∀."""
    head, _, rest = ("\n" + statement).rpartition("\ntheorem ")
    head = head[1:] if head.startswith("\n") else head
    m = re.match(r"(erdos_\d+)(.*?) :\n(.*) := by\n  sorry\s*$", rest, re.S)
    if not m:
        raise ValueError("unexpected frozen statement layout")
    name, binders, prop = m.group(1), m.group(2).strip(), m.group(3).strip()
    inner = f"∀ {binders}, {prop}" if binders else prop
    return (head + "\n" if head else "") + f"theorem {name} :\n    ¬ ({inner}) := by\n  sorry"


def discover(item: dict, statement: str, run_dir: Path, args) -> dict:
    """Run the informal stage; returns the decision, the guidance text and what it cost. The attempts are
    independent, so they run in parallel (a high-effort attempt takes ~10 min), each thread with its own backend
    so that every call's cost is read from the call that made it."""
    import harness as H
    from concurrent.futures import ThreadPoolExecutor

    def one(k: int, frame: str) -> dict:
        inner = H.ClaudeCliBackend(args.model, 3600, args.discover_budget)
        backend = H.MaskedBackend(inner)
        try:
            text = backend.complete("discover", DISCOVER_PROMPT.format(statement=item["statement_en"], lean=statement,
                                                                      frame=frame), effort_override=args.discover_effort,
                                    budget_override=args.discover_budget)
        except Exception as e:                                    # a failed attempt is simply absent -- but paid for:
            return {"frame": k, "error": str(e)[:200], "cost": round(inner.total_cost_usd, 4)}   # an over-cap call still costs
        a = {"frame": k, **json_tail_any(text), "text": text}
        if a.get("complete") and a.get("answer") in ("true", "false"):
            try:
                verdict = backend.complete("discover-critic", CRITIC_PROMPT.format(lean=statement, answer=a["answer"].upper(),
                                                                                  proof=text[-12000:]),
                                           effort_override="medium", budget_override=args.critic_budget)
                a["critic"] = json_tail_any(verdict)
                a["critic_text"] = verdict
            except Exception as e:
                a["critic"] = {"error": str(e)[:200]}
        a["cost"] = round(inner.total_cost_usd, 4)        # every call this attempt made, failed ones included
        return a

    v2 = getattr(args, "candidate", None) in ("discover-v2", "discover-v3", "discover-v4")
    # alloc: v2's first round and its single-confident rule, the calibrated floor, and no gap round (iteration 3)
    alloc = getattr(args, "candidate", None) == "alloc"
    v3floor = getattr(args, "candidate", None) in ("discover-v3", "discover-v4")
    frames = DISCOVER_FRAMES[: args.discover_attempts]

    def run_round(_r: int = 0) -> list[dict]:
        with ThreadPoolExecutor(max_workers=len(frames)) as ex:
            return list(ex.map(lambda kf: one(*kf), enumerate(frames)))
    attempts = run_round()
    for a in attempts:
        a["round"] = 1
    spent = sum(a.get("cost") or 0.0 for a in attempts)
    rounds_run = 1
    if getattr(args, "candidate", None) == "discover-v4":
        attempts, rounds_run, spent = run_more_rounds(attempts, run_round, int(args.discover_rounds),
                                                      float(args.discover_total_budget), spent)
    floor = getattr(args, "commit_floor", None)
    d = decide_direction(attempts, single_confident=0.75 if (v2 or alloc) else None,
                         floor=floor if floor is not None else (0.6 if (alloc or v3floor) else None))
    best = d.get("best") or {}
    gap_attempt = None
    if v2 and best and not (best.get("complete") and (best.get("critic") or {}).get("valid")) and best.get("gap"):
        # v2's second round: the train diagnostic #152 certified every step the route gave it and stopped at the one
        # step both attempts named as missing. Attack that step alone, harder, before any Lean is spent on it.
        gap_attempt = attack_gap(item, statement, d, best, args)
        spent += gap_attempt.get("cost") or 0.0
    guidance = ""
    if best:
        guidance = (f"An automated informal discovery stage ({len(attempts)} independent attempts, each refereed) believes "
                    f"the frozen statement is {str(d.get('answer')).upper()} (weight share {d['share']}). "
                    + ("This run attacks ONLY that direction.\n\n" if d["commit"] else "Both directions are attacked.\n\n")
                    + "Key steps of the best attempt:\n" + "\n".join(f"- {s}" for s in (best.get("key_steps") or [])[:12])
                    + (f"\n\nKnown gap: {best.get('gap')}" if best.get("gap") else "")
                    + (f"\n\nReferee's first objection: {(best.get('critic') or {}).get('first_error')}"
                       if (best.get("critic") or {}).get("first_error") else ""))
        if gap_attempt and gap_attempt.get("proved") and (gap_attempt.get("critic") or {}).get("valid"):
            guidance += ("\n\nTHE MISSING STEP, proved informally in a second round and refereed (still unverified in "
                         f"Lean):\nLemma: {gap_attempt.get('lemma')}\n" + gap_attempt.get("text", "")[-5000:])
        elif gap_attempt and gap_attempt.get("text"):
            guidance += (f"\n\nA second round attacked the missing step: proved={gap_attempt.get('proved')}, "
                         f"refuted={gap_attempt.get('refuted')}; remaining gap: {gap_attempt.get('remaining_gap')}\n"
                         + gap_attempt.get("text", "")[-2500:])
        # v1's wording and length exactly, so v1's test items (a new process, this file) run what its dev items ran
        guidance += (("\n\nThe first-round attempt in full (unverified):\n" + best.get("text", "")[-3500:]) if (v2 or alloc)
                     else "\n\nThe attempt in full (unverified):\n" + best.get("text", "")[-6000:])
    (run_dir / "discovery.json").write_text(json.dumps({"decision": {k: v for k, v in d.items() if k != "best"},
                                                        "best_frame": best.get("frame"), "rounds": rounds_run,
                                                        "attempts": attempts,
                                                        "gap_attempt": gap_attempt, "spend": round(spent, 4)},
                                                       indent=1, ensure_ascii=False))
    return {"commit": d["commit"], "answer": d.get("answer"), "share": d["share"], "guidance": guidance,
            "rounds": rounds_run, "spend": round(spent, 4), "gap_proved": bool(gap_attempt and gap_attempt.get("proved")
                                                         and (gap_attempt.get("critic") or {}).get("valid"))}


def attack_gap(item: dict, statement: str, d: dict, best: dict, args) -> dict:
    """One high-effort attempt on the named missing step, then a referee pass if it claims a proof."""
    import harness as H
    inner = H.ClaudeCliBackend(args.model, 3600, args.gap_budget)
    backend = H.MaskedBackend(inner)
    direction = "the statement is TRUE" if d.get("answer") == "true" else "the statement is FALSE (prove its negation)"
    route = "\n".join(f"- {s}" for s in (best.get("key_steps") or [])[:12]) or "(none recorded)"
    try:
        text = backend.complete("discover-gap", GAP_PROMPT.format(statement=item["statement_en"], lean=statement,
                                                                 direction=direction, route=route, gap=best.get("gap"),
                                                                 frame=DISCOVER_FRAMES[2]),
                                effort_override=args.gap_effort, budget_override=args.gap_budget)
    except Exception as e:
        return {"error": str(e)[:200], "cost": round(inner.total_cost_usd, 4)}
    g = {**json_tail_any(text), "text": text}
    if g.get("proved"):
        try:
            verdict = backend.complete("discover-critic", CRITIC_PROMPT.format(
                lean=statement, answer="TRUE" if d.get("answer") == "true" else "FALSE",
                proof=f"(The missing step of this route: {best.get('gap')})\n\n{text[-12000:]}"),
                effort_override="medium", budget_override=args.critic_budget)
            g["critic"] = json_tail_any(verdict)
        except Exception as e:
            g["critic"] = {"error": str(e)[:200]}
    g["cost"] = round(inner.total_cost_usd, 4)
    return g


# ---------------------------------------------------------------- calibrating the commit rule -------------------------

CAL_FLOORS = (None, 0.5, 0.6, 0.7, 0.8, 0.9)


def commit_at_floor(rec: dict, floor: float | None, rule: str = "v2") -> str | None:
    """The committed direction under `rule` with a confidence floor: the committed answer's attempts must average at
    least `floor`. A floor never creates a commitment; it only withholds one."""
    commit = rec[f"{rule}_commit"]
    if commit is None or floor is None:
        return commit
    ans = "true" if commit == "pos" else "false"
    confs = [a["confidence"] for a in rec["attempts"] if a.get("answer") == ans and a.get("confidence") is not None]
    return commit if confs and sum(confs) / len(confs) >= floor else None


def calibration_report(recs: list[dict]) -> dict:
    """Commit rate and wrong-commit rate per floor, under both rules, with Jeffreys 90% intervals on the error rate."""
    from predict import jeffreys
    out = {"rounds": len(recs), "items": len({r["problem"] for r in recs}),
           "spend": round(sum(r["spend"] for r in recs), 2), "floors": []}
    answered = [a for r in recs for a in r["attempts"] if a.get("answer") in ("true", "false")]
    out["attempt_accuracy"] = round(sum((a["answer"] == "true") == r["truth"] for r in recs for a in r["attempts"]
                                        if a.get("answer") in ("true", "false")) / len(answered), 3) if answered else None
    for rule in ("v1", "v2"):
        for f in CAL_FLOORS:
            calls = [(commit_at_floor(r, f, rule), r["truth"]) for r in recs]
            made = [(c, t) for c, t in calls if c]
            wrong = sum(1 for c, t in made if (c == "pos") != t)
            _, lo, hi = jeffreys(wrong, len(made)) if made else (0.0, 0.0, 1.0)
            out["floors"].append({"rule": rule, "floor": f, "commit_rate": round(len(made) / len(recs), 3) if recs else None,
                                  "commits": len(made), "wrong": wrong, "wrong_rate_90": [round(lo, 3), round(hi, 3)]})
    return out


def calibrate(args) -> int:
    """Discovery's first round alone, `--rounds` independent times per item, on a split with known answers (train by
    default: design data under the quarantine rule). No harness run: nothing is written to programs/, the Atlas or
    knowledge/. Records each attempt's answer, confidence, completeness and referee verdict, and what the v1 and v2
    rules would commit to, so the commit rule can be tuned against the truth before it touches dev."""
    from concurrent.futures import ThreadPoolExecutor
    out = RESULTS / f"calibration-{args.tag}.jsonl"
    if args.report:
        recs = [json.loads(l) for l in out.read_text().splitlines() if l.strip()] if out.exists() else []
        print(json.dumps(calibration_report(recs), indent=1))
        return 0
    items = [i for i in load_pool()["items"] if i["split"] == args.split and (not args.items or i["problem"] in args.items)
             and (i.get("mask") or {}).get("ok")]
    done = {(json.loads(l)["problem"], json.loads(l)["round"]) for l in out.read_text().splitlines() if l.strip()} \
        if out.exists() else set()
    tasks = [(i, k) for k in range(args.rounds) for i in items if (i["problem"], k) not in done]
    taken = taken_aliases()
    print(f"calibration {args.tag}: {len(tasks)} round(s) on {len(items)} {args.split} item(s)", flush=True)

    def one(task):
        item, k = task
        mask = json.loads((ROOT / item["mask"]["file"]).read_text())
        alias = alias_for(item["problem"], f"calibration-{args.tag}-r{k}", taken)
        statement = re.sub(rf"\berdos_{mask['alias_id']}\b", f"erdos_{alias}", mask["statement_lean"])
        work = RESULTS / "calibration" / args.tag / f"{item['problem']}-r{k}"
        work.mkdir(parents=True, exist_ok=True)
        ns = argparse.Namespace(model=args.model, discover_budget=args.discover_budget, discover_effort=args.discover_effort,
                                discover_attempts=args.discover_attempts, critic_budget=args.critic_budget,
                                candidate="calibrate")                 # not discover-v2: no gap round, the v1 rule
        try:
            d = discover(item, statement, work, ns)
        except Exception as e:                                         # noqa: BLE001 - one round never stops the batch
            print(f"#{item['problem']} r{k}: FAILED {type(e).__name__}: {str(e)[:200]}", flush=True)
            return
        raw = json.loads((work / "discovery.json").read_text())["attempts"]
        if any(LIMIT_RE.search(str(a.get("error") or "")) for a in raw):
            print(f"#{item['problem']} r{k}: usage limit; not recorded (rerun the command to fill it in)", flush=True)
            return
        atts = [{"frame": a.get("frame"), "answer": a.get("answer"),
                 "confidence": float(a["confidence"]) if isinstance(a.get("confidence"), (int, float)) else None,
                 "complete": bool(a.get("complete")), "referee_valid": (a.get("critic") or {}).get("valid"),
                 "error": a.get("error"), "cost": a.get("cost")} for a in raw]
        rec = {"problem": item["problem"], "round": k, "truth": bool(item["answer"]), "attempts": atts,
               "v1_commit": decide_direction(raw)["commit"], "v2_commit": decide_direction(raw, single_confident=0.75)["commit"],
               "spend": d["spend"], "work": str(work.relative_to(ROOT)),
               "settings": {"effort": args.discover_effort, "budget": args.discover_budget, "attempts": args.discover_attempts,
                            "critic_budget": args.critic_budget, "model": args.model},
               "at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        truth = "yes" if item["answer"] else "no"
        print(f"#{item['problem']} r{k}: truth={truth} answers={[a['answer'] for a in atts]} "
              f"conf={[a['confidence'] for a in atts]} v1={rec['v1_commit']} v2={rec['v2_commit']} ${d['spend']}", flush=True)

    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        list(ex.map(one, tasks))
    recs = [json.loads(l) for l in out.read_text().splitlines() if l.strip()] if out.exists() else []
    print(json.dumps(calibration_report(recs), indent=1))
    return 0


# ---------------------------------------------------------------- running one lane ------------------------------------

def git_state() -> dict:
    def g(*a):
        return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    return {"commit": g("rev-parse", "HEAD"), "dirty": bool(g("status", "--porcelain", "--untracked-files=no"))}


def file_hash(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16] if path.exists() else None


# Candidate v3 (docs/discovery-limits-2026-09-24.md): the harness's own discovery options, together. At $8 an item for
# both directions, exploration is held to $1.50 a session so that proving is not starved.
V3_FLAGS = ["--explore", "on", "--explore-budget", "1.5", "--explore-core", "on", "--empirical", "on",
            "--routes", "2", "--plan-effort", "high", "--attack-order", "core-first", "--stall-credit", "easier",
            "--literature-scope", "wide", "--child-cycles", "2"]


# Candidate alloc (loop iteration 3): budget follows the true direction and its core. Evidence: train #283, where
# proving got 13% of the spend, the refutation script 39%, and the core was deferred every cycle; and #997, whose last
# budget went on a published premise at the level of Maynard–Tao.
ALLOC_FLAGS = ["--attack-order", "core-first", "--refute", "changed", "--premise-attack", "cheap"]


# In-run discovery (2026-09-30): the harness runs discovery itself (`--discover on`), so the runner launches it with
# --open and the harness commits to a direction. discover-v5 = discover-v3's settings with the best refereed proof
# passed WHOLE (the runner passed its last 3,500 characters). blueprint = v5 + the proof as numbered steps the plan
# builds on, each child handed its step, and an outline view of long residuals. crossfed = a synthesis between
# rounds and a ladder of three easier variants (OpenAI's Navier-Stokes structure, at this budget).
IN_RUN_FLAGS = {
    "discover-v5": ["--discover", "on"],
    "blueprint": ["--discover", "on", "--blueprint", "on", "--residual-view", "outline"],
    "crossfed": ["--discover", "on", "--discover-mode", "crossfed", "--discover-rounds", "2", "--discover-ladder", "3",
                 "--discover-total-budget", "6"],
    "crossfed-blueprint": ["--discover", "on", "--discover-mode", "crossfed", "--discover-rounds", "2",
                           "--discover-ladder", "3", "--discover-total-budget", "6", "--blueprint", "on",
                           "--residual-view", "outline"],
}


def candidate_flags(args) -> list[str]:
    """Extra harness flags a candidate adds to the fixed protocol (empty for baseline and the discover arms)."""
    import shlex
    if getattr(args, "candidate", None) == "v3":
        return shlex.split(args.v3_flags) if getattr(args, "v3_flags", None) else list(V3_FLAGS)
    if getattr(args, "candidate", None) == "alloc":
        return list(ALLOC_FLAGS)
    if getattr(args, "candidate", None) in IN_RUN_FLAGS:
        return list(IN_RUN_FLAGS[args.candidate])
    return []


def protocol(args) -> dict:
    """Everything that defines 'this harness' for a result: code, knowledge, model and the run protocol."""
    import harness as H
    knowledge = Path(args.knowledge) if getattr(args, "knowledge", None) else H.KNOWLEDGE
    return {"git": git_state(), "harness_file": str(harness_file(args).relative_to(ROOT)),
            "harness_sha": file_hash(harness_file(args)), "knowledge": str(knowledge),
            "playbook_sha": file_hash(knowledge / "playbook.md"), "model": args.model, "budget": args.budget,
            "research_cycles": args.research_cycles, "hyps_per_cycle": args.hyps_per_cycle,
            "literature": args.literature, "lean_timeout": args.lean_timeout, "compile_workers": args.compile_workers,
            "open": True, "masked": True, "candidate": getattr(args, "candidate", None) or "baseline",
            **({"harness_flags": candidate_flags(args)} if candidate_flags(args) else {}),
            **({"discovery": {k: getattr(args, k, None) for k in DISCOVERY_KEYS}}
               if str(getattr(args, "candidate", None) or "").startswith("discover") or getattr(args, "candidate", None) == "alloc"
               else {})}


def harness_file(args) -> Path:
    """A pinned copy (`pin`) keeps a multi-day evaluation on one version of the code while other sessions commit."""
    return (ROOT / args.harness).resolve() if getattr(args, "harness", None) else ROOT / "harness.py"


def pin(args) -> int:
    """Freeze the code and knowledge an evaluation runs on: `harness_pin_<sha>.py` at the repo root (so its ROOT is
    unchanged and research children, which run in-process, use it too) and a copy of `knowledge/`."""
    import harness as H
    import shutil
    sha = file_hash(ROOT / "harness.py")
    # the name ends in "harness.py" so `pgrep -f "harness.py run"` (every session's lane check) still sees the lane
    dest = ROOT / f"pin_{sha}_harness.py"
    if not dest.exists():
        shutil.copyfile(ROOT / "harness.py", dest)
    kdir = HERE / "pins" / f"knowledge-{sha}"
    if not kdir.exists():
        # reference proofs and the harvested lemma store stay out: a benchmark reads neither
        shutil.copytree(H.KNOWLEDGE, kdir, ignore=shutil.ignore_patterns("solved", "lemmas.jsonl"))
        (kdir / "solved").mkdir(exist_ok=True)
    meta = {"harness": dest.name, "harness_sha": sha, "knowledge": str(kdir.relative_to(ROOT)),
            "git": git_state(), "at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
    (HERE / "pins").mkdir(exist_ok=True)
    (HERE / "pins" / f"{sha}.json").write_text(json.dumps(meta, indent=1))
    print(json.dumps(meta, indent=1))
    print(f"use: run --harness {dest.name} --knowledge {kdir.relative_to(ROOT)}")
    return 0


def default_tag(proto: dict) -> str:
    h = hashlib.sha256(json.dumps({k: v for k, v in proto.items() if k != "git"}, sort_keys=True).encode()).hexdigest()[:6]
    return f"{datetime.now().strftime('%Y%m%d')}-{proto['git']['commit'][:7]}{'-dirty' if proto['git']['dirty'] else ''}-{h}"


# discover-v3 = discover-v2's settings, fixed in code, plus the calibrated commit floor. v2's first-round settings
# lived only in its launch command (the argparse defaults are v1's), so replicating #1213 meant recovering them from a
# session transcript. The floor: 0 wrong commits of 33 at >= 0.6 on train, and dev's two wrong v2 commits (#537 at
# 0.55, #871 at 0.33) sat below it, each spending a whole run on a false statement.
DISCOVER_V3 = {"discover_attempts": 2, "discover_effort": "medium", "discover_budget": 0.8, "critic_budget": 0.3,
               "gap_budget": 1.2, "gap_effort": "medium", "commit_floor": 0.6}
# discover-v4 = v3 plus rounds until a refereed complete proof appears. Discovery is stochastic: on the train
# calibration #990 and #1037 had complete refereed proofs in 2 of 3 rounds each, and the conversion screen's single
# round got none for either, so the plan improvised a route whose key bound is as hard as the problem (#990). The
# one dev solve (#1213) came from a round that did produce one. A round costs $0.4-1.1; the cap keeps it bounded.
DISCOVER_V4 = {**DISCOVER_V3, "discover_rounds": 3, "discover_total_budget": 3.0}
DISCOVERY_KEYS = tuple(DISCOVER_V4)


def apply_candidate_settings(args) -> None:
    settings = {"discover-v3": DISCOVER_V3, "discover-v4": DISCOVER_V4}.get(getattr(args, "candidate", None))
    for k, v in (settings or {}).items():
        if k != "commit_floor" or getattr(args, k, None) is None:
            setattr(args, k, v)


def has_refereed_complete(attempts: list[dict]) -> bool:
    return any(a.get("complete") and a.get("answer") in ("true", "false") and (a.get("critic") or {}).get("valid")
               for a in attempts)


def run_more_rounds(first: list[dict], run_round, max_rounds: int, cap: float, spent: float):
    """discover-v4: further rounds of the same parallel attempts until one yields a complete proof its referee
    accepts, `max_rounds` in all. A round is never started when the previous round's cost would take the total past
    `cap`. All rounds are pooled for the direction decision, and every attempt records its round."""
    attempts, rounds, last = list(first), 1, spent
    while rounds < max_rounds and not has_refereed_complete(attempts):
        if spent + last > cap:
            break
        more = run_round(rounds)
        cost = sum(a.get("cost") or 0.0 for a in more)
        for a in more:
            a["round"] = rounds + 1
        attempts += more
        spent += cost
        last = cost
        rounds += 1
    return attempts, rounds, spent


def run(args) -> int:
    apply_candidate_settings(args)
    pool = load_pool()
    items = [i for i in pool["items"] if i["split"] == args.split and (i.get("mask") or {}).get("ok")]
    if args.items:
        items = [i for i in pool["items"] if i["problem"] in set(args.items) and (i.get("mask") or {}).get("ok")]
    proto = protocol(args)
    tag = args.tag or default_tag(proto)
    RESULTS.mkdir(parents=True, exist_ok=True)
    out = RESULTS / f"{tag}.jsonl"
    done = {json.loads(l)["problem"] for l in out.read_text().splitlines() if l.strip()} if out.exists() else set()
    items = [i for i in items if i["problem"] not in done][: args.limit or None]
    if args.detach:
        cmd = [sys.executable, __file__, "run", "--tag", tag, *sys.argv[sys.argv.index("run") + 1:]]
        cmd = [c for c in cmd if c != "--detach"]
        log = open(RESULTS / f"{tag}.log", "a")
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
        (RESULTS / f"{tag}.pid").write_text(str(p.pid))
        print(f"detached pid {p.pid}: {len(items)} item(s) -> {out.relative_to(ROOT)} (log {tag}.log)")
        return 0
    print(f"tag {tag}: {len(items)} item(s) on split {args.split}; results -> {out.relative_to(ROOT)}", flush=True)
    taken = taken_aliases()
    infra_streak = 0
    for i in items:
        live = subprocess.run(["pgrep", "-f", "harness.py run"], capture_output=True, text=True).stdout.split()
        if live and not args.allow_concurrent and not args.dry_run:
            print(f"refusing to start #{i['problem']}: a lane is live (pids {live}); CLAUDE.md says one lane at a time. "
                  f"Resume later with the same --tag.")
            return 2
        rec, ctx = run_item(i, tag, proto, args, taken)
        if rec.get("dry_run"):
            continue
        waits = 0
        while rec.get("infrastructure") and (rec.get("usage_limit") or discovery_limited(ctx)) and waits < args.limit_waits:
            # The account's usage limit is shared by every lane: waiting it out and continuing the same run costs
            # nothing, whereas stopping the lane threw away every in-flight run (all four lanes, 2026-09-24).
            with (RESULTS / f"{tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps({**rec, "handled": "waited for the usage limit"}, ensure_ascii=False) + "\n")
            try:
                fatal = (Path(ctx["run_dir"]) / f"DONE").read_text()
            except OSError:
                fatal = rec.get("infrastructure") or ""
            wait = seconds_until_reset(fatal)
            waits += 1
            print(f"#{i['problem']}: usage limit; waiting {wait / 60:.0f} min, then "
                  f"{'resuming in place' if harness_started(Path(ctx['run_dir'])) and not discovery_limited(ctx) else 'restarting'}",
                  flush=True)
            time.sleep(wait)
            if harness_started(Path(ctx["run_dir"])) and not discovery_limited(ctx):
                rec = launch(i, tag, proto, args, ctx)
            else:
                rec, ctx = run_item(i, tag, proto, args, taken)
            rec["limit_waits"] = waits
        if rec.get("infrastructure"):
            # A provider failure (usage limit, expired login) or a wall-clock kill is not a mathematical outcome: it
            # is logged beside the results, never in them, so resuming the tag retries the item.
            with (RESULTS / f"{tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            infra_streak += 1
            print(f"#{i['problem']}: INFRASTRUCTURE ({rec['infrastructure']}); not recorded as a result", flush=True)
            if infra_streak >= 2:
                print("two infrastructure failures in a row: stopping (usage limit or login?); resume with the same --tag")
                return 1
            continue
        infra_streak = 0
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{i['problem']}: solved={rec['solved']} contradiction={rec['contradiction']} spend={rec['spend']} "
              f"({rec['run_dir']})", flush=True)
    return 0


def run_item(item: dict, tag: str, proto: dict, args, taken: set[int]) -> dict:
    """One problem under the fixed protocol: a fresh alias (so no programs/ state carries over between
    evaluations), both directions, masked prompts, no web, benchmark mode (writes no knowledge)."""
    mask = json.loads((ROOT / item["mask"]["file"]).read_text())
    alias = alias_for(item["problem"], tag, taken)
    statement = re.sub(rf"\berdos_{mask['alias_id']}\b", f"erdos_{alias}", mask["statement_lean"])
    prob = {"id": str(alias), "statement": mask["statement_en"], "tags": mask.get("tags") or [], "imports": mask["imports"],
            "benchmark": {"kind": "time-split", "reference": "withheld (benchmarks/timesplit/pool.json)"}}
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-timesplit-erdos{alias}"
    run_dir.mkdir(parents=True)
    pfile = run_dir / "problem.json"          # per evaluation, inside the (gitignored) run dir, never in the tree
    pfile.write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    discovery, committed, budget, guidance_file = None, None, args.budget, None
    if getattr(args, "candidate", None) in ("discover-v1", "discover-v2", "discover-v3", "discover-v4", "alloc") and not args.dry_run:
        discovery = discover(item, statement, run_dir, args)
        budget = round(max(args.budget - discovery["spend"], 1.0), 2)       # the same $8 in total as the baseline
        committed = discovery["commit"]
        if committed == "neg":
            import harness as H
            neg = negated_statement(statement)
            res = H.LeanChecker(H.FORMAL, 900).check(H.compose(neg, mask["imports"]), run_dir / "negated-check.lean")
            if res.get("ok"):
                statement = neg
            else:                                                            # cannot state it: attack both ways
                committed = None
                discovery["negation_failed"] = [str(e)[:200] for e in res.get("errors", [])][:2]
        if discovery["guidance"]:
            guidance_file = ROOT / "atlas-data" / "research-guidance" / f"{alias}.md"
            guidance_file.write_text(discovery["guidance"])
    state = {"statement": statement, "problem_input": prob, "mode": "research", "invocations": [], "benchmark": True,
             "mode_reason": "time-split benchmark: a problem resolved after the model's training data, attacked as open"}
    if args.literature == "off":
        state["literature"] = ""
    (run_dir / "state.json").write_text(json.dumps(state, indent=2, ensure_ascii=False))
    # No MASK.json in the run dir: the agentic prover's sandbox is run_dir/sandbox/<name>, two levels below it,
    # and its reads are bounded by instruction, not by permission. The alias map lives with the results.
    with (RESULTS / f"{tag}.aliases.jsonl").open("a") as f:
        f.write(json.dumps({"alias": alias, "problem": item["problem"], "run_dir": str(run_dir.relative_to(ROOT))}) + "\n")
    cmd = [sys.executable, str(harness_file(args)), "run", "--problem", str(pfile), "--resume", str(run_dir),
           "--mode", "research", "--allow-research", "--benchmark", "--masked", *([] if committed else ["--open"]),
           "--no-brief", "--research-loop", "deductive", "--run-budget", str(budget),
           "--research-cycles", str(args.research_cycles),
           "--hyps-per-cycle", str(args.hyps_per_cycle), "--lean-timeout", str(args.lean_timeout),
           "--backend", "claude-cli", "--model", args.model] + (["--skip-literature"] if args.literature == "off" else [])
    cmd += candidate_flags(args)
    if getattr(args, "dry_run", False):
        if guidance_file and guidance_file.exists():
            guidance_file.unlink()
        print("dry run, not launched:\n  " + " ".join(cmd) + f"\n  run dir {run_dir.relative_to(ROOT)} (remove it by hand)")
        return {"problem": item["problem"], "dry_run": True, "run_dir": str(run_dir.relative_to(ROOT)), "command": cmd}, None
    if guidance_file and guidance_file.exists():                 # launch() installs it for each (re)launch
        guidance_file.unlink()
    env_extra = {"ERDOS_COMPILE_WORKERS": str(args.compile_workers)}
    if getattr(args, "knowledge", None):
        env_extra["ERDOS_KNOWLEDGE"] = str((ROOT / args.knowledge).resolve())
    ctx = {"cmd": cmd, "env": env_extra, "run_dir": str(run_dir), "alias": alias, "committed": committed,
           "discovery": discovery, "launches": 0}
    (run_dir / "launch.json").write_text(json.dumps({k: v for k, v in ctx.items() if k != "discovery"}, indent=1))
    return launch(item, tag, proto, args, ctx), ctx


def launch(item: dict, tag: str, proto: dict, args, ctx: dict) -> dict:
    """(Re)run the harness on a prepared run dir and score it. A relaunch is `--resume` on the same dir: the harness
    continues from its checkpoint and its spend accounting already holds what the interrupted launch spent."""
    run_dir, alias, committed, discovery = Path(ctx["run_dir"]), ctx["alias"], ctx["committed"], ctx["discovery"]
    ctx["launches"] += 1
    if ctx["launches"] > 1 and (run_dir / "DONE").exists():      # keep the interrupted launch's verdict for the record
        (run_dir / "DONE").replace(run_dir / f"DONE.launch{ctx['launches'] - 1}")
    guidance_file = None
    if discovery and discovery.get("guidance"):
        guidance_file = ROOT / "atlas-data" / "research-guidance" / f"{alias}.md"
        guidance_file.write_text(discovery["guidance"])
    started = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    killed = False
    try:
        with (run_dir / "lane.log").open("a") as log:
            proc = subprocess.Popen(ctx["cmd"], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                    env=dict(os.environ, **ctx["env"]), start_new_session=True)
            try:
                rc = proc.wait(timeout=args.item_hours * 3600)
            except subprocess.TimeoutExpired:
                killed = True
                os.killpg(proc.pid, 9)                  # the harness's own group ...
                rc = proc.wait()
                # ... but each Lean check runs in its own session, and orphans have outlived a run by 7 h (CLAUDE.md)
                for pat in (str(run_dir), f"erdos_{alias}"):
                    subprocess.run(["pkill", "-9", "-f", pat], capture_output=True)
    finally:
        if guidance_file and guidance_file.exists():             # nothing synthetic stays in the Atlas
            guidance_file.replace(run_dir / "guidance.md")
    rec = score_run(run_dir, str(alias), bool(item["answer"]), committed)
    if discovery:
        rec["spend"] = round((rec["spend"] or 0.0) + discovery["spend"], 2)
        rec["discovery"] = {k: v for k, v in discovery.items() if k != "guidance"}
        rec["committed"] = committed
    elif (run_dir / "discovery.json").exists():
        # in-run discovery (`--discover on`): its calls are in the harness's own log, so rec["spend"] already holds
        # them; a commit happened inside run_open, so the record reads both pos/ and neg/ as an --open run does
        try:
            dj = json.loads((run_dir / "discovery.json").read_text())
            rec["discovery"] = {"in_run": True, "decision": dj.get("decision"), "refereed_complete": dj.get("refereed_complete"),
                                "rounds": dj.get("rounds"), "spend": dj.get("spend")}
            rec["committed_in_run"] = (dj.get("decision") or {}).get("commit")
        except (OSError, ValueError):
            pass
    try:
        done = json.loads((run_dir / "DONE").read_text())
    except (OSError, ValueError):
        done = {}
    fatal = str(done.get("fatal") or "")
    infra = (f"killed after {args.item_hours} h" if killed else
             f"exit {rc}" + (f", fatal: {fatal[:160]}" if fatal else "")
             if rc == 1 or fatal else None)
    # Under --open a direction can die (a usage limit mid-program) while the other finishes, and the parent then
    # exits 3, not 1: #435 and baseline #537 were recorded as results although a direction had died on the limit.
    lost = lost_directions(done)
    if lost and not infra:
        infra = f"direction(s) {', '.join(sorted(lost))} died: {' | '.join(lost.values())[:200]}"
    out = {"problem": item["problem"], "tag": tag, "alias": alias, "run_dir": str(run_dir.relative_to(ROOT)),
           "answer": item["answer"], "split": item["split"], "started": started, "returncode": rc,
           "infrastructure": infra, "usage_limit": bool(LIMIT_RE.search(fatal) or LIMIT_RE.search(" ".join(lost.values()))),
           "lost_directions": sorted(lost), "launches": ctx["launches"], **rec, "protocol": proto}
    if not infra:                    # measured now, before anything can resume the run dir and move its program on
        try:
            record_progress(out, tag)
        except Exception as e:       # noqa: BLE001 - the measurement must never cost the lane its result
            print(f"#{item['problem']}: progress not measured ({type(e).__name__}: {e}); run `progress --tag {tag}`",
                  flush=True)
    return out


LIMIT_RE = re.compile(r"hit your (?:session |usage |weekly )?limit|usage limit|rate limit|overloaded", re.I)
# "resets 8:10am", and the weekly limit's dated form "resets Oct 13 at 9am (America/Toronto)". Until 2026-10-13 only the
# first was read: the dated reset fell back to a 30-minute wait, so during a four-day weekly limit every screen retried
# for two hours, failed, and cost the campaign ten problems that were never screened.
RESET_RE = re.compile(r"resets\s+(?:(?P<mon>Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\.?\s+(?P<day>\d{1,2})"
                      r"(?:,\s*\d{4})?\s+(?:at\s+)?)?(?P<h>\d{1,2})(?::(?P<m>\d{2}))?\s*(?P<ap>[ap]m)"
                      r"(?:\s*\((?P<tz>[A-Za-z]+(?:/[A-Za-z_]+)+)\))?", re.I)
_MONTHS = ("jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec")


def seconds_until_reset(text: str, now: datetime | None = None, cap_hours: float = 6.0) -> float:
    """Seconds to wait for the provider's stated reset, plus a margin; 30 min if none is stated. A dated reset ("resets
    Oct 13 at 9am") is waited for to that day, up to `cap_hours`. The stated zone is used when `now` is aware or absent;
    a naive `now` is read in the reset's own zone, as before."""
    from datetime import timedelta
    from zoneinfo import ZoneInfo
    m = RESET_RE.search(text or "")
    if not m:
        return 1800.0
    try:
        tz = ZoneInfo(m.group("tz")) if m.group("tz") else None
    except Exception:                                    # noqa: BLE001 - an unknown zone name: read the time locally
        tz = None
    if now is None:
        now = datetime.now(tz) if tz else datetime.now()
    elif now.tzinfo is not None and tz is not None:
        now = now.astimezone(tz)
    hour = int(m.group("h")) % 12 + (12 if m.group("ap").lower() == "pm" else 0)
    target = now.replace(hour=hour, minute=int(m.group("m") or 0), second=0, microsecond=0)
    if m.group("mon"):
        try:
            target = target.replace(month=_MONTHS.index(m.group("mon").lower()[:3]) + 1, day=int(m.group("day")))
        except ValueError:
            return 1800.0
        if (now - target).days > 180:                    # "resets Jan 2" read on Dec 31
            target = target.replace(year=target.year + 1)
        if target <= now:
            target = now
    elif target <= now:
        target = target + timedelta(days=1) if (now - target).total_seconds() > 3600 else now
    return min((target - now).total_seconds() + 180.0, cap_hours * 3600)


def harness_started(run_dir: Path) -> bool:
    """Did the harness get past its first stage? If so a relaunch resumes it; if not, the item restarts fresh."""
    try:
        state = json.loads((run_dir / "state.json").read_text())
    except (OSError, ValueError):
        return False
    return bool(state.get("literature") or (run_dir / "pos").exists() or (run_dir / "neg").exists()
                or (ROOT / "programs" / f"erdos_{run_dir.name.split('erdos')[-1]}").exists())


def discovery_limited(ctx: dict) -> bool:
    """A usage limit that struck the discovery stage leaves it degraded, so the item must restart, not resume."""
    d = (ctx or {}).get("discovery") or {}
    try:
        attempts = json.loads((Path(ctx["run_dir"]) / "discovery.json").read_text()).get("attempts", [])
    except (OSError, ValueError, KeyError, TypeError):
        attempts = []
    return bool(d) and any(LIMIT_RE.search(str(a.get("error") or "")) for a in attempts)


# ---------------------------------------------------------------- scoring ---------------------------------------------

def audit_run(run_dir: Path) -> dict:
    """`audit.py` on a run whose direction verified. `solved` needs its Lean checks to pass: the harness's own
    verification matches the frozen statement's TEXT, and a redefined `<` proves `(3 : ℕ) < 2` under a verbatim
    frozen theorem (tests/test_audit.py). The direction check is left out of `lean_ok` on purpose: a verified
    proof of the wrong direction must still reach `contradiction`, where it is re-audited, never counted."""
    sys.path.insert(0, str(ROOT))
    try:
        import audit as AU
        rep = AU.audit(run_dir)
    except Exception as e:                                  # noqa: BLE001 - an unauditable proof is not a solve
        return {"verdict": "ERROR", "lean_ok": False, "failed": [f"{type(e).__name__}: {str(e)[:200]}"]}
    reps = rep.get("all") or [rep]
    failed = sorted({k for r in reps for k, c in (r.get("checks") or {}).items() if c.get("ok") is not True})
    return {"verdict": rep.get("verdict"), "failed": failed,
            "lean_ok": not [k for k in failed if k != "direction_matches_answer"]}


def score_run(run_dir: Path, alias: str, answer: bool, committed: str | None = None) -> dict:
    """Outcome of one run against the known answer: an --open run (pos/ and neg/ children), or a run committed to
    one direction (its own state at the root; the other direction reads as not attempted).

    `solved`: the TRUE direction closed and passed every mechanical gate: compiles, sorry-free, frozen match,
    standard axioms, nothing banned. The run's own faithfulness judge is recorded but not required: each item's P was
    judged faithful when the benchmark was built, the frozen match pins the proof to P or its negation, and a run
    committed to NO has no direction for its judge to read (`direction` is set only by --open), so requiring it
    would score the two protocols differently. A verified proof of the FALSE direction is a `contradiction`: re-audit
    the item, never count it. The dense fields are reported beside the primary metric, never folded into it."""
    import harness as H
    facts = H.collect_run_facts(run_dir, alias)
    dirs = {}
    for d in ("pos", "neg"):
        path = (run_dir / "state.json") if committed == d else (run_dir / d / "state.json")
        try:
            s = json.loads(path.read_text()) if (committed in (None, d)) else {"outcome": "not attempted"}
        except (OSError, ValueError):
            s = {}
        v = s.get("verify") or {}
        clean = bool(s.get("outcome") in ("proved", "proved_unverified") and v.get("compiles") and v.get("sorry_free")
                     and v.get("frozen_match") and v.get("axioms_clean") and not v.get("banned"))
        res = s.get("residual") or {}
        dirs[d] = {"outcome": s.get("outcome"), "verified": clean, "certified": res.get("certified", 0),
                   "open": res.get("open"), "published": res.get("published", 0),
                   # every conjecture discharged, only cited theorems left open: not a solve, but the state the train
                   # diagnostic #997 nearly reached (one bridge lemma short, on a published premise)
                   "modulo_published": bool(res and res.get("open") == 0 and (res.get("published") or 0) > 0 and not clean),
                   "believed_false": bool(s.get("target_believed_false")),
                   "judge_faithful": (v.get("faithful") or {}).get("faithful") if isinstance(v.get("faithful"), dict) else None,
                   "stop_reason": str(s.get("stop_reason") or "")[:240]}
    true_d, false_d = ("pos", "neg") if answer else ("neg", "pos")
    audited = audit_run(run_dir) if (dirs[true_d]["verified"] or dirs[false_d]["verified"]) else None
    lean_ok = bool(audited and audited["lean_ok"])
    return {"solved": dirs[true_d]["verified"] and lean_ok, "contradiction": dirs[false_d]["verified"] and lean_ok,
            "audit": audited,
            "true_certified": dirs[true_d]["certified"], "true_modulo_published": dirs[true_d]["modulo_published"],
            "true_open": dirs[true_d]["open"], "false_stopped": dirs[false_d]["believed_false"],
            "true_abandoned": dirs[true_d]["believed_false"], "directions": dirs,
            "exit": facts.get("exit"), "fatals": facts.get("fatals"), "spend": round(facts.get("spend") or 0.0, 2),
            "cost_known": facts.get("cost_known"), "llm_calls": facts.get("llm_calls"), "lean_checks": facts.get("lean_checks")}


# ---------------------------------------------------------------- dense progress -------------------------------------
# Solves are the verdict, and at $8 they are rare: three arms and 20 dev runs produced none, so a solve-only gate
# cannot tell a better harness from a worse one. `pieces` counts what a run certified toward the TRUE direction's
# proof, with three guards against a lemma count that grows while the proof gets no closer:
#   closed       nothing the hypothesis rests on is open. A refinement whose sub-hypotheses are still open has no hole
#                of its own, so the harness's `certified` counts it; here it counts only once they are closed too.
#   used         the frozen theorem's proof reaches it.
#   non-trivial  the free tactic cascade (the harness's own, plus `exact?`) does not close it in isolation, with the
#                skeleton's definitions and `open`s in scope.
# Only MAXIMAL closed hypotheses count: those the frozen theorem reaches without passing through another closed one.
# So the way a prover structured a proof internally cannot change the score. A step proved through three certified
# sub-lemmas is one piece, the same as a step proved in one go. `closed_lemmas` counts every closed, used,
# non-trivial hypothesis at any depth, for reference. The count still depends on how the PLAN chunks the argument,
# which README.md names as the metric's known bias.

# 2: `certified_size`, and the comparison needs pieces AND size to call an item.
# 3: triviality is checked under full `import Mathlib`. A run's harness adds modules as it goes (unknown identifier ->
#    import), so the problem file's imports left v2 #419's `Real.logb` unknown and every statement unjudged.
PROGRESS_VERSION = 3
# The pinned harness's `CASCADE` plus `exact?`, frozen here so that the instrument does not move when a candidate
# harness changes its own cascade. Every alternative must CLOSE the goal: in the harness's own string a `simp_all` or
# `norm_num` that only simplifies counts as success for `first`, so the tactics after it never run (checked in Lean:
# `0 ≤ x * x + x + 0` with `0 ≤ x` fails there, and `positivity` closes it here).
FREE_TACTICS = ("first | omega | (simp_all; done) | positivity | (norm_num; done) | nlinarith | (decide +kernel) "
                "| (aesop; done) | exact?")
FREE_HEARTBEATS = 400000
IDENT_RE = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
DECL_NAME_RE = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                          r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[⦃]+)")


def residual_structure(skeleton: str, alias, main: str, meta: dict | None = None) -> dict:
    """Which hypotheses of a residual skeleton are closed, used and maximal. This is text analysis only; the compiler
    already accepted the skeleton when the harness adopted it.

    Every named declaration gets a qualified name from its enclosing namespaces (a spliced proof sits in `<name>_ns`,
    and a refinement nests them), and an edge to each skeleton declaration its text names. Names resolve the way Lean
    looks them up, innermost namespace first. A hypothesis name that does not resolve still gets an edge to every
    declaration with that short name, so a missed lookup can make a hypothesis look open, but never closed."""
    import harness as H
    decls: dict[str, dict] = {}
    stack: list[list[str]] = []
    for block in H.split_decls(skeleton):
        text = H.strip_comment_lines(block)
        head = text.strip()
        first = head.split("\n", 1)[0].strip()
        if re.match(r"namespace\s+\S", first):
            stack.append(first.split()[1].split("."))
            continue
        if re.match(r"(?:noncomputable\s+)?section\b", first):
            stack.append([])
            continue
        if re.match(r"end\b", first):
            if stack:
                stack.pop()
            continue
        m = DECL_NAME_RE.match(head)
        if not m:
            continue
        path = [c for comp in stack for c in comp]
        decls[".".join(path + [m.group(1)])] = {
            "path": path, "short": m.group(1).split(".")[-1], "holes": H.hole_count(block),
            "tokens": set(IDENT_RE.findall(text)), "published": bool(re.search(r"--\s*PUBLISHED:", block)),
            # certified size: non-whitespace characters outside comments; the problem's own top-level defs count nothing
            "size": 0 if (not path and H.DEF_HEAD_RE.match(head)) else len(re.sub(r"\s", "", text))}

    def resolve(tok: str, path: list[str]) -> str | None:
        parts = tok.split(".")
        for k in range(len(parts), 0, -1):          # the longest prefix naming a declaration: `foo.le`, `h_ns.h.trans`
            for i in range(len(path), -1, -1):
                q = ".".join(path[:i] + parts[:k])
                if q in decls:
                    return q
        return None

    by_short: dict[str, list[str]] = {}
    for q, d in decls.items():
        by_short.setdefault(d["short"], []).append(q)
    edges = {}
    for q, d in decls.items():
        out = set()
        for tok in d["tokens"]:
            r = resolve(tok, d["path"])
            if r:
                out.add(r)
            elif "_hyp_" in tok:
                out.update(by_short.get(tok.split(".")[-1], ()))
        out.discard(q)
        edges[q] = out

    def reach(start: str, stop=None) -> set[str]:
        seen, todo = set(), [start]
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.add(q)
            if stop is not None and q != start and stop(q):
                continue
            todo.extend(edges.get(q, ()))
        return seen

    hyp_re = re.compile(rf"erdos_{alias}(?:_neg)?_hyp_[A-Za-z0-9_'!?]+$")
    # a hypothesis, not the copy of its proof that `splice_hypothesis` keeps inside `<name>_ns`
    hyps = {q for q, d in decls.items() if hyp_re.match(d["short"]) and not (d["path"] and d["path"][-1] == d["short"] + "_ns")}
    # A glue that calls the proof copy directly (`exact h_ns.h n a hn`, as baseline #204's does) uses the hypothesis:
    # every edge to a copy goes to its hypothesis instead, except the hypothesis's own edge to its copy.
    owner = {}
    for q, d in decls.items():
        if d["path"] and d["path"][-1] == d["short"] + "_ns":
            h = ".".join(d["path"][:-1] + [d["short"]])
            if h in hyps:
                owner[q] = h
    edges = {q: {owner[t] if t in owner and owner[t] != q else t for t in out} - {q} for q, out in edges.items()}
    closed = {h for h in hyps if all(decls[q]["holes"] == 0 for q in reach(h))}
    kinds = {h["name"]: h["kind"] for h in H.parse_residual(skeleton, alias, meta, main)["hypotheses"]}
    present = main in decls
    used = reach(main) if present else set()
    maximal = (reach(main, stop=lambda q: q in closed) & closed) if present else set()
    short = lambda qs: sorted(decls[q]["short"] for q in qs)
    open_used = {q for q in used & hyps if decls[q]["holes"]}
    published = {q for q in open_used if decls[q]["published"] or kinds.get(decls[q]["short"]) == "published"}
    support = {decls[h]["short"]: sorted(reach(h)) for h in closed & used}
    return {"main_present": present, "maximal": short(maximal), "closed_used": short(closed & used),
            "unused_closed": short(closed - used), "open_conjectures": short(open_used - published),
            "open_published": short(published), "harness_certified": sum(1 for h in hyps if not decls[h]["holes"]),
            "support": support, "sizes": {q: decls[q]["size"] for qs in support.values() for q in qs}}


def statement_context(H, skeleton: str, pos: int) -> list[str]:
    """The defs and top-level `open`s in force at `pos`: the pinned harness's `skeleton_context`, kept here because
    the live harness predates its `open` fix and the instrument must not depend on which harness is live."""
    blocks = H.split_decls(H.visible_text(skeleton, pos))
    is_def = [bool(H.DEF_HEAD_RE.match(H.strip_comment_lines(d).lstrip("\n"))) for d in blocks]
    out = []
    for k, d in enumerate(blocks):
        s = H.strip_comment_lines(d).strip()
        if is_def[k]:
            out.append(d)
        elif re.match(r"open\s", s) and (not re.search(r"\bin$", s) or (k + 1 < len(blocks) and is_def[k + 1])):
            out.append(d)
    return out


def free_closable(H, checker, skeleton: str, names: list[str], imports: list[str], retry: bool = True) -> dict[str, str]:
    """For each hypothesis name: 'trivial' when the free cascade closes it in isolation, 'nontrivial' when it does not,
    'context_error' when the statement does not elaborate on its own (so the cascade result means nothing), and
    'unknown' when Lean timed out or failed without an attributable message.

    One Lean process checks them all, because the Mathlib import dominates a check. Each statement is checked twice,
    as an `example` so that nothing enters the environment. Had they been theorems, `exact?` could close one statement
    with an earlier sorry'd or failed copy, which Lean keeps as a declaration."""
    verdict: dict[str, str] = {}
    parts = []
    for k, name in enumerate(names):
        span = H.hypothesis_span(skeleton, name)
        blk = skeleton[span[0]:span[1]].rstrip() if span else ""
        idx = blk.find(":= by")
        idx = blk.rfind(":=") if idx == -1 else idx
        if idx == -1:
            verdict[name] = "context_error"
            continue
        head = re.sub(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+\S+", "example", blk[:idx].rstrip())
        ctx = "\n\n".join(statement_context(H, skeleton, span[0]))
        parts.append(f"-- TS-CTX {k}\nnamespace TSC{k}\n\n{ctx}\n\n{head} := by\n  sorry\n\nend TSC{k}")
        parts.append(f"-- TS-FREE {k}\nnamespace TSF{k}\n\n{ctx}\n\nset_option maxHeartbeats {FREE_HEARTBEATS} in\n"
                     f"{head} := by\n  {FREE_TACTICS}\n\nend TSF{k}")
    todo = [n for n in names if n not in verdict]
    if not todo:
        return verdict
    src = H.compose("\n\n".join(parts), list(imports))
    starts = sorted((ln, kind, int(k)) for ln, line in enumerate(src.splitlines(), 1)
                    for kind, k in [m.groups() for m in [re.match(r"-- TS-(CTX|FREE) (\d+)$", line)] if m])
    tag = hashlib.sha256(src.encode()).hexdigest()[:10]
    res = checker.check(src, ROOT / "runs" / "adhoc" / f"timesplit-free-{tag}.lean")
    bad: set[tuple[str, int]] = set()
    stray = res.get("timeout") or (not res.get("ok") and not res.get("errors"))
    for e in [] if res.get("timeout") else res.get("errors", []):
        m = re.match(r"line (\d+):", str(e))
        owner = [(kind, k) for ln, kind, k in starts if m and ln <= int(m.group(1))]
        if owner:
            bad.add(owner[-1])
        else:
            stray = True
    if stray:
        if retry and len(todo) > 1:                  # isolate the statement that hung or broke the file
            for n in todo:
                verdict.update(free_closable(H, checker, skeleton, [n], imports, retry=False))
        else:
            verdict.update({n: "unknown" for n in todo})
        return verdict
    for k, name in enumerate(names):
        if name not in verdict:
            verdict[name] = ("context_error" if ("CTX", k) in bad else "nontrivial" if ("FREE", k) in bad else "trivial")
    return verdict


def residual_file(alias, direction: str, committed: str | None) -> Path | None:
    """Where a direction's residual lives: the program root for a run committed to one direction, `<direction>/`
    under it for an --open run. None when a committed run never attacked `direction`."""
    prog = ROOT / "programs" / f"erdos_{alias}"
    if committed:
        return prog / "Residual.lean" if committed == direction else None
    return prog / direction / "Residual.lean"


def progress_of(run_dir: Path, alias, answer: bool, committed: str | None = None, checker=None,
                check: bool = True) -> dict:
    """The dense progress of one run toward the TRUE direction (see the section comment). `check=False` skips the
    Lean triviality pass and reports the structure only; such a record never enters a comparison."""
    import harness as H
    true_d = "pos" if answer else "neg"
    out = {"version": PROGRESS_VERSION, "direction": true_d, "pieces": 0, "closed_lemmas": 0, "certified_size": 0,
           "checked": check}
    path = residual_file(alias, true_d, committed)
    if path is None:
        return {**out, "attempted": False}
    if not path.exists():
        return {**out, "attempted": True, "skeleton": None}
    skeleton = path.read_text()
    try:
        state = json.loads(((run_dir / "state.json") if committed else (run_dir / true_d / "state.json")).read_text())
    except (OSError, ValueError):
        state = {}
    main = f"erdos_{alias}_neg" if (true_d == "neg" and not committed) else f"erdos_{alias}"
    st = residual_structure(skeleton, alias, main, (state.get("residual") or {}).get("meta"))
    verdict = {}
    if check and st["closed_used"]:
        # all of Mathlib: the run's own header grew as it went, and a lemma anywhere in Mathlib is free
        verdict = free_closable(H, checker or H.LeanChecker(H.FORMAL, 1200), skeleton, st["closed_used"], ["Mathlib"])
    pieces = [n for n in st["maximal"] if verdict.get(n) != "trivial"]
    closed = [n for n in st["closed_used"] if verdict.get(n) != "trivial"]
    under = set().union(*(st["support"][n] for n in pieces)) if pieces else set()
    return {**out, "attempted": True, "skeleton": str(path.relative_to(ROOT)),
            "skeleton_sha": hashlib.sha256(skeleton.encode()).hexdigest()[:12], "main_present": st["main_present"],
            "pieces": len(pieces), "piece_names": pieces, "closed_lemmas": len(closed),
            "certified_size": sum(st["sizes"][q] for q in under),
            "trivial": sorted(n for n, v in verdict.items() if v == "trivial"),
            "unknown": sorted(n for n, v in verdict.items() if v in ("unknown", "context_error")),
            "unused_closed": st["unused_closed"], "open_conjectures": st["open_conjectures"],
            "open_published": st["open_published"], "harness_certified": st["harness_certified"]}


def record_progress(rec: dict, tag: str, checker=None, check: bool = True) -> dict:
    """Measure a result record's progress, snapshot both directions' residuals under results/residuals/<tag>/ (a later
    resume of the same run dir, as a top-up does, rewrites the program in place), and append the measurement to
    results/<tag>.progress.jsonl. Append-only, so a live lane appending results to <tag>.jsonl never races it."""
    run_dir = ROOT / rec["run_dir"]
    p = progress_of(run_dir, rec["alias"], bool(rec["answer"]), rec.get("committed"), checker, check)
    recorded = (rec.get("directions") or {}).get(p["direction"]) or {}
    # counts as of the record, against the file measured now: a mismatch means the program moved on after the record
    p["stale"] = bool(p.get("skeleton") and recorded.get("certified") is not None
                      and recorded.get("certified") != p.get("harness_certified"))
    snap = RESULTS / "residuals" / tag
    for d in ("pos", "neg"):
        src = residual_file(rec["alias"], d, rec.get("committed"))
        if src is not None and src.exists():
            snap.mkdir(parents=True, exist_ok=True)
            (snap / f"{rec['problem']}-{d}.lean").write_text(src.read_text())
    with (RESULTS / f"{tag}.progress.jsonl").open("a") as f:
        f.write(json.dumps({"problem": rec["problem"], "run_dir": rec["run_dir"],
                            "computed": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "progress": p},
                           ensure_ascii=False) + "\n")
    return p


def load_progress(tag: str) -> dict[tuple[str, str], dict]:
    """(problem, run_dir) -> the latest checked measurement of that run."""
    path = RESULTS / f"{tag}.progress.jsonl"
    out = {}
    for line in path.read_text().splitlines() if path.exists() else []:
        if line.strip():
            r = json.loads(line)
            if r["progress"].get("checked") and r["progress"].get("version") == PROGRESS_VERSION:
                out[(r["problem"], r["run_dir"])] = r["progress"]
    return out


def sign_test_greater(w: int, l: int) -> float:
    """One-sided exact sign test: P(at least `w` wins of `w + l` untied pairs | no difference)."""
    n = w + l
    return 1.0 if n == 0 else sum(math.comb(n, k) for k in range(w, n + 1)) / 2 ** n


def dense_outcome(ra: dict, rb: dict) -> str:
    """'W', 'L' or 'T' for run A against run B on the same item. A solve outranks any partial result. Between two
    unsolved runs, a win needs MORE pieces AND a larger certified size. A plan that chunks the same argument finer
    raises pieces but not size, and a more verbose proof raises size but not pieces, so neither alone moves the call."""
    if ra["solved"] != rb["solved"]:
        return "W" if ra["solved"] else "L"
    if ra["solved"]:
        return "T"
    pa, pb = ra["progress"], rb["progress"]
    if pa["pieces"] > pb["pieces"] and pa["certified_size"] > pb["certified_size"]:
        return "W"
    if pa["pieces"] < pb["pieces"] and pa["certified_size"] < pb["certified_size"]:
        return "L"
    return "T"


def dense_compare(a: dict[str, dict], b: dict[str, dict]) -> dict:
    """Paired comparison on `dense_outcome`, with a one-sided exact sign test. Pairs where either run lacks a checked
    measurement of the current version are left out and listed. `pieces_only` is the naive count comparison, printed
    so that a verdict resting on chunking alone is visible."""
    common = sorted(set(a) & set(b), key=int)
    rated = [p for p in common if a[p].get("progress") and b[p].get("progress")
             and not a[p].get("lost_directions") and not b[p].get("lost_directions")]
    calls = {p: dense_outcome(a[p], b[p]) for p in rated}
    wins = [p for p in rated if calls[p] == "W"]
    losses = [p for p in rated if calls[p] == "L"]
    naive = lambda r: (bool(r["solved"]), r["progress"]["pieces"])
    diff = [a[p]["progress"]["pieces"] - b[p]["progress"]["pieces"] for p in rated]
    return {"pairs": len(rated), "unmeasured": [p for p in common if p not in rated],
            "lost_a_direction": [p for p in common if a[p].get("lost_directions") or b[p].get("lost_directions")],
            "wins": wins, "losses": losses,
            "ties": len(rated) - len(wins) - len(losses), "p_one_sided": round(sign_test_greater(len(wins), len(losses)), 4),
            "pieces_only": {"wins": [p for p in rated if naive(a[p]) > naive(b[p])],
                            "losses": [p for p in rated if naive(a[p]) < naive(b[p])]},
            "pieces_mean_delta": round(sum(diff) / len(diff), 3) if diff else None,
            "certified_size_delta": sum(a[p]["progress"]["certified_size"] - b[p]["progress"]["certified_size"] for p in rated),
            "closed_lemmas_delta": sum(a[p]["progress"]["closed_lemmas"] - b[p]["progress"]["closed_lemmas"] for p in rated)}


# ---------------------------------------------------------------- idea hits -----------------------------------------
# `pieces` counts only what Lean certified, so an informal leap scores nothing until it is formalised. For a time-split
# item the published route is known. A blind judge compares what a run THOUGHT (its exploration notebooks, informal
# attempts, plan notes and final hypotheses) with a reference note on the resolution's key idea. The note lives in
# ideas/<n>.md, is written from the published record only, and is never shown to the harness. It exists for train
# items only, because dev and test solutions must not inform harness design.

IDEAS = HERE / "ideas"
IDEA_GRADES = {"hit": 2, "partial": 1, "miss": 0}

IDEA_JUDGE_PROMPT = """You are grading, blind, whether a research run found the KEY IDEA of a problem's published
resolution. You see the published idea (the reference) and the run's own notes. You do not know which system wrote
the notes. Give no credit for vague gestures or for naming a whole field.

PROBLEM:
{statement}

REFERENCE (the published resolution's key idea, and what counts as a hit):
{reference}

THE RUN'S NOTES (its computations, informal attempts, plan notes and the hypotheses of its final argument):
{material}

Grade exactly one of:
- "hit": the notes state the key idea concretely enough that a mathematician would recognise the published route
  (the same construction, the same cited theorem and how it is used, the same counting argument or reformulation),
  even if details are missing or the proof is incomplete.
- "partial": the notes point the right way (the right object, family or theorem) but miss the crux the reference
  names.
- "miss": neither.
Quote the one or two sentences of the notes your grade rests on.

End with exactly one ```json block: {{"grade": "hit" | "partial" | "miss", "evidence": "<a quote from the notes, or null>",
"why": "<one sentence>"}}"""


def idea_reference(problem: str) -> str | None:
    f = IDEAS / f"{problem}.md"
    if not f.exists():
        return None
    text = f.read_text()
    return None if re.search(r"\*\*Key idea:\*\*\s*route unknown", text, re.I) else text


def run_idea_material(rec: dict, limit: int = 14000) -> str:
    """Everything a run wrote down about the mathematics, most informal first, capped at `limit` characters."""
    import harness as H
    run_dir, alias = ROOT / rec["run_dir"], str(rec["alias"])
    prog = ROOT / "programs" / f"erdos_{alias}"
    parts: list[tuple[str, str]] = []
    for nb in sorted(run_dir.rglob("NOTEBOOK.md")) + sorted(prog.rglob("NOTEBOOK.md")):
        parts.append((f"EXPLORATION NOTEBOOK ({nb.parent.name})", nb.read_text()[-5000:]))
    disc = run_dir / "discovery.json"
    if disc.exists():
        d = json.loads(disc.read_text())
        for a in d.get("attempts") or []:
            if a.get("key_steps") or a.get("gap"):
                parts.append(("INFORMAL ATTEMPT", json.dumps({k: a.get(k) for k in ("answer", "key_steps", "gap")},
                                                             ensure_ascii=False)[:3000]))
        g = d.get("gap_attempt") or {}
        if g.get("text"):
            parts.append(("ATTACK ON THE MISSING STEP", g["text"][-3000:]))
    for res in sorted(prog.rglob("Residual.lean")):
        try:
            hyps = H.parse_residual(res.read_text(), alias)["hypotheses"]
        except Exception:                                  # noqa: BLE001 - material, not a gate
            continue
        if hyps:
            parts.append((f"FINAL HYPOTHESES ({res.parent.relative_to(prog)})",
                          "\n".join(f"- [{'open' if h['open'] else 'certified'}] {h['name']}: {h['statement'][:500]}"
                                    for h in hyps)))
    for exp in sorted(prog.rglob("experiments.txt"))[-2:]:
        parts.append((f"COMPUTATIONS ({exp.parent.name})", H.experiments_digest(exp.read_text(), 2500)))
    for plan in sorted(prog.rglob("PLAN.md")):
        parts.append((f"PLAN NOTES ({plan.parent.relative_to(prog)})", plan.read_text()[-4000:]))
    out, used = [], 0
    for title, body in parts:
        room = limit - used
        if room < 400:
            break
        chunk = f"=== {title} ===\n{body.strip()[:room - 40]}"
        out.append(chunk)
        used += len(chunk) + 2
    return "\n\n".join(out) or "(the run left no notes)"


def explore_screen(args) -> int:
    """The cheap screen for changes to the idea stages: on each item (train by default), the literature memo and ONE
    exploration session, with no Lean and no research loop, then the idea judge. Records go to results/<tag>.jsonl in
    the result-record shape, so `ideas --tag <tag>` grades them like full runs."""
    items = [i for i in load_pool()["items"] if i["split"] == args.split and (not args.items or i["problem"] in args.items)
             and (i.get("mask") or {}).get("ok")]
    done = set(load_results(args.tag))
    taken = taken_aliases()
    out = RESULTS / f"{args.tag}.jsonl"
    print(f"explore-screen {args.tag}: {len([i for i in items if i['problem'] not in done])} item(s)", flush=True)
    for item in items:
        if item["problem"] in done:
            continue
        mask = json.loads((ROOT / item["mask"]["file"]).read_text())
        alias = alias_for(item["problem"], f"explore-{args.tag}", taken)
        statement = re.sub(rf"\berdos_{mask['alias_id']}\b", f"erdos_{alias}", mask["statement_lean"])
        run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-explore-erdos{alias}"
        run_dir.mkdir(parents=True)
        prob = {"id": str(alias), "statement": mask["statement_en"], "tags": mask.get("tags") or [], "imports": mask["imports"],
                "benchmark": {"kind": "time-split", "reference": "withheld (benchmarks/timesplit/pool.json)"}}
        (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
        (run_dir / "state.json").write_text(json.dumps({"statement": statement, "problem_input": prob, "mode": "research",
                                                        "invocations": [], "benchmark": True}, indent=2, ensure_ascii=False))
        cmd = [sys.executable, str(harness_file(args)), "run", "--problem", str(run_dir / "problem.json"), "--resume",
               str(run_dir), "--mode", "research", "--allow-research", "--benchmark", "--masked", "--no-brief",
               "--stop-after", "explore", "--explore-budget", str(args.explore_budget), "--explore-effort",
               args.explore_effort, "--literature-scope", args.literature_scope, "--run-budget", str(args.explore_budget + 1.0),
               "--backend", "claude-cli", "--model", args.model]
        env = dict(os.environ, **({"ERDOS_KNOWLEDGE": str((ROOT / args.knowledge).resolve())} if args.knowledge else {}))
        for attempt in range(4):
            with (run_dir / "lane.log").open("a") as log:
                rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                    env=env, timeout=3 * 3600).returncode
            text = (run_dir / "lane.log").read_text(errors="replace")[-6000:]
            if rc != 1 or not LIMIT_RE.search(text):
                break
            wait = seconds_until_reset(text)                  # a usage limit: wait it out, then resume the same run dir
            print(f"#{item['problem']}: usage limit; waiting {wait / 60:.0f} min, then resuming", flush=True)
            time.sleep(wait)
        else:
            print(f"#{item['problem']}: still limited after 4 waits; not recorded (rerun the command)", flush=True)
            continue
        import harness as H
        facts = H.collect_run_facts(run_dir, str(alias))
        try:
            st = json.loads((run_dir / "state.json").read_text())
        except (OSError, ValueError):
            st = {}
        nb = ((st.get("exploration") or {}).get("notebooks") or [{}])[-1]
        rec = {"problem": item["problem"], "tag": args.tag, "alias": alias, "run_dir": str(run_dir.relative_to(ROOT)),
               "answer": item["answer"], "split": item["split"], "returncode": rc, "solved": False, "contradiction": False,
               "spend": round(facts.get("spend") or 0.0, 2), "verdict": (nb.get("verdict") or "")[:600],
               "scripts": len(nb.get("scripts") or []), "notebook_chars": len(nb.get("text") or ""),
               "protocol": {**protocol(args), "screen": "explore-only"}}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{item['problem']}: rc={rc} ${rec['spend']} scripts={rec['scripts']} verdict={rec['verdict'][:100]!r}", flush=True)
    return 0


def library_spec(item: dict, margin_days: int = 7) -> dict:
    """The cutoff and exclusions for an item's dated library: strictly before the resolution's first public date,
    minus a margin, and nothing that names the problem (its identity must not reach a masked run)."""
    from datetime import date, timedelta
    n = str(item["problem"])
    first = date.fromisoformat(str(item["first_public"])[:10])
    return {"cutoff": (first - timedelta(days=margin_days)).isoformat(),
            "exclude": [rf"erdosproblems\.com/(?:forum/thread/|latex/)?{n}\b", rf"Erd(?:ő|o|ö|\\H\{{o\}})s\s+problem\s*(?:#|no\.?|number)?\s*{n}\b",
                        rf"\bproblem\s*#\s*{n}\b"]}


def library_cmd(args) -> int:
    """Build each item's dated literature library (library.py) under benchmarks/timesplit/library/<n>/, from the
    item's MASKED statement. A library is an input to a run (`--library`), never a reference: unlike ideas/ it holds
    nothing published on or after the resolution."""
    import library as L
    items = [i for i in load_pool()["items"] if (not args.items or i["problem"] in args.items) and (i.get("mask") or {}).get("ok")
             and (args.items or i["split"] == args.split)]
    for item in items:
        out = HERE / "library" / str(item["problem"])
        if (out / "DIGEST.md").exists() and not args.redo:
            print(f"#{item['problem']}: library exists ({out.relative_to(ROOT)})", flush=True)
            continue
        mask = json.loads((ROOT / item["mask"]["file"]).read_text())
        spec = library_spec(item, args.margin_days)
        sfile = out / "statement.md"
        out.mkdir(parents=True, exist_ok=True)
        sfile.write_text(mask["statement_en"])
        argv = ["build", "--statement-file", str(sfile), "--cutoff", spec["cutoff"], "--out", str(out),
                "--papers", str(args.papers), "--model", args.model]
        for p in spec["exclude"]:
            argv += ["--exclude", p]
        print(f"#{item['problem']}: building, cutoff {spec['cutoff']} (first public {item['first_public']})", flush=True)
        try:
            L.main(argv)
        except Exception as e:                                  # noqa: BLE001 - one item never stops the batch
            print(f"#{item['problem']}: FAILED {type(e).__name__}: {str(e)[:200]}", flush=True)
    return 0


def engine_screen_record(run_dir: Path, item: dict, alias, rc, facts: dict, args, flags: list) -> dict:
    """One results row for a research-engine screen of a whole problem. `complete` is the engine's own claim: an
    unconditional refereed chain that its novelty judges call the problem itself (`engine_complete`), and
    `refereed_true` means it lands on the TRUE side. Only Lean makes it a solve, so `solved` stays False here."""
    st = json.loads((run_dir / "state.json").read_text())
    d = st.get("discovery") or {}
    ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    truth = "true" if item["answer"] else "false"
    counts: dict = {}
    for c in ej.get("ledger") or []:
        s = (c.get("validation") or {}).get("status") or f"unvalidated-{str(c.get('status')).lower()}"
        counts[s] = counts.get(s, 0) + 1
    new = [c for c in ej.get("ledger") or [] if (c.get("validation") or {}).get("status") == "validated-new"]
    sig = lambda c: (((c.get("validation") or {}).get("novelty") or {}).get("significance") or 0)
    bp = d.get("best_proof") or {}
    complete = bool(d.get("refereed_complete"))
    import harness as H
    recognized = ej.get("recognized") if "recognized" in ej else H.engine_recognized(ej)
    return {"problem": item["problem"], "tag": args.tag, "alias": alias, "run_dir": str(run_dir.relative_to(ROOT)),
            "answer": item["answer"], "truth": truth, "split": item["split"], "returncode": rc, "solved": False,
            "contradiction": False, "spend": round(facts.get("spend") or 0.0, 2), "screen": "engine",
            "complete": complete, "complete_answer": bp.get("answer"), "complete_claim": bp.get("claim"),
            "refereed_true": int(complete and bp.get("answer") == truth),
            "refereed_false": int(complete and bp.get("answer") != truth),
            "frontier_answer": (ej.get("frontier") or {}).get("answer"),
            "direction_correct": ((ej.get("frontier") or {}).get("answer") == truth) if (ej.get("frontier") or {}).get("answer") else None,
            "recognized": recognized, "recognized_true": str(item["problem"]) in [str(x) for x in recognized or []],
            "claims": counts, "validated_new": len(new), "sig2": sum(1 for c in new if sig(c) >= 2),
            "gaps": ej.get("gaps"), "protocol": {**protocol(args), "screen": "engine", "discovery_flags": flags}}


def run_harness_lane(cmd: list[str], log, env: dict, timeout: float) -> int:
    """One harness run with a wall-clock cap. On the cap it gets SIGTERM, so it ends its tracked model sessions before it
    exits (`run_tracked`), and only then SIGKILL. `subprocess.run(timeout=...)` sends SIGKILL at once: on 2026-10-13 that
    cut off a research-program item at 3 hours, left three lemma sessions running and billing as orphans, and crashed the
    whole screen with the exception."""
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env)
    try:
        return proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.terminate()
        try:
            return proc.wait(timeout=180)
        except subprocess.TimeoutExpired:
            proc.kill()
            return proc.wait()


def seed_from_tag(src_tag: str, aliases_file: Path, items: list[dict]) -> None:
    """`--resume-from`: a later tier on the same scout, as the campaign runs one, measured on time-split items. Each
    item's latest engine run under `src_tag` is COPIED to a new run dir under the same alias, and the copy is listed in
    this tag's aliases, so the resume path below continues it and the source run stays as it was recorded. On
    2026-10-20 the engine's research program ran on iteration 4's three scouts this way, without buying them again."""
    import shutil
    src = RESULTS / f"{src_tag}.aliases.jsonl"
    rows = [json.loads(l) for l in src.read_text().splitlines() if l.strip()] if src.exists() else []
    have = {json.loads(l)["problem"] for l in aliases_file.read_text().splitlines() if l.strip()} if aliases_file.exists() else set()
    for item in items:
        if item["problem"] in have:
            continue
        mine = [r for r in rows if r["problem"] == item["problem"] and (ROOT / r["run_dir"] / "engine/checkpoint.json").exists()]
        if not mine:
            print(f"#{item['problem']}: no engine run under {src_tag}; starting afresh", flush=True)
            continue
        old = ROOT / mine[-1]["run_dir"]
        new = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-discover-erdos{mine[-1]['alias']}"
        shutil.copytree(old, new, ignore=shutil.ignore_patterns("DONE", "SUMMARY.line"))
        # the copy's log carries the source's spend: the row records it, so a budget counts only what this tier adds
        rows_src = RESULTS / f"{src_tag}.jsonl"
        prior = [r for r in (json.loads(l) for l in (rows_src.read_text().splitlines() if rows_src.exists() else [])
                             if l.strip()) if r.get("run_dir") == mine[-1]["run_dir"]]
        with aliases_file.open("a") as f:
            f.write(json.dumps({"alias": mine[-1]["alias"], "problem": item["problem"],
                                "run_dir": str(new.relative_to(ROOT)), "resumed_from": mine[-1]["run_dir"],
                                "spend_prior": float(prior[-1].get("spend") or 0.0) if prior else None}) + "\n")
        print(f"#{item['problem']}: continuing a copy of {mine[-1]['run_dir']}", flush=True)


def discover_screen(args) -> int:
    """The no-Lean screen for changes to discovery: the in-run stage alone (`harness.py --stop-after discover`) on
    each item, recorded in the result-record shape so `ideas --tag <tag>` grades it, plus what decides conversion
    downstream: the direction the stage commits to, and whether a complete proof of the TRUE direction survived the
    referee (the #1213 solve came from exactly that)."""
    items = [i for i in load_pool()["items"] if i["split"] == args.split and (not args.items or i["problem"] in args.items)
             and (i.get("mask") or {}).get("ok")]
    done = set(load_results(args.tag))
    taken = taken_aliases()
    out = RESULTS / f"{args.tag}.jsonl"
    engine = args.discover_mode == "engine"
    if engine:
        # The research engine on the WHOLE problem, framed as open (no "resolved" cue): its own budget is
        # --discover-total-budget, the rest comes from --engine-flags (e.g. "--engine-sessions 3 --engine-deep-budget 6").
        flags = ["--discover-mode", "engine", "--engine-total-budget", str(args.discover_total_budget),
                 *(args.engine_flags or "").split()]
    else:
        flags = ["--discover-mode", args.discover_mode, "--discover-attempts", str(args.discover_attempts),
                 "--discover-effort", args.discover_effort, "--discover-budget", str(args.discover_budget),
                 "--discover-rounds", str(args.discover_rounds), "--discover-total-budget", str(args.discover_total_budget),
                 "--discover-ladder", str(args.discover_ladder), "--discover-commit-floor", str(args.commit_floor),
                 "--discover-gap-round", args.gap_round]
    if getattr(args, "record", None):
        # Only write the row for one finished engine run: a screen split across parallel lanes, or a lane stopped
        # while its harness run went on, records that run without starting another.
        import harness as H
        rd = (ROOT / args.record).resolve()
        al = next(json.loads(l) for l in (RESULTS / f"{args.tag}.aliases.jsonl").read_text().splitlines()
                  if l.strip() and json.loads(l)["run_dir"] == str(rd.relative_to(ROOT)))
        item = next(i for i in load_pool()["items"] if i["problem"] == al["problem"])
        dn = json.loads((rd / "DONE").read_text()) if (rd / "DONE").exists() else {}
        rec = engine_screen_record(rd, item, al["alias"], dn.get("exit"), H.collect_run_facts(rd, str(al["alias"])), args, flags)
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{item['problem']}: truth={rec['truth']} complete={rec['complete']} answer={rec['complete_answer']} "
              f"validated_new={rec['validated_new']} sig2={rec['sig2']} ${rec['spend']} (recorded)", flush=True)
        return 0
    print(f"discover-screen {args.tag}: {len([i for i in items if i['problem'] not in done])} item(s); {' '.join(flags)}",
          flush=True)
    aliases_file = RESULTS / f"{args.tag}.aliases.jsonl"
    if engine and getattr(args, "resume_from", None):
        seed_from_tag(args.resume_from, aliases_file, [i for i in items if i["problem"] not in done])
    for item in items:
        if item["problem"] in done:
            continue
        # An item cut off part way resumes its own run: the engine checkpoints everything it buys. Starting it afresh
        # would buy the map, the round, the deep dive and every program cycle again ($46 for 2026-10-13's first item).
        earlier = [json.loads(l) for l in aliases_file.read_text().splitlines() if l.strip()] if aliases_file.exists() else []
        mine = [a for a in earlier if a["problem"] == item["problem"]
                and (ROOT / a["run_dir"] / ("engine/checkpoint.json" if engine else "state.json")).exists()]
        if engine and mine:
            alias, run_dir = mine[-1]["alias"], ROOT / mine[-1]["run_dir"]
            print(f"#{item['problem']}: resuming {run_dir.relative_to(ROOT)}", flush=True)
        else:
            mask = json.loads((ROOT / item["mask"]["file"]).read_text())
            alias = alias_for(item["problem"], f"discover-{args.tag}", taken)
            statement = re.sub(rf"\berdos_{mask['alias_id']}\b", f"erdos_{alias}", mask["statement_lean"])
            run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-discover-erdos{alias}"
            run_dir.mkdir(parents=True)
            prob = {"id": str(alias), "statement": mask["statement_en"], "tags": mask.get("tags") or [],
                    "imports": mask["imports"],
                    "benchmark": {"kind": "time-split", "reference": "withheld (benchmarks/timesplit/pool.json)"}}
            (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
            (run_dir / "state.json").write_text(json.dumps({"statement": statement, "problem_input": prob,
                                                            "mode": "research", "invocations": [], "benchmark": True},
                                                           indent=2, ensure_ascii=False))
            with aliases_file.open("a") as f:
                f.write(json.dumps({"alias": alias, "problem": item["problem"], "run_dir": str(run_dir.relative_to(ROOT))}) + "\n")
        lib_flags, lib = [], None
        if args.library_root:
            lib = ROOT / args.library_root / str(item["problem"])
            if (lib / "DIGEST.md").exists():
                lib_flags = ["--library", str(lib)]
            else:
                print(f"#{item['problem']}: no library at {lib}; screened without one", flush=True)
                lib = None
        cmd = [sys.executable, str(harness_file(args)), "run", "--problem", str(run_dir / "problem.json"), "--resume",
               str(run_dir), "--mode", "research", "--allow-research", "--benchmark", "--masked", "--no-brief",
               "--skip-literature", "--stop-after", "discover", *flags, *lib_flags,
               "--run-budget", str(round(args.discover_total_budget + 1.5, 2)), "--backend", "claude-cli", "--model", args.model]
        env = dict(os.environ, **({"ERDOS_KNOWLEDGE": str((ROOT / args.knowledge).resolve())} if args.knowledge else {}))
        for attempt in range(4):
            with (run_dir / "lane.log").open("a") as log:
                # an engine run with the research program takes hours: its budget bounds it, the cap only guards hangs
                rc = run_harness_lane(cmd, log, env, (12 if engine else 3) * 3600)
            text = (run_dir / "lane.log").read_text(errors="replace")[-6000:]
            if rc != 1 or not LIMIT_RE.search(text):
                break
            wait = seconds_until_reset(text, cap_hours=24 * 7)
            print(f"#{item['problem']}: usage limit; waiting {wait / 60:.0f} min, then resuming", flush=True)
            time.sleep(wait)
        else:
            print(f"#{item['problem']}: still limited after 4 waits; not recorded (rerun the command)", flush=True)
            continue
        if rc == 1 or not (run_dir / ("engine/engine.json" if engine else "discovery.json")).exists():
            # an infrastructure failure is never a result (the runner's rule): on 2026-10-01 a logging bug crashed
            # every --library run before its first call, and five $0 non-results were recorded as screened items
            with (RESULTS / f"{args.tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps({"problem": item["problem"], "run_dir": str(run_dir.relative_to(ROOT)), "returncode": rc,
                                    "tail": text[-400:], "at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}) + "\n")
            print(f"#{item['problem']}: INFRASTRUCTURE (exit {rc}); not recorded, see {run_dir.relative_to(ROOT)}/lane.log",
                  flush=True)
            continue
        import harness as H
        facts = H.collect_run_facts(run_dir, str(alias))
        if engine:
            rec = engine_screen_record(run_dir, item, alias, rc, facts, args, flags)
            seeded = [a for a in earlier if a["run_dir"] == str(run_dir.relative_to(ROOT)) and a.get("resumed_from")]
            if seeded and seeded[-1].get("spend_prior") is not None:
                rec.update({"resumed_from": seeded[-1]["resumed_from"], "spend_prior": seeded[-1]["spend_prior"],
                            "spend_added": round(rec["spend"] - seeded[-1]["spend_prior"], 2)})
            with out.open("a") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            print(f"#{item['problem']}: truth={rec['truth']} complete={rec['complete']} answer={rec['complete_answer']} "
                  f"validated_new={rec['validated_new']} sig2={rec['sig2']} ${rec['spend']}", flush=True)
            continue
        try:
            dj = json.loads((run_dir / "discovery.json").read_text())
        except (OSError, ValueError):
            dj = {}
        truth = "true" if item["answer"] else "false"
        atts = dj.get("attempts") or []
        refereed = [a for a in atts if a.get("complete") and (a.get("critic") or {}).get("valid") and a.get("answer") in ("true", "false")]
        dec = dj.get("decision") or {}
        rec = {"problem": item["problem"], "tag": args.tag, "alias": alias, "run_dir": str(run_dir.relative_to(ROOT)),
               "answer": item["answer"], "split": item["split"], "returncode": rc, "solved": False, "contradiction": False,
               "spend": round(facts.get("spend") or 0.0, 2), "screen": "discover-only",
               "decision": dec, "direction_correct": dec.get("answer") == truth if dec.get("answer") else None,
               "commit_correct": (dec.get("commit") == ("pos" if item["answer"] else "neg")) if dec.get("commit") else None,
               "refereed_true": sum(1 for a in refereed if a["answer"] == truth),
               "refereed_false": sum(1 for a in refereed if a["answer"] != truth),
               "attempts": len(atts), "rounds": dj.get("rounds"), "rungs": sum(1 for r in (dj.get("ladder") or []) if r.get("rung")),
               "syntheses": len(dj.get("syntheses") or []), "library": str(lib.relative_to(ROOT)) if lib else None,
               "protocol": {**protocol(args), "screen": "discover-only", "discovery_flags": flags + lib_flags}}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{item['problem']}: truth={truth} decided={dec.get('answer')} commit={dec.get('commit')} "
              f"refereed_true={rec['refereed_true']} refereed_false={rec['refereed_false']} ${rec['spend']}", flush=True)
    return 0


def calibration_as_records(tag: str, rnd: int = 0) -> dict[str, dict]:
    """One calibration round per item, in the result-record shape, so the idea judge can grade tool-less discovery
    on the same items as an exploration screen."""
    path = RESULTS / f"calibration-{tag}.jsonl"
    out = {}
    for line in path.read_text().splitlines() if path.exists() else []:
        if line.strip():
            r = json.loads(line)
            if r["round"] == rnd:
                out[r["problem"]] = {"problem": r["problem"], "run_dir": r["work"], "alias": "0", "answer": r["truth"]}
    return out


def load_ideas(tag: str) -> dict[tuple[str, str], dict]:
    path = RESULTS / f"{tag}.ideas.jsonl"
    out = {}
    for line in path.read_text().splitlines() if path.exists() else []:
        if line.strip():
            r = json.loads(line)
            out[(r["problem"], r["run_dir"])] = r
    return out


def ideas_cmd(args) -> int:
    """Grade each recorded run of a tag for the key idea of its item's published resolution (where a reference
    note exists), and compare with --baseline on the items both ran."""
    import harness as H
    recs = calibration_as_records(args.from_calibration) if getattr(args, "from_calibration", None) else load_results(args.tag)
    graded = load_ideas(args.tag)
    out = RESULTS / f"{args.tag}.ideas.jsonl"
    items = {i["problem"]: i for i in load_pool()["items"]}
    for p, r in sorted(recs.items(), key=lambda kv: int(kv[0])):
        if (args.items and p not in args.items) or ((p, r["run_dir"]) in graded and not args.redo):
            continue
        ref = idea_reference(p)
        if not ref:
            continue
        backend = H.ClaudeCliBackend(args.model, 900, 0.6)
        try:
            resp = backend.complete("idea-judge", IDEA_JUDGE_PROMPT.format(
                statement=items[p]["statement_en"], reference=ref, material=run_idea_material(r)),
                effort_override="medium", budget_override=0.6)
            v = json_tail_any(resp)
        except RuntimeError as e:
            print(f"#{p}: judge failed ({str(e)[:160]})", flush=True)
            continue
        row = {"problem": p, "run_dir": r["run_dir"], "grade": v.get("grade") if v.get("grade") in IDEA_GRADES else None,
               "evidence": str(v.get("evidence") or "")[:600], "why": str(v.get("why") or "")[:400],
               "cost_usd": round(backend.total_cost_usd, 4), "at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
        with out.open("a") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
        graded[(p, r["run_dir"])] = row
        print(f"#{p}: {row['grade']} | {row['why'][:140]}", flush=True)
    mine = {p: graded.get((p, r["run_dir"])) for p, r in recs.items() if graded.get((p, r["run_dir"]))}
    summary = {g: sorted((p for p, x in mine.items() if x["grade"] == g), key=int) for g in IDEA_GRADES}
    print(json.dumps({"tag": args.tag, "graded": len(mine), **summary}, indent=1))
    if args.baseline:
        base_recs = calibration_as_records(args.baseline_calibration) if getattr(args, "baseline_calibration", None) \
            else load_results(args.baseline)
        base = load_ideas(args.baseline)
        pairs = [(p, mine[p], base.get((p, base_recs[p]["run_dir"]))) for p in mine if p in base_recs]
        pairs = [(p, a, b) for p, a, b in pairs if b and a["grade"] and b["grade"]]
        w = [p for p, a, b in pairs if IDEA_GRADES[a["grade"]] > IDEA_GRADES[b["grade"]]]
        l = [p for p, a, b in pairs if IDEA_GRADES[a["grade"]] < IDEA_GRADES[b["grade"]]]
        print(json.dumps({"paired": len(pairs), "wins": w, "losses": l, "ties": len(pairs) - len(w) - len(l),
                          "p_one_sided": round(sign_test_greater(len(w), len(l)), 4)}, indent=1))
    return 0


def lost_directions(done: dict) -> dict[str, str]:
    """Directions of an --open run that ended in an error (the parent records it as "error: ...")."""
    return {d: v for d, v in (done.get("open") or {}).items() if isinstance(v, str) and v.startswith("error")}


def load_results(tag: str) -> dict[str, dict]:
    """problem -> record, each with its checked progress measurement (or None) under "progress", and the directions
    it lost to an error (read from the run's DONE for records written before that was recorded)."""
    path = RESULTS / f"{tag}.jsonl"
    recs = {}
    for line in path.read_text().splitlines() if path.exists() else []:
        if line.strip():
            r = json.loads(line)
            recs[r["problem"]] = r          # a re-run of the same item under the same tag replaces the earlier line
    prog = load_progress(tag)
    for p, r in recs.items():
        r["progress"] = prog.get((p, r["run_dir"]))
        if "lost_directions" not in r:
            try:
                r["lost_directions"] = sorted(lost_directions(json.loads((ROOT / r["run_dir"] / "DONE").read_text())))
            except (OSError, ValueError, KeyError):
                r["lost_directions"] = []
    return recs


def mcnemar_exact(b: int, c: int) -> float:
    """Two-sided exact McNemar p-value on the discordant pairs (b: only A solved, c: only B solved)."""
    n = b + c
    if n == 0:
        return 1.0
    tail = sum(math.comb(n, k) for k in range(0, min(b, c) + 1)) / 2 ** n
    return min(1.0, 2 * tail)


def summarize(recs: dict[str, dict]) -> dict:
    from predict import jeffreys
    n = len(recs)
    solved = sum(r["solved"] for r in recs.values())
    mean, lo, hi = jeffreys(solved, n) if n else (0.0, 0.0, 1.0)
    spend = sum(r["spend"] or 0 for r in recs.values())
    return {"items": n, "solved": solved, "rate": round(mean, 3), "rate_90": [round(lo, 3), round(hi, 3)],
            "contradictions": sorted(p for p, r in recs.items() if r["contradiction"]),
            "false_direction_stopped": sum(r["false_stopped"] for r in recs.values()),
            "true_direction_abandoned": sum(r["true_abandoned"] for r in recs.values()),
            "true_direction_certified": sum(r["true_certified"] for r in recs.values()),
            "true_closed_modulo_published": sorted(p for p, r in recs.items() if r.get("true_modulo_published")),
            "true_direction_open_left": sum((r.get("true_open") or 0) for r in recs.values()),
            "true_pieces": sum(r["progress"]["pieces"] for r in recs.values() if r.get("progress")),
            "items_with_pieces": sorted((p for p, r in recs.items() if (r.get("progress") or {}).get("pieces")), key=int),
            "progress_unmeasured": sorted((p for p, r in recs.items() if not r.get("progress")), key=int),
            "spend": round(spend, 2), "usd_per_solve": round(spend / solved, 2) if solved else None,
            "infrastructure_failures": sorted(p for p, r in recs.items() if r.get("returncode") not in (0, 2, 3) or r.get("fatals"))}


def score(args) -> int:
    a = load_results(args.tag)
    if not a:
        print(f"no results for tag {args.tag}")
        return 2
    print(f"## {args.tag}")
    for p, r in sorted(a.items(), key=lambda kv: int(kv[0])):
        d = r["directions"]
        g = r.get("progress")
        dense = (f"pieces={g['pieces']} size={g['certified_size']} closed={g['closed_lemmas']} "
                 f"trivial={len(g.get('trivial') or [])} open={len(g.get('open_conjectures') or [])}"
                 + ("" if g.get("attempted", True) else " (true direction not attempted)")
                 + (" STALE" if g.get("stale") else "")) if g else "pieces=?"
        print(f"#{p:>5} answer={'yes' if r['answer'] else 'no ':3} solved={str(r['solved']):5} "
              f"pos={d['pos']['outcome']}/{d['pos']['certified']} neg={d['neg']['outcome']}/{d['neg']['certified']} "
              f"{dense} ${r['spend']}" + ("  CONTRADICTION: re-audit the item" if r["contradiction"] else ""))
    s = summarize(a)
    print(json.dumps(s, indent=1))
    if args.baseline:
        b = load_results(args.baseline)
        common = sorted(set(a) & set(b), key=int)
        only_a = [p for p in common if a[p]["solved"] and not b[p]["solved"]]
        only_b = [p for p in common if b[p]["solved"] and not a[p]["solved"]]
        cert = sum(a[p]["true_certified"] - b[p]["true_certified"] for p in common)
        print(json.dumps({"paired_items": len(common), f"solved_only_by_{args.tag}": only_a,
                          f"solved_only_by_{args.baseline}": only_b, "mcnemar_p": round(mcnemar_exact(len(only_a), len(only_b)), 4),
                          "true_certified_delta": cert,
                          "spend_delta": round(sum((a[p]["spend"] or 0) - (b[p]["spend"] or 0) for p in common), 2),
                          "dense": dense_compare(a, b)}, indent=1))
    return 0


def topup(args) -> int:
    """Resume a tag's unsolved but nearly closed runs with a larger total budget, as a separate arm.

    A run that ends with its committed direction (or either direction of an --open run) at most `--max-open`
    conjectures short is continued IN PLACE (`--resume`): the certified hypotheses stay certified and only the
    residual is attacked. Budget follows progress instead of being raised everywhere, and the $8 arm is untouched:
    results go to `<tag>+topup<N>` with each item's total spend, so solves per dollar stay honest. The decision uses
    only the run's own residual, never the known answer."""
    src = load_results(args.tag)
    out_tag = args.out or f"{args.tag}+topup{int(args.to)}"
    out = RESULTS / f"{out_tag}.jsonl"
    done = set(load_results(out_tag))
    todo = []
    for p, r in sorted(src.items(), key=lambda kv: int(kv[0])):
        if r["solved"] or p in done or (args.items and p not in set(args.items)):
            continue
        near = [d for d in ("pos", "neg") if r["directions"][d]["outcome"] not in (None, "not attempted")
                and r["directions"][d].get("open") is not None and r["directions"][d]["open"] <= args.max_open]
        if near:
            todo.append((p, r, near))
    print(f"top-up {args.tag} -> {out_tag}: {len(todo)} item(s) within {args.max_open} open conjecture(s) of closing",
          flush=True)
    pool = {i["problem"]: i for i in load_pool()["items"]}
    for p, r, near in todo:
        run_dir = ROOT / r["run_dir"]
        ctx = json.loads((run_dir / "launch.json").read_text())
        guidance = (run_dir / "guidance.md").read_text() if (run_dir / "guidance.md").exists() else ""
        disc_spend = (r.get("discovery") or {}).get("spend") or 0.0
        ctx["discovery"] = {**(r.get("discovery") or {}), "guidance": guidance, "spend": disc_spend} if r.get("discovery") else None
        k = ctx["cmd"].index("--run-budget")
        ctx["cmd"][k + 1] = str(round(args.to - disc_spend, 2))           # the item's TOTAL, discovery included
        ctx["launches"] = max(ctx.get("launches", 0), 1)     # launch.json is written before the first launch counts it
        before = r["spend"]
        rec = launch(pool[p], out_tag, r.get("protocol") or {}, args, ctx)
        rec.update({"topup_from_tag": args.tag, "topup_to": args.to, "spend_before_topup": before, "near": near})
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{p}: solved={rec['solved']} contradiction={rec['contradiction']} spend {before} -> {rec['spend']} "
              f"({rec['run_dir']})", flush=True)
    return 0


def rerun(args) -> int:
    """Relaunch recorded runs in place (`--resume`) and append their new records, which supersede the old ones. For a
    run that lost a direction to an infrastructure failure the runner did not catch; the run dir, alias, budget and
    protocol stay those of the original launch."""
    recs = load_results(args.tag)
    pool = {i["problem"]: i for i in load_pool()["items"]}
    out = RESULTS / f"{args.tag}.jsonl"
    for p in args.items:
        r = recs.get(p)
        if not r:
            print(f"#{p}: no record under {args.tag}")
            continue
        run_dir = ROOT / r["run_dir"]
        ctx = json.loads((run_dir / "launch.json").read_text())
        disc = r.get("discovery")
        ctx["discovery"] = {**disc, "guidance": (run_dir / "guidance.md").read_text()} if disc and (run_dir / "guidance.md").exists() else None
        ctx["launches"] = max(ctx.get("launches", 0), int(r.get("launches") or 1))
        rec = launch(pool[p], args.tag, r.get("protocol") or {}, args, ctx)     # launch() adds discovery spend itself
        rec["rerun_of"] = r.get("started")
        if rec.get("infrastructure"):
            with (RESULTS / f"{args.tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            print(f"#{p}: INFRASTRUCTURE again ({rec['infrastructure']}); not recorded as a result", flush=True)
            continue
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{p}: solved={rec['solved']} contradiction={rec['contradiction']} spend={rec['spend']} ({rec['run_dir']})", flush=True)
    return 0


def rescore(args) -> int:
    """Re-score a tag from its run directories with the current rules, so every evaluation is judged the same way
    whatever version of this file was running when its items finished."""
    path = RESULTS / f"{args.tag}.jsonl"
    recs = [json.loads(l) for l in path.read_text().splitlines() if l.strip()]
    changed = 0
    for r in recs:
        new = score_run(ROOT / r["run_dir"], str(r["alias"]), bool(r["answer"]), r.get("committed"))
        if r.get("discovery"):
            new["spend"] = round((new["spend"] or 0.0) + (r["discovery"].get("spend") or 0.0), 2)
        changed += any(r.get(k) != new[k] for k in ("solved", "contradiction"))
        r.update(new)
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs))
    print(f"rescored {len(recs)} item(s) of {args.tag}; {changed} changed solved/contradiction")
    return 0


def progress_cmd(args) -> int:
    """Measure the dense progress of a tag's recorded runs (those finished before the measurement existed, or any with
    --redo). Results go to results/<tag>.progress.jsonl; the result records themselves are never rewritten."""
    import harness as H
    recs = load_results(args.tag)
    checker = H.LeanChecker(H.FORMAL, args.lean_timeout)
    todo = [r for p, r in sorted(recs.items(), key=lambda kv: int(kv[0]))
            if (args.redo or not r.get("progress")) and (not args.items or p in set(args.items))]
    print(f"{args.tag}: measuring {len(todo)} run(s)", flush=True)
    for r in todo:
        t0 = time.time()
        g = record_progress(r, args.tag, checker, check=not args.no_check)
        print(f"#{r['problem']}: pieces={g['pieces']} {g.get('piece_names') or []} size={g.get('certified_size')} closed={g['closed_lemmas']} "
              f"trivial={g.get('trivial') or []} unknown={g.get('unknown') or []} open={g.get('open_conjectures') or []} "
              f"harness_certified={g.get('harness_certified')}" + (" STALE" if g.get("stale") else "")
              + f" ({time.time() - t0:.0f}s)", flush=True)
    return 0


def status(args) -> int:
    pool = load_pool()
    m = pool["meta"]
    print(f"built {m['built']}  since {m['since']}  cutoff {m['cutoff']} ({m['model']})  formal-conjectures {m['sources']['formal_conjectures_sha'][:12]}")
    print(json.dumps(m["counts"]))
    for split in ("test", "dev", "train", "unprobed"):
        rows = [i for i in pool["items"] if i["split"] == split]
        if rows:
            print(f"\n{split} ({len(rows)}):")
            for i in rows:
                mk = i.get("mask") or {}
                print(f"  #{i['problem']:>5} first public {i['first_public']}  answer={'yes' if i['answer'] else 'no'}  "
                      f"{','.join(i['provenance'])}  probe={(i.get('probe') or {}).get('verdict')}  "
                      f"mask={'ok' if mk.get('ok') else ('FAIL' if mk else '-')}")
    ex: dict = {}
    for i in pool["items"]:
        if i["split"] == "excluded":
            why = re.sub(r"\s*\(parts:.*|:.*", "", (i["split_reason"] or "?").split("\n")[0], flags=re.S).strip()
            ex.setdefault(why, []).append(i["problem"])
    print("\nexcluded:")
    for why, ps in sorted(ex.items(), key=lambda kv: -len(kv[1])):
        print(f"  {len(ps):>3}  {why}: {', '.join(ps[:25])}{' ...' if len(ps) > 25 else ''}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--since", default=DEFAULT_SINCE, help="earliest site resolution date considered")
    b.add_argument("--cutoff", default="2026-07-01", help="first clean day, for a model not in CUTOFFS")
    b.add_argument("--model", default=DEFAULT_MODEL)
    b.add_argument("--refresh", action="store_true", help="re-fetch every source (default: use the cache)")
    p = sub.add_parser("probe")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--items", nargs="*")
    p.add_argument("--limit", type=int)
    p.add_argument("--redo", action="store_true")
    p.add_argument("--call-budget", type=float, default=0.6)
    p.add_argument("--max-spend", type=float, default=15.0, help="stop the batch at this total probe spend")
    f = sub.add_parser("freeze")
    f.add_argument("--items", nargs="*")
    f.add_argument("--redo", action="store_true", help="re-freeze every item, compiled or not")
    f.add_argument("--retry-failed", action="store_true", help="re-freeze only the items whose statement failed")
    f.add_argument("--unprobed", action="store_true", help="also freeze items the probe has not screened yet")
    f.add_argument("--no-auto-import", dest="auto_import", action="store_false",
                   help="do not add the Mathlib module of an unknown identifier and recompile")
    f.add_argument("--lean-timeout", type=int, default=900)
    f.add_argument("--batch", type=int, default=40, help="statements per batched Lean check")
    j = sub.add_parser("judge")
    j.add_argument("--items", nargs="*")
    j.add_argument("--redo", action="store_true")
    j.add_argument("--max-spend", type=float, default=10.0, help="stop the batch at this total judge spend")
    r = sub.add_parser("run")
    r.add_argument("--split", default="dev", choices=["test", "dev", "train"])
    r.add_argument("--items", nargs="*")
    r.add_argument("--limit", type=int)
    r.add_argument("--tag")
    r.add_argument("--budget", type=float, default=8.0, help="--run-budget per item, both directions together")
    r.add_argument("--research-cycles", type=int, default=2)
    r.add_argument("--hyps-per-cycle", type=int, default=3)
    r.add_argument("--literature", choices=["on", "off"], default="on",
                   help="the model-memory literature stage (no web); safe because the probe screened the resolution")
    r.add_argument("--lean-timeout", type=int, default=1800)
    r.add_argument("--model", default=DEFAULT_MODEL)
    r.add_argument("--allow-concurrent", action="store_true")
    r.add_argument("--harness", help="a pinned copy from `pin` (default: the live harness.py)")
    r.add_argument("--knowledge", help="a pinned knowledge/ copy from `pin` (default: ERDOS_KNOWLEDGE or knowledge/)")
    r.add_argument("--compile-workers", type=int, default=2, help="ERDOS_COMPILE_WORKERS for the run (a shared machine)")
    r.add_argument("--item-hours", type=float, default=3.0, help="wall-clock cap per item; a kill is infrastructure")
    r.add_argument("--limit-waits", type=int, default=4, help="usage-limit waits per item before giving up on it")
    r.add_argument("--candidate", choices=["baseline", "discover-v1", "discover-v2", "discover-v3", "discover-v4", "v3",
                                           "alloc", *IN_RUN_FLAGS],
                   default="baseline",
                   help="discover-v1: informal attempts + referee first, then commit to one direction (same total budget); "
                        "discover-v2: + a second round on the named missing step, and one confident answer may commit; "
                        "discover-v3: discover-v2 with its settings fixed in code and the calibrated 0.6 commit floor; "
                        "discover-v4: v3 plus up to --discover-rounds rounds until a refereed complete proof appears; "
                        "v3: no external discovery, the harness's own discovery options instead (V3_FLAGS)")
    r.add_argument("--v3-flags", help="override V3_FLAGS for candidate v3 (one string, shell-split)")
    r.add_argument("--commit-floor", type=float, default=None,
                   help="discover arms: commit only when the committed answer's attempts average at least this confidence "
                        "(0.6 from the train calibration; unset keeps the v1/v2 protocol)")
    r.add_argument("--gap-budget", type=float, default=1.2, help="discover-v2: cap on the missing-step attempt")
    # medium, not high: a capped call returns nothing, and on #1148 a high-effort gap attempt overran even $1.50
    r.add_argument("--gap-effort", default="medium", choices=["low", "medium", "high"])
    r.add_argument("--discover-budget", type=float, default=1.2, help="cap per informal attempt")
    r.add_argument("--discover-rounds", type=int, default=1, help="discover-v4: rounds until a refereed complete proof")
    r.add_argument("--discover-total-budget", type=float, default=3.0, help="discover-v4: cap on all rounds together")
    r.add_argument("--discover-attempts", type=int, default=2, choices=[1, 2, 3], help="parallel informal attempts")
    r.add_argument("--discover-effort", default="high", choices=["low", "medium", "high"])
    r.add_argument("--critic-budget", type=float, default=0.3, help="cap per referee call")
    r.add_argument("--detach", action="store_true")
    r.add_argument("--dry-run", action="store_true", help="prepare each run dir and print the command; launch nothing")
    s = sub.add_parser("score")
    s.add_argument("--tag", required=True)
    s.add_argument("--baseline")
    ca = sub.add_parser("calibrate")
    ca.add_argument("--tag", default="train-v2r1")
    ca.add_argument("--split", default="train", choices=["train", "dev", "test"])
    ca.add_argument("--items", nargs="*")
    ca.add_argument("--rounds", type=int, default=2, help="independent first rounds per item")
    ca.add_argument("--workers", type=int, default=2, help="items at a time (each runs its attempts in parallel)")
    ca.add_argument("--model", default=DEFAULT_MODEL)
    ca.add_argument("--discover-attempts", type=int, default=2)
    ca.add_argument("--discover-effort", default="medium", choices=["low", "medium", "high"])
    ca.add_argument("--discover-budget", type=float, default=0.8)
    ca.add_argument("--critic-budget", type=float, default=0.3)
    ca.add_argument("--report", action="store_true", help="print the report for the tag; run nothing")
    ih = sub.add_parser("ideas")
    ih.add_argument("--tag", required=True)
    ih.add_argument("--baseline")
    ih.add_argument("--items", nargs="*")
    ih.add_argument("--redo", action="store_true")
    ih.add_argument("--model", default=DEFAULT_MODEL)
    ih.add_argument("--from-calibration", help="grade a calibration's round-0 discovery attempts (records under --tag)")
    ih.add_argument("--baseline-calibration", help="the --baseline tag holds grades of this calibration's attempts")
    es = sub.add_parser("explore-screen")
    es.add_argument("--tag", required=True)
    es.add_argument("--split", default="train", choices=["train", "dev", "test"])
    es.add_argument("--items", nargs="*")
    es.add_argument("--harness", help="a pinned copy from `pin` (default: the live harness.py)")
    es.add_argument("--knowledge")
    es.add_argument("--model", default=DEFAULT_MODEL)
    es.add_argument("--explore-budget", type=float, default=1.5)
    es.add_argument("--explore-effort", default="medium", choices=["low", "medium", "high", "xhigh", "max"])
    es.add_argument("--literature-scope", default="wide", choices=["status", "wide"])
    es.add_argument("--budget", type=float, default=0.0, help=argparse.SUPPRESS)
    es.add_argument("--research-cycles", type=int, default=0, help=argparse.SUPPRESS)
    es.add_argument("--hyps-per-cycle", type=int, default=0, help=argparse.SUPPRESS)
    es.add_argument("--literature", default="on", help=argparse.SUPPRESS)
    es.add_argument("--lean-timeout", type=int, default=0, help=argparse.SUPPRESS)
    es.add_argument("--compile-workers", type=int, default=0, help=argparse.SUPPRESS)
    ds = sub.add_parser("discover-screen")
    ds.add_argument("--tag", required=True)
    ds.add_argument("--split", default="train", choices=["train", "dev", "test"])
    ds.add_argument("--items", nargs="*")
    ds.add_argument("--harness", help="a pinned copy from `pin` (default: the live harness.py)")
    ds.add_argument("--knowledge")
    ds.add_argument("--model", default=DEFAULT_MODEL)
    ds.add_argument("--discover-mode", default="independent", choices=["independent", "crossfed", "engine"])
    ds.add_argument("--engine-flags", default="", help="with --discover-mode engine: extra harness flags, one string")
    ds.add_argument("--record", help="with --discover-mode engine: only write the results row for this finished run dir")
    ds.add_argument("--resume-from", help="with --discover-mode engine: continue a copy of each item's finished run under this tag (another tier on the same scout, as the campaign does), never the run itself")
    ds.add_argument("--discover-attempts", type=int, default=2)
    ds.add_argument("--discover-effort", default="medium", choices=["low", "medium", "high", "xhigh", "max"])
    ds.add_argument("--discover-budget", type=float, default=0.8)
    ds.add_argument("--discover-rounds", type=int, default=1)
    ds.add_argument("--discover-total-budget", type=float, default=3.0)
    ds.add_argument("--discover-ladder", type=int, default=0)
    ds.add_argument("--commit-floor", type=float, default=0.6)
    ds.add_argument("--gap-round", default="on", choices=["on", "off"])
    ds.add_argument("--library-root", help="per-item libraries at <root>/<n>/DIGEST.md (timesplit.py library)")
    for hidden, default in (("--budget", 0.0), ("--research-cycles", 0), ("--hyps-per-cycle", 0), ("--literature", "off"),
                            ("--lean-timeout", 0), ("--compile-workers", 0)):
        ds.add_argument(hidden, default=default, help=argparse.SUPPRESS)
    lb = sub.add_parser("library")
    lb.add_argument("--items", nargs="*")
    lb.add_argument("--split", default="train", choices=["train", "dev", "test"])
    lb.add_argument("--papers", type=int, default=6)
    lb.add_argument("--margin-days", type=int, default=7)
    lb.add_argument("--model", default=DEFAULT_MODEL)
    lb.add_argument("--redo", action="store_true")
    pg = sub.add_parser("progress")
    pg.add_argument("--tag", required=True)
    pg.add_argument("--items", nargs="*")
    pg.add_argument("--redo", action="store_true", help="measure runs that already have a measurement again")
    pg.add_argument("--no-check", action="store_true", help="structure only, no Lean triviality pass (never compared)")
    pg.add_argument("--lean-timeout", type=int, default=1200)
    sub.add_parser("status")
    sub.add_parser("pin")
    rs = sub.add_parser("rescore")
    rs.add_argument("--tag", required=True)
    rr = sub.add_parser("rerun")
    rr.add_argument("--tag", required=True)
    rr.add_argument("--items", nargs="+", required=True)
    rr.add_argument("--item-hours", type=float, default=3.0)
    tu = sub.add_parser("topup")
    tu.add_argument("--tag", required=True, help="the arm whose nearly closed runs get more budget")
    tu.add_argument("--to", type=float, default=16.0, help="the item's new TOTAL budget, discovery included")
    tu.add_argument("--max-open", type=int, default=1, help="continue only runs this many open conjectures short")
    tu.add_argument("--items", nargs="*")
    tu.add_argument("--out", help="result tag (default <tag>+topup<to>)")
    tu.add_argument("--item-hours", type=float, default=3.0)
    args = ap.parse_args()
    return {"build": build, "probe": probe, "freeze": freeze, "judge": judge_cmd, "run": run, "score": score,
            "status": status, "pin": pin, "rescore": rescore, "topup": topup, "progress": progress_cmd,
            "calibrate": calibrate, "ideas": ideas_cmd, "explore-screen": explore_screen, "rerun": rerun,
            "discover-screen": discover_screen, "library": library_cmd}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
