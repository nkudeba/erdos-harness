#!/usr/bin/env python3
"""Rank open problems by how well they suit the DEDUCTIVE research loop (docs/deductive-research-mode.md).

The deductive loop needs three things a search-first target does not: a certified library or checked
reductions to stand on, a counterexample shape from which necessary conditions can be derived, and published
partial theorems that can enter as named hypotheses. This script scores those features from the Atlas
(`rankings.json`, `reviewed.json`, the forum caches) and the harness's cluster-library table. It makes no
model calls and costs nothing.

    python3 atlas-data/deductive_candidates.py            # top 15, markdown table to stdout
    python3 atlas-data/deductive_candidates.py --top 30 --write   # also writes atlas-data/deductive-candidates.md

The score is a heuristic ORDERING device, like `score` and `partial`; it is not a probability and it does
not say a problem can be resolved. Read the reasons column.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "atlas-data"
sys.path.insert(0, str(ROOT))
try:
    from harness import CLUSTER_LIBRARIES
except Exception:                                     # noqa: BLE001 - the ranker must not depend on Lean being set up
    CLUSTER_LIBRARIES = {"covering systems": "Formal.Library.CoveringSystems",
                         "binomial coefficients": "Formal.Library.BinomialCoefficients"}

ELEMENTARY_TAGS = {"number theory", "binomial coefficients", "covering systems", "unit fractions", "powerful",
                   "divisors", "primes", "iterated functions", "factorials", "complete sequences", "sidon sets",
                   "additive basis", "base representations", "irrationality"}
HEAVY_WORDS = re.compile(r"density|asymptotic|\\log|o\(|→\s*∞|measure|almost all|for all large|sufficiently large|"
                         r"lim(?:inf|sup)?|\\epsilon|\\varepsilon|\\ll|\\gg", re.I)
PREMISE_WORDS = re.compile(r"proved (?:that|for|when|in the case)|it is known that|implies|conditional on|assuming|"
                           r"under (?:GRH|the abc|abc)|abc conjecture|reduces to|equivalent to|theorem \d|Theorem [A-Z0-9]|"
                           r"special case|partial result|is true for|holds for", re.I)
DEDUCTIVE_WORDS = re.compile(r"certified|sorry-free|Lean|reduction|conditional theorem|⇐|implies|necessary condition|"
                             r"forces|must satisfy|smooth|parity|residue|congruence", re.I)
RESEARCH_WORDS = re.compile(r"new mathematics|research-grade|Thue|Siegel|Baker|ineffective|deep|hopeless", re.I)


def load(path, default):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return default


def forum_text(pid: int) -> str:
    d = load(DATA / "forum" / f"{pid}.json", {})
    return " ".join(str(d.get(k) or "") for k in ("thread", "claims"))


def score_problem(p: dict, reviewed: dict) -> tuple[int, list[str]]:
    pts, why = 0, []
    tags = {str(t).lower() for t in (p.get("tags") or [])}
    stmt = p.get("statement") or ""
    rv = reviewed.get(str(p["id"]), {})
    rationale = " ".join(rv.get("rationale") or []) + " " + " ".join(rv.get("requirements") or [])

    libs = [m for t, m in CLUSTER_LIBRARIES.items() if t in tags]
    if libs:
        pts += 20; why.append(f"cluster library {libs[0].split('.')[-1]}")
    if DEDUCTIVE_WORDS.search(rationale):
        pts += 15; why.append("reviewed notes record reductions/certified lemmas to stand on")
    if p.get("harness") in ("Attempted", "Partial result"):
        pts += 5; why.append("frozen statement and run history exist")
    if any(s.get("label", "").startswith("External formal statement") for s in (p.get("signals") or [])):
        pts += 8; why.append("external formal statement")
    state = str(p.get("state") or "").lower()
    if state == "falsifiable":
        pts += 10; why.append("falsifiable: a counterexample has a shape to derive conditions from")
    elif state == "decidable":
        pts += 4; why.append("decidable: finite check plus a tail")
    elif state == "verifiable":
        pts -= 8; why.append("verifiable-only: the content is a witness, which deduction cannot supply")
    if tags & ELEMENTARY_TAGS and not (tags & {"analysis", "geometry", "polynomials"}):
        pts += 10; why.append("elementary objects")
    if HEAVY_WORDS.search(stmt):
        pts -= 10; why.append("asymptotic/density statement")
    ft = forum_text(p["id"])
    if ft and PREMISE_WORDS.search(ft):
        pts += 12; why.append("thread carries published partial theorems usable as named premises")
    if RESEARCH_WORDS.search(rationale):
        pts -= 6; why.append("reviewed notes flag a research-grade core")
    floor = rv.get("search_floor")
    if isinstance(floor, (int, float)) and floor > 1e9 and state == "verifiable":
        pts -= 10; why.append(f"witness floor {floor:.2g} past reach")
    partial = p.get("partial")
    ps = partial.get("score") if isinstance(partial, dict) else (partial or 0)
    pts += int(0.3 * (ps or 0))
    if rv.get("residual"):
        why.append("a residual is already recorded")
    return pts, why


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--write", action="store_true", help="write atlas-data/deductive-candidates.md")
    args = ap.parse_args()
    rankings = load(DATA / "rankings.json", {})
    reviewed = load(DATA / "reviewed.json", {})
    rows = []
    for p in rankings.get("problems", []):
        if p.get("status") != "Unsolved":
            continue
        pts, why = score_problem(p, reviewed)
        rows.append((pts, p, why))
    rows.sort(key=lambda r: (-r[0], r[1]["id"]))
    lines = ["| # | deductive fit | score | partial | state | why |", "|---|---|---|---|---|---|"]
    for pts, p, why in rows[: args.top]:
        partial = p.get("partial")
        ps = partial.get("score") if isinstance(partial, dict) else partial
        lines.append(f"| {p['id']} | {pts} | {p['score']} | {ps} | {p.get('state')} | {'; '.join(why)} |")
    table = "\n".join(lines)
    print(table)
    if args.write:
        head = ("# Deductive-loop candidates\n\nGenerated by `atlas-data/deductive_candidates.py`. The fit column is a "
                "heuristic ordering device for the deductive research loop, not a probability and not a claim that "
                "the problem can be resolved. `score`/`partial` are the Atlas axes.\n\n")
        (DATA / "deductive-candidates.md").write_text(head + table + "\n")
        print(f"\nwrote {DATA / 'deductive-candidates.md'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
