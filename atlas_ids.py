"""Benchmark runs are filed under synthetic ids, so the Atlas never saw them. Resolve an id to the catalogue number.

A time-split launch records its fresh alias in `benchmarks/timesplit/results/<tag>.aliases.jsonl`. A masked
deductive benchmark records its alias in `benchmarks/deductive/masks/<n>.json`, as `alias_id` and `true_problem`,
and so do the time-split masks. Everything here reads local files only, and nothing here makes a model call.

What a resolved run may carry to the Atlas is STATUS, never content: runs, certified counts, verified or not.
A dev or test item's route must not reach a file a later design decision could read (CLAUDE.md, time-split
quarantine). The ranker and the publisher already carry no statement, proof or prompt text for any run.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CATALOGUE = range(1, 1218)


def _jsonl(path: Path):
    try:
        for line in path.read_text().splitlines():
            if line.strip():
                try:
                    yield json.loads(line)
                except ValueError:
                    continue
    except OSError:
        return


def benchmark_aliases(root: Path = ROOT) -> dict[int, dict]:
    """alias -> {"problem": catalogue number, "benchmark": "timesplit" | "deductive", "split": ...}.
    An alias is only ever a synthetic id outside the catalogue, so a real problem number is never remapped."""
    out: dict[int, dict] = {}
    split: dict[int, str] = {}
    pool = root / "benchmarks" / "timesplit" / "pool.json"
    try:
        items = json.loads(pool.read_text())
        items = items["items"] if isinstance(items, dict) and "items" in items else items
        for it in items if isinstance(items, list) else []:
            if str(it.get("problem", "")).isdigit():
                split[int(it["problem"])] = it.get("split")
    except (OSError, ValueError, TypeError):
        pass

    def add(alias, problem, kind, tag=None):
        try:
            a, p = int(alias), int(problem)
        except (TypeError, ValueError):
            return
        if a in CATALOGUE or p not in CATALOGUE:
            return
        out.setdefault(a, {"problem": p, "benchmark": kind, "split": split.get(p) if kind == "timesplit" else None,
                           **({"tag": tag} if tag else {})})

    for f in sorted((root / "benchmarks" / "timesplit" / "results").glob("*.aliases.jsonl")):
        for r in _jsonl(f):
            add(r.get("alias"), r.get("problem"), "timesplit", f.name[: -len(".aliases.jsonl")])
    for f in sorted((root / "benchmarks" / "timesplit" / "results").glob("*.jsonl")):
        if any(x in f.name for x in (".aliases.", ".infra.", ".ideas.", ".progress.")):
            continue
        for r in _jsonl(f):
            add(r.get("alias"), r.get("problem"), "timesplit", f.name[: -len(".jsonl")])
    for d, kind in ((root / "benchmarks" / "timesplit" / "masks", "timesplit"),
                    (root / "benchmarks" / "deductive" / "masks", "deductive")):
        for f in sorted(d.glob("*.json")):
            try:
                m = json.loads(f.read_text())
            except (OSError, ValueError):
                continue
            add(m.get("alias_id"), m.get("true_problem"), kind)
    return out


def resolve(pid, aliases: dict[int, dict]) -> tuple[int | None, dict | None]:
    """(catalogue number or None, benchmark info or None) for a run's own problem id."""
    try:
        n = int(pid)
    except (TypeError, ValueError):
        return None, None
    if n in CATALOGUE:
        return n, None
    info = aliases.get(n)
    return (info["problem"], info) if info else (None, None)


def audited_evidence(root: Path = ROOT) -> set[int]:
    """Catalogue numbers whose blind benchmark proof is kept in benchmarks/timesplit/evidence/<n>/ with an audit
    PASS (audit.py). An assembled proof (`<n>-assembled`) is not a harness solve, so it does not count."""
    out = set()
    for d in (root / "benchmarks" / "timesplit" / "evidence").glob("*"):
        if not (d.is_dir() and d.name.isdigit() and int(d.name) in CATALOGUE):
            continue
        for a in d.rglob("AUDIT.json"):
            try:
                if json.loads(a.read_text()).get("verdict") == "PASS":
                    out.add(int(d.name))
                    break
            except (OSError, ValueError):
                continue
    return out
