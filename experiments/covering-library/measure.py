#!/usr/bin/env python3
"""Build the compounding-measurement table from run facts.

Every number in REPORT.md comes from here, so a reader can reproduce it. Facts are taken from
`collect_run_facts(run_dir, pid)` and never from a single `state.json` (CLAUDE.md): --open children
and research sub-runs keep their own state, and reading the parent alone has produced wrong reports.

    python3 experiments/covering-library/measure.py <run_dir> [<run_dir> ...]
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import harness as H  # noqa: E402

COLS = ["run", "problem", "library", "outcome", "exit", "mode", "llm_calls", "lean_checks",
        "spend", "certified", "reductions", "floors"]


def row(run_dir: Path) -> dict:
    pid = run_dir.name.split("erdos")[-1]
    f = H.collect_run_facts(run_dir, pid)
    lib = sorted({e.get("module") for e in f["events"]
                  if e.get("stage") == "library" and e.get("event") == "available"})
    spend = f"${f['spend']:.2f}" if f["cost_known"] else f"unavailable(>=${f['spend']:.2f})"
    return {
        "run": run_dir.name,
        "problem": f["problem"],
        "library": ",".join(m.split(".")[-1] for m in lib) or "none",
        "outcome": f["outcome"],
        "exit": f["exit"],
        "mode": f["mode"],
        "llm_calls": f["llm_calls"],
        "lean_checks": f["lean_checks"],
        "spend": spend,
        "certified": len(f["certified"]),
        "reductions": len(f["reductions"]),
        "floors": len(f["search_floors"]),
        "_certified_names": f["certified"],
        "_partial_dirs": f["partial_dirs"],
        "_directions": f["directions"],
        "_stop": f["stop_reasons"],
    }


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    rows = [row(Path(a).resolve()) for a in argv]
    print("| " + " | ".join(COLS) + " |")
    print("|" + "|".join("---" for _ in COLS) + "|")
    for r in rows:
        print("| " + " | ".join(str(r[c]) for c in COLS) + " |")
    print()
    for r in rows:
        print(f"{r['run']}: directions={r['_directions']} stop={r['_stop']}")
        print(f"  certified artifacts ({len(r['_certified_names'])}): {r['_certified_names']}")
        print(f"  partial dirs: {r['_partial_dirs']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
