#!/usr/bin/env python3
"""Replay the breadth-first sweep's cheap attempt on steps an earlier train run left open and never attacked.

    python3 benchmarks/timesplit/analysis/replay_sweep.py --list never_attacked.json --index 3

Each replay works on a COPY of the run's direction state under runs/replay-sweep-<date>/, so the original run's
spend accounting and program directory are untouched (sub-runs are attributed to a run by `owner_runs`). The
attempt is exactly `_attack_substatement(..., cheap=True)`: one one-shot round, no agentic, no decompose, capped at
--sweep-budget. Train items only (quarantine)."""
from __future__ import annotations
import argparse, json, shutil, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import harness as H


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--index", type=int, required=True)
    ap.add_argument("--out", default=str(ROOT / "runs" / "replay-sweep-20260926"))
    ap.add_argument("--full", action="store_true", help="a depth attack (the round caps apply) instead of the cheap one")
    ap.add_argument("--budget", type=float, default=None, help="cap the parent copy's run budget (full attacks)")
    a = ap.parse_args()
    o = json.loads(Path(a.list).read_text())[a.index]
    run_dir = ROOT / o["run_dir"]
    direction_dir = run_dir / o["direction"] if (run_dir / o["direction"] / "state.json").exists() else run_dir
    base = Path(a.out).resolve() / f"{o['alias']}-{o['name']}"
    parent = base / "parent"
    parent.mkdir(parents=True, exist_ok=True)
    shutil.copy(direction_dir / "state.json", parent / "state.json")
    pfile = next(p for p in (direction_dir / "problem.json", run_dir / "problem.json") if p.exists())
    shutil.copy(pfile, parent / "problem.json")
    cmd = json.loads((run_dir / "launch.json").read_text())["cmd"]
    argv = [x for x in cmd[2:] if x != "--open"]                   # drop the interpreter and harness path
    i = argv.index("--resume")
    argv[i + 1] = str(parent)
    j = argv.index("--problem")
    argv[j + 1] = str(parent / "problem.json")
    args = H.build_parser().parse_args(argv)
    if a.budget:
        args.run_budget = a.budget
    h = H.Harness(args)
    h.direction = o["direction"] if o["direction"] in ("pos", "neg") else None
    skeleton = (ROOT / o["skeleton"]).read_text()
    sub = H.hypothesis_substatement(skeleton, o["name"])
    rec = {**o, "replay_dir": str(base.relative_to(ROOT)), "substatement_found": bool(sub)}
    if sub:
        rc, child = h._attack_substatement(sub, o["name"], base / "sweep", 99, None, 1, recursive=False, cheap=not a.full)
        # the child sits outside the parent copy's tree, so it is read directly, not through the parent's spend
        rec.update({"exit": rc, "proved": bool(rc == 0 and child is not None and child.state.get("proof")),
                    "spent_usd": round(child.spent_usd(), 4) if child is not None else 0.0,
                    "frozen_decls_restored": any("frozen_decls_restored" in l for l in
                                                 (base / "sweep" / "log.jsonl").read_text().splitlines())
                    if (base / "sweep" / "log.jsonl").exists() else False})
    (base / "RESULT.json").write_text(json.dumps(rec, indent=1))
    print(json.dumps({k: rec.get(k) for k in ("problem", "name", "rating", "exit", "proved", "spent_usd")}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
