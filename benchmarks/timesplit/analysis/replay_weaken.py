#!/usr/bin/env python3
"""Replay the premise-weakening move (--premise-weaken on) on a train run that ended in the premise endgame.

    python3 benchmarks/timesplit/analysis/replay_weaken.py --list benchmarks/timesplit/analysis/weaken_678.json --index 0
    python3 benchmarks/timesplit/analysis/replay_weaken.py --list ... --index 0 --candidate <skeleton.lean> --weakened <name>

Each replay works on COPIES: the run's direction state, its problem file and its program directory (Residual.lean,
Lemmas.lean, failures, ledger) go under <out>/<alias>-<premise>[-free]/parent/, so neither the original run's spend
accounting nor its program directory is touched, and every child the move starts logs inside the copy, where the copy's
`spent_usd` counts it.

With --candidate the proposal is read from a file, e.g. a skeleton a plan wrote during the run, and the replay is FREE:
no model call and no child. It reports what the free checks make of the candidate: does it compile, which restated
steps get their certificates back, does Lean derive the weakened premise from the original. Without --candidate the
move runs as it would in a cycle: one proposal call, the free checks, the attack on the weakened premise. Train items
only (quarantine): never point this at a dev or test item.

Run it from a git worktree with --data-root and --lean-project naming the main checkout, where runs/, programs/ and the
built Lean project live."""
from __future__ import annotations
import argparse, json, shutil, sys, time
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import harness as H


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--index", type=int, required=True)
    ap.add_argument("--data-root", default=str(ROOT), help="where runs/ and programs/ live (the main checkout)")
    ap.add_argument("--lean-project", default=None, help="a built Lean project (default: <harness>/formal)")
    ap.add_argument("--out", default=None, help="default: <data-root>/runs/replay-weaken-<date>")
    ap.add_argument("--budget", type=float, default=6.0, help="the copy's run budget (paid replays)")
    ap.add_argument("--candidate", default=None, help="a skeleton file to use as the proposal: a FREE replay")
    ap.add_argument("--weakened", default=None, help="with --candidate: the weakened premise's name in that skeleton")
    a = ap.parse_args()
    data = Path(a.data_root).resolve()
    if a.lean_project and Path(a.lean_project).resolve() != H.FORMAL:
        H.FORMAL = Path(a.lean_project).resolve()
        H.MATHLIB_SRC = H.FORMAL / ".lake" / "packages" / "mathlib" / "Mathlib"
        H._INDEX, H._decl_cache = H.DeclIndex(), {}
    o = json.loads(Path(a.list).read_text())[a.index]
    if o.get("split") != "train":
        raise SystemExit(f"{o.get('problem')} is not a train item: replays are for train items only")
    run_dir = data / o["run_dir"]
    direction_dir = run_dir / o["direction"] if (run_dir / str(o.get("direction")) / "state.json").exists() else run_dir
    out = Path(a.out or data / "runs" / f"replay-weaken-{datetime.now().strftime('%Y%m%d')}").resolve()
    base = out / f"{o['alias']}-{o['premise']}{'-free' if a.candidate else ''}"
    parent = base / "parent"
    if parent.exists():
        raise SystemExit(f"{parent} exists: a replay is never resumed over an earlier one")
    parent.mkdir(parents=True)
    shutil.copy(direction_dir / "state.json", parent / "state.json")
    pfile = next(p for p in (direction_dir / "problem.json", run_dir / "problem.json") if p.exists())
    shutil.copy(pfile, parent / "problem.json")
    pdir = parent / "program"
    shutil.copytree(data / o["program_dir"], pdir, ignore=shutil.ignore_patterns("cycles", "sub", "alternatives"))
    cmd = json.loads((run_dir / "launch.json").read_text())["cmd"]
    argv = [x for x in cmd[2:] if x != "--open"]
    argv[argv.index("--resume") + 1] = str(parent)
    argv[argv.index("--problem") + 1] = str(parent / "problem.json")
    args = H.build_parser().parse_args(argv)
    args.run_budget, args.premise_weaken = a.budget, "on"
    H.RUNS = out                         # the `current` link goes beside the replay, never over the checkout's runs/current
    h = H.Harness(args)
    h.direction = o["direction"] if o.get("direction") in ("pos", "neg") else None
    pid = h.problem["id"]
    main_thm = getattr(h, "thm_name", None) or f"erdos_{pid}"
    skeleton = (pdir / "Residual.lean").read_text()
    meta = ((h.state.get("residual") or {}).get("meta")) or {}
    parsed = H.parse_residual(skeleton, pid, meta, main=main_thm)
    target = next((x for x in parsed["hypotheses"] if x["name"] == o["premise"]), None)
    if not target or not (target["open"] and target["kind"] == "published"):
        raise SystemExit(f"{o['premise']} is not an open published premise of {pdir / 'Residual.lean'}")
    chosen = h._weakening_target(parsed, skeleton, H.failure_counts(pdir))
    premise_pol = getattr(args, "premise_attack", "full")
    if a.candidate:
        cand = (data / a.candidate).read_text() if not Path(a.candidate).is_absolute() else Path(a.candidate).read_text()
        reply = ("```lean\n" + cand + "\n```\n```json\n" + json.dumps({"weakenings": [{
            "premise": o["premise"], "weakened": a.weakened, "how": "replayed", "mathlib": None, "from_premise": None,
            "difficulty": "unrated", "why": f"replayed from {a.candidate}"}]}) + "\n```\n")

        def ask(purpose, prompt, **kw):
            if purpose != "weaken":
                raise RuntimeError(f"free replay: no model call ({purpose})")
            return reply
        h.ask = ask
        h._attack_substatement = lambda *x, **k: (None, None)       # no child in a free replay
        h._circular_premise = lambda *x, **k: None                  # its judge is a model call; reported as not run
        h.args.plan_repairs = 0                                     # a repair round is a model call too
        premise_pol = "cheap"
    cdir = pdir / "cycles" / f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-replay"
    cdir.mkdir(parents=True)
    t0, spent0 = time.time(), h.spent_usd()
    r = h._weaken_premise(pdir, cdir, 99, skeleton, parsed, meta, H.statement_prefix(h.state["statement"]), main_thm,
                          None, target, premise_pol, pdir / "Lemmas.lean", pdir / "Residual.lean", pdir / "ledger.jsonl")
    events = []
    for line in h.log.path.read_text().splitlines():
        e = json.loads(line)
        if e.get("stage") == "program" and str(e.get("event", "")).startswith(
                ("premise_weake", "weakening_", "pieces_", "weaken_", "plan_repair", "hypothesis_discharged", "splice_failed")):
            events.append({k: v for k, v in e.items() if k not in ("ts", "stage")})
    final = H.parse_residual((pdir / "Residual.lean").read_text(), pid, r["meta"], main=main_thm)
    rec = {**o, "replay_dir": str(base), "mode": "free" if a.candidate else "paid", "candidate": a.candidate,
           "chosen_by_harness": chosen["name"] if chosen else None, "premise_attack": premise_pol,
           "proposal": (h.state.get("weakenings") or [None])[-1], "events": events,
           "adopted": any(e.get("event") == "premise_weakened" for e in events), "proved": r["proved"],
           "metric_before": parsed["metric"], "metric_after": final["metric"],
           "open_after": [x["name"] for x in final["hypotheses"] if x["open"]],
           "spent_usd": round(h.spent_usd() - spent0, 4), "wall_s": round(time.time() - t0, 1)}
    (base / "RESULT.json").write_text(json.dumps(rec, indent=1, default=str))
    print(json.dumps({k: rec[k] for k in ("problem", "alias", "premise", "mode", "adopted", "proved", "metric_after",
                                          "open_after", "spent_usd", "wall_s")}, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
