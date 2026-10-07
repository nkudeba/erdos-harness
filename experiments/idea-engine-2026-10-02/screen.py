"""Run the research engine (harness.py --discover-mode engine --stop-after discover) on OPEN problems, one lane, no Lean.

Each problem gets:
- its formal-conjectures main theorem with the answer stripped, as in experiments/open-discovery-2026-10-02;
- that experiment's library: the forum digest, or for #455 the OpenAlex papers plus the forum;
- --blackboard on, so the engine starts from what earlier runs on the problem learned, and leaves its own entry.

A validated claim here is informal. It passed a step referee, an adversary and a novelty judge, and nothing more. These
problems are open, so a claim needs human review, and ideally Lean, before it means anything; claimEligible stays false.

    python3 experiments/idea-engine-2026-10-02/screen.py --tag v1 455 1203 153
"""
import argparse, json, subprocess, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PREV = ROOT / "experiments" / "open-discovery-2026-10-02"
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
sys.path.insert(0, str(ROOT))
import timesplit as T


def target_summary(ej: dict) -> dict:
    """The map-and-rate screen's result: every frontier target with the judges' pre-rating (step 3, 2026-10-07).
    The panel is conservative (`engine_novelty_panel`): `new` only if both judges say new, the lower significance and
    the lower reach. `open_targets` counts targets rated new at significance >= 2 with reach medium or high."""
    f = ej.get("frontier") or {}
    ratings = ej.get("ratings") or {}
    reach = {"low": 0, "medium": 1, "high": 2}
    rows = []
    for t in f.get("targets") or []:
        r = ratings.get(t.get("id")) or {}
        rows.append({"id": t.get("id"), "type": t.get("type"), "map_significance": t.get("significance"),
                     "verdict": r.get("verdict"), "significance": r.get("significance"), "reach": r.get("reach"),
                     "judges": [{k: j.get(k) for k in ("verdict", "significance", "reach")} for j in r.get("panel") or []
                                if isinstance(j, dict)],
                     "statement": " ".join(str(t.get("statement") or "").split())[:400]})
    new = [x for x in rows if x["verdict"] == "new" and isinstance(x["significance"], (int, float))]
    sig2 = [x for x in new if x["significance"] >= 2]
    open_ = [x for x in sig2 if reach.get(str(x["reach"] or ""), -1) >= 1]
    best = max(open_, key=lambda x: (x["significance"], reach.get(str(x["reach"]), -1)), default=None)
    return {"frontier_cost": f.get("cost"), "targets": rows, "n_targets": len(rows),
            "n_rated": sum(1 for x in rows if x["verdict"]), "n_new": len(new), "n_new_sig2": len(sig2),
            "open_targets": len(open_), "best_open": ({k: best[k] for k in ("id", "significance", "reach", "statement")}
                                                      if best else None)}


def record(run_dir: Path, n: str, tag: str, rc) -> dict | None:
    """One results.jsonl row for a finished engine run (also usable on a run started outside this script)."""
    try:
        ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        return None
    counts: dict = {}
    for c in ej.get("ledger") or []:
        st = (c.get("validation") or {}).get("status") or f"unvalidated-{str(c.get('status')).lower()}"
        counts[st] = counts.get(st, 0) + 1
    import harness as H
    rec = {"tag": tag, "problem": n, "run_dir": str(run_dir.relative_to(ROOT)), "exit": rc,
           "spend_engine": ej.get("spend"), "spend_run": H.collect_run_facts(run_dir, n).get("spend"),
           "sessions": sum(len(r.get("sessions") or []) for r in ej.get("rounds") or []),
           "claims": counts, "validated": [{k: c.get(k) for k in ("session", "id", "type", "statement")}
                                           for c in ej.get("validated") or []],
           "significance": [((c.get("validation") or {}).get("novelty") or {}).get("significance")
                            for c in ej.get("validated") or []],
           **target_summary(ej),
           "at": datetime.now().isoformat(timespec="seconds")}
    with (HERE / "results.jsonl").open("a") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problems", nargs="*")
    ap.add_argument("--tag", required=True, help="the engine version, e.g. v1")
    ap.add_argument("--total", type=float, default=30.0, help="engine budget per problem, USD")
    ap.add_argument("--flags", default="", help="extra harness flags, one string")
    ap.add_argument("--record", default=None, help="only write the results row for this finished run dir")
    ap.add_argument("--src", default=str(PREV), help="the directory holding fc/<n>.lean and library/<n>/ (default: the "
                    "open-discovery experiment; step 3 uses step3/)")
    ap.add_argument("--resume", action="append", default=[], help="a cut-off run dir to resume first, repeatable (the "
                    "engine picks up from engine/checkpoint.json); one value per flag, so it never swallows the problems")
    args = ap.parse_args()
    if args.record:
        rd = (ROOT / args.record).resolve()
        rec = record(rd, rd.name.split("erdos")[-1], args.tag, json.loads((rd / "DONE").read_text()).get("exit"))
        print(json.dumps(rec, ensure_ascii=False)[:600] if rec else "no engine record")
        return 0
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    jobs = [((ROOT / r).resolve().name.split("erdos")[-1], (ROOT / r).resolve()) for r in args.resume]
    jobs += [(n, None) for n in args.problems]
    for n, run_dir in jobs:
        src = Path(args.src).resolve()
        lib = src / "library" / (f"{n}-full" if (src / "library" / f"{n}-full").exists() else n)
        if run_dir is None:
            fc = T.parse_fc((src / "fc" / f"{n}.lean").read_text(), int(n))
            if fc.get("error"):
                print(f"#{n}: formal-conjectures parse failed: {fc['error']}", flush=True)
                continue
            statement = T.frozen_statement(fc, int(n))
            run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-erdos{n}"
            run_dir.mkdir(parents=True)
            prob = {"id": n, "statement": ranks[n]["statement"], "tags": ranks[n].get("tags") or [],
                    "url": f"https://www.erdosproblems.com/{n}",
                    "notes": "OPEN problem on erdosproblems.com. Frozen statement: formal-conjectures main theorem, answer "
                             f"stripped ({fc.get('form')}). Research engine screen {args.tag} (no Lean)."}
            (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
            (run_dir / "state.json").write_text(json.dumps({"statement": statement, "problem_input": prob, "mode": "research",
                                                            "invocations": [], "statement_source": "formal-conjectures main "
                                                            "theorem, answer stripped, via timesplit.parse_fc"}, indent=2,
                                                           ensure_ascii=False))
        cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
               str(run_dir), "--mode", "research", "--allow-research", "--no-brief", "--skip-literature",
               "--stop-after", "discover", "--discover", "on", "--discover-mode", "engine",
               "--engine-total-budget", str(args.total), "--blackboard", "on", "--library", str(lib),
               "--run-budget", str(args.total + 5), "--backend", "claude-cli", "--model", "claude-opus-5-5", "--llm-timeout", "5400",
               *args.flags.split()]
        with (run_dir / "lane.log").open("a") as log:
            rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                timeout=6 * 3600).returncode
        rec = record(run_dir, n, args.tag, rc)
        if rec is None:
            print(f"#{n}: no engine record (exit {rc}); see {run_dir}/lane.log", flush=True)
            with (HERE / f"{args.tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps({"problem": n, "run_dir": str(run_dir.relative_to(ROOT)), "exit": rc}) + "\n")
            continue
        print(f"#{n} [{args.tag}]: {len(rec['validated'])} validated new of {sum(rec['claims'].values())} claims; "
              f"targets {rec['n_targets']} (new {rec['n_new']}, sig>=2 {rec['n_new_sig2']}, open {rec['open_targets']}); "
              f"best {rec['best_open']['significance'] if rec['best_open'] else None}; ${rec['spend_run']}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
