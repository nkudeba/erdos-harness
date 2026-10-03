"""The hard-step bank: open steps that past train runs rated HARD and never proved, attacked by the research engine.

"Steps rated hard succeed 1 time in 20" is the deductive loop's wall. Each step here comes from a time-split TRAIN
item: a problem resolved in 2026 and unknown to the model, whose run reduced it to hypotheses and left this one open.
The step is a closed Lean statement, already masked (alias ids), so its success is objective. Did the engine produce an
informal proof or refutation of the step itself, which its referee and adversary both pass? A later stage hands the proof
to Lean (blueprint + deductive loop).

    python3 experiments/idea-engine-2026-10-02/hardsteps.py --list
    python3 experiments/idea-engine-2026-10-02/hardsteps.py --tag hs1 --pick 0 4 8

Train items only: lessons may be harvested from train, never from dev or test (benchmarks/timesplit/README.md).
"""
import argparse, json, subprocess, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import harness as H

STEP_FRAME = """This is ONE STEP of an argument for the problem below, and it is the step that resisted every attack. The rest of
the argument is already proved in Lean. The step may be true or false as stated: prove it, or refute it with an explicit
counterexample. A proof of exactly this step is the goal.

THE WHOLE PROBLEM (context; it was resolved recently, and you are not told how):
{problem}

THE STEP is the Lean statement given below as THE PRECISE STATEMENT."""


def bank() -> list[dict]:
    pool = json.loads((ROOT / "benchmarks" / "timesplit" / "pool.json").read_text())
    items = pool.get("items", pool) if isinstance(pool, dict) else pool
    split = {str(i.get("problem")): i for i in items}
    out, seen = [], set()
    for f in sorted((ROOT / "benchmarks" / "timesplit" / "results").glob("*.aliases.jsonl")):
        tag = f.name.replace(".aliases.jsonl", "")
        for line in f.read_text().splitlines():
            r = json.loads(line)
            prob = str(r["problem"])
            if (split.get(prob) or {}).get("split") != "train":
                continue
            rd = ROOT / r["run_dir"]
            for d in ("pos", ""):
                sp = (rd / d / "state.json") if d else (rd / "state.json")
                if not sp.exists():
                    continue
                st = json.loads(sp.read_text())
                res = st.get("residual") or {}
                meta = {h.get("name"): h for h in ((res.get("meta") or {}).get("hypotheses") or []) if isinstance(h, dict)}
                skel = Path(res.get("skeleton") or "")
                text = skel.read_text() if skel.is_file() else ""
                for h in res.get("hypotheses") or []:
                    m = meta.get(h["name"]) or {}
                    if not (h.get("open") and h.get("kind") == "conjecture" and m.get("difficulty") == "hard"):
                        continue
                    sub = H.hypothesis_substatement(text, h["name"]) if text else None
                    key = (prob, " ".join(sub.split()))
                    if not sub or key in seen:
                        continue
                    seen.add(key)
                    out.append({"problem": prob, "alias": str(r["alias"]), "tag": tag, "run_dir": r["run_dir"],
                                "direction": d or "committed", "name": h["name"], "lean": sub,
                                "mask": (split[prob].get("mask") or {}).get("file")})
                break
    return out


def record(out: Path, tag: str, i: int, s: dict, run_dir: Path, rc) -> None:
    """Append the bank row for a finished engine run. Shared by a launch and by `--record`, which files a run
    whose launcher was killed after the engine finished (#435's first run lost its row that way)."""
    try:
        ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        print(f"[{i}] #{s['problem']} {s['name']}: no engine record (exit {rc})", flush=True)
        return
    led = ej.get("ledger") or []
    counts: dict = {}
    for c in led:
        st = (c.get("validation") or {}).get("status") or f"unvalidated-{str(c.get('status')).lower()}"
        counts[st] = counts.get(st, 0) + 1
    sound = [c for c in led if (c.get("validation") or {}).get("status", "").startswith(("valid", "validated"))]
    rec = {"tag": tag, "index": i, **{k: s[k] for k in ("problem", "alias", "name", "tag", "run_dir")},
           "engine_run": str(run_dir.relative_to(ROOT)), "exit": rc, "spend": ej.get("spend"), "claims": counts,
           "sound": [{k: c.get(k) for k in ("session", "id", "status", "type", "statement")} for c in sound],
           "at": datetime.now().isoformat(timespec="seconds")}
    with out.open("a") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print(f"[{i}] #{s['problem']} {s['name']}: {counts}; ${ej.get('spend')}", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--tag", default="hs")
    ap.add_argument("--pick", type=int, nargs="*", default=[])
    ap.add_argument("--total", type=float, default=15.0, help="engine budget per step, USD")
    ap.add_argument("--flags", default="--engine-sessions 3 --engine-rounds 2")
    ap.add_argument("--record", help="file the row for this finished engine run of the single --pick, launch nothing")
    args = ap.parse_args()
    b = bank()
    if args.list:
        for i, s in enumerate(b):
            print(f"[{i}] #{s['problem']} {s['name']} ({s['tag']}, {s['direction']}): {' '.join(s['lean'].split())[:160]}")
        return 0
    out = HERE / "hardsteps.jsonl"
    if args.record:
        if len(args.pick) != 1:
            print("--record needs exactly one --pick")
            return 2
        rd = (ROOT / args.record).resolve()
        done = (rd / "DONE").read_text().strip() if (rd / "DONE").exists() else None
        record(out, args.tag, args.pick[0], b[args.pick[0]], rd, f"recorded after the launcher died; DONE={done}")
        return 0
    for i in args.pick:
        s = b[i]
        mask = json.loads((ROOT / s["mask"]).read_text())
        sid = f"7{s['alias']}"                         # a fresh synthetic id: no program dir or Atlas entry is shared
        run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-hardstep-erdos{sid}"
        run_dir.mkdir(parents=True)
        prob = {"id": sid, "statement": STEP_FRAME.format(problem=mask["statement_en"]), "tags": [],
                "imports": mask["imports"], "benchmark": {"kind": "hard-step", "reference": "withheld"}}
        (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
        (run_dir / "state.json").write_text(json.dumps({"statement": s["lean"], "problem_input": prob, "mode": "research",
                                                        "invocations": [], "benchmark": True,
                                                        "statement_source": f"open hard step {s['name']} of {s['run_dir']}"},
                                                       indent=2, ensure_ascii=False))
        cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
               str(run_dir), "--mode", "research", "--allow-research", "--benchmark", "--masked", "--no-brief",
               "--skip-literature", "--stop-after", "discover", "--discover", "on", "--discover-mode", "engine",
               "--engine-total-budget", str(args.total), "--run-budget", str(args.total + 4),
               "--backend", "claude-cli", "--model", "claude-opus-5-5", "--llm-timeout", "5400", *args.flags.split()]
        with (run_dir / "lane.log").open("w") as log:
            rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                timeout=6 * 3600).returncode
        record(out, args.tag, i, s, run_dir, rc)
    return 0


if __name__ == "__main__":
    sys.exit(main())
