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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problems", nargs="+")
    ap.add_argument("--tag", required=True, help="the engine version, e.g. v1")
    ap.add_argument("--total", type=float, default=30.0, help="engine budget per problem, USD")
    ap.add_argument("--flags", default="", help="extra harness flags, one string")
    args = ap.parse_args()
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    out = HERE / "results.jsonl"
    for n in args.problems:
        fc = T.parse_fc((PREV / "fc" / f"{n}.lean").read_text(), int(n))
        if fc.get("error"):
            print(f"#{n}: formal-conjectures parse failed: {fc['error']}", flush=True)
            continue
        statement = T.frozen_statement(fc, int(n))
        lib = PREV / "library" / (f"{n}-full" if (PREV / "library" / f"{n}-full").exists() else n)
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
               "--run-budget", str(args.total + 5), "--backend", "claude-cli", "--model", "claude-opus-5-5",
               *args.flags.split()]
        with (run_dir / "lane.log").open("w") as log:
            rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                timeout=6 * 3600).returncode
        try:
            ej = json.loads((run_dir / "engine" / "engine.json").read_text())
        except (OSError, ValueError):
            print(f"#{n}: no engine record (exit {rc}); see {run_dir}/lane.log", flush=True)
            with (HERE / f"{args.tag}.infra.jsonl").open("a") as f:
                f.write(json.dumps({"problem": n, "run_dir": str(run_dir.relative_to(ROOT)), "exit": rc}) + "\n")
            continue
        counts: dict = {}
        for c in ej.get("ledger") or []:
            st = (c.get("validation") or {}).get("status") or f"unvalidated-{str(c.get('status')).lower()}"
            counts[st] = counts.get(st, 0) + 1
        import harness as H
        rec = {"tag": args.tag, "problem": n, "run_dir": str(run_dir.relative_to(ROOT)), "exit": rc,
               "spend_engine": ej.get("spend"), "spend_run": H.collect_run_facts(run_dir, n).get("spend"),
               "sessions": sum(len(r.get("sessions") or []) for r in ej.get("rounds") or []),
               "claims": counts, "validated": [{k: c.get(k) for k in ("session", "id", "type", "statement")}
                                               for c in ej.get("validated") or []],
               "at": datetime.now().isoformat(timespec="seconds")}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{n} [{args.tag}]: {len(rec['validated'])} validated new of {sum(counts.values())} claims; {counts}; "
              f"${rec['spend_run']}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
