"""REPORT 3.9: the ripeness screen's SETTLE CHANCE on the open problems whose frontier maps are already on disk.

No new map. For each open campaign target (unsolved in the Atlas, not claimed by openai/math) with an engine checkpoint
holding a map, two draws from its LATEST map through the screen's own code (`harness.engine_settle_screen`), unmasked as
the campaign runs. One row per problem in `step3/settle_open.jsonl`; a problem already there is skipped, so a cut-off run
resumes. `resolution.py import-screens` takes the rows at or above the bar into the campaign.

    python3 experiments/idea-engine-2026-10-02/step3/settle_open.py [--dry-run]
"""
import json, sys
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
import harness as H

OUT = HERE / "settle_open.jsonl"


def targets() -> dict[int, Path]:
    ranks = {int(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    om = json.loads((ROOT / "atlas-data" / "openai-math-2026-10-06.json").read_text())
    claimed = {int(r["problem"]) for k in ("claimed_resolved", "claimed_partial") for r in om.get(k) or []}
    latest: dict[int, Path] = {}
    for run in sorted((ROOT / "runs").glob("*-erdos*")):
        tail = run.name.split("erdos")[-1]
        if not tail.isdigit() or int(tail) in claimed or (ranks.get(int(tail)) or {}).get("status") != "Unsolved":
            continue
        try:
            ck = json.loads((run / "engine" / "checkpoint.json").read_text())
        except (OSError, ValueError):
            continue
        if (ck.get("frontier") or {}).get("text"):
            latest[int(tail)] = run                      # sorted by name, so the last one is the newest
    return latest


def call(purpose, prompt, effort, budget):
    be = H.ClaudeCliBackend(H.DEFAULT_CLAUDE_MODEL, timeout=1800, call_budget_usd=float(budget or 2.0))
    try:
        text = be.complete(purpose, prompt, effort_override=effort, budget_override=budget)
    except RuntimeError as e:
        if H.ClaudeCliBackend.HARD_RE.search(str(e)):
            raise                                        # a usage limit stops the script; a rerun resumes it
        raise H.DiscoveryCallFailed(str(e)[:300], cost=float((getattr(be, "last_meta", {}) or {}).get("cost_usd") or 0.0))
    return text, float((getattr(be, "last_meta", {}) or {}).get("cost_usd") or 0.0)


def main() -> int:
    done = {json.loads(l)["problem"] for l in OUT.read_text().splitlines() if l.strip()} if OUT.exists() else set()
    todo = {n: r for n, r in sorted(targets().items()) if n not in done}
    print(f"{len(todo)} problems to draw ({len(done)} done)", flush=True)
    if "--dry-run" in sys.argv:
        for n, r in todo.items():
            print(n, r.name)
        return 0
    s = H.EngineSettings(settle_draws=2)

    def one(item):
        n, run = item
        ck = json.loads((run / "engine" / "checkpoint.json").read_text())
        statement = json.loads((run / "problem.json").read_text())["statement"]
        scr = H.engine_settle_screen(call, s, statement, H.frontier_block(ck["frontier"]), H._DiscoverySpend(10.0))
        settings = (json.loads((run / "engine" / "engine.json").read_text()).get("settings") or {}
                    if (run / "engine" / "engine.json").exists() else {})
        rec = {"problem": n, "run_dir": str(run.relative_to(ROOT)), "objective": settings.get("objective", "advance"),
               "mean": scr["mean"], "draws": [d.get("chance") for d in scr["draws"]], "cost": scr["cost"],
               "goals": [d.get("goal", "")[:600] for d in scr["draws"]], "at": datetime.now().isoformat(timespec="seconds")}
        with OUT.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{n}: {rec['draws']} mean {rec['mean']} ${rec['cost']:.2f}", flush=True)

    with ThreadPoolExecutor(max_workers=4) as ex:
        list(ex.map(one, todo.items()))
    rows = [json.loads(l) for l in OUT.read_text().splitlines() if l.strip()]
    means = sorted((r["mean"] for r in rows if r["mean"] is not None), reverse=True)
    print(f"\n{len(rows)} problems, ${sum(r['cost'] for r in rows):.2f}; at or above 0.3: "
          f"{[r['problem'] for r in rows if (r['mean'] or 0) >= 0.3]}; median {means[len(means) // 2] if means else None}; "
          f"draws within 0.1: {sum(1 for r in rows if None not in r['draws'] and max(r['draws']) - min(r['draws']) <= 0.1)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
