"""Re-rate step 3's existing frontier targets under the fixed reach rubric (2026-10-07), to isolate its effect.

The screen's judges rated reach as the chance of a proof "in a day" while the map built targets for "weeks"; 69 of 70
significant new targets came out low. The fixed rubric asks for the chance in ONE focused week, with a probability
(P_WEEK). Same targets, same two judges, new rubric: the change in OPEN targets (new, significance >= 2, reach medium
or high) is the rubric's effect alone. The map's stepping-stone ladder needs new maps and is not measured here.

    python3 experiments/idea-engine-2026-10-02/step3/rerate.py
"""
import json, sys
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import harness as H


def call(purpose, prompt, effort, budget):
    be = H.ClaudeCliBackend(model="claude-opus-5-5", timeout=1800, call_budget_usd=max(float(budget or 0.5), 0.5))
    try:
        text = be.complete(purpose, prompt, effort_override=effort, budget_override=budget)
    except Exception as e:                                   # noqa: BLE001 - a failed judge is a missing verdict
        raise H.DiscoveryCallFailed(str(e)[:300], cost=float((getattr(be, "last_meta", None) or {}).get("cost_usd") or 0))
    return text, float((getattr(be, "last_meta", None) or {}).get("cost_usd") or 0)


def open_count(f, ratings):
    n = 0
    for t in f.get("targets") or []:
        r = ratings.get(t.get("id")) or {}
        if r.get("verdict") == "new" and (r.get("significance") or 0) >= 2 and H.REACH_RANK.get(str(r.get("reach")), -1) >= 1:
            n += 1
    return n


def one(row):
    ej = json.loads((ROOT / row["run_dir"] / "engine" / "engine.json").read_text())
    st = json.loads((ROOT / row["run_dir"] / "state.json").read_text())
    prob = json.loads((ROOT / row["run_dir"] / "problem.json").read_text())
    f = ej["frontier"]
    known = H.clip_middle(H.frontier_block(f), 16000)
    s, spend = H.EngineSettings(), H._DiscoverySpend(10.0)
    new = H.engine_rate_targets(call, prob["statement"], known, f.get("targets") or [], s, spend, workers=4)
    old = ej.get("ratings") or {}
    return {"problem": row["problem"], "run_dir": row["run_dir"], "open_old": open_count(f, old), "open_new": open_count(f, new),
            "new_ratings": {k: {kk: v.get(kk) for kk in ("verdict", "significance", "reach", "p_week")} for k, v in new.items()},
            "cost": round(spend.total, 4), "at": datetime.now().isoformat(timespec="seconds")}


def main() -> int:
    rows = {}
    for line in (HERE.parent / "results.jsonl").read_text().splitlines():
        if '"s3-map"' in line:
            r = json.loads(line)
            rows[r["problem"]] = r
    out = HERE / "rerate.jsonl"
    with ThreadPoolExecutor(max_workers=3) as ex:
        for res in ex.map(one, rows.values()):
            with out.open("a") as f:
                f.write(json.dumps(res, ensure_ascii=False) + "\n")
            print(f"#{res['problem']}: OPEN {res['open_old']} -> {res['open_new']}  (${res['cost']})", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
