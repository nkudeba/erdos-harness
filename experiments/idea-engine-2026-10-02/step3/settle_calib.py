"""REPORT 3.8: does the deep dive's SETTLE CHANCE, asked before any work, separate solvable problems from the rest?

Step 2's six unrecognized dev items with known outcomes. For each, the deep-dive plan prompt under the resolve objective,
given only that run's frontier map (KNOWN, BARRIERS, CORE) and no results, masked as the run was; two draws each.

    python3 experiments/idea-engine-2026-10-02/step3/settle_calib.py
"""
import json, re, sys
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
import harness as H

ITEMS = {"401": True, "618": True, "1125": True, "570": False, "865": False, "888": False}


def chance(text: str):
    m = re.search(r"(?i)SETTLE CHANCE\s*:\s*\**\s*([01](?:\.\d+)?|\.\d+)", text or "")
    return float(m.group(1)) if m else None


def main() -> int:
    rows = {}
    for l in (ROOT / "benchmarks" / "timesplit" / "results" / "engine-v5-dev.jsonl").read_text().splitlines():
        r = json.loads(l)
        rows[r["problem"]] = r
    out = HERE / "settle_calib.jsonl"
    for n, solved in ITEMS.items():
        run = ROOT / rows[n]["run_dir"]
        ej = json.loads((run / "engine" / "engine.json").read_text())
        prob = json.loads((run / "problem.json").read_text())
        prompt = H.DEEP_PLAN_PROMPT.format(statement=prob["statement"], frontier=H.frontier_block(ej["frontier"]),
                                           results="(none yet: this assessment comes before any work)",
                                           objective=H.DEEP_OBJECTIVES["resolve"])
        draws = []
        for k in range(2):
            be = H.MaskedBackend(H.ClaudeCliBackend("claude-opus-5-5", timeout=1800, call_budget_usd=2.0))
            text = be.complete("engine-deep-plan", prompt, effort_override="high", budget_override=2.0)
            meta = getattr(be, "last_meta", None) or getattr(getattr(be, "_inner", None), "last_meta", {}) or {}
            draws.append({"chance": chance(text), "cost": meta.get("cost_usd"), "goal": text[:600]})
        rec = {"problem": n, "solved": solved, "draws": draws, "at": datetime.now().isoformat(timespec="seconds")}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{n} solved={solved} chances={[d['chance'] for d in draws]}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
