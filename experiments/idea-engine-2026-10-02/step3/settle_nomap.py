"""REPORT 3.10: SETTLE CHANCE with no frontier map, one call per problem, as a cheap order for the campaign's queue.

The screen's prompt (the deep plan under the resolve objective, before any work) with the map slot left empty: the model
judges from the statement and what it knows. About $0.40 a call against $3-6 for a map.

    python3 experiments/idea-engine-2026-10-02/step3/settle_nomap.py --calib   # 3.8's dev items (2 draws, masked as
                                                                              # their runs were) and 3.9's open problems
    python3 experiments/idea-engine-2026-10-02/step3/settle_nomap.py --sweep   # every problem in the campaign's queue

Rows go to `step3/settle_nomap.jsonl` (calibration) or `resolution/prescreen.jsonl` (the sweep, read by
`resolution.queue`); a problem already there is skipped, so a cut-off run resumes. Dev items never enter the sweep: the
queue holds only unsolved catalogue problems.
"""
import json, sys
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
import harness as H

NO_MAP = "(none drawn yet: judge from the problem statement and what you know of the literature)"
DEV = {"401": True, "618": True, "1125": True, "570": False, "865": False, "888": False}    # 3.8's items and outcomes


def prompt(statement: str, lean: str) -> str:
    return H.DEEP_PLAN_PROMPT.format(statement=statement, lean=lean, frontier=NO_MAP, results=H.SETTLE_SCREEN_RESULTS,
                                     objective=H.DEEP_OBJECTIVES["resolve"])


def draw(statement: str, lean: str, masked: bool) -> dict:
    inner = H.ClaudeCliBackend(H.DEFAULT_CLAUDE_MODEL, timeout=1800, call_budget_usd=2.0)
    be = H.MaskedBackend(inner) if masked else inner
    try:
        text = be.complete("engine-settle-prescreen", prompt(statement, lean), effort_override="high", budget_override=2.0)
    except RuntimeError as e:
        if H.ClaudeCliBackend.HARD_RE.search(str(e)):
            raise                                        # a usage limit stops the script; a rerun resumes it
        text = None
    meta = getattr(inner, "last_meta", {}) or {}
    goal = dict((k.upper(), b) for k, b in H.delimited_sections(text or "")).get("GOAL") or text or ""
    return {"chance": H.settle_chance(text), "cost": round(float(meta.get("cost_usd") or 0.0), 4), "goal": goal[:600]}


def jobs_calib() -> list[dict]:
    out = []
    rows = {}
    for l in (ROOT / "benchmarks" / "timesplit" / "results" / "engine-v5-dev.jsonl").read_text().splitlines():
        r = json.loads(l)
        rows[r["problem"]] = r
    for n, solved in DEV.items():
        prob = json.loads((ROOT / rows[n]["run_dir"] / "problem.json").read_text())
        lean = json.loads((ROOT / rows[n]["run_dir"] / "state.json").read_text())["statement"]
        out.append({"problem": n, "set": "dev", "solved": solved, "statement": prob["statement"], "lean": lean,
                    "masked": True, "k": 2})
    for l in (HERE / "settle_open_b.jsonl").read_text().splitlines():
        r = json.loads(l)
        prob = json.loads((ROOT / r["run_dir"] / "problem.json").read_text())
        lean = json.loads((ROOT / r["run_dir"] / "state.json").read_text())["statement"]
        out.append({"problem": str(r["problem"]), "set": "open", "map_mean": r["mean"], "statement": prob["statement"],
                    "lean": lean, "masked": False, "k": 1})
    return out


def jobs_sweep() -> list[dict]:
    """Every queued problem with a formal-conjectures main theorem, frozen exactly as the campaign's screen freezes it
    (the pinned commit, the answer stripped). A problem with none is one the campaign skips at prep, so it is left out."""
    import resolution as R
    import timesplit as T
    cfg = R.load_cfg()
    ranks = {int(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    out = []
    for n in R.queue(R.load_state(), cfg):
        src = T.fetch(T.SOURCES["fc_file"].format(sha=cfg["fc_sha"], n=n), R.CAMP / "fc" / f"{n}.lean", pause=0.1)
        fc = T.parse_fc(src, int(n)) if src.strip() else {"error": "no formal-conjectures file"}
        if fc.get("error"):
            continue
        out.append({"problem": str(n), "set": "queue", "statement": ranks[n]["statement"],
                    "lean": T.frozen_statement(fc, int(n)), "masked": False, "k": 1})
    return out


def main() -> int:
    sweep = "--sweep" in sys.argv
    out = (ROOT / "resolution" / "prescreen.jsonl") if sweep else (HERE / "settle_nomap.jsonl")
    done = {json.loads(l)["problem"] for l in out.read_text().splitlines() if l.strip()} if out.exists() else set()
    todo = [j for j in (jobs_sweep() if sweep else jobs_calib()) if j["problem"] not in done]
    print(f"{len(todo)} problems to draw ({len(done)} done) -> {out}", flush=True)

    def one(j):
        draws = [draw(j["statement"], j["lean"], j["masked"]) for _ in range(j["k"])]
        vals = [d["chance"] for d in draws if d["chance"] is not None]
        rec = {k: v for k, v in j.items() if k not in ("statement", "lean", "k")}
        rec.update({"mean": round(sum(vals) / len(vals), 4) if vals else None, "draws": [d["chance"] for d in draws],
                    "cost": round(sum(d["cost"] for d in draws), 4), "goals": [d["goal"] for d in draws],
                    # UTC in the campaign's own format: resolution.spent_since counts a sweep's cost against the daily cap
                    "at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")})
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{j['problem']} [{j['set']}]: {rec['draws']} mean {rec['mean']} ${rec['cost']:.2f}"
              + (f" (map {j['map_mean']})" if "map_mean" in j else "") + (f" solved={j['solved']}" if "solved" in j else ""),
              flush=True)

    with ThreadPoolExecutor(max_workers=4) as ex:
        list(ex.map(one, todo))
    return 0


if __name__ == "__main__":
    sys.exit(main())
