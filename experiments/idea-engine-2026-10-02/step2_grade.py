"""Grade step 2's engine runs after the fact, with the two checks #204 showed the first rule needed.

- **Recognition.** Did the engine name the real problem? A masked run that names it recalled the problem, so its
  answer is no evidence of unaided research. On #204 the frontier map wrote "I believe this is Erdős Problem #204" and
  recalled the 2025 resolution.
- **Complete.** An unconditional valid claim that BOTH settles judges agree answers the problem, whatever its novelty
  verdict. It is correct if it lands on the true side. #204's two refereed proofs of the full answer were rated "known"
  by judges who remembered the paper, so the novelty-based rule (`valid-restatement`) missed them.

The settles judges run through the harness's own backend, masked: 2 calls for each of the top `--max` claims of a
run. Runs from the engine that already carry settles verdicts are not re-judged.

    python3 experiments/idea-engine-2026-10-02/step2_grade.py --tag engine-v5-dev [--problems 204]
"""
import argparse, json, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import harness as H

RESULTS = ROOT / "benchmarks" / "timesplit" / "results"


def call(purpose: str, prompt: str, effort, budget):
    """The discovery `call`: one fresh masked backend per call, so parallel judges keep their own costs."""
    be = H.MaskedBackend(H.ClaudeCliBackend(model="claude-opus-5-5", timeout=1800, call_budget_usd=max(float(budget or 0.5), 0.5)))
    try:
        text = be.complete(purpose, prompt, effort_override=effort, budget_override=budget)
    except Exception as e:                                   # noqa: BLE001 - a failed judge is a missing verdict
        raise H.DiscoveryCallFailed(str(e)[:300], cost=float((getattr(be, "last_meta", None) or {}).get("cost_usd") or 0))
    return text, float((getattr(be, "last_meta", None) or {}).get("cost_usd") or 0)


def grade(row: dict, truth: str, k: int) -> dict:
    run = ROOT / row["run_dir"]
    ej = json.loads((run / "engine" / "engine.json").read_text())
    st = json.loads((run / "state.json").read_text())
    prob = json.loads((run / "problem.json").read_text())
    led = ej.get("ledger") or []
    H.engine_resolve(led)
    s, spend = H.EngineSettings(), H._DiscoverySpend(50)
    cands = sorted((c for c in led if c.get("status") in ("PROVED", "REFUTED")
                    and H._valid_status((c.get("validation") or {}).get("status"))),
                   key=lambda c: (str(((c.get("validation") or {}).get("novelty") or {}).get("verdict")) in ("restatement", "known"),
                                  ((c.get("validation") or {}).get("novelty") or {}).get("significance") or 0, H._claim_rank(c)),
                   reverse=True)[:k]
    checked = []
    for c in cands:
        v = c["validation"]
        if "settles" not in v:
            v["settles"] = H.engine_settles(call, s, prob["statement"], st["statement"], c, spend)
        checked.append({"claim": H.engine_claim_key(c), "novelty": (v.get("novelty") or {}).get("verdict"),
                        "settles": v["settles"].get("settles"), "answer": v["settles"].get("answer"),
                        "why": [str(j.get("why"))[:200] for j in v["settles"].get("judges") or []],
                        "statement": " ".join(str(c.get("statement")).split())[:300]})
    best = H.engine_complete({"ledger": led})
    answer = ((((best or {}).get("validation") or {}).get("settles") or {}).get("answer")) if best else None
    rec = ej.get("recognized") if "recognized" in ej else H.engine_recognized(ej)
    return {"problem": row["problem"], "truth": truth, "run_dir": row["run_dir"], "recognized": rec,
            "recognized_true": str(row["problem"]) in [str(x) for x in rec or []],
            "complete": bool(best and answer), "answer": answer, "correct": bool(best and answer == truth),
            "claim": H.engine_claim_key(best) if best else None, "checked": checked,
            "grade_cost": round(spend.total, 4), "engine_spend": row.get("spend"),
            "at": datetime.now().isoformat(timespec="seconds")}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tag", required=True)
    ap.add_argument("--problems", nargs="*")
    ap.add_argument("--max", type=int, default=3, help="claims checked per run")
    args = ap.parse_args()
    pool = {i["problem"]: i for i in json.loads((ROOT / "benchmarks" / "timesplit" / "pool.json").read_text())["items"]}
    rows = {}
    for line in (RESULTS / f"{args.tag}.jsonl").read_text().splitlines():
        if line.strip():
            r = json.loads(line)
            rows[r["problem"]] = r                            # the latest row per problem
    out = RESULTS / f"{args.tag}.grades.jsonl"
    for n, row in sorted(rows.items(), key=lambda kv: int(kv[0])):
        if args.problems and n not in args.problems:
            continue
        g = grade(row, "true" if pool[n]["answer"] else "false", args.max)
        with out.open("a") as f:
            f.write(json.dumps(g, ensure_ascii=False) + "\n")
        print(f"#{n}: truth={g['truth']} recognized_true={g['recognized_true']} complete={g['complete']} "
              f"answer={g['answer']} correct={g['correct']} claim={g['claim']} grade ${g['grade_cost']}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
