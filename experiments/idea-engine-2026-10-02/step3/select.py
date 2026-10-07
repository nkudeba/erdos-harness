"""Step 3 selection from the map-and-rate screen (`results.jsonl`, tag s3-map). No model calls.

Two rankings, printed side by side:
- PRE-REGISTERED: the best OPEN target's significance (new, significance >= 2, reach medium or high), then the number of
  OPEN targets, then `partial`.
- SIGNIFICANCE ONLY, a deviation used only if reach does not discriminate: the number of targets rated new at
  significance 3, then at significance >= 2, then `partial`. It exists because on open problems the judges rated every
  new significant target low reach (all 20 of the first four problems' significance-2 and -3 targets), so the
  pre-registered rule degenerates to `partial` alone.

    python3 experiments/idea-engine-2026-10-02/step3/select.py
"""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REACH = {"low": 0, "medium": 1, "high": 2}


def main() -> int:
    rows = {}
    for line in (HERE.parent / "results.jsonl").read_text().splitlines():
        if '"s3-map"' in line:
            r = json.loads(line)
            rows[r["problem"]] = r                      # the latest row per problem
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    table = []
    reach_by_sig = Counter()
    for n, r in rows.items():
        ts = r.get("targets") or []
        new = [t for t in ts if t.get("verdict") == "new" and isinstance(t.get("significance"), (int, float))]
        for t in new:
            reach_by_sig[(int(t["significance"]), t.get("reach"))] += 1
        open_ = [t for t in new if t["significance"] >= 2 and REACH.get(str(t.get("reach")), -1) >= 1]
        partial = ((ranks.get(n) or {}).get("partial") or {}).get("score") or 0
        table.append({"problem": n, "open_best": max((t["significance"] for t in open_), default=0),
                      "open": len(open_), "sig3": sum(1 for t in new if t["significance"] >= 3),
                      "sig2": sum(1 for t in new if t["significance"] >= 2), "partial": partial,
                      "spend": round(float(r.get("spend_run") or 0), 2),
                      "best3": next((t["statement"][:160] for t in new if t["significance"] >= 3), "")})
    pre = sorted(table, key=lambda x: (-x["open_best"], -x["open"], -x["partial"]))
    sig = sorted(table, key=lambda x: (-x["sig3"], -x["sig2"], -x["partial"]))
    print(f"{len(table)} problems screened, ${sum(x['spend'] for x in table):.2f}")
    print("new targets by (significance, reach):", dict(sorted(reach_by_sig.items(), key=str)))
    print("\nPRE-REGISTERED ranking (open_best, open, partial):")
    for x in pre[:6]:
        print(f"  #{x['problem']:>5} open_best={x['open_best']} open={x['open']} partial={x['partial']}")
    print("\nSIGNIFICANCE-ONLY ranking (sig3, sig2, partial):")
    for x in sig[:8]:
        print(f"  #{x['problem']:>5} sig3={x['sig3']} sig2={x['sig2']} partial={x['partial']}  {x['best3']}")
    (HERE / "selection.json").write_text(json.dumps({"pre_registered": pre, "significance_only": sig,
                                                      "reach_by_significance": {str(k): v for k, v in reach_by_sig.items()}},
                                                     indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
