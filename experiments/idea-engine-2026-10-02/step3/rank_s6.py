"""Select the full v6 runs from the v6 map-and-probe screen (tag s6-probe, REPORT 3.5). No model calls.

The rule was fixed before the screen launched. Rank the problems by:
1. the best probe claim's validated significance (validated-new only);
2. then the number of validated-new probe claims;
3. then the number of OPEN targets (new, significance >= 2, reach medium or high);
4. then `partial`.
Take the top 2. Writes step3/s6-selection.json.

    python3 experiments/idea-engine-2026-10-02/step3/rank_s6.py
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def probe_claims(row: dict) -> list[dict]:
    """Every judged claim of the row's probes, from the run's ledger: a probe claim that was repaired and then validated
    (#686's p4/C1r) is a probe claim too. The row's own probe list holds only the claims as first written."""
    ej = json.loads((ROOT / row["run_dir"] / "engine" / "engine.json").read_text())
    labels = {x.get("label") for x in ej.get("probes") or []}
    return [{"validation": (c.get("validation") or {}).get("status"),
             "significance": ((c.get("validation") or {}).get("novelty") or {}).get("significance")}
            for c in ej.get("ledger") or [] if c.get("session") in labels]


def key(row: dict, partial: dict) -> tuple:
    new = [c for c in probe_claims(row) if c.get("validation") == "validated-new"]
    best = max((int(c.get("significance") or 0) for c in new), default=-1)
    return (best, len(new), int(row.get("open_targets") or 0), int(partial.get(str(row["problem"])) or 0))


def main() -> int:
    rows = {}
    for line in (HERE.parent / "results.jsonl").read_text().splitlines():
        if '"s6-probe"' in line:
            r = json.loads(line)
            rows[str(r["problem"])] = r                      # a re-run problem keeps its latest row
    ranks = json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]
    partial = {str(p["id"]): p.get("partial") for p in ranks}
    order = sorted(rows.values(), key=lambda r: key(r, partial), reverse=True)
    out = [{"problem": r["problem"], "best_validated_sig": key(r, partial)[0], "validated_new": key(r, partial)[1],
            "open_targets": key(r, partial)[2], "partial": key(r, partial)[3], "spend": r.get("spend_run"),
            "run_dir": r.get("run_dir")} for r in order]
    (HERE / "s6-selection.json").write_text(json.dumps({"rule": __doc__.split("\n\n")[1], "ranked": out,
                                                        "selected": [x["problem"] for x in out[:2]]}, indent=1))
    for x in out:
        print(x)
    print("selected:", [x["problem"] for x in out[:2]])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
