"""Score the v6 map-and-probe screen (tag s6-probe) against REPORT 3.5's predictions. No model calls.

For each problem, from its latest results row and its engine.json:
- OPEN targets: rated new, significance >= 2, reach medium or high;
- validated-new probe claims, by significance;
- traction: probes with score >= 2 or progress "strong";
- spend.

Then the totals beside the predictions, and the pre-registered comparison: probes on targets against probes on angles,
on validated-new claims per dollar.

    python3 experiments/idea-engine-2026-10-02/step3/s6_summary.py
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main() -> int:
    rows = {}
    for line in (HERE.parent / "results.jsonl").read_text().splitlines():
        if '"s6-probe"' in line:
            r = json.loads(line)
            rows[str(r["problem"])] = r
    tot = {"open": 0, "with_open": 0, "new": 0, "with_new": 0, "new2": 0, "with_new2": 0, "traction": 0, "probes": 0,
           "spend": 0.0}
    kind = {"target": {"n": 0, "cost": 0.0, "new": 0}, "angle": {"n": 0, "cost": 0.0, "new": 0}}
    print("| problem | OPEN | validated-new (significance) | traction | spend |")
    print("|---|---|---|---|---|")
    for n, r in rows.items():
        ej = json.loads((ROOT / r["run_dir"] / "engine" / "engine.json").read_text())
        probes = ej.get("probes") or []
        labels = {x.get("label") for x in probes}
        # from the ledger, so a probe claim that was repaired and then validated (#686's p4/C1r) counts for its probe
        new = [c for c in ej.get("ledger") or [] if c.get("session") in labels
               and (c.get("validation") or {}).get("status") == "validated-new"]
        sig = sorted((int(((c.get("validation") or {}).get("novelty") or {}).get("significance") or 0) for c in new),
                     reverse=True)
        trac = sum(1 for x in probes if (x.get("score") or 0) >= 2 or (x.get("verdict") or {}).get("progress") == "strong")
        spend = float(r.get("spend_run") or 0.0)
        print(f"| #{n} | {r.get('open_targets')} | {len(new)} ({', '.join(map(str, sig)) or '-'}) | {trac} of {len(probes)} | ${spend:.2f} |")
        tot["open"] += int(r.get("open_targets") or 0)
        tot["with_open"] += 1 if r.get("open_targets") else 0
        tot["new"] += len(new)
        tot["with_new"] += 1 if new else 0
        tot["new2"] += sum(1 for s in sig if s >= 2)
        tot["with_new2"] += 1 if any(s >= 2 for s in sig) else 0
        tot["traction"] += trac
        tot["probes"] += len(probes)
        tot["spend"] += spend
        for x in probes:
            k = (x.get("item") or {}).get("kind") or "target"
            k = "angle" if k == "angle" else "target"
            kind[k]["n"] += 1
            kind[k]["cost"] += float(x.get("cost") or 0.0)
            kind[k]["new"] += sum(1 for c in new if c.get("session") == x.get("label"))
    m = len(rows)
    print(f"\nproblems: {m}; spend ${tot['spend']:.2f} (predicted $90-130)")
    print(f"problems with an OPEN target: {tot['with_open']} of {m} (predicted 5, range 3-8); OPEN targets {tot['open']} "
          f"(predicted 12, range 5-24)")
    print(f"validated-new from probes: {tot['new']} (predicted 6, range 2-14) in {tot['with_new']} problems (predicted 4, 2-7)")
    print(f"validated-new at significance >= 2: {tot['new2']} (predicted 2, range 0-6) in {tot['with_new2']} problems "
          f"(predicted 2, 0-5)")
    print(f"probes with traction: {tot['traction']} of {tot['probes']} (predicted 10 of 32, range 4-18)")
    for k, v in kind.items():
        rate = v["new"] / v["cost"] if v["cost"] else 0.0
        print(f"probes on {k}s: {v['n']}, ${v['cost']:.2f}, {v['new']} validated-new, {rate:.2f} per dollar")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
