#!/usr/bin/env python3
"""Where an arm's money went, from aggregate counts only: spend by direction (true or false) and by call purpose, and
how often the deductive loop's mechanisms fired. No transcript, prompt or proof text is read, so it is safe on dev and
test items (the time-split quarantine allows aggregates).

    python3 benchmarks/timesplit/analysis/spend_breakdown.py --tag dev-main-a88fab5 --tag baseline-v2-84f21c5 \
        --items 150 202 204 392 401

A run's tree is its run directory (the `pos`/`neg` children live under it) plus its research sub-runs under
`programs/erdos_<alias>*`. Every evaluation has a fresh alias, so that tree belongs to this run alone. A sub-run's
direction comes from its state.json (`open_direction`, else `direction`).
"""
from __future__ import annotations
import argparse, collections, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RESULTS = ROOT / "benchmarks" / "timesplit" / "results"
MECHANISMS = ("sweep", "sweep_attempt", "premises_attacked", "premise_endgame", "premise_kept", "hypotheses_deferred",
              "descent_stalled", "target_believed_false", "budget_handover", "skeleton", "skeleton_candidate_rejected")


def _jsonl(path: Path):
    try:
        for line in path.read_text().splitlines():
            try:
                yield json.loads(line)
            except ValueError:
                continue
    except OSError:
        return


def direction_of(log: Path, run_dir: Path) -> str:
    try:
        rel = log.resolve().relative_to(run_dir.resolve())
        if rel.parts and rel.parts[0] in ("pos", "neg"):
            return rel.parts[0]
        if len(rel.parts) == 1:
            return "parent"
    except ValueError:
        pass
    # a research sub-run: programs/erdos_<alias>/<pos|neg>/..., else its owner chain names the direction child
    try:
        rel = log.resolve().relative_to((ROOT / "programs").resolve())
        if len(rel.parts) > 1 and rel.parts[1] in ("pos", "neg"):
            return rel.parts[1]
    except ValueError:
        pass
    try:
        st = json.loads((log.parent / "state.json").read_text())
    except (OSError, ValueError):
        st = {}
    d = st.get("open_direction") or st.get("direction")
    if d in ("pos", "neg"):
        return d
    for owner in st.get("owner_runs") or []:
        if Path(owner).name in ("pos", "neg"):
            return Path(owner).name
    return "unknown"


def breakdown(rec: dict) -> dict:
    run_dir = ROOT / rec["run_dir"]
    logs = list(run_dir.rglob("log.jsonl")) + list((ROOT / "programs").glob(f"erdos_{rec['alias']}*/**/log.jsonl"))
    true_dir = "pos" if rec["answer"] else "neg"
    by_dir, by_purpose, events = collections.Counter(), collections.Counter(), collections.Counter()
    fallback = collections.Counter()
    for log in logs:
        d = direction_of(log, run_dir)
        role = "true" if d == true_dir else "false" if d in ("pos", "neg") else d
        for e in _jsonl(log):
            if e.get("stage") == "llm" and e.get("event") == "response" and e.get("cost_usd"):
                by_dir[role] += float(e["cost_usd"])
                by_purpose[str(e.get("purpose") or "?")] += float(e["cost_usd"])
            if e.get("stage") == "program" and e.get("event") in MECHANISMS:
                events[f"{role}:{e['event']}"] += 1
                if e["event"] == "sweep" and e.get("via") == "fallback":
                    fallback[role] += 1
                    fallback[f"{role}_proved"] += int(e.get("proved") or 0)
                    fallback[f"{role}_attempted"] += int(e.get("attempted") or 0)
    return {"problem": rec["problem"], "spend": rec.get("spend"), "by_direction": {k: round(v, 2) for k, v in by_dir.items()},
            "by_purpose": {k: round(v, 2) for k, v in by_purpose.most_common()}, "events": dict(events),
            "fallback": dict(fallback)}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tag", action="append", required=True)
    ap.add_argument("--items", nargs="*")
    a = ap.parse_args()
    for tag in a.tag:
        recs = [r for r in _jsonl(RESULTS / f"{tag}.jsonl") if not a.items or str(r["problem"]) in a.items]
        rows = [breakdown(r) for r in recs]
        tot_dir, tot_purpose, tot_events = collections.Counter(), collections.Counter(), collections.Counter()
        for r in rows:
            tot_dir.update(r["by_direction"]); tot_purpose.update(r["by_purpose"]); tot_events.update(r["events"])
            print(json.dumps({"tag": tag, **r}))
        print(json.dumps({"tag": tag, "TOTAL_by_direction": {k: round(v, 2) for k, v in tot_dir.items()},
                          "TOTAL_by_purpose": {k: round(v, 2) for k, v in tot_purpose.most_common(8)},
                          "TOTAL_events": dict(sorted(tot_events.items()))}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
