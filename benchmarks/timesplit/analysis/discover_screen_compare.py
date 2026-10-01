"""Compare a discover-screen tag with the pooled train calibration (calibration-train-v2r1, three independent v2 rounds)
on the pre-registered measures: a referee-accepted complete proof of the TRUE direction, a fooled referee, the
decided direction, and the idea grade (the best over calibration rounds 0-2 is the baseline).

    python3 benchmarks/timesplit/analysis/discover_screen_compare.py --tag train-crossfed-b222d03 [--baseline-tag T]

With --baseline-tag the baseline is another discover-screen tag instead (Screen B against Screen A)."""
import argparse, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
RES = HERE / "results"
G = {"hit": 2, "partial": 1, "miss": 0}


def jl(path):
    return [json.loads(l) for l in path.read_text().splitlines() if l.strip()] if path.exists() else []


def grades(tag):
    out = {}
    for r in jl(RES / f"{tag}.ideas.jsonl"):
        out.setdefault(r["problem"], []).append(r["grade"])
    return out


def calibration_baseline():
    recs = jl(RES / "calibration-train-v2r1.jsonl")
    by = {}
    for r in recs:
        t = "true" if r["truth"] else "false"
        b = by.setdefault(r["problem"], {"refereed_true": 0, "refereed_false": 0, "rounds": 0, "spend": 0.0, "answers": []})
        b["rounds"] += 1
        b["spend"] += r["spend"]
        for a in r["attempts"]:
            if a.get("answer") in ("true", "false"):
                b["answers"].append(a["answer"])
            if a.get("complete") and a.get("referee_valid") and a.get("answer") in ("true", "false"):
                b["refereed_true" if a["answer"] == t else "refereed_false"] += 1
        b["truth"] = t
    pooled = {}
    for tag in ("calib-ideas", "calib-ideas-r1", "calib-ideas-r2"):
        for p, gs in grades(tag).items():
            pooled.setdefault(p, []).extend(gs)
    for p, b in by.items():
        gs = [g for g in pooled.get(p, []) if g in G]
        b["idea"] = max(gs, key=G.get) if gs else None
        maj = max(set(b["answers"]), key=b["answers"].count) if b["answers"] else None
        b["direction_correct"] = maj == b["truth"] if maj else None
    return by


def screen(tag):
    out = {}
    ideas = grades(tag)
    for r in jl(RES / f"{tag}.jsonl"):
        gs = [g for g in ideas.get(r["problem"], []) if g in G]
        out[r["problem"]] = {"refereed_true": r.get("refereed_true", 0), "refereed_false": r.get("refereed_false", 0),
                             "direction_correct": r.get("direction_correct"), "commit": (r.get("decision") or {}).get("commit"),
                             "commit_correct": r.get("commit_correct"), "spend": r.get("spend"),
                             "idea": gs[-1] if gs else None, "rungs": r.get("rungs"), "syntheses": r.get("syntheses"),
                             "rounds": r.get("rounds")}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tag", required=True)
    ap.add_argument("--baseline-tag")
    a = ap.parse_args()
    new = screen(a.tag)
    base = screen(a.baseline_tag) if a.baseline_tag else calibration_baseline()
    rows, w, l = [], [], []
    for p in sorted(new, key=int):
        n, b = new[p], base.get(p, {})
        if n["idea"] and b.get("idea"):
            if G[n["idea"]] > G[b["idea"]]:
                w.append(p)
            elif G[n["idea"]] < G[b["idea"]]:
                l.append(p)
        rows.append(f"#{p:>5}  refereed_true {n['refereed_true']} (base {b.get('refereed_true')})  "
                    f"refereed_false {n['refereed_false']} (base {b.get('refereed_false')})  "
                    f"direction {n['direction_correct']} (base {b.get('direction_correct')})  commit {n['commit']}  "
                    f"idea {n['idea']} (base {b.get('idea')})  ${n['spend']} (base ${round(b.get('spend') or 0, 2)})")
    print("\n".join(rows))
    weak = [p for p in new if (base.get(p) or {}).get("refereed_true") == 0]
    print(json.dumps({
        "items": len(new),
        "refereed_true_items": sorted((p for p in new if new[p]["refereed_true"]), key=int),
        "refereed_true_on_base_never": sorted((p for p in weak if new[p]["refereed_true"]), key=int),
        "base_never_items": len(weak),
        "fooled_referee_items": sorted((p for p in new if new[p]["refereed_false"]), key=int),
        "direction_correct": sum(1 for p in new if new[p]["direction_correct"]),
        "base_direction_correct": sum(1 for p in new if (base.get(p) or {}).get("direction_correct")),
        "idea_wins": w, "idea_losses": l,
        "spend": round(sum(n["spend"] or 0 for n in new.values()), 2)}, indent=1))


if __name__ == "__main__":
    sys.exit(main())
