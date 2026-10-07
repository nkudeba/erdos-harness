"""A seeded random sample of unsolved problems, for the v6 screen on TYPICAL open problems. No model calls.

Step 3 screened the top of the `partial` ranking, which favours heavily studied problems. Their forum discussions are
several times longer than the median unsolved problem's (`--depth` prints the comparison). A uniform sample measures
what the harness does on the open problems it would meet at random. That is the operator's question: whether the
harness applies to most open problems, not to the most promising few.

Candidates:
- every problem the Atlas lists as Unsolved;
- minus step 3's twenty, and minus the problems openai/math claims;
- minus any problem with a campaign blackboard, because an earlier run would change the engine's input.

The candidates are shuffled with a fixed seed. The script walks them in that order until K have a parseable
formal-conjectures main theorem at step 3's pinned commit. Each picked problem gets:
- its forum thread and proof-claims page re-fetched (`atlas-data/fetch_forum.py --refresh`), so a fresh claimed
  resolution is seen;
- a `library/<n>/DIGEST.md`, built as prep.py builds it.

Writes step3/sample.json.

    python3 experiments/idea-engine-2026-10-02/step3/sample_open.py --k 12
    python3 experiments/idea-engine-2026-10-02/step3/sample_open.py --depth      # study depth only, no fetching
"""
import argparse, importlib.util, json, random, re, statistics, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
import timesplit as T

_spec = importlib.util.spec_from_file_location("od_screen", ROOT / "experiments" / "open-discovery-2026-10-02" / "screen.py")
OD = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(OD)

SEED = 20261007
STEP3 = {7, 488, 20, 273, 120, 686, 835, 366, 617, 364, 647, 396, 536, 677, 307, 951, 886, 885, 138, 873}


def forum_chars(n: int) -> int | None:
    """Characters of actual forum comments: the thread between "Order by" and the site's footer, menus excluded."""
    f = ROOT / "atlas-data" / "forum" / f"{n}.json"
    if not f.exists():
        return None
    t = json.loads(f.read_text()).get("thread") or ""
    i = t.find("Order by")
    return len((t[i:] if i >= 0 else "").split("All comments are the responsibility of the user")[0])


def refs(n: int, parsed: dict) -> int:
    return len(set(re.findall(r"\[([A-Za-z][A-Za-z]*\d{2}[a-z]?)\]", (parsed.get(n) or {}).get("discussion") or "")))


def candidates() -> list[int]:
    ranks = json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]
    om = json.loads((ROOT / "atlas-data" / "openai-math-2026-10-06.json").read_text())
    claimed = {int(r["problem"]) for kind in ("claimed_resolved", "claimed_partial") for r in om.get(kind) or []}
    return sorted(p["id"] for p in ranks if p.get("status") == "Unsolved" and p["id"] not in STEP3 and p["id"] not in claimed
                  and not (ROOT / "programs" / f"erdos_{p['id']}" / "BLACKBOARD.md").exists())


def depth_report(ids_by_name: dict[str, list[int]]) -> dict:
    parsed = {p["id"]: p for p in json.loads((ROOT / "atlas-data" / "parsed.json").read_text())}
    out = {}
    for name, ids in ids_by_name.items():
        fc = [x for x in (forum_chars(i) for i in ids) if x is not None]
        out[name] = {"n": len(ids), "median_forum_comment_chars": statistics.median(fc) if fc else None,
                     "median_refs": statistics.median(refs(i, parsed) for i in ids) if ids else None}
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=12)
    ap.add_argument("--depth", action="store_true", help="print the study-depth comparison only")
    a = ap.parse_args()
    cands = candidates()
    unsolved = [p["id"] for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]
                if p.get("status") == "Unsolved"]
    if a.depth:
        print(json.dumps(depth_report({"step-3 twenty": sorted(STEP3), "all unsolved": unsolved,
                                       "sample candidates": cands}), indent=1))
        return 0
    order = cands[:]
    random.Random(SEED).shuffle(order)
    sha = (HERE / "fc-sha.txt").read_text().strip()
    picked, skipped = [], []
    for n in order:
        if len(picked) >= a.k:
            break
        src = T.fetch(T.SOURCES["fc_file"].format(sha=sha, n=n), HERE / "fc" / f"{n}.lean", pause=0.1)
        fc = T.parse_fc(src, int(n)) if src.strip() else {"error": "no formal-conjectures file"}
        if fc.get("error"):
            skipped.append({"problem": n, "why": fc["error"][:200]})
            continue
        picked.append({"problem": n, "form": fc.get("form"), "statement_chars": len(T.frozen_statement(fc, int(n)))})
        print(json.dumps(picked[-1]), flush=True)
    nums = [str(x["problem"]) for x in picked]
    subprocess.run([sys.executable, str(ROOT / "atlas-data" / "fetch_forum.py"), "--refresh", "--problems", *nums], check=True)
    for x in picked:
        lib = HERE / "library" / str(x["problem"])
        lib.mkdir(parents=True, exist_ok=True)
        (lib / "DIGEST.md").write_text(OD.thread_digest(str(x["problem"])))
        x["digest_chars"] = len((lib / "DIGEST.md").read_text())
    rep = depth_report({"step-3 twenty": sorted(STEP3), "all unsolved": unsolved, "sample": [x["problem"] for x in picked]})
    (HERE / "sample.json").write_text(json.dumps({"seed": SEED, "fc_sha": sha, "candidates": len(cands),
                                                  "order_head": order[:80], "picked": picked, "skipped": skipped,
                                                  "depth": rep}, indent=1))
    print(json.dumps(rep, indent=1))
    print(f"{len(picked)} picked, {len(skipped)} skipped for no single main theorem: {' '.join(nums)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
