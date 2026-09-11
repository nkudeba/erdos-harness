"""Feed what a run or an assessment taught us back into the Erdős Atlas.

The ranker already picks up mechanical evidence on its own (it scans runs/ and knowledge/solved/). What it
cannot see is the qualitative half: a feasibility assessment, a published exhaustive check that makes a
search pointless, a third-party resolution claim. This records that half and re-ranks.

    python3 atlas-data/record_finding.py --problem 287 --score 8 \
        --rationale "Counterexample floor 4e19 from published prime chains; no finite search can reach it." \
        --requirement "Target the p-adic obstruction lemma, not a search." \
        --search-floor 4e19 --source experiments/open-top3/287-assessment.md

Writing a --search-floor also stamps problems/erdos_<n>.json so the harness's triage gate can skip a futile
search on the next run without spending a model call. Run with --no-rerank to batch several findings.
"""
import argparse, datetime as dt, json, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "atlas-data"
REVIEWED = DATA / "reviewed.json"
BRIEFS = DATA / "briefs"


def load(path, default):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return default


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", required=True, help="erdosproblems.com problem number")
    ap.add_argument("--score", type=int, help="revised 0-99 feasibility score (omit to keep the current one)")
    ap.add_argument("--rationale", action="append", default=[], help="why; repeatable")
    ap.add_argument("--requirement", action="append", default=[], help="what an attempt would have to do; repeatable")
    ap.add_argument("--search-floor", type=float, default=None,
                    help="a witness/counterexample is excluded below this size (e.g. 4e19)")
    ap.add_argument("--source", action="append", default=[], help="path or URL backing this finding; repeatable")
    ap.add_argument("--assessed", help="ISO date of the assessment (default: today)")
    ap.add_argument("--partial", type=int,
                    help="revised 1-80 partial-value score (unsolved problems only): how much CERTIFIED "
                         "partial value is reachable. Independent of --score, which asks whether a COMPLETE "
                         "proof is reachable. Never sum them.")
    ap.add_argument("--floor-kind", choices=["screen", "exhaustive", "published"],
                    help="how the --search-floor was obtained: 'screen' = ruled out by a cheap arithmetic "
                         "filter, 'exhaustive' = every case actually enumerated, 'published' = a third-party "
                         "check we did not rerun. A floor is only as strong as what produced it.")
    ap.add_argument("--brief", help="path to a plain-language brief (markdown), or '-' for stdin; "
                                    "stored as atlas-data/briefs/<n>.md and shown on the problem page")
    ap.add_argument("--no-rerank", action="store_true", help="do not regenerate the rankings now")
    args = ap.parse_args()

    pid = str(int(args.problem))
    reviewed = load(REVIEWED, {})
    entry = reviewed.get(pid, {})
    if args.score is not None:
        if not 0 <= args.score <= 99:
            print("score must be 0-99", file=sys.stderr)
            return 2
        entry["score"] = args.score
    for key, values in (("rationale", args.rationale), ("requirements", args.requirement),
                        ("sources", args.source)):
        if values:
            entry[key] = list(dict.fromkeys(list(entry.get(key, [])) + values))
    if args.partial is not None:
        if not 1 <= args.partial <= 80:
            print("partial must be 1-80", file=sys.stderr)
            return 2
        entry["partial"] = args.partial
    if args.search_floor is not None:
        entry["search_floor"] = args.search_floor
        if args.floor_kind:
            entry["search_floor_kind"] = args.floor_kind
    if args.brief:
        text = sys.stdin.read() if args.brief == "-" else Path(args.brief).read_text()
        if not text.strip():
            print("--brief is empty", file=sys.stderr)
            return 2
        BRIEFS.mkdir(parents=True, exist_ok=True)
        (BRIEFS / f"{pid}.md").write_text(text.rstrip() + "\n")
        entry["brief_updated"] = dt.date.today().isoformat()
        print(f"atlas-data/briefs/{pid}.md: {len(text.split())} words")
    if entry:
        entry["assessed"] = args.assessed or dt.date.today().isoformat()
    if not entry:
        print("nothing to record", file=sys.stderr)
        return 2
    reviewed[pid] = entry
    REVIEWED.write_text(json.dumps(dict(sorted(reviewed.items(), key=lambda kv: int(kv[0]))),
                                   ensure_ascii=False, indent=2) + "\n")
    print(f"reviewed.json: #{pid} -> score={entry.get('score', '(unchanged)')}, "
          f"partial={entry.get('partial', '(unchanged)')}, "
          f"{len(entry.get('rationale', []))} rationale, {len(entry.get('requirements', []))} requirement(s)")

    # Stamp the problem file too, so the harness's triage gate sees the floor without a model call.
    if args.search_floor is not None:
        pf = ROOT / "problems" / f"erdos_{pid}.json"
        if pf.exists():
            prob = load(pf, {})
            prob["search_floor"] = args.search_floor
            # The kind travels with the number, or the next search cannot tell a cheap screen from an
            # executed sweep -- which is the entire point of typing floors.
            if args.floor_kind:
                prob["search_floor_kind"] = args.floor_kind
            elif entry.get("search_floor_kind"):
                prob["search_floor_kind"] = entry["search_floor_kind"]
            pf.write_text(json.dumps(prob, ensure_ascii=False, indent=2) + "\n")
            print(f"problems/erdos_{pid}.json: search_floor={args.search_floor:g}"
                  + (f" kind={prob['search_floor_kind']}" if prob.get("search_floor_kind") else ""))
        else:
            print(f"(no problems/erdos_{pid}.json yet; floor recorded in the Atlas only)")

    if args.no_rerank:
        print("skipped re-ranking (--no-rerank); run `python3 atlas-data/rank_problems.py` when done")
        return 0
    r = subprocess.run([sys.executable, str(DATA / "rank_problems.py")], cwd=str(ROOT),
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout[-2000:] + r.stderr[-2000:], file=sys.stderr)
        return 1
    print("rankings regenerated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
