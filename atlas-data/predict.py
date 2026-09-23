"""Predictions and calibration for the Erdős Atlas.

The priority `score` is a sum of hand-assigned points. It has never been checked against an outcome, so
it cannot be read as a probability — and the two outcomes it silently merges are very different events:

    reconstruct a resolution that already exists in the literature   19 attempts, 19 successes
    resolve a problem that is open                                    7 attempts,  0 successes

You cannot calibrate from zero successes, and you cannot calibrate at all without predictions recorded
BEFORE the outcome. This module does both halves: it writes a prediction row per attempt, and it scores
the log once outcomes land.

    python3 atlas-data/predict.py estimate --problem 273     # decomposed, zero model calls
    python3 atlas-data/predict.py estimate --all             # every catalogue problem, still free
    python3 atlas-data/predict.py record --problem 273 --p-resolve 0.001 --basis "..."
    python3 atlas-data/predict.py score                      # Brier + calibration, once outcomes exist

Estimates are REFERENCE-CLASS CEILINGS, not calibrated probabilities, and say so in every row.
"""
import argparse, datetime as dt, json, math, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "atlas-data"
LOG = DATA / "predictions.jsonl"
SEARCH_REACH = 10 ** 9          # what a bounded search in this harness can actually enumerate
MODEL = "decomposed-v1"

FINITE_CLASSES = {"falsifiable", "verifiable", "decidable"}


def load(path, default):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return default


def jeffreys(successes: int, trials: int) -> tuple[float, float, float]:
    """Point estimate and a 90% interval under the Jeffreys prior, so 0/7 does not become exactly 0."""
    a, b = successes + 0.5, trials - successes + 0.5
    mean = a / (a + b)
    # crude but adequate beta quantiles by bisection on the regularised incomplete beta
    def cdf(x):
        # Integrate the density numerically (trials here are tiny). Midpoints, not endpoints: with
        # successes = 0 the Jeffreys density has a = 0.5 and blows up at t = 0.
        steps = 4000
        tot = s = 0.0
        for i in range(steps):
            t = (i + 0.5) / steps
            w = (t ** (a - 1)) * ((1 - t) ** (b - 1))
            tot += w
            if t <= x:
                s += w
        return s / tot if tot else 0.0
    def q(p):
        lo, hi = 0.0, 1.0
        for _ in range(40):
            mid = (lo + hi) / 2
            if cdf(mid) < p:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2
    return mean, q(0.05), q(0.95)


_JEFF = {}


def jeffreys_cached(successes: int, trials: int):
    key = (successes, trials)
    if key not in _JEFF:
        _JEFF[key] = jeffreys(successes, trials)
    return _JEFF[key]


def outcomes() -> dict:
    """What actually happened, split by event class. Read from the ranker's own evidence labels."""
    ranked = load(DATA / "rankings.json", {}).get("problems", [])
    known = [p for p in ranked if p["status"] == "Solved" and p["harness"] != "Untried"]
    openp = [p for p in ranked if p["status"] == "Unsolved" and p["harness"] != "Untried"]
    return {
        "reconstruct": {"trials": len(known), "successes": sum(1 for p in known if p["harness"] == "Verified")},
        "resolve_open": {"trials": len(openp), "successes": sum(1 for p in openp if p["harness"] == "Verified")},
    }


def estimate(problem: dict, obs: dict) -> dict:
    """P(complete resolution) = reachability x class base rate. Both factors free to compute.

    The reachability factor is the honest one: it is arithmetic, not opinion. A recorded search floor
    beyond what a bounded search can enumerate pins it to 0 regardless of anything else, which is why
    most of the catalogue costs nothing to triage.
    """
    solved = problem["status"] == "Solved"
    cls = "reconstruct" if solved else "resolve_open"
    o = obs[cls]
    base, lo, hi = jeffreys_cached(o["successes"], o["trials"])
    floor = (problem.get("assessed") or {}).get("searchFloor")
    finite = problem.get("state") in FINITE_CLASSES
    reasons = []
    reach = 1.0
    if not solved:
        if not finite:
            reach = 0.0
            reasons.append("open and not in a finite-certificate class: a resolution needs an infinite "
                           "argument either way, which is new mathematics")
        elif isinstance(floor, (int, float)) and floor > SEARCH_REACH:
            reach = 0.0
            reasons.append(f"recorded search floor {floor:.3g} exceeds the bounded-search reach "
                           f"{SEARCH_REACH:.0g}: any witness is out of range")
        elif isinstance(floor, (int, float)):
            reasons.append(f"finite-certificate class with a floor of {floor:.3g}, inside reach")
        else:
            reasons.append("finite-certificate class, no floor recorded: reachability unknown, "
                           "not assumed favourable")
    else:
        reasons.append("already resolved in the literature, so the event is reconstruction, not a solve")
        if problem.get("harness") == "Untried":
            # 19/19 was earned on targets CHOSEN for being reconstructable (short community proofs).
            # Applying it to a problem nobody has looked at would launder that selection into a
            # prediction. Refuse to emit a number instead.
            reasons.append("never attempted: the reference class is selection-biased upward and no "
                           "conditioning feature (community-proof length) is recorded for this problem, "
                           "so no estimate is given rather than a flattering one")
            return {"problem": problem["id"], "event": cls, "p_resolve_ceiling": None,
                    "class_base_rate": round(base, 4), "class_observed": f"{o['successes']}/{o['trials']}",
                    "reachability": None, "partial_axis": (problem.get("partial") or {}).get("score"),
                    "calibrated": False, "estimable": False, "model": MODEL, "reasons": reasons}
    p = reach * base
    return {"problem": problem["id"], "event": cls, "p_resolve_ceiling": round(p, 6),
            "class_base_rate": round(base, 4), "class_interval_90": [round(lo, 4), round(hi, 4)],
            "class_observed": f"{o['successes']}/{o['trials']}", "reachability": reach,
            "partial_axis": (problem.get("partial") or {}).get("score"),
            "calibrated": False, "model": MODEL, "reasons": reasons}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("estimate", help="decomposed reference-class ceiling; no model calls")
    e.add_argument("--problem"); e.add_argument("--all", action="store_true")
    e.add_argument("--nonzero", action="store_true", help="only problems whose ceiling is not 0")
    r = sub.add_parser("record", help="log a prediction BEFORE the outcome is known")
    r.add_argument("--problem", required=True)
    r.add_argument("--p-resolve", type=float, required=True)
    r.add_argument("--p-partial", type=float)
    r.add_argument("--basis", required=True, help="why; recorded so a wrong prediction is diagnosable")
    r.add_argument("--by", default="harness")
    sc = sub.add_parser("score", help="Brier score and calibration over the log")
    sc.add_argument("--log", default=str(LOG), help="predictions log (default: atlas-data/predictions.jsonl)")
    sc.add_argument("--runs", default=str(ROOT / "runs"), help="run directories to settle predictions against")
    args = ap.parse_args()

    ranked = {str(p["id"]): p for p in load(DATA / "rankings.json", {}).get("problems", [])}
    obs = outcomes()

    if args.cmd == "estimate":
        if args.problem:
            p = ranked.get(str(int(args.problem)))
            if not p:
                print(f"unknown problem {args.problem}", file=sys.stderr)
                return 2
            print(json.dumps(estimate(p, obs), indent=2))
            return 0
        rows = [estimate(p, obs) for p in ranked.values()]
        estimable = [r for r in rows if r["p_resolve_ceiling"] is not None]
        skipped = len(rows) - len(estimable)
        rows = estimable
        if args.nonzero:
            rows = [r for r in rows if r["p_resolve_ceiling"] > 0]
        rows.sort(key=lambda r: -r["p_resolve_ceiling"])
        print(f"observed outcomes: reconstruct {obs['reconstruct']['successes']}/"
              f"{obs['reconstruct']['trials']}, resolve_open {obs['resolve_open']['successes']}/"
              f"{obs['resolve_open']['trials']}")
        print(f"{skipped} problems not estimated (already resolved, never attempted: the reconstruction "
              f"reference class is selection-biased and nothing here conditions it)")
        print(f"{len(rows)} estimated; these are reference-class CEILINGS, not calibrated probabilities\n")
        print(f"{'problem':>8} {'ceiling':>9} {'event':>13} {'partial':>8}")
        for r in rows[:25]:
            print(f"{r['problem']:>8} {r['p_resolve_ceiling']:9.4f} {r['event']:>13} "
                  f"{str(r['partial_axis']):>8}")
        zero = sum(1 for r in rows if r["p_resolve_ceiling"] == 0)
        print(f"\n{zero} of {len(rows)} pin to exactly 0 by reachability arithmetic alone")
        return 0

    if args.cmd == "record":
        row = {"problem": str(int(args.problem)), "at": dt.datetime.now(dt.timezone.utc).isoformat(),
               "p_resolve": args.p_resolve, "p_partial": args.p_partial, "basis": args.basis,
               "by": args.by, "model": MODEL,
               "score_at_prediction": (ranked.get(str(int(args.problem))) or {}).get("score")}
        with open(LOG, "a") as fh:
            fh.write(json.dumps(row) + "\n")
        print(f"recorded: #{row['problem']} p_resolve={args.p_resolve}")
        return 0

    return score(Path(args.log), Path(args.runs))


def _when(ts: str):
    try:
        return dt.datetime.fromisoformat(str(ts).replace("Z", "+00:00"))
    except ValueError:
        return None


def attempts(runs_dir: Path) -> dict:
    """Every finished-or-not attempt under runs/: {run name: {problem, start, settled, resolved}}.

    `start` is the first timestamp in the run's own log (UTC; the directory name is local time). An attempt is
    settled when its DONE file records a finished session: resolved iff it exited 0 (proved AND verified; for an
    --open run, either direction). A fatal DONE is an infrastructure failure, not an outcome, so it stays
    unsettled. Benchmark runs are not attempts on a catalogue problem and are skipped. A resumed run is scored on
    its latest DONE, so a later session can turn a 0 into a 1: the score is recomputed, never stored."""
    out = {}
    if not runs_dir.exists():
        return out
    for d in runs_dir.iterdir():
        m = re.search(r"-erdos(\d+)$", d.name)
        if not m or "-bench-" in d.name or not (d / "log.jsonl").exists():
            continue
        start = None
        try:
            with open(d / "log.jsonl") as fh:
                for line in fh:
                    if line.strip():
                        start = _when(json.loads(line).get("ts"))
                        break
        except (OSError, ValueError):
            continue
        settled = resolved = None
        done = load(d / "DONE", None)
        if isinstance(done, dict) and "fatal" not in done:
            settled = True
            if "exit" in done:
                resolved = done["exit"] == 0
            else:
                resolved = done.get("outcome") == "proved" and done.get("verify") is True
        out[d.name] = {"problem": m.group(1), "start": start, "settled": bool(settled), "resolved": resolved}
    return out


def settle(row: dict, runs: dict):
    """The outcome of the attempt a prediction was made FOR, or None while it is unknown.

    A harness row names its run (`by: triage/<run>`). Any other row is settled by the first attempt on that
    problem that STARTED after the prediction was written. Scoring by the problem's current status instead (the
    old rule) broke the write-ahead design twice over: a prediction written before a new attempt was settled at
    once by an older one, and a failed attempt's prediction would flip to a success when a later run solved it."""
    by = str(row.get("by") or "")
    if by.startswith("triage/"):
        a = runs.get(by.split("/", 1)[1])
    else:
        at = _when(row.get("at"))
        later = [a for a in runs.values() if a["problem"] == str(row["problem"]) and a["start"] and at and a["start"] >= at]
        a = min(later, key=lambda a: a["start"]) if later else None
    if not a or not a["settled"]:
        return None
    return 1.0 if a["resolved"] else 0.0


def score(log: Path, runs_dir: Path) -> int:
    rows = [json.loads(l) for l in log.read_text().splitlines() if l.strip()] if log.exists() else []
    if not rows:
        print("no predictions logged yet; calibration is impossible until there are")
        return 0
    runs = attempts(runs_dir)
    scored = [(float(r["p_resolve"]), a, str(r["problem"])) for r in rows
              for a in [settle(r, runs)] if a is not None]
    print(f"{len(rows)} predictions logged, {len(scored)} with a settled outcome "
          f"({len(rows) - len(scored)} still waiting on their attempt)")
    if not scored:
        print("none settled yet: no Brier score, no calibration. Keep logging.")
        return 0
    base = sum(a for _, a, _ in scored) / len(scored)
    if base in (0.0, 1.0):
        # Four settled 0-probability predictions of four failures used to print "Brier score: 0.0000". With no
        # variance in the outcomes a constant guess scores just as well, so the number measures nothing.
        preds = sorted(p for p, _, _ in scored)
        print(f"no Brier score: all {len(scored)} settled outcomes are {int(base)}, so a Brier score cannot separate "
              f"forecasting skill from a constant guess (predictions ranged {preds[0]:g}–{preds[-1]:g}). Keep logging.")
        return 0
    brier = sum((p - a) ** 2 for p, a, _ in scored) / len(scored)
    ref = base * (1 - base)
    print(f"Brier score: {brier:.4f} over n={len(scored)} (0 perfect); a constant forecast at the observed rate "
          f"{base:.3f} scores {ref:.4f}, skill {1 - brier / ref:+.3f} (above 0 beats it)")
    if len(scored) < 20:
        print(f"  n={len(scored)} is too few to calibrate: read this as a record, not a calibration")
    for lo, hi in ((0, .01), (.01, .1), (.1, .5), (.5, 1.01)):
        band = [(p, a) for p, a, _ in scored if lo <= p < hi]
        if band:
            print(f"  predicted [{lo:.2f},{hi:.2f}): n={len(band)} mean_pred="
                  f"{sum(p for p, _ in band)/len(band):.3f} observed={sum(a for _, a in band)/len(band):.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
