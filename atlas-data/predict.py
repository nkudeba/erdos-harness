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
import argparse, datetime as dt, json, math, sys
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
    sub.add_parser("score", help="Brier score and calibration over the log")
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

    rows = [json.loads(l) for l in LOG.read_text().splitlines() if l.strip()] if LOG.exists() else []
    if not rows:
        print("no predictions logged yet; calibration is impossible until there are")
        return 0
    scored = []
    for row in rows:
        p = ranked.get(row["problem"])
        if not p or p["harness"] == "Untried":
            continue
        actual = 1.0 if p["harness"] == "Verified" else 0.0
        scored.append((row["p_resolve"], actual, row["problem"]))
    print(f"{len(rows)} predictions logged, {len(scored)} with a settled outcome")
    if not scored:
        print("none settled yet: no Brier score, no calibration. Keep logging.")
        return 0
    brier = sum((p - a) ** 2 for p, a, _ in scored) / len(scored)
    print(f"Brier score: {brier:.4f}  (0 perfect, 0.25 = always saying 50%)")
    for lo, hi in ((0, .01), (.01, .1), (.1, .5), (.5, 1.01)):
        band = [(p, a) for p, a, _ in scored if lo <= p < hi]
        if band:
            print(f"  predicted [{lo:.2f},{hi:.2f}): n={len(band)} mean_pred="
                  f"{sum(p for p, _ in band)/len(band):.3f} observed={sum(a for _, a in band)/len(band):.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
