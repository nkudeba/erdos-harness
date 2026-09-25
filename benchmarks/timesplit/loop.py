#!/usr/bin/env python3
"""The harness improvement loop's machinery (docs/improvement-loop.md): its state, its budget ledger, a diagnosis of
where runs get blocked, and commits to its own branch. No model calls anywhere in this file.

    python3 benchmarks/timesplit/loop.py status             # stop signals, phase, iteration, budget, in flight
    python3 benchmarks/timesplit/loop.py ack --tag <t> --problem <n> --note "..."   # a stop signal was handled
    python3 benchmarks/timesplit/loop.py diagnose [--since 2026-09-24T00:00]   # blockers, from every log on disk
    python3 benchmarks/timesplit/loop.py register --kind run --name <tag> --estimate 40
    python3 benchmarks/timesplit/loop.py can-spend --usd 40  # exit 1 if the cap would be crossed
    python3 benchmarks/timesplit/loop.py set --phase screen [--note "..."]
    python3 benchmarks/timesplit/loop.py commit -m "iteration 1: ..."   # to branch harness-loop, HEAD untouched
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, sys, tempfile
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LOOP = HERE / "loop"
STATE = LOOP / "state.json"
RESULTS = HERE / "results"
BRANCH = "harness-loop"
# what a loop commit may contain. The atlas guidance files are per-run temporaries and never belong in a commit.
COMMIT_PATHS = ["harness.py", "CLAUDE.md", ".gitignore", "docs", "tests", "benchmarks/timesplit"]
CO_AUTHOR = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------- state ---------------------------------------------

def load_state() -> dict:
    return json.loads(STATE.read_text()) if STATE.exists() else {}


def save_state(state: dict) -> None:
    LOOP.mkdir(exist_ok=True)
    state["updated"] = now()
    tmp = STATE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, indent=1, ensure_ascii=False) + "\n")
    os.replace(tmp, STATE)


# ---------------------------------------------------------------- budget --------------------------------------------
# The cap covers what the loop launches: harness runs, screens, calibrations and judges, all of which record their cost.
# The session driving the loop spends too, and that is not measurable from here; it is not counted, and the protocol
# says so.

def _jsonl(path: Path) -> list[dict]:
    try:
        return [json.loads(l) for l in path.read_text().splitlines() if l.strip()]
    except (OSError, ValueError):
        return []


def entry_spend(e: dict) -> float:
    """Actual recorded spend of one ledger entry."""
    kind, name = e.get("kind"), e.get("name")
    if kind in ("run", "explore-screen"):
        rows = _jsonl(RESULTS / f"{name}.jsonl") + _jsonl(RESULTS / f"{name}.infra.jsonl")
        return sum(float(r.get("spend") or 0) for r in rows)
    if kind == "calibration":
        return sum(float(r.get("spend") or 0) for r in _jsonl(RESULTS / f"calibration-{name}.jsonl"))
    if kind == "ideas":
        return sum(float(r.get("cost_usd") or 0) for r in _jsonl(RESULTS / f"{name}.ideas.jsonl"))
    return float(e.get("usd") or 0)                     # manual


def budget(state: dict) -> dict:
    cap = float(state.get("budget_usd") or 200.0)
    rows = []
    for e in state.get("ledger") or []:
        spent = entry_spend(e)
        # while an entry is in flight its remaining estimate stays reserved, so two launches cannot both fit
        reserve = max(0.0, float(e.get("estimate") or 0) - spent) if e.get("in_flight") else 0.0
        rows.append({**e, "spent": round(spent, 2), "reserved": round(reserve, 2)})
    spent = sum(r["spent"] for r in rows)
    reserved = sum(r["reserved"] for r in rows)
    return {"cap": cap, "spent": round(spent, 2), "reserved": round(reserved, 2),
            "left": round(cap - spent - reserved, 2), "entries": rows}


def can_spend(state: dict, usd: float) -> bool:
    return budget(state)["left"] >= usd


# ---------------------------------------------------------------- stop signals --------------------------------------
# Stopping conditions 1 and 4 are read from EVERY results file, the operator's lanes included. The loop once scored only
# its own tags, and a dev solve in the operator's discover-v2 lane (#1213, 2026-09-25) sat unnoticed for 8 hours.

NOT_RESULTS = (".infra.jsonl", ".ideas.jsonl", ".progress.jsonl", ".aliases.jsonl")


def stop_signals(state: dict | None = None) -> list[dict]:
    """Every record with a verified TRUE direction (`solved`) or a verified wrong one (`contradiction`), on any split,
    marked `acknowledged` once `loop.py ack` has recorded that it was handled."""
    acked = {(a.get("tag"), str(a.get("problem"))) for a in (state or {}).get("acknowledged") or []}
    out = []
    for f in sorted(RESULTS.glob("*.jsonl")):
        if f.name.endswith(NOT_RESULTS) or f.name.startswith("calibration-"):
            continue
        tag = f.name[: -len(".jsonl")]
        for r in _jsonl(f):
            if not (r.get("solved") or r.get("contradiction")):
                continue
            p = str(r.get("problem"))
            out.append({"tag": tag, "problem": p, "split": r.get("split"),
                        "kind": "contradiction" if r.get("contradiction") else "solve",   # the wrong direction wins
                        "run_dir": r.get("run_dir"), "started": r.get("started"),
                        "acknowledged": (tag, p) in acked})
    return out


def stops_the_loop(s: dict) -> bool:
    """Condition 1 is a solve on dev or test; condition 4 is a contradiction anywhere."""
    return s["kind"] == "contradiction" or s.get("split") in ("dev", "test")


# ---------------------------------------------------------------- diagnosis -----------------------------------------
# Counts only. It reads every log on disk, dev and test runs included, and prints numbers, never their content, so the
# loop's proposer can use it under the quarantine rule.

def iter_events(since: str | None = None):
    for f in list((ROOT / "runs").rglob("log.jsonl")) + list((ROOT / "programs").rglob("log.jsonl")):
        try:
            lines = f.read_text(errors="replace").splitlines()
        except OSError:
            continue
        for line in lines:
            if not line.strip():
                continue
            try:
                e = json.loads(line)
            except ValueError:
                continue
            if since and str(e.get("ts") or "") < since:
                continue
            yield f, e


def _bucket(reason: str) -> str:
    r = reason or ""
    for key, pat in (("compile: unknown identifier", r"Unknown (identifier|constant)"), ("compile: other", r"does not compile"),
                     ("not better than the incumbent", r"no improvement"), ("circular premise", r"circular|routine"),
                     ("refuted statement", r"refuted"), ("frozen theorem altered/missing", r"frozen"),
                     ("sorry in the glue", r"glue"), ("banned construct", r"banned")):
        if re.search(pat, r, re.I):
            return key
    return r[:40] or "(none)"


def diagnose(since: str | None = None) -> dict:
    ev = Counter()
    plan_reject = Counter()
    stop = Counter()
    cost = defaultdict(list)
    closed_by = Counter()
    recent_cost = defaultdict(list)
    cutoff = datetime.now(timezone.utc).timestamp() - 86400
    runs, recovered, cascade_passes = set(), 0, 0
    for f, e in iter_events(since):
        stage, name = e.get("stage"), e.get("event")
        ev[(stage, name)] += 1
        runs.add(str(f.parent))
        if stage == "llm" and e.get("recovered_over_budget"):
            recovered += 1
        if stage == "lean" and name == "check" and e.get("name") == "cascade":
            cascade_passes += 1
        if name == "skeleton_candidate_rejected":
            plan_reject[_bucket(str(e.get("reason")))] += 1
        elif name == "hole_closed":
            closed_by[str(e.get("by"))] += 1
        elif stage == "llm" and name in ("response", "response_failed") and e.get("cost_usd") is not None:
            cost[str(e.get("purpose"))].append(float(e["cost_usd"]))
            try:
                ts = datetime.strptime(e["ts"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()
            except (KeyError, ValueError):
                ts = 0
            if ts >= cutoff:
                recent_cost[str(e.get("purpose"))].append(float(e["cost_usd"]))
        elif name in ("descent_stalled", "target_believed_false", "stopped_on_budget", "budget_exhausted",
                      "hypotheses_deferred", "refinement_not_easier", "split_only_refinement", "notebook_missing"):
            stop[name] += 1
    g = lambda s, n: ev.get((s, n), 0)
    total = sum(sum(v) for v in cost.values())
    spend = sorted(((p, len(v), round(sum(v), 2), round(sum(v) / len(v), 3)) for p, v in cost.items()), key=lambda x: -x[2])
    rates = {
        "plans adopted / plan candidates": [g("program", "conditional_certified"),
                                             g("program", "conditional_certified") + g("program", "skeleton_candidate_rejected")],
        "plan repairs that worked": [g("program", "plan_repaired"), g("program", "plan_repair")],
        "hypotheses discharged / attacked": [g("program", "hypothesis_discharged"),
                                             g("program", "hypothesis_discharged") + g("program", "hypothesis_failed")
                                             + g("program", "refine_failed")],
        "refinements spliced / proposed": [g("program", "hypothesis_refined"),
                                           g("program", "hypothesis_refined") + stop["refinement_not_easier"]
                                           + stop["split_only_refinement"]],
        "cascade closures / cascade passes": [closed_by.get("specialist-cascade", 0), cascade_passes],
        "exploration notebooks missing / sessions": [stop["notebook_missing"], g("explore", "notebook")],
        "over-budget answers recovered / over-budget retries": [recovered, g("llm", "budget_retry")],
    }
    flags = []
    for label, (num, den) in rates.items():
        if den >= 20 and num == 0 and "missing" not in label and "recovered" not in label:
            flags.append(f"never succeeds: {label} = 0 of {den}")
    for p, v in recent_cost.items():
        old = [c for c in cost[p]][: max(0, len(cost[p]) - len(v))]
        if len(v) >= 5 and len(old) >= 10:
            a, b = sum(v) / len(v), sum(old) / len(old)
            if b > 0 and a / b > 2:
                flags.append(f"cost jump: {p} mean ${a:.2f} in the last 24 h vs ${b:.2f} before")
    if spend:
        top = spend[0]
        flags.append(f"largest spend: {top[0]} ${top[2]} ({top[2] / total:.0%} of ${total:.0f})")
    return {"since": since, "runs_with_logs": len(runs), "total_spend": round(total, 2), "rates": rates,
            "plan_rejections": dict(plan_reject.most_common()), "stops": dict(stop), "cascade_closures": dict(closed_by),
            "spend_by_purpose": spend[:14], "flags": flags}


def print_diagnosis(d: dict) -> None:
    print(f"# Diagnosis ({d['runs_with_logs']} logs" + (f", since {d['since']}" if d["since"] else "") + ")")
    print(f"\nlogged spend: ${d['total_spend']}")
    print("\n## Rates")
    for k, (n, m) in d["rates"].items():
        print(f"- {k}: {n} of {m}" + (f" ({n / m:.0%})" if m else ""))
    print("\n## Plan rejections by reason")
    for k, v in d["plan_rejections"].items():
        print(f"- {k}: {v}")
    print("\n## Stops and refusals")
    for k, v in d["stops"].items():
        print(f"- {k}: {v}")
    print("\n## Spend by purpose (calls, total, mean)")
    for p, n, t, m in d["spend_by_purpose"]:
        print(f"- {p}: {n}, ${t}, ${m}")
    print("\n## Flags")
    for f in d["flags"] or ["(none)"]:
        print(f"- {f}")


# ---------------------------------------------------------------- commits -------------------------------------------
# Both sessions share this checkout, so the loop never moves HEAD: a commit is built in a temporary index from the
# branch tip plus the working tree's version of COMMIT_PATHS, and the branch ref is moved to it. The working tree,
# the real index and HEAD are untouched, and the live harness keeps its fixes for every lane.

def git(*a, env=None, check=True) -> str:
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True, env=env)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(a)}: {r.stderr.strip()[:400]}")
    return r.stdout.strip()


def commit_to_branch(message: str, paths: list[str] | None = None, branch: str = BRANCH) -> str | None:
    paths = paths or COMMIT_PATHS
    tip = git("rev-parse", "--verify", "-q", f"refs/heads/{branch}", check=False)
    parent = tip or git("rev-parse", "HEAD")
    with tempfile.TemporaryDirectory() as d:
        env = {**os.environ, "GIT_INDEX_FILE": str(Path(d) / "index")}
        git("read-tree", parent, env=env)
        existing = [p for p in paths if (ROOT / p).exists()]
        git("add", "-A", "--", *existing, env=env)
        tree = git("write-tree", env=env)
    if tree == git("rev-parse", f"{parent}^{{tree}}"):
        return None
    body = message.rstrip() + "\n\n" + CO_AUTHOR + "\n"
    commit = git("commit-tree", tree, "-p", parent, "-m", body)
    # the expected old value makes the update atomic: an empty one means the branch must not exist yet
    git("update-ref", f"refs/heads/{branch}", commit, tip or "")
    return commit


# ---------------------------------------------------------------- CLI -----------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status")
    d = sub.add_parser("diagnose")
    d.add_argument("--since")
    d.add_argument("--json", action="store_true")
    r = sub.add_parser("register")
    r.add_argument("--kind", required=True, choices=["run", "explore-screen", "calibration", "ideas", "manual"])
    r.add_argument("--name", required=True)
    r.add_argument("--estimate", type=float, default=0.0)
    r.add_argument("--usd", type=float, default=0.0, help="manual entries only")
    r.add_argument("--note", default="")
    f = sub.add_parser("finish")
    f.add_argument("--name", required=True)
    c = sub.add_parser("can-spend")
    c.add_argument("--usd", type=float, required=True)
    s = sub.add_parser("set")
    s.add_argument("--phase")
    s.add_argument("--iteration", type=int)
    s.add_argument("--candidate")
    s.add_argument("--note")
    s.add_argument("--stop")
    m = sub.add_parser("commit")
    m.add_argument("-m", "--message", required=True)
    k = sub.add_parser("ack", help="record that a stop signal was handled")
    k.add_argument("--tag", required=True)
    k.add_argument("--problem", required=True)
    k.add_argument("--note", required=True)
    args = ap.parse_args()
    state = load_state()
    if args.cmd == "status":
        for s in stop_signals(state):
            if stops_the_loop(s) and not s["acknowledged"]:
                print(f"STOP SIGNAL: {s['kind']} of {s['split']} #{s['problem']} in {s['tag']} ({s['run_dir']}). Handle "
                      f"it (docs/improvement-loop.md), then: loop.py ack --tag {s['tag']} --problem {s['problem']} --note ...")
        b = budget(state)
        print(json.dumps({k: state.get(k) for k in ("goal", "iteration", "phase", "candidate", "baseline", "stop", "updated")},
                         indent=1, ensure_ascii=False))
        print(f"budget: ${b['spent']} spent, ${b['reserved']} reserved, ${b['left']} left of ${b['cap']}")
        for e in b["entries"]:
            print(f"  {e['kind']:14} {e['name']:32} spent ${e['spent']:<7} reserved ${e['reserved']:<6}"
                  + (" IN FLIGHT" if e.get("in_flight") else ""))
        for n in (state.get("notes") or [])[-5:]:
            print(f"  note {n.get('at')}: {n.get('text')}")
        return 0
    if args.cmd == "diagnose":
        out = diagnose(args.since)
        print(json.dumps(out, indent=1)) if args.json else print_diagnosis(out)
        return 0
    if args.cmd == "register":
        state.setdefault("ledger", []).append({"kind": args.kind, "name": args.name, "estimate": args.estimate,
                                               "usd": args.usd, "note": args.note, "in_flight": args.kind != "manual",
                                               "registered": now()})
        save_state(state)
        print(json.dumps(budget(state), indent=1))
        return 0
    if args.cmd == "finish":
        for e in state.get("ledger") or []:
            if e.get("name") == args.name:
                e["in_flight"] = False
                e["finished"] = now()
        save_state(state)
        return 0
    if args.cmd == "can-spend":
        b = budget(state)
        ok = b["left"] >= args.usd
        print(f"{'OK' if ok else 'NO'}: ${b['left']} left of ${b['cap']}, asking ${args.usd}")
        return 0 if ok else 1
    if args.cmd == "set":
        for k in ("phase", "iteration", "candidate", "stop"):
            if getattr(args, k) is not None:
                state[k] = getattr(args, k)
        if args.note:
            state.setdefault("notes", []).append({"at": now(), "text": args.note})
        save_state(state)
        return 0
    if args.cmd == "commit":
        sha = commit_to_branch(args.message)
        print(f"{BRANCH} -> {sha}" if sha else "nothing to commit")
        return 0
    if args.cmd == "ack":
        if not any(s["tag"] == args.tag and s["problem"] == str(args.problem) for s in stop_signals(state)):
            print(f"no stop signal for #{args.problem} in {args.tag}")
            return 1
        state.setdefault("acknowledged", []).append({"tag": args.tag, "problem": str(args.problem), "at": now(),
                                                     "note": args.note})
        save_state(state)
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
