"""The resolution campaign: the harness works through the open catalogue with no one in the loop (2026-10-08).

Not to be confused with campaign.py, the dependency-aware campaign DAG that `harness.py campaign` uses.

The operator's direction: aim at significance-3 results, check everything possible in Lean, run without human
intervention. Step 2 showed the research engine can settle a problem. On six problems open until 2026 that it did not
recognize, it wrote complete, refereed proofs of three, and one is proved in Lean. Step 3 pointed it at the most-studied
open problems and at partial targets, and produced partial results. So the campaign aims at the answer, tries first the
problems where an answer is most likely within reach, and sends every complete answer to Lean.

A problem moves through tiers. Each tier resumes the run before it, so nothing is bought twice.
- **scout**: the engine on the whole problem, with the deep dive aimed at settling it (`--engine-objective resolve`) and
  PARI/GP in its sandbox. A complete answer is a valid claim that BOTH settles judges say answers the formal statement.
- **deep**: a problem with traction gets a second, longer pass on the same run: a round planned by the team lead, the
  deep dive's line continued (a marathon leg), and gap closing. Traction is a validated-new claim at significance >= 2, or
  a valid restatement of the core.
- **lean**: a complete answer goes to the deductive loop, in the direction it proves, as a normal open-problem run with
  the whole chain as its blueprint, then the audit (kernel replay, axioms, Comparator, nanoda). A verified proof of an
  open problem goes to `resolution/REVIEW-NEEDED.md`: the honesty rules require human review before any claim of
  resolution, and `claimEligible` stays false until then. Nothing waits on that review.

Every stage appends a row to `resolution/results.jsonl` and, when it learned something, a finding to the Atlas.

Pacing:
- one lane: a stage never starts while another harness run is live;
- a daily dollar cap (`resolution/config.json`);
- a usage limit is waited out, and the same run resumed.

    python3 resolution.py status
    python3 resolution.py queue [--show 20]
    python3 resolution.py once          # the next stage, then stop
    python3 resolution.py loop          # forever: what the LaunchAgent runs
"""
from __future__ import annotations

import argparse, importlib.util, json, re, subprocess, sys, time
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CAMP = ROOT / "resolution"
STATE = CAMP / "state.json"
RESULTS = CAMP / "results.jsonl"
SCREEN_RESULTS = CAMP / "screen-results.jsonl"
CONFIG = CAMP / "config.json"
LOG = CAMP / "resolution.log"
REVIEW = CAMP / "REVIEW-NEEDED.md"
SCREEN = ROOT / "experiments" / "idea-engine-2026-10-02" / "screen.py"
sys.path.insert(0, str(ROOT / "atlas-data"))
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
sys.path.insert(0, str(ROOT))
from atomic import atomic_write, atomic_write_json, locked       # noqa: E402

DEFAULTS = {
    "daily_cap_usd": 150.0,
    # Known lines that PARI/GP may now finish: #366's 5,238 open fibres need Thue solving, #686's odd cases need
    # computational arithmetic geometry; #488 has its next rung; #873 has the step-3 significance-2 result.
    "priority": [366, 686, 488, 873],
    # --results-library on: other runs' validated results and the openai/math families relevant to the problem, so one
    # run builds on another's (never in a benchmark run; no dev or test item enters it).
    "scout": {"total": 18.0,
              "flags": "--engine-objective resolve --engine-sessions 3 --engine-rounds 1 --engine-core-share 0.67 "
                       "--engine-deep-budget 5 --engine-gap-rounds 1 --engine-gap-max 1 --engine-session-legs 2 "
                       "--results-library on"},
    "deep": {"extra": 40.0,
             "flags": "--engine-objective resolve --engine-sessions 3 --engine-rounds 2 --engine-core-share 0.67 "
                      "--engine-deep-budget 5 --engine-marathon-legs 2 --engine-marathon-leg-budget 8 "
                      "--engine-gap-rounds 2 --engine-gap-max 2 --engine-session-legs 3 --results-library on"},
    "lean": {"budget": 25.0, "extend": 10.0, "extend_max": 60.0, "cycles": 6},
    "max_errors": 2,
    "fc_sha": None,
}


# ---------------------------------------------------------------- state, config, log

def load_cfg() -> dict:
    cfg = json.loads(json.dumps(DEFAULTS))
    if CONFIG.exists():
        for k, v in json.loads(CONFIG.read_text()).items():
            cfg[k] = {**cfg[k], **v} if isinstance(cfg.get(k), dict) and isinstance(v, dict) else v
    return cfg


def load_state() -> dict:
    try:
        return json.loads(STATE.read_text())
    except (OSError, ValueError):
        return {"problems": {}}


def save_state(st: dict) -> None:
    CAMP.mkdir(exist_ok=True)
    atomic_write_json(STATE, st, indent=1)


def log(msg: str) -> None:
    CAMP.mkdir(exist_ok=True)
    line = f"[{datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}] {msg}"
    with LOG.open("a") as f:
        f.write(line + "\n")
    print(line, flush=True)


def result(row: dict) -> dict:
    row = {"at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), **row}
    CAMP.mkdir(exist_ok=True)
    with locked(RESULTS):
        with RESULTS.open("a") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    return row


def rows() -> list[dict]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text().splitlines() if l.strip()]


def spent_since(hours: float = 24.0, now: datetime | None = None) -> float:
    now = now or datetime.now(timezone.utc)
    cut = now - timedelta(hours=hours)
    total = 0.0
    for r in rows():
        try:
            at = datetime.strptime(r["at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
        except (KeyError, ValueError):
            continue
        if at >= cut:
            total += float(r.get("spend") or 0.0)
    return total


# ---------------------------------------------------------------- the queue

def forum_chars(n: int) -> int:
    """Characters of actual forum comments (the thread between "Order by" and the footer): how studied a problem is."""
    f = ROOT / "atlas-data" / "forum" / f"{n}.json"
    try:
        t = json.loads(f.read_text()).get("thread") or ""
    except (OSError, ValueError):
        return 10 ** 9
    i = t.find("Order by")
    return len((t[i:] if i >= 0 else "").split("All comments are the responsibility of the user")[0])


def queue(state: dict, cfg: dict) -> list[int]:
    """The order problems are tried in. The configured priority list first, then every problem the Atlas lists as
    unsolved, least studied first and higher `partial` breaking ties. A problem openai/math claims, and one the campaign
    has already taken up, are left out. Step 3's heavily studied problems (4.5x the median forum discussion) gave only
    partial results, while recently open ones gave complete proofs, so how studied a problem is orders the queue."""
    ranks = json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]
    unsolved = {int(p["id"]): p for p in ranks if p.get("status") == "Unsolved"}
    try:
        om = json.loads((ROOT / "atlas-data" / "openai-math-2026-10-06.json").read_text())
        claimed = {int(r["problem"]) for kind in ("claimed_resolved", "claimed_partial") for r in om.get(kind) or []}
    except (OSError, ValueError):
        claimed = set()
    taken = {int(k) for k in state.get("problems", {})}
    first = [int(n) for n in cfg.get("priority") or [] if int(n) in unsolved]
    rest = sorted((n for n in unsolved if n not in first),
                  key=lambda n: (forum_chars(n), -float(((unsolved[n].get("partial") or {}).get("score")) or 0), n))
    return [n for n in first + rest if n not in taken and n not in claimed]


# ---------------------------------------------------------------- preparing a problem

def _thread_digest():
    spec = importlib.util.spec_from_file_location(
        "od_screen", ROOT / "experiments" / "open-discovery-2026-10-02" / "screen.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m.thread_digest


def prep(n: int, cfg: dict) -> dict:
    """The frozen statement (formal-conjectures' main theorem at one pinned commit, answer stripped, as the time-split
    benchmark builds it) and a fresh forum digest. A problem with no single main theorem cannot be frozen and is skipped:
    Lean needs a statement whose faithfulness rests on an external source."""
    import timesplit as T
    if not cfg.get("fc_sha"):
        cfg["fc_sha"] = json.loads(T.fetch(T.SOURCES["fc_head"], CAMP / "fc-head.json", True))["sha"]
        atomic_write_json(CONFIG, {**(json.loads(CONFIG.read_text()) if CONFIG.exists() else {}), "fc_sha": cfg["fc_sha"]},
                          indent=1)
    src = T.fetch(T.SOURCES["fc_file"].format(sha=cfg["fc_sha"], n=n), CAMP / "fc" / f"{n}.lean", pause=0.1)
    fc = T.parse_fc(src, int(n)) if src.strip() else {"error": "no formal-conjectures file"}
    if fc.get("error"):
        return {"ok": False, "why": str(fc["error"])[:200]}
    subprocess.run([sys.executable, str(ROOT / "atlas-data" / "fetch_forum.py"), "--refresh", "--problems", str(n)],
                   cwd=ROOT, capture_output=True, timeout=300)
    lib = CAMP / "library" / str(n)
    lib.mkdir(parents=True, exist_ok=True)
    (lib / "DIGEST.md").write_text(_thread_digest()(str(n)))
    return {"ok": True, "form": fc.get("form")}


# ---------------------------------------------------------------- running a tier

# Any driver of model runs: a harness run, or a lane script between two of its runs (screen.py records one problem and
# starts the next a second later, and a poll in that gap must not start a second lane).
LANE_PATTERN = r"harness\.py run|idea-engine-2026-10-02/screen\.py|hardsteps_lean\.py|timesplit\.py (run|discover-screen)"


def harness_live() -> bool:
    return subprocess.run(["pgrep", "-f", LANE_PATTERN], capture_output=True).returncode == 0


def wait_for_lane(poll: int = 60) -> None:
    """One lane: never start a stage while another harness run is live (a screen, a Lean run, an operator's run)."""
    said = False
    while harness_live():
        if not said:
            log("another harness run is live; waiting for the lane")
            said = True
        time.sleep(poll)


def screen_row(n: int, tag: str) -> dict | None:
    if not SCREEN_RESULTS.exists():
        return None
    out = None
    for line in SCREEN_RESULTS.read_text().splitlines():
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if str(r.get("problem")) == str(n) and r.get("tag") == tag:
            out = r
    return out


def run_screen(n: int, tag: str, total: float, flags: str, resume: str | None = None) -> tuple[dict | None, int]:
    """One engine pass through screen.py, the one path that runs the engine on an open problem. It waits out a usage
    limit and resumes the same run. Returns its results row (None on an infrastructure failure) and its exit code."""
    cmd = [sys.executable, str(SCREEN), "--tag", tag, "--src", str(CAMP), "--total", str(round(total, 2)),
           "--flags", flags, "--results", str(SCREEN_RESULTS)]
    cmd += ["--resume", resume] if resume else [str(n)]
    before = screen_row(n, tag)
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=12 * 3600)
    with (CAMP / "screen.log").open("a") as f:
        f.write(r.stdout[-6000:] + r.stderr[-3000:])
    row = screen_row(n, tag)
    return (row if row is not None and row != before else None), r.returncode


def classify(run_dir: Path) -> tuple[str, dict]:
    """What a finished engine pass found: `complete` (a valid claim BOTH settles judges say answers the formal statement,
    via the engine's own `engine_complete`), `traction` (a validated-new claim at significance >= 2, or a valid
    restatement of the core, the line a deep pass should push), or `none`."""
    import harness as H
    try:
        ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        return "none", {"why": "no engine.json"}
    comp = H.engine_complete(ej)
    if comp is not None:
        st = (comp.get("validation") or {}).get("settles") or {}
        answer = st.get("answer") or ("true" if comp.get("status") == "PROVED" else "false")
        return "complete", {"claim": H.engine_claim_key(comp), "answer": answer,
                            "statement": " ".join(str(comp.get("statement")).split())[:400]}
    best = []
    for c in ej.get("ledger") or []:
        v = c.get("validation") or {}
        sig = (v.get("novelty") or {}).get("significance") or 0
        if (v.get("status") == "validated-new" and sig >= 2) or v.get("status") == "valid-restatement":
            best.append((sig, H.engine_claim_key(c), " ".join(str(c.get("statement")).split())[:300], v.get("status")))
    if best:
        best.sort(reverse=True)
        return "traction", {"claims": [{"claim": k, "significance": s, "status": st, "statement": t}
                                       for s, k, t, st in best[:5]]}
    return "none", {}


def validated_summary(run_dir: Path) -> tuple[int, list[int], str]:
    try:
        ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        return 0, [], ""
    new = [c for c in ej.get("ledger") or [] if (c.get("validation") or {}).get("status") == "validated-new"]
    sigs = sorted((int(((c.get("validation") or {}).get("novelty") or {}).get("significance") or 0) for c in new),
                  reverse=True)
    best = max(new, key=lambda c: ((c.get("validation") or {}).get("novelty") or {}).get("significance") or 0, default=None)
    return len(new), sigs, (" ".join(str(best.get("statement")).split())[:240] if best else "")


# ---------------------------------------------------------------- Lean

def build_lean_run(n: int, engine_run: Path, claim: str, answer: str) -> Path:
    """A normal open-problem run (not a benchmark: a verified proof belongs in knowledge/ and the Atlas) on the engine
    run's frozen statement, with the engine's whole chain as the proof the blueprint follows, committed to the direction
    the chain proves. Open mode formalizes the negation when the chain is a disproof."""
    import harness as H
    ej = json.loads((engine_run / "engine" / "engine.json").read_text())
    sess, cid = claim.split("/", 1)
    c = next(x for x in ej["ledger"] if x.get("session") == sess and x.get("id") == cid)
    chain = H.engine_chain_text(c, ej["ledger"])
    st = json.loads((engine_run / "state.json").read_text())
    prob = json.loads((engine_run / "problem.json").read_text())
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-resolve-lean-erdos{n}"
    run_dir.mkdir(parents=True)
    (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    disc = {"decision": {"commit": "pos" if answer == "true" else "neg", "answer": answer, "share": 1.0},
            "best_proof": {"text": chain, "answer": answer, "complete": True, "claim": claim},
            "guidance": (f"An informal proof of the whole problem, refereed and judged complete by two settles judges, "
                         f"unverified: research-engine run {engine_run.name}, claim {claim} with every lemma under it:\n"
                         + chain[:24000]),
            "refereed_complete": True, "mode": "engine-resolution"}
    (run_dir / "state.json").write_text(json.dumps({
        "statement": st["statement"], "problem_input": prob, "mode": "research", "invocations": [], "discovery": disc,
        "statement_source": st.get("statement_source"),
        "assistance": [f"none: the informal proof is the harness's own research-engine output ({engine_run.name}, "
                       f"{claim}); no operator input"]}, indent=2, ensure_ascii=False))
    return run_dir


def lean_cmd(run_dir: Path, cfg: dict) -> list[str]:
    lc = cfg["lean"]
    return [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
            str(run_dir), "--open", "--discover", "on", "--mode", "research", "--allow-research", "--blueprint", "on",
            "--residual-view", "outline", "--research-cycles", str(lc["cycles"]), "--run-budget", str(lc["budget"]),
            "--budget-extend", str(lc["extend"]), "--budget-extend-max", str(lc["extend_max"]), "--skip-literature",
            "--lean-timeout", "1800", "--llm-timeout", "5400", "--backend", "claude-cli", "--model", "claude-opus-5-5"]


def run_lean(run_dir: Path, cfg: dict) -> tuple[int, str]:
    """Run (or resume) the Lean stage, waiting out a usage limit up to three times."""
    import timesplit as T
    rc = 1
    for _ in range(4):
        with (run_dir / "lane.log").open("a") as f:
            rc = subprocess.run(lean_cmd(run_dir, cfg), cwd=ROOT, stdout=f, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, timeout=20 * 3600).returncode
        tail = (run_dir / "lane.log").read_text(errors="replace")[-6000:]
        if rc != 1 or not T.LIMIT_RE.search(tail):
            break
        wait = T.seconds_until_reset(tail)
        log(f"{run_dir.name}: usage limit; waiting {wait / 60:.0f} min, then resuming")
        time.sleep(wait)
    line = (run_dir / "SUMMARY.line").read_text().strip() if (run_dir / "SUMMARY.line").exists() else ""
    return rc, line


def run_spend(run_dir: Path) -> float:
    m = re.search(r"spend=\$([\d.]+)", (run_dir / "SUMMARY.line").read_text()) if (run_dir / "SUMMARY.line").exists() else None
    return float(m.group(1)) if m else 0.0


# ---------------------------------------------------------------- recording

def record_atlas(n: int, rationale: str, requirement: str | None = None) -> None:
    cmd = [sys.executable, str(ROOT / "atlas-data" / "record_finding.py"), "--problem", str(n), "--rationale", rationale,
           "--source", "resolution/results.jsonl"]
    if requirement:
        cmd += ["--requirement", requirement]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        log(f"#{n}: record_finding failed: {(r.stderr or r.stdout)[-300:]}")


def flag_for_review(n: int, run_dir: Path, summary: str, claim: str, engine_run: Path) -> None:
    head = ("# Verified results awaiting human review\n\nEach entry is a Lean proof of an OPEN problem's formal statement "
            "that passed the harness's verification and audit. The honesty rules require independent human review before "
            "any claim of resolution; until then `claimEligible` stays false.\n")
    text = REVIEW.read_text() if REVIEW.exists() else head
    text += (f"\n## #{n} — {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n- Lean run: `{run_dir.relative_to(ROOT)}`"
             f"\n- informal proof: `{engine_run.relative_to(ROOT)}` claim {claim}\n- summary: `{summary}`\n")
    atomic_write(REVIEW, text)


def commit(paths: list[str], msg: str) -> None:
    """Best effort: commit the resolution campaign's own files. The publisher commits atlas-data."""
    subprocess.run(["git", "add", "--", *paths], cwd=ROOT, capture_output=True)
    r = subprocess.run(["git", "commit", "-q", "-m", msg + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>",
                        "--", *paths], cwd=ROOT, capture_output=True, text=True)
    if r.returncode == 0:
        subprocess.run(["git", "push", "-q", "origin", "main"], cwd=ROOT, capture_output=True, timeout=120)


# ---------------------------------------------------------------- one step

def next_action(state: dict, cfg: dict) -> tuple[str, int | None]:
    """lean first, then deep, then a stage cut off part way, then the next problem in the queue."""
    probs = state.get("problems", {})
    for want in ("lean", "deep"):
        for n, p in probs.items():
            if p.get("next") == want and p.get("errors", 0) < cfg["max_errors"]:
                return want, int(n)
    for n, p in probs.items():
        if p.get("running") and p.get("errors", 0) < cfg["max_errors"]:
            return p["running"], int(n)
    q = queue(state, cfg)
    return ("scout", q[0]) if q else ("idle", None)


def step(cfg: dict) -> bool:
    """Run the next stage. Returns False when there is nothing to do."""
    state = load_state()
    action, n = next_action(state, cfg)
    if action == "idle":
        log("queue empty")
        return False
    p = state["problems"].setdefault(str(n), {"history": []})
    key = str(n)
    if action == "scout":
        if not p.get("prepped"):
            info = prep(n, cfg)
            if not info["ok"]:
                p.update({"status": "skipped", "why": info["why"], "next": None})
                save_state(state)
                result({"problem": n, "tier": "prep", "outcome": "skipped", "why": info["why"], "spend": 0.0})
                log(f"#{n}: skipped ({info['why']})")
                return True
            p["prepped"] = True
        p["running"] = "scout"
        save_state(state)
        log(f"#{n}: scout")
        row, rc = run_screen(n, "resolve-scout", cfg["scout"]["total"], cfg["scout"]["flags"], p.get("run_dir"))
    elif action == "deep":
        p["running"] = "deep"
        save_state(state)
        prior = float(p.get("spend") or 0.0)
        log(f"#{n}: deep pass on {p['run_dir']}")
        row, rc = run_screen(n, "resolve-deep", prior + cfg["deep"]["extra"], cfg["deep"]["flags"], p["run_dir"])
    else:                                                # lean
        p["running"] = "lean"
        save_state(state)
        engine_run = ROOT / p["run_dir"]
        if not p.get("lean_run"):
            p["lean_run"] = str(build_lean_run(n, engine_run, p["complete"]["claim"], p["complete"]["answer"]).relative_to(ROOT))
            save_state(state)
        lean_run = ROOT / p["lean_run"]
        log(f"#{n}: Lean on {p['complete']['claim']} ({p['complete']['answer']}) in {lean_run.name}")
        rc, line = run_lean(lean_run, cfg)
        spend = run_spend(lean_run)
        verified = rc == 0
        p.update({"running": None, "next": None, "status": "verified" if verified else "lean-partial",
                  "lean_summary": line})
        p["history"].append({"tier": "lean", "rc": rc, "summary": line})
        save_state(state)
        result({"problem": n, "tier": "lean", "outcome": "verified" if verified else "not verified", "rc": rc,
                "spend": spend, "lean_run": p["lean_run"], "summary": line})
        if verified:
            flag_for_review(n, lean_run, line, p["complete"]["claim"], engine_run)
            record_atlas(n, f"Resolution campaign {datetime.now().date()}: the research engine's complete answer ({p['complete']['claim']}, "
                            f"{p['complete']['answer']}) is PROVED IN LEAN on formal-conjectures' statement and passed the "
                            f"audit ({lean_run.name}). Open problem: awaiting human review before any claim of resolution.")
        else:
            record_atlas(n, f"Resolution campaign {datetime.now().date()} (${spend:.2f}): Lean on the engine's complete answer "
                            f"({p['complete']['claim']}) did not close: {line[:200]}")
        commit(["resolution"], f"resolution: #{n} Lean {'verified' if verified else 'not verified'}")
        return True
    # scout or deep finished
    if row is None:
        p["errors"] = int(p.get("errors") or 0) + 1
        p["running"] = None if p["errors"] >= cfg["max_errors"] else action
        save_state(state)
        result({"problem": n, "tier": action, "outcome": "infrastructure", "rc": rc, "spend": 0.0})
        log(f"#{n}: {action} failed (exit {rc}); errors {p['errors']}")
        return True
    run_dir = ROOT / row["run_dir"]
    total = float(row.get("spend_run") or 0.0)
    delta = round(total - float(p.get("spend") or 0.0), 4)
    p.update({"run_dir": row["run_dir"], "spend": total, "running": None})
    outcome, info = classify(run_dir)
    n_new, sigs, best = validated_summary(run_dir)
    if outcome == "complete":
        p.update({"next": "lean", "status": "complete", "complete": info})
    elif outcome == "traction" and action == "scout":
        p.update({"next": "deep", "status": "traction", "traction": info})
    else:
        p.update({"next": None, "status": "done" if outcome == "none" else outcome})
    p["history"].append({"tier": action, "outcome": outcome, "spend": delta})
    save_state(state)
    result({"problem": n, "tier": action, "outcome": outcome, "spend": delta, "run_dir": row["run_dir"],
            "validated_new": n_new, "significance": sigs, **info})
    log(f"#{n}: {action} -> {outcome} (${delta:.2f}; {n_new} validated new {sigs})")
    if outcome == "complete":
        record_atlas(n, f"Resolution campaign {datetime.now().date()} (${total:.2f}, informal): the research engine wrote a complete "
                        f"answer ({info['answer']}) that a referee, an adversary and both settles judges accepted: "
                        f"{info['statement'][:300]}. Sent to Lean.")
    elif n_new:
        record_atlas(n, f"Resolution campaign {action} {datetime.now().date()} (${total:.2f}, informal): {n_new} validated-new claims "
                        f"(significance {', '.join(map(str, sigs))}); best: {best}")
    commit(["resolution"], f"resolution: #{n} {action} -> {outcome}")
    return True


# ---------------------------------------------------------------- entry points

def status() -> None:
    st, cfg = load_state(), load_cfg()
    by: dict = {}
    for n, p in st.get("problems", {}).items():
        by.setdefault(p.get("status") or p.get("running") or "?", []).append(int(n))
    print(f"daily cap ${cfg['daily_cap_usd']:.0f}; spent last 24h ${spent_since():.2f}, last 7 days ${spent_since(168):.2f}")
    for k, v in sorted(by.items()):
        print(f"  {k}: {len(v)}  {sorted(v)[:20]}")
    tackled = [int(n) for n, p in st.get("problems", {}).items() if p.get("run_dir")]
    sig3 = sorted({int(r["problem"]) for r in rows() if r.get("outcome") in ("complete", "verified")
                   or 3 in (r.get("significance") or [])})
    print(f"significance 3 (a complete answer, or a claim both novelty judges rate 3): {len(sig3)} of {len(tackled)} "
          f"problems tackled {sig3}")
    act, n = next_action(st, cfg)
    print(f"next: {act} {n or ''}")
    for r in rows()[-8:]:
        print("  ", {k: r.get(k) for k in ("at", "problem", "tier", "outcome", "spend", "validated_new", "significance")})
    if REVIEW.exists():
        print(f"REVIEW NEEDED: {REVIEW.relative_to(ROOT)}")


def loop() -> None:
    log("resolution campaign loop starting")
    while True:
        cfg = load_cfg()
        spent = spent_since()
        if spent >= cfg["daily_cap_usd"]:
            log(f"daily cap reached (${spent:.2f} of ${cfg['daily_cap_usd']:.0f}); sleeping 1 h")
            time.sleep(3600)
            continue
        wait_for_lane()
        try:
            did = step(cfg)
        except Exception as e:                           # noqa: BLE001 - the loop must survive any one stage
            log(f"step failed: {type(e).__name__}: {str(e)[:300]}")
            time.sleep(300)
            continue
        if not did:
            time.sleep(3600)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["status", "queue", "once", "loop"])
    ap.add_argument("--show", type=int, default=20)
    a = ap.parse_args()
    CAMP.mkdir(exist_ok=True)
    if a.cmd == "status":
        status()
    elif a.cmd == "queue":
        q = queue(load_state(), load_cfg())
        print(f"{len(q)} problems queued; first {a.show}:")
        for n in q[: a.show]:
            print(f"  #{n}  forum {forum_chars(n)} chars")
    elif a.cmd == "once":
        wait_for_lane()
        step(load_cfg())
    else:
        loop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
