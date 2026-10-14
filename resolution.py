"""The resolution campaign: the harness works through the open catalogue with no one in the loop (2026-10-08).

Not to be confused with campaign.py, the dependency-aware campaign DAG that `harness.py campaign` uses.

The operator's direction: aim at significance-3 results, check everything possible in Lean, run without human
intervention. Step 2 showed the research engine can settle a problem. On six problems open until 2026 that it did not
recognize, it wrote complete, refereed proofs of three, and one is proved in Lean. Step 3 pointed it at the most-studied
open problems and at partial targets, and produced partial results. So the campaign aims at the answer, tries first the
problems where an answer is most likely within reach, and sends every complete answer to Lean.

A problem moves through tiers. Each tier resumes the run before it, so nothing is bought twice.
- **screen**: the engine's frontier map and two draws of its team lead's SETTLE CHANCE from the map alone, before any
  work (about $3-6). A problem at or above `screen.pass` (0.3) is scouted; one below it is scouted only in the control
  arm, a fixed share (`screen.control`, a quarter) chosen by a hash of its number. On step 2's dev items the number put
  the problems the engine went on to settle first (mean 0.46 against 0.09) but missed #1125 (0.085), so the control arm
  measures what the bar costs (REPORT 3.8).
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
    python3 resolution.py import-screens --file experiments/idea-engine-2026-10-02/step3/settle_open.jsonl
    python3 resolution.py loop          # forever: what the LaunchAgent runs
"""
from __future__ import annotations

import argparse, hashlib, importlib.util, json, re, subprocess, sys, time
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CAMP = ROOT / "resolution"
STATE = CAMP / "state.json"
RESULTS = CAMP / "results.jsonl"
SCREEN_RESULTS = CAMP / "screen-results.jsonl"
PRESCREEN = CAMP / "prescreen.jsonl"
CONFIG = CAMP / "config.json"
LOG = CAMP / "resolution.log"
REVIEW = CAMP / "REVIEW-NEEDED.md"
FINDINGS = CAMP / "STATEMENT-FINDINGS.md"
SCREEN = ROOT / "experiments" / "idea-engine-2026-10-02" / "screen.py"
sys.path.insert(0, str(ROOT / "atlas-data"))
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
sys.path.insert(0, str(ROOT))
from atomic import atomic_write, atomic_write_json, locked       # noqa: E402

# The least settle chance (the deep dive's own `SETTLE CHANCE`) that buys a deep pass, unless a claim is already rated 3.
SETTLE_FLOOR = 0.1

DEFAULTS = {
    "daily_cap_usd": 150.0,
    # Known lines that PARI/GP may now finish: #366's 5,238 open fibres need Thue solving, #686's odd cases need
    # computational arithmetic geometry; #488 has its next rung; #873 has the step-3 significance-2 result.
    "priority": [366, 686, 488, 873],
    # --results-library on: other runs' validated results and the openai/math families relevant to the problem, so one
    # run builds on another's (never in a benchmark run; no dev or test item enters it).
    # The ripeness screen (REPORT 3.8): the map and two SETTLE CHANCE draws, no sessions. The scout resumes its run.
    "screen": {"total": 12.0, "pass": 0.3, "control": 0.25,
               "flags": "--engine-objective resolve --engine-sessions 0 --engine-deep-budget 0 --engine-gap-rounds 0 "
                        "--engine-settle-draws 2 --engine-intent-judges 2 --results-library on"},
    "scout": {"total": 18.0,
              "flags": "--engine-objective resolve --engine-settle-draws 2 --engine-intent-judges 2 --engine-sessions 3 --engine-rounds 1 --engine-core-share 0.67 "
                       "--engine-deep-budget 5 --engine-gap-rounds 1 --engine-gap-max 1 --engine-session-legs 2 "
                       "--results-library on"},
    "deep": {"extra": 40.0,
             "flags": "--engine-objective resolve --engine-intent-judges 2 --engine-sessions 3 --engine-rounds 2 "
                      "--engine-core-share 0.67 --engine-deep-budget 5 --engine-marathon-legs 2 --engine-marathon-leg-budget 8 "
                      "--engine-gap-rounds 2 --engine-gap-max 2 --engine-session-legs 3 --results-library on"},
    # The analytical deep tier for the new-mathematics track: the research program (harness `engine_program`), a proof
    # skeleton whose glue is refereed and whose lemmas are attacked and judged one by one, resuming the scout's run.
    "program": {"extra": 90.0,
                "flags": "--engine-objective resolve --engine-intent-judges 2 --engine-sessions 3 --engine-rounds 1 "
                         "--engine-core-share 0.67 --engine-deep-budget 5 --engine-program-cycles 6 "
                         "--engine-program-budget 80 --engine-program-session-budget 4 --engine-program-lemmas 3 "
                         "--engine-session-legs 3 --engine-gap-rounds 2 --engine-gap-max 2 --results-library on"},
    # Recursive children get 3 cycles and one more level: with the default 1, #888's upper-bound child certified 3 of its
    # 4 pieces, planned its next move, and was cut off twice; with 4 cycles and depth 3 it finished (REPORT 3.11).
    "lean": {"budget": 25.0, "extend": 10.0, "extend_max": 60.0, "cycles": 6, "child_cycles": 3, "residual_depth": 3},
    # A validated-new claim at this significance or more gets a Lean run of its own: the harness formalizes its statement
    # (candidates, a crosscheck judge, recorded readings) and proves it with the engine's chain as the blueprint.
    "lean_claims": {"min_significance": 2, "budget": 15.0, "extend": 5.0, "extend_max": 30.0, "cycles": 4,
                    "child_cycles": 3, "residual_depth": 3},
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


def save_problem(n, p: dict) -> None:
    """Write one problem's entry and nothing else, re-reading the file under its lock. A stage that saved the whole state
    it read when it started would erase any entry written meanwhile (an import, a test, another tool)."""
    CAMP.mkdir(exist_ok=True)
    with locked(STATE):
        st = load_state()
        st.setdefault("problems", {})[str(n)] = p
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
    """What the campaign spent in the window: its stages, plus any prescreen sweep (`prescreen.jsonl`, one row and its
    `cost` per problem), which runs beside the loop."""
    now = now or datetime.now(timezone.utc)
    cut = now - timedelta(hours=hours)
    total = 0.0
    pre = [json.loads(l) for l in PRESCREEN.read_text().splitlines() if l.strip()] if PRESCREEN.exists() else []
    for r in rows() + [{"at": x.get("at"), "spend": x.get("cost")} for x in pre]:
        try:
            at = datetime.strptime(r["at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
        except (KeyError, TypeError, ValueError):
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


def prescreen() -> dict[int, float]:
    """Each queued problem's map-free SETTLE CHANCE, when a sweep has drawn one (REPORT 3.10, `step3/settle_nomap.py
    --sweep`). It only orders the queue: every problem still gets the screen proper before any scout."""
    out: dict[int, float] = {}
    if PRESCREEN.exists():
        for line in PRESCREEN.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r.get("mean"), (int, float)):
                out[int(r["problem"])] = float(r["mean"])
    return out


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
    # Forum size is a weak proxy: 98 queued problems have an empty thread, the Littlewood conjecture (#495) among them.
    # A prescreen's chance, where one exists, comes first.
    pre = prescreen()
    rest = sorted((n for n in unsolved if n not in first),
                  key=lambda n: (-pre.get(n, 0.0), forum_chars(n),
                                 -float(((unsolved[n].get("partial") or {}).get("score")) or 0), n))
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


def engine_runs(n: int) -> list[Path]:
    """This problem's engine runs started by the campaign, newest first."""
    out = []
    for r in (ROOT / "runs").glob(f"*-erdos{n}"):
        try:
            if "Research engine screen resolve-" in json.loads((r / "problem.json").read_text()).get("notes", ""):
                out.append(r)
        except (OSError, ValueError):
            continue
    return sorted(out, key=lambda r: r.name, reverse=True)


def run_progress(run: Path) -> float:
    try:
        return float(json.loads((run / "engine" / "checkpoint.json").read_text()).get("spend") or 0.0)
    except (OSError, ValueError):
        return 0.0


def adopt_run(n: int) -> str | None:
    """After an interruption: the campaign's run of this problem with the most work in its checkpoint, to resume. On
    2026-10-08 a restart began #366's scout afresh and abandoned a run holding its map and a whole round ($9.85),
    because the run dir was recorded only when a stage finished."""
    runs = [r for r in engine_runs(n) if run_progress(r) > 0]
    return str(max(runs, key=run_progress).relative_to(ROOT)) if runs else None


def run_screen(n: int, tag: str, total: float, flags: str, resume: str | None = None,
               on_start=None) -> tuple[dict | None, int]:
    """One engine pass through screen.py, the one path that runs the engine on an open problem. It waits out a usage
    limit and resumes the same run. `on_start(run_dir)` is called as soon as the run exists, so an interrupted stage
    can be resumed. Returns its results row (None on an infrastructure failure) and its exit code."""
    cmd = [sys.executable, str(SCREEN), "--tag", tag, "--src", str(CAMP), "--total", str(round(total, 2)),
           "--flags", flags, "--results", str(SCREEN_RESULTS)]
    cmd += ["--resume", resume] if resume else [str(n)]
    before = screen_row(n, tag)
    known = set(engine_runs(n))
    with (CAMP / "screen.log").open("a") as out:
        proc = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        reported = bool(resume)
        deadline = time.time() + 12 * 3600
        while proc.poll() is None:
            if not reported:
                new = [r for r in engine_runs(n) if r not in known]
                if new and on_start:
                    on_start(str(new[0].relative_to(ROOT)))
                    reported = True
            if time.time() > deadline:
                proc.terminate()
                break
            time.sleep(5)
        rc = proc.wait()
    row = screen_row(n, tag)
    return (row if row is not None and row != before else None), rc


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
        intent = (comp.get("validation") or {}).get("intent") or {}
        return "complete", {"claim": H.engine_claim_key(comp), "answer": answer,
                            "statement": " ".join(str(comp.get("statement")).split())[:400],
                            "intent": intent.get("class"), "intent_source": intent.get("source")}
    best = []
    for c in ej.get("ledger") or []:
        v = c.get("validation") or {}
        sig = (v.get("novelty") or {}).get("significance") or 0
        if (v.get("status") == "validated-new" and sig >= 2) or v.get("status") == "valid-restatement":
            best.append((sig, H.engine_claim_key(c), " ".join(str(c.get("statement")).split())[:300], v.get("status")))
    chance = (ej.get("deep") or {}).get("settle_chance")
    if best:
        best.sort(reverse=True)
        info = {"claims": [{"claim": k, "significance": s, "status": st, "statement": t} for s, k, t, st in best[:5]],
                "settle_chance": chance}
        # The deep tier is for problems a settle could still come from. On 2026-10-08 #366's own team lead wrote that no
        # line could settle it (a proof needs abc-strength results; a counterexample lies past the 1e22 floor).
        if best[0][0] < 3 and isinstance(chance, (int, float)) and chance < SETTLE_FLOOR:
            return "not ripe", info
        return "traction", info
    return "none", {"settle_chance": chance}


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


def engine_json(run_dir: Path) -> dict:
    try:
        return json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        return {}


def screen_result(run_dir: Path) -> dict | None:
    """The ripeness screen the engine recorded (`settle_screen`: its draws and their mean), or None."""
    ej = engine_json(run_dir)
    return ej.get("settle_screen") if isinstance(ej.get("settle_screen"), dict) else None


def track_for(arm_: str, intent: str | None) -> str | None:
    """A pass whose line the intent judges call a formalization gap or a known result goes to the statement-findings
    track: the scout and Lean, reported as a finding about the formal statement. Every other pass is a candidate for new
    mathematics and gets the research program. The control arm stays a measurement. REPORT 3.10: the prescreen's five
    best scores were all gaps or known results."""
    if arm_ == "pass":
        return "statement" if intent in ("formalization-gap", "known-result") else "new-math"
    return "control" if arm_ == "control" else None


def arm(n: int, chance: float, cfg: dict) -> str:
    """`pass` (scouted), `control` (below the bar and scouted anyway: a fixed share of problems, chosen by a hash of the
    number and never by the chance) or `screened out`. Comparing the two scouted arms' settle rates measures the screen
    on the problems it is used for."""
    sc = cfg["screen"]
    if chance >= float(sc["pass"]):
        return "pass"
    h = int(hashlib.sha256(f"resolution-control-{n}".encode()).hexdigest()[:8], 16) / 0xFFFFFFFF
    return "control" if h < float(sc["control"]) else "screened out"


def finish_screen(n: int, p: dict, cfg: dict, run_dir: Path, delta: float) -> bool:
    scr = screen_result(run_dir) or {}
    chance, draws = scr.get("mean"), [d.get("chance") for d in scr.get("draws") or []]
    if chance is None:                                   # no draw gave a number: resume re-draws, max_errors gives up
        p["errors"] = int(p.get("errors") or 0) + 1
        p["running"] = "screen" if p["errors"] < cfg["max_errors"] else None
        p["status"] = None if p["running"] else "screen failed"
        save_problem(n, p)
        result({"problem": n, "tier": "screen", "outcome": "no settle chance", "draws": draws, "spend": delta,
                "run_dir": p["run_dir"]})
        log(f"#{n}: screen gave no settle chance (draws {draws}); errors {p['errors']}")
        return True
    a = arm(n, chance, cfg)
    intent = (engine_json(run_dir).get("intent") or {}).get("class")
    track = track_for(a, intent)
    p.update({"settle_chance": chance, "arm": a, "next": None if a == "screened out" else "scout",
              "status": "screened out" if a == "screened out" else "screened", "track": track, "intent": intent})
    p["history"].append({"tier": "screen", "outcome": a, "settle_chance": chance, "spend": delta, "track": track})
    save_problem(n, p)
    result({"problem": n, "tier": "screen", "outcome": a, "settle_chance": chance, "draws": draws, "spend": delta,
            "run_dir": p["run_dir"], "track": track, "intent": intent})
    log(f"#{n}: screen -> {a} (settle chance {chance:.2f}, draws {draws}; ${delta:.2f})"
        + (f"; track {track} (intent {intent})" if track and track != "control" else ""))
    goal = next((d.get("goal") for d in scr.get("draws") or [] if d.get("goal")), "") or ""
    line = " ".join(re.sub(r"(?i)SETTLE CHANCE\s*:\s*\S+", "", goal).replace("*", "").split())[:260]
    record_atlas(n, f"Resolution campaign ripeness screen {datetime.now().date()}: SETTLE CHANCE {chance:.2f}, the mean of "
                    f"{len(draws)} draws of the research engine's team lead reading only its frontier map, before any work "
                    f"(an unvalidated model estimate; on step 2's dev items it ranked the problems the engine settled "
                    f"first without separating them)." + (f" The line it would take: {line}" if line else ""))
    commit(["resolution"], f"resolution: #{n} screen -> {a} (settle chance {chance:.2f})")
    return True


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


def claims_for_lean(run_dir: Path, min_sig: int, skip: set[str]) -> list[str]:
    """Validated-new PROVED claims at `min_sig` or more, strongest first, minus `skip` (the complete answer, which the
    main Lean stage covers, and claims already sent)."""
    import harness as H
    try:
        ej = json.loads((run_dir / "engine" / "engine.json").read_text())
    except (OSError, ValueError):
        return []
    out = []
    for c in ej.get("ledger") or []:
        v = c.get("validation") or {}
        sig = int((v.get("novelty") or {}).get("significance") or 0)
        k = H.engine_claim_key(c)
        if c.get("status") == "PROVED" and v.get("status") == "validated-new" and sig >= min_sig and k not in skip:
            out.append((sig, k))
    return [k for s, k in sorted(out, reverse=True)]


def build_claim_lean_run(n: int, engine_run: Path, claim: str, k: int) -> Path:
    """A Lean run for one partial result. Its statement is the CLAIM, which the harness formalizes itself (no statement
    is preset), under a fresh id so it never mixes with the problem's own program directory."""
    import harness as H
    ej = json.loads((engine_run / "engine" / "engine.json").read_text())
    sess, cid = claim.split("/", 1)
    c = next(x for x in ej["ledger"] if x.get("session") == sess and x.get("id") == cid)
    chain = H.engine_chain_text(c, ej["ledger"])
    orig = json.loads((engine_run / "problem.json").read_text())
    sid = str(10_000_000 + n * 100 + k)
    prob = {"id": sid, "statement": " ".join(str(c.get("statement")).split()), "tags": orig.get("tags") or [],
            "notes": (f"A partial result on Erdős problem #{n}, not the problem itself: claim {claim} of the research-engine "
                      f"run {engine_run.name}, proved informally and validated by its judges. Formalize THIS statement.")}
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-resolve-claim-erdos{sid}"
    run_dir.mkdir(parents=True)
    (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    disc = {"decision": {"commit": "pos", "answer": "true", "share": 1.0},
            "best_proof": {"text": chain, "answer": "true", "complete": True, "claim": claim},
            "guidance": f"An informal proof of this statement, refereed and validated as new, unverified ({engine_run.name}, "
                        f"{claim}, with every lemma under it):\n" + chain[:24000],
            "refereed_complete": True, "mode": "engine-resolution-claim"}
    (run_dir / "state.json").write_text(json.dumps({
        "problem_input": prob, "mode": "research", "invocations": [], "discovery": disc, "partial_of": n, "claim": claim,
        "assistance": [f"none: the informal proof is the harness's own research-engine output ({engine_run.name}, {claim})"]},
        indent=2, ensure_ascii=False))
    return run_dir


def claim_lean_cmd(run_dir: Path, cfg: dict) -> list[str]:
    lc = cfg["lean_claims"]
    return [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
            str(run_dir), "--discover", "on", "--mode", "research", "--allow-research", "--blueprint", "on",
            "--residual-view", "outline", "--research-cycles", str(lc["cycles"]), "--run-budget", str(lc["budget"]),
            "--budget-extend", str(lc["extend"]), "--budget-extend-max", str(lc["extend_max"]), "--skip-literature",
            "--child-cycles", str(lc.get("child_cycles", 3)), "--residual-depth", str(lc.get("residual_depth", 3)),
            "--lean-timeout", "1800", "--llm-timeout", "5400", "--backend", "claude-cli", "--model", "claude-opus-5-5"]


def lean_cmd(run_dir: Path, cfg: dict) -> list[str]:
    lc = cfg["lean"]
    return [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
            str(run_dir), "--open", "--discover", "on", "--mode", "research", "--allow-research", "--blueprint", "on",
            "--residual-view", "outline", "--research-cycles", str(lc["cycles"]), "--run-budget", str(lc["budget"]),
            "--budget-extend", str(lc["extend"]), "--budget-extend-max", str(lc["extend_max"]), "--skip-literature",
            "--child-cycles", str(lc.get("child_cycles", 3)), "--residual-depth", str(lc.get("residual_depth", 3)),
            "--lean-timeout", "1800", "--llm-timeout", "5400", "--backend", "claude-cli", "--model", "claude-opus-5-5"]


def limit_wait(run_dir: Path) -> float | None:
    """Seconds to the stated reset when a stage's run ended on a usage limit (its log's last lines), else None. From
    2026-10-09 to 10-13 the weekly limit made every screen fail twice and the campaign gave up ten problems it never
    screened: a limit is an outage, not a verdict on the problem."""
    import timesplit as T
    try:
        tail = (run_dir / "lane.log").read_text(errors="replace")[-1500:]
    except OSError:
        return None
    return T.seconds_until_reset(tail, cap_hours=24 * 7) if T.LIMIT_RE.search(tail) else None


def run_lean(run_dir: Path, cfg: dict, cmd: list[str] | None = None) -> tuple[int, str]:
    """Run (or resume) a Lean stage, waiting out each usage limit to its stated reset."""
    import timesplit as T
    rc = 1
    for _ in range(12):
        with (run_dir / "lane.log").open("a") as f:
            rc = subprocess.run(cmd or lean_cmd(run_dir, cfg), cwd=ROOT, stdout=f, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, timeout=20 * 3600).returncode
        tail = (run_dir / "lane.log").read_text(errors="replace")[-6000:]
        if rc != 1 or not T.LIMIT_RE.search(tail):
            break
        wait = T.seconds_until_reset(tail, cap_hours=24 * 7)
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
            "any claim of resolution; until then `claimEligible` stays false.\n\nCheck two things first. Does the proof "
            "settle the problem as Erdős posed it, or only the formal statement's wording (a gap in the formalization)? "
            "And is the result already published? The prescreen's highest scores were mostly one or the other "
            "(REPORT 3.10: #655's regular n-gon, #32's Ruzsa 1998).\n")
    text = REVIEW.read_text() if REVIEW.exists() else head
    text += (f"\n## #{n} — {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n- Lean run: `{run_dir.relative_to(ROOT)}`"
             f"\n- informal proof: `{engine_run.relative_to(ROOT)}` claim {claim}\n- summary: `{summary}`\n")
    atomic_write(REVIEW, text)


def flag_statement_finding(n: int, run_dir: Path, summary: str, complete: dict, engine_run: Path) -> None:
    head = ("# Findings about formal statements\n\nEach entry is a Lean proof, verified and audited, that settles "
            "formal-conjectures' statement of an OPEN problem along a line its intent judges classified as a gap between "
            "the problem and its formalization, or as a known result. It is not a resolution of the problem as posed. A "
            "gap is worth reporting to formal-conjectures, and a known result to erdosproblems.com.\n")
    text = FINDINGS.read_text() if FINDINGS.exists() else head
    text += (f"\n## #{n} — {complete.get('intent')} — {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n"
             f"- answer: {complete.get('answer')}; statement: {complete.get('statement')}\n"
             + (f"- source named by the judges: {complete.get('intent_source')}\n" if complete.get("intent_source") else "")
             + f"- Lean run: `{run_dir.relative_to(ROOT)}`\n- informal proof: `{engine_run.relative_to(ROOT)}` claim "
             f"{complete.get('claim')}\n- summary: `{summary}`\n")
    atomic_write(FINDINGS, text)


def commit(paths: list[str], msg: str) -> None:
    """Best effort: commit the resolution campaign's own files. The publisher commits atlas-data."""
    subprocess.run(["git", "add", "--", *paths], cwd=ROOT, capture_output=True)
    r = subprocess.run(["git", "commit", "-q", "-m", msg + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>",
                        "--", *paths], cwd=ROOT, capture_output=True, text=True)
    if r.returncode == 0:
        subprocess.run(["git", "push", "-q", "origin", "main"], cwd=ROOT, capture_output=True, timeout=120)


# ---------------------------------------------------------------- one step

def next_action(state: dict, cfg: dict) -> tuple[str, int | None]:
    """lean first, then deep, then a stage cut off part way, then Lean on partial results, then a screened problem's
    scout (the pass arm first, highest settle chance first, then the control arm), then the next problem's screen."""
    probs = state.get("problems", {})
    for want in ("lean", "program", "deep"):
        for n, p in probs.items():
            if p.get("next") == want and p.get("errors", 0) < cfg["max_errors"]:
                return want, int(n)
    for n, p in probs.items():
        if p.get("running") and p.get("errors", 0) < cfg["max_errors"]:
            return p["running"], int(n)
    for n, p in probs.items():
        if p.get("claims_todo") and p.get("errors", 0) < cfg["max_errors"]:
            return "lean-claim", int(n)
    pending = [(p.get("arm") == "pass", float(p.get("settle_chance") or 0.0), -int(n)) for n, p in probs.items()
               if p.get("next") == "scout" and p.get("errors", 0) < cfg["max_errors"]]
    if pending:
        return "scout", -max(pending)[2]
    q = queue(state, cfg)
    return ("screen", q[0]) if q else ("idle", None)


def step(cfg: dict) -> bool:
    """Run the next stage. Returns False when there is nothing to do."""
    state = load_state()
    action, n = next_action(state, cfg)
    if action == "idle":
        log("queue empty")
        return False
    p = state["problems"].setdefault(str(n), {"history": []})
    key = str(n)
    if action in ("screen", "scout"):
        if not p.get("prepped"):
            info = prep(n, cfg)
            if not info["ok"]:
                p.update({"status": "skipped", "why": info["why"], "next": None})
                save_problem(n, p)
                result({"problem": n, "tier": "prep", "outcome": "skipped", "why": info["why"], "spend": 0.0})
                log(f"#{n}: skipped ({info['why']})")
                return True
            p["prepped"] = True
        p["running"] = action
        if not p.get("run_dir"):
            p["run_dir"] = adopt_run(n)                  # a stage cut off before its run dir was recorded
        save_problem(n, p)
        log(f"#{n}: {action}" + (f" (resuming {p['run_dir']})" if p.get("run_dir") else ""))

        def started(run_dir: str) -> None:
            p["run_dir"] = run_dir
            save_problem(key, p)
        # a screened problem's scout resumes the screen's run, so its total counts the screen's spend
        row, rc = run_screen(n, f"resolve-{action}", float(p.get("spend") or 0.0) + cfg[action]["total"],
                             cfg[action]["flags"], p.get("run_dir"), on_start=started)
    elif action in ("deep", "program"):
        p["running"] = action
        save_problem(n, p)
        prior = float(p.get("spend") or 0.0)
        log(f"#{n}: {'research program' if action == 'program' else 'deep pass'} on {p['run_dir']}")
        row, rc = run_screen(n, f"resolve-{action}", prior + cfg[action]["extra"], cfg[action]["flags"], p["run_dir"])
    elif action == "lean-claim":
        claim = p["claims_todo"][0]
        engine_run = ROOT / p["run_dir"]
        done = p.setdefault("claims_done", {})
        rec = done.setdefault(claim, {})
        if not rec.get("lean_run"):
            rec["lean_run"] = str(build_claim_lean_run(n, engine_run, claim, len(done)).relative_to(ROOT))
            save_problem(n, p)
        lean_run = ROOT / rec["lean_run"]
        log(f"#{n}: Lean on partial result {claim} in {lean_run.name}")
        rc, line = run_lean(lean_run, cfg, claim_lean_cmd(lean_run, cfg))
        spend = run_spend(lean_run)
        rec.update({"rc": rc, "summary": line, "verified": rc == 0})
        p["claims_todo"] = p["claims_todo"][1:]
        save_problem(n, p)
        result({"problem": n, "tier": "lean-claim", "claim": claim, "outcome": "verified" if rc == 0 else "not verified",
                "rc": rc, "spend": spend, "lean_run": rec["lean_run"], "summary": line})
        stmt = json.loads((lean_run / "problem.json").read_text())["statement"]
        if rc == 0:
            record_atlas(n, f"Resolution campaign {datetime.now().date()}: the partial result {claim} is CERTIFIED IN LEAN "
                            f"({lean_run.name}; the harness formalized the claim with a crosscheck judge, then the audit): "
                            f"{stmt[:260]}")
        commit(["resolution"], f"resolution: #{n} Lean on {claim}: {'verified' if rc == 0 else 'not verified'}")
        return True
    else:                                                # lean
        p["running"] = "lean"
        save_problem(n, p)
        engine_run = ROOT / p["run_dir"]
        if not p.get("lean_run"):
            p["lean_run"] = str(build_lean_run(n, engine_run, p["complete"]["claim"], p["complete"]["answer"]).relative_to(ROOT))
            save_problem(n, p)
        lean_run = ROOT / p["lean_run"]
        log(f"#{n}: Lean on {p['complete']['claim']} ({p['complete']['answer']}) in {lean_run.name}")
        rc, line = run_lean(lean_run, cfg)
        spend = run_spend(lean_run)
        verified = rc == 0
        p.update({"running": None, "next": None, "status": "verified" if verified else "lean-partial",
                  "lean_summary": line})
        p["history"].append({"tier": "lean", "rc": rc, "summary": line})
        save_problem(n, p)
        cls = (p.get("complete") or {}).get("intent")
        result({"problem": n, "tier": "lean", "outcome": "verified" if verified else "not verified", "rc": rc,
                "spend": spend, "lean_run": p["lean_run"], "summary": line, "track": p.get("track"), "intent": cls})
        if verified and cls in ("formalization-gap", "known-result"):
            flag_statement_finding(n, lean_run, line, p["complete"], engine_run)
            src = p["complete"].get("intent_source")
            record_atlas(n, f"Resolution campaign {datetime.now().date()}: formal-conjectures' statement is settled IN LEAN "
                            f"({p['complete']['answer']}, {lean_run.name}, audited), along a line its intent judges call a "
                            f"{cls}{' (' + str(src) + ')' if src else ''}. A finding about the formal statement, not a "
                            f"resolution of the problem as posed.")
        elif verified:
            flag_for_review(n, lean_run, line, p["complete"]["claim"], engine_run)
            record_atlas(n, f"Resolution campaign {datetime.now().date()}: the research engine's complete answer ({p['complete']['claim']}, "
                            f"{p['complete']['answer']}) is PROVED IN LEAN on formal-conjectures' statement and passed the "
                            f"audit ({lean_run.name}). Open problem: awaiting human review before any claim of resolution.")
        else:
            record_atlas(n, f"Resolution campaign {datetime.now().date()} (${spend:.2f}): Lean on the engine's complete answer "
                            f"({p['complete']['claim']}) did not close: {line[:200]}")
        commit(["resolution"], f"resolution: #{n} Lean {'verified' if verified else 'not verified'}")
        return True
    # screen, scout or deep finished
    wait = limit_wait(ROOT / p["run_dir"]) if row is None and p.get("run_dir") else None
    if wait is not None and int(p.get("limit_waits") or 0) < 20:
        p["limit_waits"] = int(p.get("limit_waits") or 0) + 1
        p["running"] = action
        save_problem(n, p)
        result({"problem": n, "tier": action, "outcome": "usage limit", "rc": rc, "spend": 0.0})
        log(f"#{n}: {action} stopped by a usage limit; waiting {wait / 3600:.1f} h for its reset, then resuming")
        time.sleep(wait)
        return True
    if row is None:
        p["errors"] = int(p.get("errors") or 0) + 1
        p["running"] = None if p["errors"] >= cfg["max_errors"] else action
        save_problem(n, p)
        result({"problem": n, "tier": action, "outcome": "infrastructure", "rc": rc, "spend": 0.0})
        log(f"#{n}: {action} failed (exit {rc}); errors {p['errors']}")
        return True
    run_dir = ROOT / row["run_dir"]
    total = float(row.get("spend_run") or 0.0)
    delta = round(total - float(p.get("spend") or 0.0), 4)
    p.update({"run_dir": row["run_dir"], "spend": total, "running": None, "limit_waits": 0})
    if action == "screen":
        return finish_screen(n, p, cfg, run_dir, delta)
    outcome, info = classify(run_dir)
    n_new, sigs, best = validated_summary(run_dir)
    if p.get("arm") == "pass" and not p.get("track"):        # screened before tracks: its scout classified the line
        p["intent"] = (engine_json(run_dir).get("intent") or {}).get("class")
        p["track"] = track_for("pass", p["intent"])
    chance = info.get("settle_chance")
    ripe = not (isinstance(chance, (int, float)) and chance < SETTLE_FLOOR)
    if outcome == "complete":
        p.update({"next": "lean", "status": "complete", "complete": info})
    elif action == "scout" and p.get("track") == "new-math" and ripe:
        p.update({"next": "program", "status": "program", "traction": info})
    elif outcome == "traction" and action == "scout" and p.get("track") != "statement":
        p.update({"next": "deep", "status": "traction", "traction": info})
    else:
        p.update({"next": None, "status": "done" if outcome == "none" else outcome})
    p["history"].append({"tier": action, "outcome": outcome, "spend": delta})
    skip = set((p.get("claims_done") or {})) | set(p.get("claims_todo") or [])
    if outcome == "complete":
        skip.add(info["claim"])
    p["claims_todo"] = (p.get("claims_todo") or []) + claims_for_lean(run_dir, cfg["lean_claims"]["min_significance"], skip)
    save_problem(n, p)
    result({"problem": n, "tier": action, "outcome": outcome, "spend": delta, "run_dir": row["run_dir"],
            "validated_new": n_new, "significance": sigs, "arm": p.get("arm"),
            "settle_screen": (screen_result(run_dir) or {}).get("mean"), **info})
    log(f"#{n}: {action} -> {outcome} (${delta:.2f}; {n_new} validated new {sigs})")
    if outcome == "complete":
        record_atlas(n, f"Resolution campaign {datetime.now().date()} (${total:.2f}, informal): the research engine wrote a complete "
                        f"answer ({info['answer']}) that a referee, an adversary and both settles judges accepted: "
                        f"{info['statement'][:300]}. Sent to Lean.")
    elif action == "program":
        prog = engine_json(run_dir).get("program") or {}
        sk = prog.get("skeleton") or {}
        est = [l for l in sk.get("lemmas") or [] if l.get("status") == "established"]
        op = [l for l in sk.get("lemmas") or [] if l.get("status") == "open"]
        record_atlas(n, f"Resolution campaign research program {datetime.now().date()} (${total:.2f}, informal): "
                        f"{prog.get('cycles')} cycle(s), stopped: {prog.get('stop')}. "
                        + (f"Skeleton for {str(sk.get('answer')).upper()}: {len(est)} lemma(s) established, {len(op)} open. "
                           + "Open: " + " | ".join(" ".join(str(l.get('statement')).split())[:160] for l in op[:3])
                           if sk else "No skeleton passed its glue check."))
    elif n_new:
        record_atlas(n, f"Resolution campaign {action} {datetime.now().date()} (${total:.2f}, informal): {n_new} validated-new claims "
                        f"(significance {', '.join(map(str, sigs))}); best: {best}")
    commit(["resolution"], f"resolution: #{n} {action} -> {outcome}")
    return True


def import_screens(path: Path, cfg: dict) -> list[int]:
    """Take screen rows made outside the campaign into it (REPORT 3.9: two draws from a map already on disk). Only a row
    at or above the bar comes in, as the pass arm labelled as a backfill. Its map may predate the resolve objective, so a
    problem below the bar is not screened out on it: it keeps its place in the queue and gets the proper screen in turn.
    Every row's cost is logged once, so the daily cap counts it."""
    eligible, took = set(queue(load_state(), cfg)), []
    seen = {(r.get("problem"), r.get("map_run")) for r in rows() if r.get("source") == "backfill"}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        n, m = int(r["problem"]), r.get("mean")
        if (n, r["run_dir"]) in seen:
            continue
        passed = m is not None and m >= float(cfg["screen"]["pass"]) and n in eligible
        result({"problem": n, "tier": "screen", "outcome": "pass" if passed else "below the bar or not a target",
                "settle_chance": m, "draws": r.get("draws"), "spend": float(r.get("cost") or 0.0), "source": "backfill",
                "map_run": r["run_dir"]})
        if passed:
            save_problem(n, {"history": [{"tier": "screen", "outcome": "pass", "settle_chance": m, "map_run": r["run_dir"]}],
                             "settle_chance": m, "arm": "pass", "screen_source": f"backfill from {r['run_dir']}",
                             "next": "scout", "status": "screened"})
            log(f"#{n}: screen (backfill from {r['run_dir']}) -> pass (settle chance {m:.2f})")
            took.append(n)
    return took


# ---------------------------------------------------------------- entry points

def status() -> None:
    st, cfg = load_state(), load_cfg()
    by: dict = {}
    for n, p in st.get("problems", {}).items():
        by.setdefault(p.get("status") or p.get("running") or "?", []).append(int(n))
    print(f"daily cap ${cfg['daily_cap_usd']:.0f}; spent last 24h ${spent_since():.2f}, last 7 days ${spent_since(168):.2f}")
    for k, v in sorted(by.items()):
        print(f"  {k}: {len(v)}  {sorted(v)[:20]}")
    tackled = [int(n) for n, p in st.get("problems", {}).items()
               if any(h.get("tier") in ("scout", "deep", "program", "lean") for h in p.get("history") or [])]
    tracks: dict = {}
    for n, p in st.get("problems", {}).items():
        if int(n) not in tackled:
            continue
        x = tracks.setdefault(p.get("track") or "before tracks", {"tackled": 0, "complete": 0, "verified": 0, "new": 0})
        x["tackled"] += 1
        x["complete"] += bool(p.get("complete"))
        x["verified"] += p.get("status") == "verified"
        x["new"] += bool(p.get("complete")) and (p.get("complete") or {}).get("intent") == "new-math"
    for tr in ("new-math", "statement", "control", "before tracks"):
        if tr in tracks:
            x = tracks[tr]
            print(f"track {tr}: {x['tackled']} tackled, {x['complete']} complete answer(s)"
                  + (f", {x['new']} judged new mathematics" if tr != "statement" else "")
                  + f", {x['verified']} verified in Lean")
    sig3 = sorted({int(r["problem"]) for r in rows() if r.get("outcome") in ("complete", "verified")
                   or 3 in (r.get("significance") or [])})
    print(f"significance 3 (a complete answer, or a claim both novelty judges rate 3): {len(sig3)} of {len(tackled)} "
          f"problems tackled {sig3}")
    arms: dict = {}
    for n, p in st.get("problems", {}).items():
        if p.get("arm") or p.get("settle_chance") is not None:
            a = arms.setdefault(p.get("arm") or "priority", {"screened": 0, "scouted": 0, "complete": 0, "chance": 0.0,
                                                             "backfill": 0})
            a["screened"] += 1
            a["backfill"] += bool(p.get("screen_source"))
            a["chance"] += float(p.get("settle_chance") or 0.0)
            a["scouted"] += any(h.get("tier") == "scout" for h in p.get("history") or [])
            a["complete"] += bool(p.get("complete"))
    for k, a in sorted(arms.items()):
        print(f"screen arm {k}: {a['screened']} screened ({a['backfill']} from maps on disk; mean settle chance "
              f"{a['chance'] / a['screened']:.2f}), {a['scouted']} scouted, {a['complete']} complete")
    act, n = next_action(st, cfg)
    print(f"next: {act} {n or ''}")
    for r in rows()[-8:]:
        print("  ", {k: r.get(k) for k in ("at", "problem", "tier", "outcome", "spend", "validated_new", "significance")})
    if REVIEW.exists():
        print(f"REVIEW NEEDED: {REVIEW.relative_to(ROOT)}")
    if FINDINGS.exists():
        print(f"statement findings: {FINDINGS.relative_to(ROOT)}")


def single_instance():
    """An exclusive lock held for the loop's lifetime. A second loop (a second terminal) exits at once instead of racing
    the first for the same problem, as two did on 2026-10-08."""
    import fcntl
    CAMP.mkdir(exist_ok=True)
    fh = open(CAMP / "loop.lock", "w")
    try:
        fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        return None
    fh.write(str(__import__("os").getpid()))
    fh.flush()
    return fh


def loop() -> None:
    lock = single_instance()
    if lock is None:
        log("another resolution campaign loop is already running; this one exits")
        return
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
    ap.add_argument("cmd", choices=["status", "queue", "once", "loop", "import-screens"])
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("--file", help="import-screens: a jsonl of screen rows (step3/settle_open.jsonl)")
    a = ap.parse_args()
    CAMP.mkdir(exist_ok=True)
    if a.cmd == "status":
        status()
    elif a.cmd == "queue":
        q = queue(load_state(), load_cfg())
        print(f"{len(q)} problems queued; first {a.show}:")
        for n in q[: a.show]:
            print(f"  #{n}  forum {forum_chars(n)} chars")
    elif a.cmd == "import-screens":
        print("imported to the pass arm:", import_screens(Path(a.file), load_cfg()))
    elif a.cmd == "once":
        wait_for_lane()
        step(load_cfg())
    else:
        loop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
