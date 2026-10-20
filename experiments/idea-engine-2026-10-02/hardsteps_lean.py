"""Lean stage for the hard-step bank: hand an engine-proved hard step to the deductive loop, with the proof as its blueprint.

The engine's informal proof of a step is only refereed. Here Lean decides whether it holds:
- a fresh run gets the step as its frozen statement (identifiers renamed to a fresh id, so no earlier program directory
  is reused);
- its state carries the engine's proof as `discovery.best_proof`;
- it runs `--mode research --allow-research --blueprint on`.

A proof that closes the residual and passes the audit is a Lean-certified step the harness had failed before. The step
belongs to a problem resolved in the literature, so an audit PASS is the verification.

    python3 experiments/idea-engine-2026-10-02/hardsteps_lean.py --engine-run runs/<...>-hardstep-erdos7NNNNN --claim r1s2/C1
"""
import argparse, json, re, subprocess, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
RESULTS = ROOT / "benchmarks" / "timesplit" / "results"


def engine_record(engine_run: Path) -> tuple[str | None, dict | None]:
    """The time-split results row of the engine run whose proof this Lean stage formalizes, if it was a time-split
    evaluation (a hard-step run on a train item is not: its frame says the problem was resolved)."""
    rel = str(engine_run.resolve().relative_to(ROOT))
    for f in sorted(RESULTS.glob("*.jsonl")):
        if any(x in f.name for x in (".infra.", ".ideas.", ".progress.", ".aliases.", ".grades.")):
            continue
        for line in f.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("run_dir") == rel and r.get("alias") is not None:
                return f.name[: -len(".jsonl")], r
    return None, None


def record_alias(engine_run: Path, lean_run: Path, sid: str) -> None:
    """At launch: the fresh id resolves to its catalogue number (atlas_ids.py), so the Atlas attributes the run while
    it is still going."""
    tag, er = engine_record(engine_run)
    if er:
        af = RESULTS / f"{tag}-lean.aliases.jsonl"
        if af.exists() and any(json.loads(l).get("alias") == int(sid) for l in af.read_text().splitlines() if l.strip()):
            return
        with af.open("a") as f:
            f.write(json.dumps({"alias": int(sid), "problem": er["problem"],
                                "run_dir": str(lean_run.resolve().relative_to(ROOT))}) + "\n")


def record_result(engine_run: Path, lean_run: Path, claim: str, sid: str, rc: int | None) -> dict | None:
    """At the end: a results row pointing at the Lean run, in `<engine tag>-lean.jsonl`.

    Without it the audit's blindness checks (provenance, probe, masking, no identity in any prompt) never run. #1125's
    Lean proof passed all seven Lean checks and still got the verdict FAIL on `benchmark_record` ("no time-split record
    points at this run"), so the Atlas could not count it. `solved` follows the runner's meaning: the TRUE direction
    verified. The row names the engine run, whose prompts the audit scans as well."""
    tag, er = engine_record(engine_run)
    if not er:
        return None
    st = json.loads((lean_run / "state.json").read_text()) if (lean_run / "state.json").exists() else {}
    done = json.loads((lean_run / "DONE").read_text()) if (lean_run / "DONE").exists() else {}
    # the direction proved, relative to the benchmark's statement: a FALSE item's stage proves its negation, in an
    # --open run committed to `neg`, whose verification lives in that direction's own state
    committed = st.get("benchmark_direction") or "pos"
    vst = st
    if st.get("open_results") is not None and (lean_run / committed / "state.json").exists():
        vst = json.loads((lean_run / committed / "state.json").read_text())
    verified = done.get("exit") == 0 and bool((vst.get("verify") or {}).get("all_clear"))
    right = (committed == "pos") == (er.get("truth") == "true")
    line = (lean_run / "SUMMARY.line").read_text() if (lean_run / "SUMMARY.line").exists() else ""
    m = re.search(r"spend=\$([0-9.]+)", line)
    row = {"problem": er["problem"], "tag": f"{tag}-lean", "alias": int(sid),
           "run_dir": str(lean_run.resolve().relative_to(ROOT)), "answer": er.get("answer"), "truth": er.get("truth"),
           "split": er.get("split"), "returncode": done.get("exit", rc),
           "solved": verified and right, "contradiction": verified and not right, "committed": committed,
           "spend": float(m.group(1)) if m else None, "stage": "lean",
           "engine_run": er["run_dir"], "engine_alias": er.get("alias"), "engine_claim": claim,
           "engine_spend": er.get("spend"),
           "protocol": {"masked": True, "benchmark": bool(st.get("benchmark")), "stage": "lean",
                        "knowledge": "lemma store excluded (--benchmark)", "blueprint": f"{er['run_dir']} {claim}",
                        "engine_tag": tag},
           "at": datetime.now().isoformat(timespec="seconds")}
    with (RESULTS / f"{tag}-lean.jsonl").open("a") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
    return row


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--engine-run", required=True)
    ap.add_argument("--claim", required=True, help="session/claim id of the proof to use, e.g. r1s2/C1")
    ap.add_argument("--budget", type=float, default=15.0)
    ap.add_argument("--cycles", type=int, default=4)
    ap.add_argument("--extend", type=float, default=0.0, help="--budget-extend: USD added while the residual still shrinks")
    ap.add_argument("--extend-max", type=float, default=0.0, help="--budget-extend-max: the hard cap, USD")
    ap.add_argument("--full-run", help="target the WHOLE problem: this original run's frozen statement, not the step")
    ap.add_argument("--chain", action="store_true", help="the blueprint is the claim with every lemma under it")
    ap.add_argument("--id", help="the fresh synthetic id (default: the engine run's)")
    ap.add_argument("--record-only", metavar="LEAN_RUN",
                    help="write the time-split alias and results rows for an existing Lean run, then stop")
    args = ap.parse_args()
    er = (ROOT / args.engine_run).resolve()
    # Only a WHOLE-problem Lean stage on the engine run's own statement is a time-split evaluation; a single step is not.
    timesplit = bool(args.full_run) and (ROOT / args.full_run).resolve() == er
    if args.record_only:
        lr = (ROOT / args.record_only).resolve()
        sid = args.id or re.search(r"erdos(\d+)$", lr.name).group(1)
        row = None
        if timesplit:
            record_alias(er, lr, sid)
            row = record_result(er, lr, args.claim, sid, None)
        print(json.dumps(row)[:300] if row else "not a whole-problem stage of a time-split engine run; nothing written")
        return 0
    src = (ROOT / args.full_run).resolve() if args.full_run else er
    st = json.loads((src / "state.json").read_text())
    prob = json.loads((src / "problem.json").read_text())
    ej = json.loads((er / "engine" / "engine.json").read_text())
    sess, cid = args.claim.split("/")
    c = next(x for x in ej["ledger"] if x.get("session") == sess and x.get("id") == cid)
    if c.get("status") not in ("PROVED", "REFUTED"):
        print(f"{args.claim} is {c.get('status')}, not a proof or refutation")
        return 2
    m = re.search(r"\berdos_(\d+)", st["statement"])
    old_id = m.group(1) if m else None
    sid = str(args.id or (json.loads((er / "problem.json").read_text())["id"] if not args.full_run else prob["id"]))
    prob = {**prob, "id": sid}
    # (?!\d), not \b: every identifier continues with "_" (erdos_27285_hyp_top, erdos_27285_Rep), and \b after the
    # digits never matched, so the first #435 Lean run kept the old ids and no plan could parse against the new one.
    lean = re.sub(rf"\berdos_{old_id}(?!\d)", f"erdos_{sid}", st["statement"]) if old_id else st["statement"]
    # The step's theorem becomes the run's main theorem `erdos_<sid>`. A run started from the CLI looks for exactly
    # that name (only in-process research children get another `thm_name`), so with `erdos_<sid>_hyp_top` kept, the
    # second #435 Lean run matched no plan at all and logged "no skeleton block in the plan" for a complete skeleton.
    thms = re.findall(rf"(?m)^\s*theorem\s+(erdos_{sid}\w*)", lean)
    if thms and thms[-1] != f"erdos_{sid}":
        lean = re.sub(rf"\b{re.escape(thms[-1])}(?![\w'!?])", f"erdos_{sid}", lean)
    answer = "true" if c["status"] == "PROVED" else "false"
    # A whole time-split problem settled FALSE: the run attacks the negation as an --open run committed to `neg`. The
    # harness builds the negation itself (`erdos_<id>_neg`, Lean-checked), and every prompt of that direction knows
    # it is the negation. Until 2026-10-20 a FALSE answer was recorded and never run. Then, for one launch, the negated
    # text was the frozen statement of a plain run: its plans read the original statement, called "the target" false
    # and stopped (`target_believed_false`) on dev #537 and #871 within a cycle.
    negate = answer == "false" and timesplit
    run_answer = answer
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-hardlean-erdos{sid}"
    run_dir.mkdir(parents=True)
    if timesplit:
        record_alias(er, run_dir, sid)
    (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    if args.chain:
        sys.path.insert(0, str(ROOT))
        import harness as H
        proof = H.engine_chain_text(c, ej["ledger"])     # the claim with every lemma under it, gap-closed versions in place
    else:
        proof = f"CLAIM: {c['statement']}\n\nPROOF:\n{c.get('proof') or ''}"
    disc = {"decision": {"commit": "pos" if run_answer == "true" else "neg", "answer": run_answer, "share": 1.0},
            "best_proof": {"text": proof, "answer": run_answer, "complete": True},
            "guidance": f"An informal proof{' of the whole problem' if args.full_run else ' of this step'}, refereed but "
                        f"unverified, from a research-engine run ({er.name}, {args.claim}"
                        f"{', with every lemma under it' if args.chain else ''})"
                        f"{'. It REFUTES the original statement; the target here is that statement negated, which this argument proves' if negate else ''}"
                        f":\n{proof[:24000]}",
            "refereed_complete": True, "mode": "engine-hardstep"}
    (run_dir / "state.json").write_text(json.dumps({
        "statement": lean, "problem_input": prob, "mode": "research", "invocations": [], "benchmark": True,
        "discovery": disc, "statement_source": f"{'the whole problem' if args.full_run else 'hard step'} from {st.get('statement_source')}, ids renamed erdos_{old_id} -> erdos_{sid}",
        "assistance": [f"the informal proof came from the research engine run {er.name} ({args.claim}); no operator proof"],
        **({"benchmark_direction": "neg"} if negate else {})},
        indent=2, ensure_ascii=False))
    if answer == "false" and not negate:
        print("a refuted step: the deductive loop would need the negation; recorded, not run")
        return 0
    cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
           str(run_dir), "--mode", "research", "--allow-research", "--benchmark", "--masked", "--no-brief",
           "--skip-literature", "--blueprint", "on", "--residual-view", "outline", "--research-cycles", str(args.cycles),
           "--run-budget", str(args.budget), "--lean-timeout", "1800", "--llm-timeout", "5400",
           "--backend", "claude-cli", "--model", "claude-opus-5-5", *(["--open", "--discover", "on"] if negate else []),
           *(["--budget-extend", str(args.extend), "--budget-extend-max", str(args.extend_max)] if args.extend > 0 else [])]
    with (run_dir / "lane.log").open("w") as log:
        rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                            timeout=16 * 3600).returncode       # a self-funding run may outlast the old 8 hours
    line = (run_dir / "SUMMARY.line").read_text().strip() if (run_dir / "SUMMARY.line").exists() else ""
    if timesplit:
        record_result(er, run_dir, args.claim, sid, rc)
    with (HERE / "hardsteps_lean.jsonl").open("a") as f:
        f.write(json.dumps({"engine_run": str(er.relative_to(ROOT)), "claim": args.claim, "lean_run": str(run_dir.relative_to(ROOT)),
                            "exit": rc, "summary": line, "at": datetime.now().isoformat(timespec="seconds")}) + "\n")
    print(line or f"exit {rc}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
