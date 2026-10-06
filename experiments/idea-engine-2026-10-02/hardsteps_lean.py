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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--engine-run", required=True)
    ap.add_argument("--claim", required=True, help="session/claim id of the proof to use, e.g. r1s2/C1")
    ap.add_argument("--budget", type=float, default=15.0)
    ap.add_argument("--cycles", type=int, default=4)
    ap.add_argument("--extend", type=float, default=0.0, help="--budget-extend: USD added while the residual still shrinks")
    ap.add_argument("--extend-max", type=float, default=0.0, help="--budget-extend-max: the hard cap, USD")
    args = ap.parse_args()
    er = (ROOT / args.engine_run).resolve()
    st = json.loads((er / "state.json").read_text())
    prob = json.loads((er / "problem.json").read_text())
    ej = json.loads((er / "engine" / "engine.json").read_text())
    sess, cid = args.claim.split("/")
    c = next(x for x in ej["ledger"] if x.get("session") == sess and x.get("id") == cid)
    if c.get("status") not in ("PROVED", "REFUTED"):
        print(f"{args.claim} is {c.get('status')}, not a proof or refutation")
        return 2
    m = re.search(r"\berdos_(\d+)", st["statement"])
    old_id = m.group(1) if m else None
    sid = str(prob["id"])
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
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-hardlean-erdos{sid}"
    run_dir.mkdir(parents=True)
    (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    proof = f"CLAIM: {c['statement']}\n\nPROOF:\n{c.get('proof') or ''}"
    disc = {"decision": {"commit": "pos" if answer == "true" else "neg", "answer": answer, "share": 1.0},
            "best_proof": {"text": proof, "answer": answer, "complete": True},
            "guidance": f"An informal proof of this step, refereed but unverified, from a research-engine run "
                        f"({er.name}, {args.claim}):\n{proof[:12000]}",
            "refereed_complete": True, "mode": "engine-hardstep"}
    (run_dir / "state.json").write_text(json.dumps({
        "statement": lean, "problem_input": prob, "mode": "research", "invocations": [], "benchmark": True,
        "discovery": disc, "statement_source": f"hard step from {st.get('statement_source')}, ids renamed erdos_{old_id} -> erdos_{sid}",
        "assistance": [f"the informal proof came from the research engine run {er.name} ({args.claim}); no operator proof"]},
        indent=2, ensure_ascii=False))
    if answer == "false":
        print("a refuted step: the deductive loop would need the negation; recorded, not run")
        return 0
    cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
           str(run_dir), "--mode", "research", "--allow-research", "--benchmark", "--masked", "--no-brief",
           "--skip-literature", "--blueprint", "on", "--residual-view", "outline", "--research-cycles", str(args.cycles),
           "--run-budget", str(args.budget), "--lean-timeout", "1800", "--llm-timeout", "5400",
           "--backend", "claude-cli", "--model", "claude-opus-5-5",
           *(["--budget-extend", str(args.extend), "--budget-extend-max", str(args.extend_max)] if args.extend > 0 else [])]
    with (run_dir / "lane.log").open("w") as log:
        rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                            timeout=8 * 3600).returncode
    line = (run_dir / "SUMMARY.line").read_text().strip() if (run_dir / "SUMMARY.line").exists() else ""
    with (HERE / "hardsteps_lean.jsonl").open("a") as f:
        f.write(json.dumps({"engine_run": str(er.relative_to(ROOT)), "claim": args.claim, "lean_run": str(run_dir.relative_to(ROOT)),
                            "exit": rc, "summary": line, "at": datetime.now().isoformat(timespec="seconds")}) + "\n")
    print(line or f"exit {rc}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
