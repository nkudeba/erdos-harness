#!/usr/bin/env python3
"""Set up a BLIND deductive re-derivation of an already-solved problem (docs/deductive-research-mode.md §6).

The 19 proofs in knowledge/solved/ were produced with the site's resolution notes in the problem file. A
benchmark withholds them: the run sees only the English statement, the tags and the frozen Lean statement
that the saved proof certifies, and must build a residual skeleton on its own. Comparing the skeleton with
the saved proof says whether the deductive loop arrives at the same route.

    python3 benchmarks/deductive/prepare.py --problem 645                 # print the command
    python3 benchmarks/deductive/prepare.py --problem 645 --launch        # start it in the background (nohup)

The run passes `--benchmark`, so it never writes knowledge/solved, harvests no lemmas and writes no brief.
Judge it by `programs/erdos_<n>/RESIDUAL.md` and `Residual.lean`, then by `RUN-SUMMARY` (`residual=`),
never by `lemmas=` alone. Cost is real: pass `--run-budget` deliberately and keep to one lane.
"""
from __future__ import annotations
import argparse, json, os, subprocess, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / "benchmarks" / "deductive"
BLIND_KEYS = ("id", "statement", "tags", "url")          # everything else in problems/erdos_<n>.json may leak the answer


def blind_problem(pid: str) -> dict:
    solved = json.loads((ROOT / "knowledge" / "solved" / f"Erdos{pid}.json").read_text())
    src = ROOT / "problems" / f"erdos_{pid}.json"
    full = json.loads(src.read_text()) if src.exists() else {"id": pid, "statement": ""}
    prob = {k: full[k] for k in BLIND_KEYS if k in full}
    prob["id"] = str(prob.get("id", pid))
    prob["imports"] = solved.get("imports") or full.get("imports")
    prob["benchmark"] = {"kind": "blind deductive re-derivation", "reference": f"knowledge/solved/Erdos{pid}.lean",
                         "withheld": sorted(k for k in full if k not in BLIND_KEYS)}
    return prob, solved["statement"]


def masked_problem(pid: str) -> tuple[dict, str, dict]:
    """A de-identified variant from benchmarks/deductive/masks/<n>.json: synthetic id, paraphrased statement,
    alpha-renamed frozen theorem, no tags (so no cluster library and none of its Erdős-named declarations).
    The true id lives only in the mask file and in a sidecar the harness never reads."""
    mask = json.loads((BENCH / "masks" / f"{pid}.json").read_text())
    # A literature-solved problem has no saved solve: its frozen statement is the mask's own (operator-written,
    # compile- and faithfulness-checked, recorded as such in the mask), and its imports come from the mask.
    solved_path = ROOT / "knowledge" / "solved" / f"Erdos{pid}.json"
    solved = json.loads(solved_path.read_text()) if solved_path.exists() else {}
    alias = str(int(mask["alias_id"]))
    prob = {"id": alias, "statement": mask["statement_en"], "imports": mask.get("imports") or solved.get("imports"),
            "benchmark": {"kind": "masked deductive re-derivation", "reference": "withheld (see benchmarks/deductive/masks/)"}}
    return prob, mask["statement_lean"], mask


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", required=True, help="a problem with a saved proof in knowledge/solved/")
    ap.add_argument("--masked", action="store_true",
                    help="use benchmarks/deductive/masks/<n>.json: synthetic id, paraphrase, renamed theorem, prompts scrubbed")
    ap.add_argument("--no-check", action="store_true", help="skip the Lean compile check of the frozen statement")
    ap.add_argument("--check-only", action="store_true",
                    help="compile the frozen statement and stop: writes no problem file and creates no run dir")
    ap.add_argument("--run-budget", type=float, default=8.0)
    ap.add_argument("--research-cycles", type=int, default=2)
    ap.add_argument("--hyps-per-cycle", type=int, default=3)
    ap.add_argument("--model", default="claude-opus-5-5", help="CLAUDE.md: the CLI default hits its usage limit early")
    ap.add_argument("--backend", default="claude-cli", choices=["claude-cli", "codex-cli"])
    ap.add_argument("--open", action="store_true",
                    help="attack the frozen statement AND its negation (two directions, each its own deductive program; "
                         "the budget is split between them)")
    ap.add_argument("--min-child-budget", type=float, default=None)
    ap.add_argument("--launch", action="store_true", help="start the run now, detached, logging to <run_dir>/lane.log")
    args = ap.parse_args()
    pid = str(int(args.problem))
    mask = None
    if args.masked:
        prob, frozen, mask = masked_problem(pid)
        run_id = prob["id"]
    else:
        prob, frozen = blind_problem(pid)
        run_id = pid
    if args.launch:
        # check the lane BEFORE writing anything: a refused launch used to leave an empty run dir behind
        live = subprocess.run(["pgrep", "-f", "harness.py run"], capture_output=True, text=True).stdout.strip()
        if live:
            print(f"refusing to launch: a lane is already live (pids {live.split()}); CLAUDE.md says one lane at a time")
            return 2
    if not args.no_check:
        sys.path.insert(0, str(ROOT))
        import harness as H
        res = H.LeanChecker(H.FORMAL, 420).check(H.compose(frozen, prob.get("imports") or H.DEFAULT_IMPORTS),
                                                   ROOT / "runs" / "adhoc" / f"bench-statement-{run_id}.lean")
        # (runs/adhoc is scratch; --check-only stops right after this check)
        if not res["ok"]:
            print("frozen statement does not compile:", res["errors"][:2]); return 2
        print("frozen statement compiles (with sorry)")
    if args.check_only:
        return 0
    pdir = BENCH / "problems"
    pdir.mkdir(parents=True, exist_ok=True)
    pfile = pdir / f"erdos_{run_id}.json"
    pfile.write_text(json.dumps(prob, indent=2, ensure_ascii=False))
    run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-bench-erdos{run_id}"
    run_dir.mkdir(parents=True)
    state = {"statement": frozen, "problem_input": prob, "literature": "", "mode": "research",
             "mode_reason": "deductive benchmark: blind re-derivation of a solved problem (notes withheld)"
                            + (", identity masked" if mask else ""),
             "invocations": [], "benchmark": True}
    (run_dir / "state.json").write_text(json.dumps(state, indent=2, ensure_ascii=False))
    if mask:
        (run_dir / "MASK.json").write_text(json.dumps({"true_problem": pid, "alias_id": run_id,
                                                        "reference": mask.get("reference"), "changes": mask.get("changes")}, indent=2))
    cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(pfile), "--resume", str(run_dir),
           "--mode", "research", "--allow-research", "--benchmark", "--skip-literature", "--no-brief",
           *(["--masked"] if mask else []), *(["--open"] if args.open else []),
           *(["--min-child-budget", str(args.min_child_budget)] if args.min_child_budget else []),
           "--research-loop", "deductive", "--run-budget", str(args.run_budget),
           "--research-cycles", str(args.research_cycles), "--hyps-per-cycle", str(args.hyps_per_cycle),
           "--backend", args.backend] + (["--model", args.model] if args.model else [])
    print("blind problem:", pfile.relative_to(ROOT))
    print("run dir:      ", run_dir.relative_to(ROOT))
    print("reference:    ", f"knowledge/solved/Erdos{pid}.lean" + (f"  (masked as #{run_id}; MASK.json in the run dir)" if mask else ""))
    print("command:\n  " + " ".join(cmd))
    if not args.launch:
        return 0
    live = subprocess.run(["pgrep", "-f", "harness.py run"], capture_output=True, text=True).stdout.strip()
    if live:                                    # a lane started during the statement check
        print(f"refusing to launch: a lane is already live (pids {live.split()}); CLAUDE.md says one lane at a time")
        return 2
    log = open(run_dir / "lane.log", "w")
    proc = subprocess.Popen(cmd, cwd=str(ROOT), stdout=log, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL, start_new_session=True, env=dict(os.environ))
    (run_dir / "lane.pid").write_text(str(proc.pid))
    print(f"launched pid {proc.pid}; watch with: tail -1 {run_dir.relative_to(ROOT)}/SUMMARY.line "
          f"(or python3 harness.py summary --run {run_dir.relative_to(ROOT)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
