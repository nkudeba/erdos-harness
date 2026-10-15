"""Discovery-only screen of OPEN Erdős problems (2026-10-02): which of them does the in-run discovery stage
(crossfed rounds + a ladder of easier variants, harness.py --stop-after discover) write a REFEREED complete proof
for? No Lean is run, so the screen can share the machine with a Lean lane.

Each problem gets:
  - its formal-conjectures main theorem, answer stripped (benchmarks/timesplit/timesplit.py parse_fc +
    frozen_statement), as the Lean statement the attempts and the referee read. Nothing is compiled here;
  - its erdosproblems.com forum thread (atlas-data/forum/<n>.json, refreshed the same day) as its literature
    (--library), because the thread is where the known partial results and withdrawn claims live;
  - --blackboard on, so a later full run on the same problem starts from what this screen learned.

A refereed proof here is a CANDIDATE, nothing more: one medium-effort referee, no Lean. These problems are open, so
any claim would also need human review; claimEligible stays false.

    python3 experiments/open-discovery-2026-10-02/screen.py 153 1203 455 ...
"""
import json, re, subprocess, sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
sys.path.insert(0, str(ROOT))
import timesplit as T


def thread_digest(n: str) -> str:
    """The problem page (statement and the site's notes on what is known), the forum comments and the proof claims.

    Until 2026-10-14 two markers silently emptied sections. The page was cut at "OPEN", a word #769's page never uses,
    so its literature (Hadwiger, Burgess–Erdős, Hudelson, Connor–Marmorino) never reached the engine. The claims were
    cut at "Order by", which only the THREAD page has, so no proof claim ever did: the campaign's Lean-verified
    disproof of #769 turned out to be a weaker form of two claims posted there in July and August 2026."""
    d = json.loads((ROOT / "atlas-data" / "forum" / f"{n}.json").read_text())
    t = d.get("thread") or ""
    i = t.find("Order by")
    body = t[i:] if i >= 0 else t
    body = body.split("All comments are the responsibility of the user")[0]
    end = t.find("Proof expositions")
    nav = t.rfind("Random", 0, end) if end >= 0 else -1          # the last navigation item before the statement
    head = t[(nav + len("Random")) if nav >= 0 else 0:end] if end >= 0 else ""
    claims = d.get("claims") or ""
    m = re.search(r"There (?:are|is) \d+ proof claims?", claims)
    claims = claims[m.start():].split("All comments are the responsibility of the user")[0] if m else ""
    return (f"# erdosproblems.com #{n}: problem page and forum thread (fetched {d.get('fetched', 'recently')})\n\n"
            "Comments and proof claims are unverified; several withdraw earlier claims.\n\n## Page\n" + head.strip()[:4000]
            + "\n\n## Forum comments\n" + body.strip()[:9000]
            + ("\n\n## Proof claims page\n" + claims.strip()[:8000] if claims.strip() else ""))


def main(nums: list[str]) -> int:
    ranks = {str(p["id"]): p for p in json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]}
    out = HERE / "results.jsonl"
    for n in nums:
        src = (HERE / "fc" / f"{n}.lean").read_text()
        fc = T.parse_fc(src, int(n))
        if fc.get("error"):
            print(f"#{n}: formal-conjectures parse failed: {fc['error']}", flush=True)
            continue
        statement = T.frozen_statement(fc, int(n))
        lib = HERE / "library" / n
        lib.mkdir(parents=True, exist_ok=True)
        (lib / "DIGEST.md").write_text(thread_digest(n))
        run_dir = ROOT / "runs" / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-erdos{n}"
        run_dir.mkdir(parents=True)
        prob = {"id": n, "statement": ranks[n]["statement"], "tags": ranks[n].get("tags") or [],
                "url": f"https://www.erdosproblems.com/{n}",
                "notes": "OPEN problem on erdosproblems.com. Frozen statement: formal-conjectures main theorem, answer "
                         "stripped (" + str(fc.get("form")) + "). Discovery screen only (no Lean)."}
        (run_dir / "problem.json").write_text(json.dumps(prob, indent=2, ensure_ascii=False))
        (run_dir / "state.json").write_text(json.dumps({"statement": statement, "problem_input": prob, "mode": "research",
                                                        "invocations": [], "statement_source": "formal-conjectures main "
                                                        "theorem, answer stripped, via timesplit.parse_fc"}, indent=2,
                                                       ensure_ascii=False))
        cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(run_dir / "problem.json"), "--resume",
               str(run_dir), "--mode", "research", "--allow-research", "--no-brief", "--skip-literature",
               "--stop-after", "discover", "--discover-mode", "crossfed", "--discover-rounds", "2", "--discover-ladder", "3",
               "--discover-draws", "1", "--discover-total-budget", "5", "--blackboard", "on", "--library", str(lib),
               "--run-budget", "6.5", "--backend", "claude-cli", "--model", "claude-opus-5-5"]
        with (run_dir / "lane.log").open("w") as log:
            rc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                timeout=3 * 3600).returncode
        try:
            dj = json.loads((run_dir / "discovery.json").read_text())
        except (OSError, ValueError):
            print(f"#{n}: no discovery record (exit {rc}); see {run_dir}/lane.log", flush=True)
            continue
        dec = dj.get("decision") or {}
        best = dj.get("best_proof") or {}
        import harness as H
        spend = H.collect_run_facts(run_dir, n).get("spend")
        rec = {"problem": n, "run_dir": str(run_dir.relative_to(ROOT)), "exit": rc, "decision": dec,
               "refereed_complete": dj.get("refereed_complete"), "best_answer": best.get("answer"),
               "best_confidence": best.get("confidence"), "attempts": len(dj.get("attempts") or []),
               "rungs": sum(1 for r in (dj.get("ladder") or []) if r.get("rung")), "spend": spend,
               "key_steps": (best.get("key_steps") or [])[:8], "at": datetime.now().isoformat(timespec="seconds")}
        with out.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(f"#{n}: decided={dec.get('answer')} share={dec.get('share')} refereed={dj.get('refereed_complete')} "
              f"${spend}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
