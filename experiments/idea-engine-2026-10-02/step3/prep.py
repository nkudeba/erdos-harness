"""Step 3 prep: the frozen statements and forum libraries for the open-problem screen. No model calls.

For each candidate:
- its formal-conjectures file at ONE pinned commit (`fc-sha.txt`), parsed and answer-stripped exactly as the time-split
  benchmark does (`timesplit.parse_fc` + `frozen_statement`), cached in `fc/<n>.lean`;
- its erdosproblems.com page, forum thread and proof-claims page, as `library/<n>/DIGEST.md`, built by the earlier
  open-problem screen's `thread_digest` from `atlas-data/forum/<n>.json` (refreshed 2026-10-06).

A candidate with no formal-conjectures file, or one that does not parse, is reported and left out: the screen needs a
Lean statement to freeze.

    python3 experiments/idea-engine-2026-10-02/step3/prep.py 7 264 488 ...
"""
import importlib.util, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
import timesplit as T

_spec = importlib.util.spec_from_file_location("od_screen", ROOT / "experiments" / "open-discovery-2026-10-02" / "screen.py")
OD = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(OD)


def main(nums: list[str]) -> int:
    sha_file = HERE / "fc-sha.txt"
    if not sha_file.exists():
        sha_file.write_text(json.loads(T.fetch(T.SOURCES["fc_head"], HERE / "fc-head.json", True))["sha"])
    sha = sha_file.read_text().strip()
    rows = []
    for n in nums:
        src = T.fetch(T.SOURCES["fc_file"].format(sha=sha, n=n), HERE / "fc" / f"{n}.lean", pause=0.1)
        fc = T.parse_fc(src, int(n)) if src.strip() else {"error": "no formal-conjectures file"}
        row = {"problem": n, "fc": "ok" if not fc.get("error") else fc["error"], "form": fc.get("form")}
        if not fc.get("error"):
            row["statement_chars"] = len(T.frozen_statement(fc, int(n)))
            lib = HERE / "library" / n
            lib.mkdir(parents=True, exist_ok=True)
            (lib / "DIGEST.md").write_text(OD.thread_digest(n))
            row["digest_chars"] = len((lib / "DIGEST.md").read_text())
        rows.append(row)
        print(json.dumps(row), flush=True)
    (HERE / "prep.json").write_text(json.dumps({"fc_sha": sha, "rows": rows}, indent=2))
    ok = [r["problem"] for r in rows if r["fc"] == "ok"]
    print(f"{len(ok)} of {len(rows)} ready: {' '.join(ok)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
