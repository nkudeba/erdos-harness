#!/usr/bin/env python3
"""Recall probe: does the model recognise the benchmark statement, and does masking remove the cue?

    python3 benchmarks/deductive/probe.py --problem 275            # both versions: identified and masked
    python3 benchmarks/deductive/probe.py --problem 275 --only masked

One short `claude -p` call per version. The answer is saved verbatim under benchmarks/deductive/probes/ with
its cost. A probe cannot prove the model does NOT remember a solution; it records what the model says when
asked directly, before the run, so the benchmark result can be read against it.
"""
from __future__ import annotations
import argparse, json, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import harness as H

PROBE = """You are being asked a calibration question before a benchmark; answer plainly and honestly.

Below is a theorem statement in Lean 4 with an informal rendering.

INFORMAL:
{en}

LEAN:
```lean
{lean}
```

1. Do you recognise this as a specific named problem, conjecture or published result? If yes, give the name,
   the source (author, year, or where it is catalogued) and how confident you are. If no, say so.
2. Without writing a proof, describe in 3-6 sentences the proof strategy you would try first, and say whether
   that strategy is one you REMEMBER from a source or one you are proposing now.
3. If you remember a specific published proof or a specific formal (Lean) proof of this statement, say where."""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problem", required=True)
    ap.add_argument("--only", choices=["identified", "masked"], default=None)
    ap.add_argument("--model", default="claude-opus-5-5")
    args = ap.parse_args()
    pid = str(int(args.problem))
    solved = json.loads((ROOT / "knowledge" / "solved" / f"Erdos{pid}.json").read_text())
    prob = json.loads((ROOT / "problems" / f"erdos_{pid}.json").read_text())
    versions = {}
    if args.only in (None, "identified"):
        versions["identified"] = (f"Erdős problem #{pid} (erdosproblems.com/{pid}): " + prob["statement"], solved["statement"])
    mask_path = ROOT / "benchmarks" / "deductive" / "masks" / f"{pid}.json"
    if args.only in (None, "masked"):
        if not mask_path.exists():
            print(f"no mask for #{pid}: {mask_path}", file=sys.stderr)
            return 2
        m = json.loads(mask_path.read_text())
        versions["masked"] = (m["statement_en"], m["statement_lean"])
    out_dir = ROOT / "benchmarks" / "deductive" / "probes"
    out_dir.mkdir(parents=True, exist_ok=True)
    backend = H.ClaudeCliBackend(args.model, 900, 1.5)
    for kind, (en, lean) in versions.items():
        prompt = PROBE.format(en=en, lean=lean)
        if kind == "masked":
            prompt = H.mask_prompt(prompt)
        answer = backend.complete("probe", prompt)
        meta = getattr(backend, "last_meta", {}) or {}
        cost = meta.get("cost_usd")
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
        path = out_dir / f"{pid}-{kind}-{stamp}.md"
        path.write_text(f"# Recall probe — #{pid}, {kind} statement ({stamp}Z)\n\nmodel: {args.model}  cost_usd: {cost}\n\n"
                        f"## Prompt\n\n```\n{prompt}\n```\n\n## Answer\n\n{answer}\n")
        print(f"[{kind}] cost={cost} -> {path.relative_to(ROOT)}")
        print(answer[:1500])
        print("-" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())
