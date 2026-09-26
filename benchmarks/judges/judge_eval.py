#!/usr/bin/env python3
"""Can a fast, cheap model judge which hypothesis attacks will succeed, well enough to steer the budget?

    python3 benchmarks/judges/judge_eval.py --model claude-haiku-4-5-20251001      # ~$0.10-1 for 87 items
    python3 benchmarks/judges/judge_eval.py --score-only                           # re-score saved answers

Data: `attacks.jsonl`, one row per past hypothesis attack. Each row has the closed Lean statement it attacked,
whether it was proved, what it cost, and the plan's own difficulty rating. Rows come from train items and from
runs outside the benchmark only. Dev and test attacks are excluded, because a judge calibrated on them would carry
their solutions into every later dev evaluation.

A judge is worth wiring into the harness only if it beats what the harness already has for free: the plan's own
difficulty rating. The report prints both, and a length baseline.
"""
from __future__ import annotations
import argparse, json, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "attacks.jsonl"

PROMPT = """You are a triage judge for a Lean 4 + Mathlib theorem-proving system. Below is one closed Lean statement
that the system will try to prove. Estimate the probability that ONE attempt by a strong model (write a complete
proof in one go, then fix it using the compiler's errors a few times) produces a proof that Lean accepts.

Judge by the mathematics and the Lean effort: an elementary fact with Mathlib support is likely, and a statement
that packages a deep theorem or an open problem is unlikely.

STATEMENT:
{statement}

Answer with ONLY a JSON object on one line:
{{"p_success": <number between 0 and 1>, "difficulty": "elementary" | "moderate" | "hard"}}"""


def ask(model: str, statement: str, budget: float) -> tuple[dict, float]:
    cmd = ["claude", "-p", "--output-format", "json", "--max-budget-usd", str(budget), "--model", model,
           "--setting-sources", "", "--strict-mcp-config", "--mcp-config", '{"mcpServers":{}}', "--tools", ""]
    r = subprocess.run(cmd, input=PROMPT.format(statement=statement[:6000]), capture_output=True, text=True, timeout=300)
    try:
        d = json.loads(r.stdout)
    except ValueError:
        return {"error": (r.stdout or r.stderr)[:200]}, 0.0
    cost = float(d.get("total_cost_usd") or 0.0)
    m = re.search(r"\{[^{}]*\"p_success\"[^{}]*\}", d.get("result") or "")
    if not m:
        return {"error": "no JSON in answer: " + (d.get("result") or "")[:200]}, cost
    try:
        return json.loads(m.group(0)), cost
    except ValueError:
        return {"error": "bad JSON: " + m.group(0)[:200]}, cost


def auc(scores: list[float], labels: list[bool]) -> float | None:
    """P(score of a random success > score of a random failure), ties count half."""
    pos = [s for s, y in zip(scores, labels) if y]
    neg = [s for s, y in zip(scores, labels) if not y]
    if not pos or not neg:
        return None
    wins = sum((p > n) + 0.5 * (p == n) for p in pos for n in neg)
    return wins / (len(pos) * len(neg))


def brier(ps: list[float], labels: list[bool]) -> float:
    return sum((p - y) ** 2 for p, y in zip(ps, labels)) / len(ps)


RANK = {"elementary": 3, "moderate": 2, "hard": 1}


def report(rows: list[dict], key: str) -> str:
    out = []
    y = [r["proved"] for r in rows]
    base = sum(y) / len(y)
    out.append(f"items: {len(rows)} (proved {sum(y)}, failed {len(y) - sum(y)}); base rate {base:.2f}, "
               f"Brier of always-{base:.2f} {brier([base] * len(y), y):.3f}")
    rated = [r for r in rows if r.get("difficulty") in RANK]
    unrated = [r for r in rows if r.get("difficulty") not in RANK]
    judged = [r for r in rows if isinstance((r.get(key) or {}).get("p_success"), (int, float))]
    def line(label, sub, score):
        a = auc([score(r) for r in sub], [r["proved"] for r in sub])
        return f"  {label:48s} n={len(sub):3d}  AUC={'n/a' if a is None else f'{a:.3f}'}"
    out.append("AUC, the chance a random proved attack scores above a random failed one (0.5 = no signal):")
    out.append(line("plan's own rating (free), rated items", rated, lambda r: RANK[r["difficulty"]]))
    out.append(line("shorter statement (free), all items", rows, lambda r: -len(r["statement"])))
    if judged:
        out.append(line(f"{key}: p_success, all judged items", judged, lambda r: r[key]["p_success"]))
        jr = [r for r in judged if r.get("difficulty") in RANK]
        ju = [r for r in judged if r.get("difficulty") not in RANK]
        out.append(line(f"{key}: p_success, on the plan-rated items", jr, lambda r: r[key]["p_success"]))
        out.append(line(f"{key}: p_success, on items the plan did NOT rate", ju, lambda r: r[key]["p_success"]))
        out.append(f"  {key} Brier (calibration + discrimination): "
                   f"{brier([r[key]['p_success'] for r in judged], [r['proved'] for r in judged]):.3f}")
        agree = [r for r in jr if (r[key].get("difficulty") or "") == r["difficulty"]]
        out.append(f"  {key} difficulty agrees with the plan's on {len(agree)} of {len(jr)} rated items")
        cost = sum(float(r.get(key + "_cost") or 0) for r in judged)
        out.append(f"  {key} cost: ${cost:.3f} for {len(judged)} judgments (${cost / max(1, len(judged)):.4f} each)")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--model", default="claude-haiku-4-5-20251001")
    ap.add_argument("--budget", type=float, default=0.05, help="cap per judgment call")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--score-only", action="store_true")
    args = ap.parse_args()
    rows = [json.loads(l) for l in DATA.read_text().splitlines() if l.strip()]
    key = "judge_" + re.sub(r"\W", "_", args.model)
    if not args.score_only:
        todo = [r for r in rows if key not in r]
        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            outs = list(ex.map(lambda r: ask(args.model, r["statement"], args.budget), todo))
        for r, (ans, cost) in zip(todo, outs):
            r[key], r[key + "_cost"] = ans, cost
        DATA.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    print(report(rows, key))
    return 0


if __name__ == "__main__":
    sys.exit(main())
