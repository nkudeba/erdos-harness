"""Replay the novelty panel on #1179's r1s3/C1 ((3/2+δ)·log2 N, weaker than Erdős–Hall 1976), current prompt vs a
'strongest known result first' variant. Masked, as the run was. Writes one JSON line per call."""
import json, sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT = Path("/Users/nicolas.kudeba/workspace/erdos-harness")
sys.path.insert(0, str(ROOT))
import harness as H
R = ROOT / "runs" / "20261003-083314-684014-hardstep-erdos799065"
ej = json.loads((R / "engine" / "engine.json").read_text())
prob = json.loads((R / "problem.json").read_text())
c = next(x for x in ej["ledger"] if x.get("session") == "r1s3" and x.get("id") == "C1")
known = H.clip_middle(H.frontier_block(ej["frontier"]), 16000)
claim = H._claim_text(c)
base = H.NOVELTY_PROMPT.format(statement=prob["statement"], known=known, claim=claim)
marker = "Then rate SIGNIFICANCE"
assert marker in base
variant = base.replace(marker, "Before you decide, write down the STRONGEST result you know on the same question, published or "
                       "folklore, whether or not the list above has it: the quantity, the best bound or strongest statement, "
                       "and its source. A claim weaker than a known result is KNOWN, however new its proof.\n" + marker)
be = H.MaskedBackend(H.ClaudeCliBackend(model="claude-opus-5-5", timeout=1800, call_budget_usd=1.0))
def one(job):
    tag, prompt = job
    try:
        t = be.complete("engine-novelty", prompt, effort_override="high", budget_override=0.6)
        j = H.json_tail_any(t) or {}
    except Exception as e:  # noqa
        t, j = "", {"error": str(e)[:200]}
    return {"prompt": tag, "verdict": j.get("verdict"), "significance": j.get("significance"), "cite": j.get("cite"),
            "why": str(j.get("why") or "")[:300], "mentions_erdos_hall": ("Hall" in (t or "")), "error": j.get("error")}
jobs = [("current", base), ("current", base), ("strongest-first", variant), ("strongest-first", variant)]
with ThreadPoolExecutor(max_workers=4) as ex:
    for r in ex.map(one, jobs):
        print(json.dumps(r, ensure_ascii=False), flush=True)
