"""Screen two cascade defects on the harness's own saved cascade passes, outside time-split dev/test. Lean only.

Each `attempts/cascade.lean` is the last pass of `_close_holes_without_model` in that directory: an attempt with every
`sorry` hole replaced by the harness's cascade. Four compiles per pass:
  S   every hole back to `sorry`        -> which hole lines are clean to begin with, and whether the attempt compiles
  H   the pass exactly as saved         -> the lines the harness would have called closed (its own line attribution)
  H'  `(HARN) <;> done`                 -> what the harness's cascade REALLY closes: a leftover goal now errs on its line
  G'  `(GUARD) <;> done`                -> what the guarded cascade closes
The harness keeps its line-closed holes only if the file then compiles, else it reverts the whole pass. So a pass
with a falsely closed hole (in H, not in H') realised nothing, whatever it closed genuinely."""
import json, re, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path("/Users/nicolas.kudeba/workspace/erdos-harness")
sys.path.insert(0, str(ROOT))
import harness as H

HARN = "first | omega | (simp_all) | positivity | (norm_num) | (nlinarith) | (decide +kernel) | (aesop)"
GUARD = "first | omega | (simp_all; done) | positivity | (norm_num; done) | nlinarith | (decide +kernel) | (aesop; done)"

pool = {i["problem"]: i["split"] for i in json.load(open(ROOT / "benchmarks/timesplit/pool.json"))["items"]}
bad = set()
for f in (ROOT / "benchmarks/timesplit/results").glob("*.aliases.jsonl"):
    for l in f.read_text().splitlines():
        if l.strip():
            a = json.loads(l)
            if pool.get(a["problem"]) != "train":
                bad.add(str(a["alias"]))
files = sorted(p for p in list((ROOT / "runs").rglob("cascade.lean")) + list((ROOT / "programs").rglob("cascade.lean"))
               if not any(f"erdos{a}" in str(p) or f"erdos_{a}" in str(p) for a in bad) and HARN in p.read_text())
checker = H.LeanChecker(H.FORMAL, 1200)
out_dir = ROOT / "runs" / "adhoc" / "cascade-holes"
out_path = Path(__file__).with_name("cascade_replay.jsonl")
done = {json.loads(l)["file"] for l in out_path.read_text().splitlines() if l.strip()} if out_path.exists() else set()


def error_lines(src: str, dest: str):
    res = checker.check(src, out_dir / dest)
    if res.get("timeout"):
        return None, False
    return {int(m.group(1)) for e in res.get("errors", []) for m in [re.match(r"line (\d+):", str(e))] if m}, bool(res.get("ok"))


def one(k_path):
    k, path = k_path
    rel = str(path.relative_to(ROOT))
    if rel in done:
        return None
    src = path.read_text()
    holes = [n for n, line in enumerate(src.splitlines(), 1) if HARN in line]
    s_err, s_ok = error_lines(src.replace(HARN, "sorry"), f"{k:03d}-S.lean")
    h_err, _ = error_lines(src, f"{k:03d}-H.lean")
    hp_err, _ = error_lines(src.replace(HARN, f"({HARN}) <;> done"), f"{k:03d}-Hp.lean")
    gp_err, _ = error_lines(src.replace(HARN, f"({GUARD}) <;> done"), f"{k:03d}-Gp.lean")
    if None in (s_err, h_err, hp_err, gp_err):
        row = {"file": rel, "holes": len(holes), "timeout": True}
    else:
        eligible = [n for n in holes if n not in s_err]
        h_line = {n for n in eligible if n not in h_err}
        h_true = {n for n in eligible if n not in hp_err}
        g_true = {n for n in eligible if n not in gp_err}
        false_closed = sorted(h_line - h_true)
        realised = sorted(h_line) if (s_ok and not false_closed) else []
        row = {"file": rel, "holes": len(holes), "attempt_compiles": s_ok, "eligible": len(eligible),
               "harness_line_closed": len(h_line), "harness_true": len(h_true), "guarded_true": len(g_true),
               "false_closed": false_closed, "harness_realised": len(realised),
               "lost_to_revert": len(h_true) if (false_closed and s_ok) else 0,
               "guarded_only": sorted(g_true - h_true), "harness_only": sorted(h_true - g_true)}
    with out_path.open("a") as fh:
        fh.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
    return row


with ThreadPoolExecutor(max_workers=2) as ex:
    list(ex.map(one, enumerate(files)))
print("HOLES-DONE", flush=True)
