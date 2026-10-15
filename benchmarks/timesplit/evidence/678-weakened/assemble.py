#!/usr/bin/env python3
"""Audit train #678's residuals after the premise-weakening replays (2026-10-15). Evaluation only: nothing the harness
runs may read this directory.

    python3 benchmarks/timesplit/evidence/678-weakened/assemble.py --data-root <main checkout> [--lean-project <formal>]

- 55963: the replay's own final residual. Ramanujan's premise was replaced by `hyp_bertrand_gap`, which the replay
  certified, and nothing is left open.
- 81727: the replay's final residual (Nagura replaced by `hyp_halfprime`, certified) with Nair spliced in from the
  2026-09-30 premise replay (`runs/replay-premises-678c/81727-erdos_81727_hyp_nair`). That splice is operator assembly.

Each is compiled under its run's header and put through `audit.lean_checks`. Writes `<alias>_proof.lean` and
`<alias>-checks.json` beside this script. Neither is an autonomous solve; see README.md."""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT))
import harness as H
import audit as AU

RUNS = {
    "55963": ("runs/20260930-162114-886885-timesplit-erdos55963", "erdos_55963_hyp_ramanujan", None),
    "81727": ("runs/20260930-194040-857690-timesplit-erdos81727", "erdos_81727_hyp_nagura",
              ("erdos_81727_hyp_nair", "runs/replay-premises-678c/81727-erdos_81727_hyp_nair/sweep/state.json")),
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--data-root", required=True)
    ap.add_argument("--lean-project", default=None)
    ap.add_argument("--replays", default="runs/replay-weaken-20261014")
    a = ap.parse_args()
    data = Path(a.data_root).resolve()
    if a.lean_project:
        proj = Path(a.lean_project).resolve()
        H.FORMAL, H.MATHLIB_SRC = proj, proj / ".lake" / "packages" / "mathlib" / "Mathlib"
        AU.FORMAL, AU.AUDIT_DIR = proj, proj / ".lake" / "audit"
    ok_all = True
    for alias, (run, premise, splice) in RUNS.items():
        state = json.loads((data / run / "state.json").read_text())
        parent = data / a.replays / f"{alias}-{premise}" / "parent"
        skel = (parent / "program" / "Residual.lean").read_text()
        # modules the replay auto-imported for the weakened premise's proof live in its state, not in the skeleton text
        extra = list(state.get("auto_imports") or []) + list(json.loads((parent / "state.json").read_text()).get("auto_imports") or [])
        if splice:
            name, proof_state = splice
            pst = json.loads((data / proof_state).read_text())
            skel = H.splice_hypothesis(skel, name, H.strip_imports(pst["proof"]))
            extra += list(pst.get("auto_imports") or [])
        imports = list(dict.fromkeys(list(H.DEFAULT_IMPORTS) + extra))
        src = H.compose(skel, imports)
        (HERE / f"{alias}_proof.lean").write_text(src)
        checks = AU.lean_checks(src, state["statement"], imports, f"678-weakened-{alias}")
        passed = H.audit_passes(checks)
        ok_all = ok_all and passed
        (HERE / f"{alias}-checks.json").write_text(json.dumps({"alias": alias, "holes": H.hole_count(skel),
                                                               "passes": passed, "checks": checks}, indent=1))
        print(alias, "PASS" if passed else "FAIL", {k: v.get("ok") for k, v in checks.items()})
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
