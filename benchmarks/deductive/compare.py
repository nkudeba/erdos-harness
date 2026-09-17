#!/usr/bin/env python3
"""Route similarity between a benchmark's produced proof and the saved reference proof.

    python3 benchmarks/deductive/compare.py --run runs/<ts>-bench-erdosNNNNN --reference knowledge/solved/Erdos275.lean

Prints Jaccard overlaps of four token bags — declaration names, numerals, dotted Mathlib identifiers and
tactic keywords — plus the distinctive identifiers the two proofs share. It is a heuristic reading aid for
the question "did the loop take the known route?"; it cannot tell recall from rediscovery, and a high overlap
on Mathlib identifiers is expected whenever two proofs use the same standard machinery.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMMON = {"Finset.sum_congr", "Finset.mem_univ", "Nat.cast_add", "Nat.cast_one", "Finset.sum_insert", "Nat.succ_le_iff"}
TACTICS = ("omega", "simp", "ring", "linarith", "nlinarith", "decide", "norm_num", "induction", "cases", "rcases",
           "obtain", "refine", "exact", "intro", "apply", "rw", "calc", "linear_combination", "by_contra", "use",
           "constructor", "field_simp", "positivity", "aesop", "simpa", "subst", "specialize", "have")


def bags(src: str) -> dict:
    body = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    body = re.sub(r"--[^\n]*", " ", body)
    names = set(re.findall(r"(?m)^\s*(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?]*)", body))
    haves = set(re.findall(r"\bhave\s+([A-Za-z_][A-Za-z0-9_'!?]*)\s*[:(]", body))
    numerals = set(n for n in re.findall(r"(?<![A-Za-z_.'])(\d+)(?![A-Za-z_'])", body) if int(n) >= 2)
    idents = set(t for t in re.findall(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_'!?]+)+)\b", body)) - COMMON
    tactics = set(t for t in TACTICS if re.search(rf"\b{t}\b", body))
    return {"declarations": names | haves, "numerals": numerals, "identifiers": idents, "tactics": tactics}


def jaccard(a: set, b: set) -> float:
    return len(a & b) / len(a | b) if (a | b) else 0.0


def proof_of_run(run: Path) -> str:
    st = json.loads((run / "state.json").read_text())
    if st.get("proof"):
        return st["proof"]
    res = ROOT / "programs" / f"erdos_{st.get('problem_input', {}).get('id')}" / "Residual.lean"
    return res.read_text() if res.exists() else ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", help="benchmark run directory (its state.json proof, else the program's Residual.lean)")
    ap.add_argument("--proof", help="a .lean file instead of --run")
    ap.add_argument("--reference", required=True, help="the saved reference proof, e.g. knowledge/solved/Erdos275.lean")
    args = ap.parse_args()
    produced = Path(args.proof).read_text() if args.proof else proof_of_run(Path(args.run))
    if not produced.strip():
        print("no produced proof found"); return 2
    a, b = bags(produced), bags(Path(args.reference).read_text())
    print(f"{'bag':14s} {'jaccard':>8s}  shared")
    for k in ("declarations", "numerals", "identifiers", "tactics"):
        shared = sorted(a[k] & b[k])
        print(f"{k:14s} {jaccard(a[k], b[k]):8.2f}  {', '.join(shared)[:150]}")
    distinctive = sorted(x for x in (a["identifiers"] & b["identifiers"]) if x.count(".") >= 1)
    print("\nshared distinctive identifiers:", ", ".join(distinctive) or "(none)")
    print("produced-only identifiers:", ", ".join(sorted(a["identifiers"] - b["identifiers"]))[:300] or "(none)")
    print("reference-only identifiers:", ", ".join(sorted(b["identifiers"] - a["identifiers"]))[:300] or "(none)")
    print("\nReading: high identifier overlap with the SAME distinctive machinery (e.g. roots of unity for a covering "
          "problem) means the known route was taken; whether it was recalled or rediscovered is not decidable here — "
          "read the recall probe.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
