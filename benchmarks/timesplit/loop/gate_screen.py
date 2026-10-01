#!/usr/bin/env python3
"""The README's screen-first gate, read from `timesplit.py score --tag T --baseline B` output (aggregates only, no
dev transcript): extend only if the screen lost no solve, produced no contradiction, and has W >= L on the dense
rule. Usage: gate_screen.py <score output file> <baseline tag>. Exit 0 = extend, 1 = stop."""
import json, sys

text, baseline = open(sys.argv[1]).read(), sys.argv[2]
objs, dec, i = [], json.JSONDecoder(), 0
while (i := text.find("{", i)) != -1:
    try:
        obj, i = dec.raw_decode(text, i)
        objs.append(obj)
    except ValueError:
        i += 1
arm = next((o for o in objs if "items" in o and "solved" in o), None)
pair = next((o for o in objs if "paired_items" in o), None)
if not (arm and pair):
    print("GATE: could not read the score output -> STOP")
    sys.exit(1)
lost = pair.get(f"solved_only_by_{baseline}", [])
wins, losses = len(pair["dense"]["wins"]), len(pair["dense"]["losses"])
ok = not lost and not arm.get("contradictions") and wins >= losses
print(f"GATE: pairs={pair['dense']['pairs']} wins={wins} losses={losses} ties={pair['dense']['ties']} "
      f"lost_solves={lost} contradictions={arm.get('contradictions')} -> {'EXTEND' if ok else 'STOP'}")
sys.exit(0 if ok else 1)
