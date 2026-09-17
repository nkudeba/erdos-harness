#!/bin/bash
# Erdos 699, second attempt: FULL RESOLUTION. ONE lane.
# Research mode + both directions. The agentic-round budget clamp (harness.py, prove-agentic) and the
# --open "split what is left" fix both landed before this run, so --run-budget is now a real cap:
# the previous attempt overshot $12 -> $18.61 because one round of 3 samples x $8 --call-budget was
# checked only after the fact, which then starved stage_brief.
cd "$(dirname "$0")/../.."
python3 harness.py run --problem problems/erdos_699.json --open \
  --model claude-opus-5 \
  --informal-context experiments/699-full-attempt/CONTEXT.md \
  --allow-research --research-cycles 2 \
  --reduce always \
  --rounds 3 --samples 3 --decompose-rounds 4 \
  --run-budget 35
EX=$?
echo "LANE-EXIT=$EX"
