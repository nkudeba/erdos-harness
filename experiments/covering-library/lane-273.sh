#!/bin/bash
# One lane, one run. Exit code captured on the very next line after the command (AGENTS.md).
# --model claude-opus-5: the CLI default (Fable) is over its usage limit on this account, and opus-5
# is also what the BASELINE run used, so this keeps the comparison controlled.
cd /Users/nicolas.kudeba/workspace/erdos-harness
python3 harness.py run --problem problems/erdos_273.json --open \
  --model claude-opus-5 \
  --resume runs/20260911-151747-638616-erdos273 \
  --rounds 2 --samples 3 --decompose-rounds 3 \
  --reduce always --run-budget 20
EX=$?
echo "LANE-EXIT=$EX"
