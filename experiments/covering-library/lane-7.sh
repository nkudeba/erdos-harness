#!/bin/bash
# Second run in the cluster. IDENTICAL flags to the #273 library run — no thumb on the scale.
cd /Users/nicolas.kudeba/workspace/erdos-harness
python3 harness.py run --problem problems/erdos_7.json --open \
  --model claude-opus-5-5 \
  --rounds 2 --samples 3 --decompose-rounds 3 \
  --reduce always --run-budget 20
EX=$?
echo "LANE-EXIT=$EX"
