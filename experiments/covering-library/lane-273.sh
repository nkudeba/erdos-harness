#!/bin/bash
# One lane, one run. Exit code captured on the very next line after the command (AGENTS.md).
# --model claude-opus-5-5: the CLI default (Fable) is over its usage limit on this account. The BASELINE
# run used claude-opus-5 (retired 2026-09-23), so a rerun against it is a model switch; say so in the report.
cd /Users/nicolas.kudeba/workspace/erdos-harness
python3 harness.py run --problem problems/erdos_273.json --open \
  --model claude-opus-5-5 \
  --resume runs/20260911-151747-638616-erdos273 \
  --rounds 2 --samples 3 --decompose-rounds 3 \
  --reduce always --run-budget 20
EX=$?
echo "LANE-EXIT=$EX"
