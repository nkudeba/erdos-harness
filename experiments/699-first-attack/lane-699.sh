#!/bin/bash
# Erdos 699, first full-resolution attempt. ONE lane: do not start while another harness run is live.
# Codex's original invocation died instantly with `--problem 699`; --problem takes a PATH to the frozen
# problem file. CONTEXT.md goes in via --informal-context, which records it as operator-supplied
# assistance (sha256 + "operator_supplied_informal_context") rather than passing it off as the model's own.
# The bounded search stage is expected to be SKIPPED by search_futility: the Atlas now carries a published
# floor of 4.17e19 candidate triples (Cong, n <= 10^7), 4.2e10x the 1e9 bounded-search reach.
cd "$(dirname "$0")/../.."
python3 harness.py run --problem problems/erdos_699.json --open \
  --model claude-opus-5 \
  --informal-context experiments/699-first-attack/CONTEXT.md \
  --rounds 2 --samples 3 --decompose-rounds 3 \
  --reduce always --run-budget 12
EX=$?
echo "LANE-EXIT=$EX"
