#!/bin/sh
# Run C then Screen D (pre-registered in RESULTS.md, "Navier-Stokes lessons, built and screened"), one lane, in sequence.
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
PIN="--harness pin_710dfc814b1887af_harness.py --knowledge benchmarks/timesplit/pins/knowledge-710dfc814b1887af"
R=benchmarks/timesplit/results
echo "NSLEAN: run C start $(date)"
python3 benchmarks/timesplit/timesplit.py run --split train --items 435 678 $PIN --candidate blueprint \
  --budget 16 --research-cycles 6 --tag train-blueprint-710dfc8 --allow-concurrent > $R/train-blueprint-710dfc8.log 2>&1
echo "NSLEAN: run C done $(date)"
python3 benchmarks/timesplit/timesplit.py run --split train --items 152 259 1179 1141 $PIN --candidate crossfed-blueprint \
  --budget 16 --research-cycles 6 --tag train-crossfed-blueprint-710dfc8 --allow-concurrent > $R/train-crossfed-blueprint-710dfc8.log 2>&1
echo "NSLEAN: screen D done $(date)"
