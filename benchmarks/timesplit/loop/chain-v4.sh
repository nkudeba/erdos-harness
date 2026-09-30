#!/bin/sh
# After the #678 cheap-fallback rerun, run discover-v4 on #990 and #1037 (pre-registered in RESULTS.md).
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
while pgrep -f "tag train-678-fallback-543fd9d" >/dev/null; do sleep 60; done
echo "CHAINV4: #678 rerun done $(date)"
python3 benchmarks/timesplit/timesplit.py run --split train --items 990 1037 --candidate discover-v4 \
  --harness pin_543fd9de3521d2f3_harness.py --knowledge benchmarks/timesplit/pins/knowledge-543fd9de3521d2f3 \
  --budget 16 --research-cycles 6 --tag train-v4-543fd9d > benchmarks/timesplit/results/train-v4-543fd9d.log 2>&1
echo "CHAINV4: v4 done $(date)"
