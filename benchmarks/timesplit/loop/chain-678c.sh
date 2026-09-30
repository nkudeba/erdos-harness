#!/bin/sh
# After the v4 lane, the third fresh #678 run with both fixes (pre-registered in RESULTS.md).
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
while pgrep -f "chain-v4.sh" >/dev/null || pgrep -f "tag train-v4-543fd9d" >/dev/null; do sleep 60; done
echo "CHAIN678C: v4 lane done $(date)"
python3 benchmarks/timesplit/timesplit.py run --split train --items 678 --candidate discover-v3 \
  --harness pin_f27eaff0efc862ad_harness.py --knowledge benchmarks/timesplit/pins/knowledge-f27eaff0efc862ad \
  --budget 16 --research-cycles 6 --tag train-678-both-f27eaff > benchmarks/timesplit/results/train-678-both-f27eaff.log 2>&1
echo "CHAIN678C: done $(date)"
