#!/bin/sh
# Loop iteration 3, mechanical start: when the dev screen of the fixed harness is done, launch the pre-registered
# alloc train screen on the iteration-2 items, on pin 00e9304, if the budget allows.
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
while pgrep -f "tag dev-fixes-ea6d987" >/dev/null || pgrep -f "chain-iter2.sh" >/dev/null; do sleep 60; done
echo "CHAIN3: dev screen done $(date)"
if python3 benchmarks/timesplit/loop.py can-spend --usd 36; then
  python3 benchmarks/timesplit/loop.py register --kind run --name train-alloc-00e9304 --estimate 36 --note "iteration 3 train screen" >/dev/null
  echo "CHAIN3: alloc train screen launched $(date)"
  python3 benchmarks/timesplit/timesplit.py run --split train --items 283 435 997 1141 --candidate alloc \
    --discover-attempts 2 --discover-effort medium --discover-budget 0.8 --critic-budget 0.3 \
    --harness pin_00e9304755a20291_harness.py --knowledge benchmarks/timesplit/pins/knowledge-00e9304755a20291 \
    --budget 8 --research-cycles 6 --allow-concurrent --tag train-alloc-00e9304 > benchmarks/timesplit/results/train-alloc-00e9304.log 2>&1
  python3 benchmarks/timesplit/loop.py finish --name train-alloc-00e9304
  echo "CHAIN3: alloc train screen done $(date)"
else
  echo "CHAIN3: budget refused the alloc train screen"
fi
