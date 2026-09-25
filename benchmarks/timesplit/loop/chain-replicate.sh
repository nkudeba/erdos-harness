#!/bin/sh
# Stopping condition 1 (docs/improvement-loop.md): dev #1213 was solved by the operator's discover-v2 lane. When the
# in-flight alloc train screen is done, replicate the solve on a fresh alias with the solving lane's exact settings,
# then run baseline v2 on #1213, which the paused baseline never reached. Both are pre-registered in RESULTS.md
# ("Stop signal: dev #1213").
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
while pgrep -f "tag train-alloc-00e9304" >/dev/null || pgrep -f "chain-iter3.sh" >/dev/null; do sleep 60; done
echo "CHAINR: alloc train screen done $(date)"
PIN="--harness pin_84f21c561c540e02_harness.py --knowledge benchmarks/timesplit/pins/knowledge-8b5a5b08da0eb6f4"
if python3 benchmarks/timesplit/loop.py can-spend --usd 8; then
  python3 benchmarks/timesplit/loop.py register --kind run --name replicate-1213-84f21c5 --estimate 8 \
    --note "replication of the #1213 solve (stopping condition 1)" >/dev/null
  echo "CHAINR: replication launched $(date)"
  python3 benchmarks/timesplit/timesplit.py run --split dev --items 1213 $PIN --budget 8 --research-cycles 6 \
    --candidate discover-v2 --discover-attempts 2 --discover-budget 0.8 --discover-effort medium \
    --gap-budget 1.2 --gap-effort medium --allow-concurrent --tag replicate-1213-84f21c5 \
    > benchmarks/timesplit/results/replicate-1213-84f21c5.log 2>&1
  python3 benchmarks/timesplit/loop.py finish --name replicate-1213-84f21c5
  echo "CHAINR: replication done $(date)"
else
  echo "CHAINR: budget refused the replication"
  exit 0
fi
if python3 benchmarks/timesplit/loop.py can-spend --usd 8; then
  python3 benchmarks/timesplit/loop.py register --kind run --name baseline-v2-84f21c5-1213 --estimate 8 \
    --note "baseline v2 on #1213, the v2 verdict's missing pair" >/dev/null
  echo "CHAINR: baseline on #1213 launched $(date)"
  python3 benchmarks/timesplit/timesplit.py run --split dev --items 1213 $PIN --budget 8 --allow-concurrent \
    --tag baseline-v2-84f21c5-1213 > benchmarks/timesplit/results/baseline-v2-84f21c5-1213.log 2>&1
  python3 benchmarks/timesplit/loop.py finish --name baseline-v2-84f21c5-1213
  echo "CHAINR: baseline on #1213 done $(date)"
else
  echo "CHAINR: budget refused the baseline on #1213"
fi
