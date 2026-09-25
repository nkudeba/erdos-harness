#!/bin/sh
# Loop iteration 2, mechanical tail: finish the conversion lane, rerun #435 in place, then launch the pre-registered
# dev screen of the fixed harness if the budget allows. Each step logs to results/<tag>.log.
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
while pgrep -f "tag train-fixes-conv" >/dev/null; do sleep 60; done
echo "CHAIN: conversion lane done $(date)"
python3 benchmarks/timesplit/timesplit.py rerun --tag train-fixes-conv --items 435 >> benchmarks/timesplit/results/train-fixes-conv.log 2>&1
python3 benchmarks/timesplit/loop.py finish --name train-fixes-conv
echo "CHAIN: #435 rerun done $(date)"
if python3 benchmarks/timesplit/loop.py can-spend --usd 42; then
  python3 benchmarks/timesplit/loop.py register --kind run --name dev-fixes-ea6d987 --estimate 42 --note "iteration 2 dev screen" >/dev/null
  echo "CHAIN: dev screen launched $(date)"
  python3 benchmarks/timesplit/timesplit.py run --split dev --items 150 202 204 392 401 \
    --harness pin_ea6d9878462aac38_harness.py --knowledge benchmarks/timesplit/pins/knowledge-ea6d9878462aac38 \
    --budget 8 --research-cycles 6 --allow-concurrent --tag dev-fixes-ea6d987 > benchmarks/timesplit/results/dev-fixes-ea6d987.log 2>&1
  python3 benchmarks/timesplit/loop.py finish --name dev-fixes-ea6d987
  echo "CHAIN: dev screen done $(date)"
else
  echo "CHAIN: budget refused the dev screen"
fi
