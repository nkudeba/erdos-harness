#!/bin/sh
# Baseline replicate (pre-registered in RESULTS.md, "Baseline replicate"): baseline-v2-84f21c5's own pin and protocol
# on the 5 dev screen items; then every arm re-measured with the same progress code, and the two comparisons.
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
TAG=baseline-v2-84f21c5-rep1
ITEMS="150 202 204 392 401"
R=benchmarks/timesplit/results
echo "BASEREP: start $(date)"
python3 benchmarks/timesplit/timesplit.py run --split dev --items $ITEMS \
  --harness pin_84f21c561c540e02_harness.py --knowledge benchmarks/timesplit/pins/knowledge-8b5a5b08da0eb6f4 \
  --budget 8 --research-cycles 2 --tag $TAG --allow-concurrent > $R/$TAG.log 2>&1
echo "BASEREP: runs done $(date)"
for T in baseline-v2-84f21c5 dev-main-a88fab5; do
  python3 benchmarks/timesplit/timesplit.py progress --tag $T --items $ITEMS --redo >> $R/$TAG.remeasure.log 2>&1
done
echo "BASEREP: re-measured $(date)"
python3 benchmarks/timesplit/timesplit.py score --tag $TAG --baseline baseline-v2-84f21c5 > $R/$TAG.vs-original.txt 2>&1
python3 benchmarks/timesplit/timesplit.py score --tag dev-main-a88fab5 --baseline $TAG > $R/$TAG.main-vs-rep.txt 2>&1
echo "BASEREP: scored $(date)"
