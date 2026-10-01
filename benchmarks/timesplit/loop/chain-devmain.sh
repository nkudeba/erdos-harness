#!/bin/sh
# Dev measurement of main (pre-registered in RESULTS.md, "Dev measurement of main"): the 5-item screen, then the
# other 12 pairable dev items only if the screen passes the README's gate (loop/gate_screen.py, aggregates only).
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
TAG=dev-main-a88fab5
PIN="--harness pin_a88fab528c17c999_harness.py --knowledge benchmarks/timesplit/pins/knowledge-a88fab528c17c999"
R=benchmarks/timesplit/results
echo "DEVMAIN: screen start $(date)"
python3 benchmarks/timesplit/timesplit.py run --split dev --items 150 202 204 392 401 $PIN \
  --budget 8 --research-cycles 2 --tag $TAG > $R/$TAG.log 2>&1
echo "DEVMAIN: screen done $(date)"
python3 benchmarks/timesplit/timesplit.py score --tag $TAG --baseline baseline-v2-84f21c5 > $R/$TAG.screen-score.txt 2>&1
if ! python3 benchmarks/timesplit/loop/gate_screen.py $R/$TAG.screen-score.txt baseline-v2-84f21c5; then
  echo "DEVMAIN: screen gate STOP, not extending $(date)"
  exit 0
fi
echo "DEVMAIN: extension start $(date)"
python3 benchmarks/timesplit/timesplit.py run --split dev --items 419 457 570 618 729 825 865 871 888 1125 1180 1213 $PIN \
  --budget 8 --research-cycles 2 --tag $TAG >> $R/$TAG.log 2>&1
echo "DEVMAIN: done $(date)"
