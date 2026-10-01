#!/bin/sh
# Replaces chain-devmain.sh, stopped on 2026-10-01 while its first item (#150) was running. The runner's per-item lane
# guard (timesplit.py `run`) would have refused the screen's next item while another session's light, Lean-free
# discovery lane is live. So the screen and its extension now run with --allow-concurrent. Same tag, protocol and
# gate; items already recorded under the tag are skipped.
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
TAG=dev-main-a88fab5
PIN="--harness pin_a88fab528c17c999_harness.py --knowledge benchmarks/timesplit/pins/knowledge-a88fab528c17c999"
R=benchmarks/timesplit/results
OLD=42088   # the first runner, which records #150 and then stops at the lane guard
while kill -0 $OLD 2>/dev/null; do sleep 60; done
echo "DEVMAIN: first runner done $(date)"
python3 benchmarks/timesplit/timesplit.py run --split dev --items 150 202 204 392 401 $PIN \
  --budget 8 --research-cycles 2 --tag $TAG --allow-concurrent >> $R/$TAG.log 2>&1
echo "DEVMAIN: screen done $(date)"
python3 benchmarks/timesplit/timesplit.py score --tag $TAG --baseline baseline-v2-84f21c5 > $R/$TAG.screen-score.txt 2>&1
if ! python3 benchmarks/timesplit/loop/gate_screen.py $R/$TAG.screen-score.txt baseline-v2-84f21c5; then
  echo "DEVMAIN: screen gate STOP, not extending $(date)"
  exit 0
fi
echo "DEVMAIN: extension start $(date)"
python3 benchmarks/timesplit/timesplit.py run --split dev --items 419 457 570 618 729 825 865 871 888 1125 1180 1213 $PIN \
  --budget 8 --research-cycles 2 --tag $TAG --allow-concurrent >> $R/$TAG.log 2>&1
echo "DEVMAIN: done $(date)"
