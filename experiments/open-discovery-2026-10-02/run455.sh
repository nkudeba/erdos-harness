#!/bin/sh
# The full run on open problem #455 (pre-registered in experiments/open-discovery-2026-10-02/REPORT.md).
cd /Users/nicolas.kudeba/workspace/erdos-harness || exit 1
RD=runs/20261001-230105-000000-erdos455
python3 harness.py run --problem problems/erdos_455.json --resume $RD --mode research --allow-research --open \
  --discover on --discover-mode crossfed --discover-rounds 2 --discover-ladder 3 --discover-draws 3 --discover-total-budget 9 \
  --blueprint on --blueprint-reroute on --residual-view outline --rediscover 2 --blackboard on \
  --library experiments/open-discovery-2026-10-02/library/455-full \
  --run-budget 40 --research-cycles 6 --hyps-per-cycle 3 --lean-timeout 1800 \
  --backend claude-cli --model claude-opus-5-5 >> $RD/lane.log 2>&1
EX=$?
echo "EXIT $EX $(date -u +%FT%TZ)" >> $RD/lane.log
