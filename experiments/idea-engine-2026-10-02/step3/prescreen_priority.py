"""After a prescreen sweep, put its ranking where the running campaign loop will see it. No model calls.

The loop running since 2026-10-08 14:03 EDT predates `resolution.queue`'s prescreen ordering (1312895). It does re-read
`resolution/config.json` every iteration, and it screens the configured `priority` list first. So the sweep's ranking
goes there: every swept problem at or above `--min` (default 0.1), highest first, or the top `--top` (default 20) if
none reaches it. A restarted loop orders the rest of the queue by the prescreen itself. Every problem still gets the
screen proper before any scout; this only changes the order.

    python3 experiments/idea-engine-2026-10-02/step3/prescreen_priority.py [--wait-pid PID] [--dry-run]
"""
import argparse, json, os, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "atlas-data"))
from atomic import atomic_write_json, locked        # noqa: E402

CONFIG = ROOT / "resolution" / "config.json"
PRESCREEN = ROOT / "resolution" / "prescreen.jsonl"


def ranking(rows: list[dict], floor: float, top: int) -> list[int]:
    best: dict[int, float] = {}
    for r in rows:
        if isinstance(r.get("mean"), (int, float)):
            best[int(r["problem"])] = float(r["mean"])
    order = sorted(best, key=lambda n: (-best[n], n))
    above = [n for n in order if best[n] >= floor]
    return above or order[:top]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--wait-pid", type=int, help="wait for this process (the sweep's continuation) to exit first")
    ap.add_argument("--min", type=float, default=0.1)
    ap.add_argument("--top", type=int, default=20)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    if a.wait_pid:
        while True:
            try:
                os.kill(a.wait_pid, 0)
            except ProcessLookupError:
                break
            time.sleep(30)
    rows = [json.loads(l) for l in PRESCREEN.read_text().splitlines() if l.strip()] if PRESCREEN.exists() else []
    order = ranking(rows, a.min, a.top)
    if not order:
        print("no prescreen rows; config unchanged")
        return 0
    print(f"priority ({len(order)}): {order[:30]}")
    if not a.dry_run:
        with locked(CONFIG):
            cfg = json.loads(CONFIG.read_text()) if CONFIG.exists() else {}
            cfg.update({"priority": order, "priority_source": f"prescreen sweep, {len(rows)} problems, mean >= {a.min} "
                                                              f"(REPORT 3.10; step3/prescreen_priority.py)"})
            atomic_write_json(CONFIG, cfg, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
