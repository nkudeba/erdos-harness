#!/usr/bin/env python3
"""Run either implementation with the same Codex provider for controlled comparisons.

This adapter leaves harness_baseline.py unchanged. It runs text-only search in both
implementations, so tool-enabled agent sessions do not confound the comparison.
"""
import argparse
import importlib
import json
import hashlib
from pathlib import Path
import sys
import harness


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--engine', choices=['baseline', 'current'], required=True)
    parser.add_argument('--problem', required=True)
    parser.add_argument('--resume')
    parser.add_argument('--model', default=None)
    parser.add_argument('--llm-timeout', type=int, default=900)
    parser.add_argument('--lean-timeout', type=int, default=420)
    parser.add_argument('--rounds', type=int, default=2)
    parser.add_argument('--samples', type=int, default=1)
    parser.add_argument('--decompose-rounds', type=int, default=2)
    args = parser.parse_args()
    engine = importlib.import_module('harness_baseline') if args.engine == 'baseline' else harness
    # Constructor compatibility with both the old and new Claude backend call sites.
    engine.ClaudeCliBackend = lambda model, timeout, *rest: harness.CodexCliBackend(model, timeout)
    sys.argv = [engine.__file__, 'run', '--problem', args.problem,
                '--backend', 'claude-cli', '--rounds', str(args.rounds),
                '--samples', str(args.samples), '--decompose-rounds', str(args.decompose_rounds),
                '--llm-timeout', str(args.llm_timeout), '--lean-timeout', str(args.lean_timeout)]
    if args.model:
        sys.argv += ['--model', args.model]
    if args.engine == 'current':
        sys.argv += ['--agentic', 'off']
    if args.resume:
        sys.argv += ['--resume', args.resume]
    if args.resume:
        run = Path(args.resume)
        run.mkdir(parents=True, exist_ok=True)
        # Isolate the legacy global `runs/current` pointer in concurrent comparisons.
        # This changes bookkeeping only, not baseline proof-search behavior.
        engine.RUNS = run / 'housekeeping'
        engine.RUNS.mkdir(exist_ok=True)
        (run / 'comparison.json').write_text(json.dumps({
            'engine': args.engine, 'provider': 'codex-cli', 'model': args.model,
            'reasoning': 'high', 'rounds': args.rounds, 'samples': args.samples,
            'decompose_rounds': args.decompose_rounds, 'llm_timeout': args.llm_timeout,
            'lean_timeout': args.lean_timeout, 'agentic': False,
            'engine_sha256': hashlib.sha256(Path(engine.__file__).read_bytes()).hexdigest(),
        }, indent=2))
    return engine.main()


if __name__ == '__main__':
    raise SystemExit(main())
