#!/bin/sh
# Verification tools for audit.py (2026-10-07): leanprover/comparator, leanprover/lean4export (matching our Lean,
# v4.32.0-rc1), the comparator repo's fake-landrun shim (macOS has no Landlock sandbox), and nanoda (independent kernel).
set -e
T=/Users/nicolas.kudeba/workspace/erdos-harness/tools
cd "$T"
echo "== comparator $(date -u +%FT%TZ)"
[ -d comparator ] || git clone --depth 1 https://github.com/leanprover/comparator.git comparator
(cd comparator && lake build)
echo "== lean4export v4.32.0-rc1 $(date -u +%FT%TZ)"
[ -d lean4export ] || git clone --depth 1 --branch v4.32.0-rc1 https://github.com/leanprover/lean4export.git lean4export
(cd lean4export && lake build)
cp comparator/scripts/fake-landrun.sh landrun && chmod +x landrun
echo "== rust $(date -u +%FT%TZ)"
[ -x "$HOME/.cargo/bin/cargo" ] || curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --no-modify-path
echo "== nanoda $(date -u +%FT%TZ)"
[ -d nanoda_lib ] || git clone --depth 1 https://github.com/ammkrn/nanoda_lib.git nanoda_lib
(cd nanoda_lib && "$HOME/.cargo/bin/cargo" build --release)
echo "== done $(date -u +%FT%TZ)"
ls -la comparator/.lake/build/bin lean4export/.lake/build/bin nanoda_lib/target/release 2>&1 | grep -E "comparator|lean4export|nanoda_bin"
