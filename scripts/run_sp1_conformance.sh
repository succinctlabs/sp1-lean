#!/usr/bin/env bash
# run_sp1_conformance.sh — the inverted conformance check, as a script.
#
# Runs the SP1-side witgen conformance check: SP1's real `MachineAir::generate_trace`
# over the deterministic batteries, checked against the vendored Lean-verified witness
# generators (inputs recovered through the symbolic row maps, hints from the real
# events, full-row cell-for-cell equality + every exported AIR constraint = 0, all 25
# chips).
#
# The check lives in the SP1 tree as a deliberately **standalone, opt-in** package
# (`crates/core/compiler/conformance-check` — its own cargo workspace, excluded from
# SP1's, so no `cargo build`/`cargo test --workspace` there ever builds or runs it).
# This script is its only driver for now; promoting the check into SP1 CI is a later
# hardening step, and this repo's CI deliberately runs no cargo either.
#
# Fences before running: `$SP1_DIR` must be a clean checkout of exactly
# `SP1_PINNED_COMMIT` (so a pass is a statement about the pin), and the vendored
# artifacts must be byte-identical to the committed `export/witgen/`
# (`vendor_witgen_artifacts.sh --check`).
#
# Usage: SP1_DIR=../sp1 scripts/run_sp1_conformance.sh   (from the repo root)
set -uo pipefail
cd "$(dirname "$0")/.."

SP1_DIR="${SP1_DIR:-../sp1}"
PIN=$(python3 -c "
import re
src = open('update_extracted.py').read()
print(re.search(r'SP1_PINNED_COMMIT = \"([0-9a-f]{40})\"', src).group(1))
")

ACTUAL=$(git -C "$SP1_DIR" rev-parse HEAD 2>/dev/null)
if [[ "$ACTUAL" != "$PIN" ]]; then
  echo "FAIL: $SP1_DIR is at ${ACTUAL:-<no git>}, expected pinned extraction commit $PIN" >&2
  exit 1
fi
DIRTY=$(git -C "$SP1_DIR" status --porcelain=v1 | grep -v '^??' || true)
if [[ -n "$DIRTY" ]]; then
  echo "FAIL: $SP1_DIR has uncommitted changes:" >&2
  echo "$DIRTY" >&2
  exit 1
fi

SP1_DIR="$SP1_DIR" scripts/vendor_witgen_artifacts.sh --check || exit 1

# Share the workspace target dir so the dependency tree is built once.
SP1_ABS=$(cd "$SP1_DIR" && pwd)
(cd "$SP1_ABS" && CARGO_TARGET_DIR="$SP1_ABS/target" cargo run --release --quiet \
    --manifest-path crates/core/compiler/conformance-check/Cargo.toml)
