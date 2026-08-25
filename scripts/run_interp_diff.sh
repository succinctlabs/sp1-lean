#!/usr/bin/env bash
# run_interp_diff.sh — the Lean ↔ Rust witness-generation differential.
#
# Runs the Rust reference interpreter (`rust/witgen-interp`) over the committed
# `export/` artifacts: every fixture row under `export/testdata/` must reproduce its
# `expectedWitness` cells exactly (the Lean reference evaluation over the shared
# operation list). All 25 chips carry SP1-anchored event rows (inputs recovered from
# SP1's real `generate_trace` rows by the generation-time gate): on those the
# interpreter additionally reconstructs the full Rust row through the row map,
# matches it verbatim, and checks every extracted AIR constraint evaluates to zero.
#
# Cargo is deliberately NOT part of the Lean CI (see rust/README.md); run this
# manually after touching the exporter, the fixtures, or the interpreter.
#
# Modes:
#   default   run the differential against the committed export/ tree.
#   --regen   first re-verify the committed tree is byte-identical to a fresh export
#             (`check_witgen_export.sh --regen`; needs `lake build SP1CleanTest`),
#             then run the differential. Extra args after the flags pass through to
#             the interpreter (e.g. `--chip Add --verbose`).
#
# Usage: scripts/run_interp_diff.sh [--regen] [-- interpreter args]
set -uo pipefail
cd "$(dirname "$0")/.."

if [[ "${1:-}" == "--regen" ]]; then
  shift
  scripts/check_witgen_export.sh --regen || exit 1
fi

exec cargo run --quiet --release --manifest-path rust/witgen-interp/Cargo.toml -- \
  check --export-dir export "$@"
