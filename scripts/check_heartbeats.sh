#!/usr/bin/env bash
# check_heartbeats.sh — the no-increase invariant for per-declaration elaboration-budget escape hatches.
#
# Covers BOTH `set_option maxHeartbeats` and `set_option maxRecDepth`. A raised ceiling is (almost always)
# a masked `whnf` blowup, not a fix. This guard fails if the number of sites GROWS beyond the recorded
# baseline (scripts/heartbeats_baseline.txt), so a future dev must FOLD the blowup
# (docs/agents/proof-patterns.md §"maxHeartbeats: the fold recipe") instead of bumping a number.
# Genuinely term-intrinsic additions require a conscious baseline bump in the same PR — visible in
# review. Ratcheting DOWN is always fine.
#
# Why maxRecDepth is here: it was NOT tracked until 2026-08, and the omission turned out to be
# load-bearing. Several declarations had their heartbeat ceiling removed by a real fix while the
# recursion-depth bump sitting on the same declaration survived untouched — nothing ever forced the
# question. The two hatches co-locate, because both are usually the same `congr`-chain or unfolded-list
# blowup, so they now ratchet together.
#
# Upstream Clean, for calibration: ZERO maxHeartbeats in 44,603 lines, and 4 maxRecDepth sites — all in
# constant tables, capped at 2048, none in a proof.
#
# Mirrors scripts/check_no_native_decide.sh / check_no_skipkerneltc.sh: exits non-zero on violation.
# Run from the repo root. Never redirect stderr to /dev/null on Lean-adjacent commands (hook-enforced).
set -euo pipefail
cd "$(dirname "$0")/.."

baseline_file="scripts/heartbeats_baseline.txt"
if [ ! -f "$baseline_file" ]; then
  echo "FAIL: $baseline_file not found"; exit 1
fi

status=0

# check_one <baseline-key> <lean-option> <human-label> <lib-dir>
check_one() {
  local key="$1" opt="$2" label="$3" lib="$4"
  local base cur
  base=$(awk -v l="$key" '$1==l {print $2}' "$baseline_file")
  if [ -z "${base:-}" ]; then
    echo "FAIL: no baseline entry for '$key' in $baseline_file"; status=1; return
  fi
  cur=$(grep -rc "set_option $opt" "$lib/" | awk -F: '{s+=$2} END {print s+0}')
  if [ "$cur" -gt "$base" ]; then
    echo "FAIL: $label sites $cur > baseline $base (+$((cur-base)) new override(s))."
    echo "      Fold the blowup instead of bumping a ceiling — see docs/agents/proof-patterns.md"
    echo "      §\"maxHeartbeats: the fold recipe + no-bump discipline\", and perf-findings.md §12"
    echo "      (extract over OPAQUE arguments; check what the extraction can still see)."
    echo "      If genuinely term-intrinsic, bump '$key' in $baseline_file with a commit note."
    status=1
  elif [ "$cur" -lt "$base" ]; then
    echo "OK (ratchet down): $label $cur < baseline $base — please lower the baseline to $cur."
  else
    echo "OK: $label $cur = baseline $base."
  fi
}

for lib in SP1Clean SP1CleanTest; do
  check_one "$lib"          maxHeartbeats "$lib maxHeartbeats" "$lib"
  check_one "$lib-recdepth" maxRecDepth   "$lib maxRecDepth"   "$lib"
done

if [ "$status" -ne 0 ]; then
  echo "check_heartbeats: FAILED"
  exit 1
fi
echo "check_heartbeats: PASS"
