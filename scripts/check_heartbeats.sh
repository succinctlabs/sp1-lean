#!/usr/bin/env bash
# check_heartbeats.sh — the no-increase invariant for `set_option maxHeartbeats` overrides.
#
# A raised ceiling is (almost always) a masked `whnf` blowup, not a fix. This guard fails if the number
# of `set_option maxHeartbeats` sites GROWS beyond the recorded baseline (scripts/heartbeats_baseline.txt),
# so a future dev must FOLD the blowup (docs/agents/proof-patterns.md §"maxHeartbeats: the fold recipe")
# instead of bumping a number. Genuinely term-intrinsic additions (the DivRem/Mul/Shift/Sail/Word KEEP-set)
# require a conscious baseline bump in the same PR — visible in review. Ratcheting DOWN is always fine.
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
for lib in SP1Clean SP1CleanTest; do
  base=$(awk -v l="$lib" '$1==l {print $2}' "$baseline_file")
  if [ -z "${base:-}" ]; then
    echo "FAIL: no baseline entry for $lib in $baseline_file"; status=1; continue
  fi
  cur=$(grep -rc "set_option maxHeartbeats" "$lib/" | awk -F: '{s+=$2} END {print s+0}')
  if [ "$cur" -gt "$base" ]; then
    echo "FAIL: $lib maxHeartbeats sites $cur > baseline $base (+$((cur-base)) new override(s))."
    echo "      Fold the blowup instead of bumping a ceiling — see docs/agents/proof-patterns.md"
    echo "      §\"maxHeartbeats: the fold recipe + no-bump discipline\". If genuinely term-intrinsic"
    echo "      (DivRem/Mul/Shift/Sail/Word KEEP-set), bump '$lib' in $baseline_file with a commit note."
    status=1
  elif [ "$cur" -lt "$base" ]; then
    echo "OK (ratchet down): $lib $cur < baseline $base — please lower the baseline to $cur."
  else
    echo "OK: $lib $cur = baseline $base."
  fi
done

if [ "$status" -ne 0 ]; then
  echo "check_heartbeats: FAILED"
  exit 1
fi
echo "check_heartbeats: PASS"
