#!/usr/bin/env bash
# Gate: each library's root index must import every module under its tree, and must not import a
# module that no longer exists. AGENTS.md makes "wire every new module's import there" binding;
# this script is the machine check behind that rule (a 2026-08 sweep found 33 silent omissions, so
# the rule needs a gate, not a convention).
#
# Covers the four hand-written trees: `SP1Clean/` and the upstream-destined `ToClean/`,
# `ToPolyFun/`, `ToMathlib/`. `SP1Clean/` has two indices: `SP1Clean/Core.lean` (the `SP1Core`
# library root, strata 0–6 of `scripts/layering.txt` — its exact contents are gated by
# `scripts/check_layering.sh`) and the umbrella `SP1Clean.lean`, which imports `SP1Clean.Core` and
# everything else; coverage is checked over the union of the two.
#
# Import lines may carry the module-system modifiers (`public`, `meta`, `all`).
#
# Run from anywhere; part of `scripts/run_audit.sh` and the CI `guards` job. Exit 0 = in sync.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
total=0

check_tree() {
  local tree="$1" index="$2"
  [ -d "$tree" ] || return 0
  if [ ! -f "$index" ]; then
    echo "FAIL: $tree/ exists on disk but its root index $index is missing."
    fail=1
    return 0
  fi

  local on_disk indexed missing dangling dupes
  on_disk=$(find "$tree" -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | sort)
  # The umbrella may reach modules through a sub-index it imports (`SP1Clean.Core`); the sub-index
  # itself is a module on disk and must be imported by the umbrella like any other.
  indexed=$( { grep -E "^(public )?(meta )?import (all )?${tree}" "$index";
               for sub in $(grep -oE "^(public )?(meta )?import (all )?${tree}\.Core$" "$index" | sed -E 's/^(public )?(meta )?import (all )?//'); do
                 grep -E "^(public )?(meta )?import (all )?${tree}" "$(echo "$sub" | sed 's|\.|/|g').lean";
               done; } | sed -E 's/^(public )?(meta )?import (all )?//' | sort)

  missing=$(comm -13 <(echo "$indexed") <(echo "$on_disk"))
  dangling=$(comm -23 <(echo "$indexed") <(echo "$on_disk"))
  dupes=$(echo "$indexed" | uniq -d)

  if [ -n "$missing" ]; then
    echo "FAIL: module(s) on disk but not imported by $index:"
    echo "$missing" | sed 's/^/  /'
    fail=1
  fi
  if [ -n "$dangling" ]; then
    echo "FAIL: $index imports module(s) that do not exist:"
    echo "$dangling" | sed 's/^/  /'
    fail=1
  fi
  if [ -n "$dupes" ]; then
    echo "FAIL: duplicate import(s) in $index:"
    echo "$dupes" | sed 's/^/  /'
    fail=1
  fi
  total=$((total + $(echo "$on_disk" | wc -l | tr -d ' ')))
}

check_tree SP1Clean SP1Clean.lean
check_tree ToClean ToClean.lean
check_tree ToPolyFun ToPolyFun.lean
check_tree ToMathlib ToMathlib.lean

if [ "$fail" -eq 0 ]; then
  echo "PASS: root indices import all $total modules across SP1Clean/ToClean/ToMathlib/ToPolyFun, no dangling imports"
fi
exit "$fail"
