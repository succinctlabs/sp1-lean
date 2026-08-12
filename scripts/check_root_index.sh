#!/usr/bin/env bash
# Gate: each library's root index must import every module under its tree, and must not import a
# module that no longer exists. AGENTS.md makes "wire every new module's import there" binding;
# this script is the machine check behind that rule (a 2026-08 sweep found 33 silent omissions, so
# the rule needs a gate, not a convention).
#
# Covers all three hand-written trees: `SP1Clean/`, and the two upstream-destined libraries
# `ToClean/` and `ToMathlib/`. The latter two are checked only once they exist on disk, so this
# script is correct both before and after they are created.
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
  indexed=$(grep "^import ${tree}" "$index" | sed 's/^import //' | sort)

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
check_tree ToMathlib ToMathlib.lean

if [ "$fail" -eq 0 ]; then
  echo "PASS: root indices import all $total modules across SP1Clean/ToClean/ToMathlib, no dangling imports"
fi
exit "$fail"
