#!/usr/bin/env bash
# Gate: the root index `SP1Clean.lean` must import every module under `SP1Clean/`, and must
# not import a module that no longer exists. AGENTS.md makes "wire every new module's import
# there" binding; this script is the machine check behind that rule (a 2026-08 sweep found 33
# silent omissions, so the rule needs a gate, not a convention).
#
# Run from anywhere; part of `scripts/run_audit.sh` and the CI `guards` job. Exit 0 = in sync.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

on_disk=$(find SP1Clean -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | sort)
indexed=$(grep '^import SP1Clean' SP1Clean.lean | sed 's/^import //' | sort)

missing=$(comm -13 <(echo "$indexed") <(echo "$on_disk"))
dangling=$(comm -23 <(echo "$indexed") <(echo "$on_disk"))
dupes=$(echo "$indexed" | uniq -d)

if [ -n "$missing" ]; then
  echo "FAIL: module(s) on disk but not imported by SP1Clean.lean:"
  echo "$missing" | sed 's/^/  /'
  fail=1
fi
if [ -n "$dangling" ]; then
  echo "FAIL: SP1Clean.lean imports module(s) that do not exist:"
  echo "$dangling" | sed 's/^/  /'
  fail=1
fi
if [ -n "$dupes" ]; then
  echo "FAIL: duplicate import(s) in SP1Clean.lean:"
  echo "$dupes" | sed 's/^/  /'
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "PASS: root index imports all $(echo "$on_disk" | wc -l | tr -d ' ') SP1Clean modules, no dangling imports"
fi
exit "$fail"
