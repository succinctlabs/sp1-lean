#!/usr/bin/env bash
# Gate the audit-surface index: every declaration named in docs/audit-surface.md must still exist
# at the file named beside it.
#
# The point is bidirectional. A premise silently ADDED to the boundary, or a definition renamed out
# from under the index, fails here. A premise REMOVED (the good direction — e.g. the 2026-08 W3
# wave deriving MemoryPullTimestampHighBound, which took the count from twelve to eleven) also
# fails, forcing the index and its prose to be updated to claim the win rather than drift.
#
# This is a resolution check, not a semantic one: it says the audit surface is where the doc says it
# is. What those definitions MEAN is what a human auditor reads them for.
#
# Part of the release harness (scripts/run_audit.sh and the CI `guards` job); run from the repo root.
set -euo pipefail

doc="docs/audit-surface.md"
[ -f "$doc" ] || { echo "FAIL: $doc missing"; exit 1; }

fail=0
checked=0

# Rows are `| `Decl` | `path` | question |`. Pull the first two backticked fields of each such row.
while IFS=$'\t' read -r decl file; do
  [ -z "${decl:-}" ] && continue
  [ -z "${file:-}" ] && continue
  checked=$((checked + 1))

  if [ ! -f "$file" ]; then
    echo "FAIL: $doc names $decl in $file, which does not exist"
    fail=1
    continue
  fi

  # A declaration may be written bare or namespace-qualified at its definition site, and the doc
  # may cite it either way (`Commit.progOf` is defined as `def progOf` inside `namespace Commit`;
  # `SP1MachineModel.UsesOrdinarySchedule` is defined dotted). Accept both spellings. Escape the
  # `?` accepted in Lean identifiers as well as namespace dots before using either spelling as an
  # extended regular expression.
  bare="${decl##*.}"
  decl_re="${decl//./\\.}"
  decl_re="${decl_re//\?/\\?}"
  bare_re="${bare//\?/\\?}"
  kw='(def|abbrev|structure|inductive|theorem|class|instance)'
  if grep -qE "^[[:space:]]*(private |protected |noncomputable )*${kw} (${decl_re}|${bare_re})\b" "$file"; then
    continue
  fi

  echo "FAIL: $doc names $decl in $file, but no such declaration is there"
  echo "      (if it was deliberately removed, update the index and say so — a premise that"
  echo "       disappeared is a result worth claiming, not a line to delete quietly)"
  fail=1
done < <(grep -E '^\| `[^`]+` \| `[^`]+` \|' "$doc" \
         | sed -E 's/^\| `([^`]+)` \| `([^`]+)` \|.*/\1\t\2/')

if [ "$checked" -eq 0 ]; then
  echo "FAIL: $doc yielded no checkable rows — the table format changed and this gate went blind"
  exit 1
fi

if [ "$fail" -eq 0 ]; then
  noun="declarations"; [ "$checked" -eq 1 ] && noun="declaration"
  echo "check_audit_surface: PASS ($checked $noun resolve)"
else
  echo "check_audit_surface: FAIL"
fi
exit "$fail"
