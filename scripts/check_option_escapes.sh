#!/usr/bin/env bash
# Gate: elaboration-budget escape hatches are PROHIBITED except on an explicit measured allowlist.
#
# Covers `set_option maxHeartbeats` and `set_option maxRecDepth` under `SP1Clean/` and `SP1CleanTest/`.
#
# Hand-written Lean in this repo carries **zero** `maxHeartbeats`, matching upstream Clean, which has
# none in 44,603 lines and enforces that in review. The allowlisted sites are generated definitions and
# a small number of measured structural cases; each is named in `scripts/option_escapes_allowlist.txt`
# with its floor bracket and mechanism. Anything else fails the build.
#
# This is a prohibition, not a budget. It does not count sites, and it does not permit a new escape
# hatch in exchange for an old one — the failure mode a count baseline allows.
#
# Allowlist format (one entry per line, `#` comments and blank lines ignored):
#
#   <option>  <path>  <value>  <count>  <justification…>
#
# The key is (option, path, value) and the count must match EXACTLY — so adding a second site with the
# same value to an already-listed file fails, as does silently raising a listed value. Line numbers are
# deliberately not part of the key: they drift, and a drifting key trains people to edit the allowlist
# instead of fixing the cause.
#
# **Adding an entry is a last resort, not a way to make a build pass.** The bar is in
# `docs/agents/proof-patterns.md` § "Elaboration budgets": a measured floor bracket, a named
# mechanism, at least one attempted fix with its result, and a reason the cause cannot be moved.
# Start from its compile-time section — extract over opaque arguments and check what the
# extraction can still see. If the site is generated, fix the emitter in `update_extracted.py`
# rather than allowlisting its output.
#
# Mirrors scripts/check_no_native_decide.sh / check_no_skipkerneltc.sh: exit 0 = clean, 1 = violation.
# Run from the repo root.

set -uo pipefail
cd "$(dirname "$0")/.."

allow="scripts/option_escapes_allowlist.txt"
if [ ! -f "$allow" ]; then
  echo "FAIL: $allow not found" >&2; exit 1
fi

status=0
tmp_actual=$(mktemp)
tmp_allow=$(mktemp)
trap 'rm -f "$tmp_actual" "$tmp_allow"' EXIT

# Actual sites: one "<option> <path> <value>" line per occurrence, aggregated to counts.
for opt in maxHeartbeats maxRecDepth; do
  grep -rn "set_option $opt " SP1Clean SP1CleanTest ToClean ToMathlib --include='*.lean' 2>/dev/null \
    | sed -E "s|^([^:]+):[0-9]+:.*set_option $opt ([0-9]+).*|$opt \1 \2|"
done | sort | uniq -c | awk '{print $2, $3, $4, $1}' | sort > "$tmp_actual"

# Allowlist: strip comments/blank lines, keep the first four fields.
grep -vE '^\s*(#|$)' "$allow" | awk '{print $1, $2, $3, $4}' | sort > "$tmp_allow"

if ! diff -u "$tmp_allow" "$tmp_actual" > /tmp/.option_escapes_diff 2>&1; then
  echo "FAIL: elaboration-budget escape hatches do not match the allowlist." >&2
  echo "      '-' = allowlisted but absent — the site is gone; delete its allowlist entry." >&2
  echo "      '+' = present but NOT allowlisted (a new or raised ceiling — this is the failure)." >&2
  echo >&2
  sed -n '3,$p' /tmp/.option_escapes_diff >&2
  echo >&2
  echo "      Fix the cause instead of adding an entry — docs/agents/proof-patterns.md:" >&2
  echo "      extract over OPAQUE arguments, and check what the extraction can still see." >&2
  echo "      Adding an allowlist entry is a LAST RESORT and has a documented bar:" >&2
  echo "      a measured floor bracket, a named mechanism, an attempted fix with its result," >&2
  echo "      and a reason the cause cannot be moved. Generated site? Fix update_extracted.py." >&2
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "check_option_escapes: FAILED" >&2
  exit 1
fi

total=$(awk '{s+=$4} END {print s+0}' "$tmp_actual")
echo "check_option_escapes: PASS ($total allowlisted site(s), 0 unlisted)"
