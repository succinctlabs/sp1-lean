#!/usr/bin/env bash
# Gate: elaboration-budget escape hatches are PROHIBITED except on an explicit measured allowlist.
#
# Covers `set_option maxHeartbeats` and `set_option maxRecDepth` under `SP1Clean/` and `SP1CleanTest/`.
#
# This replaces the old count-ratchet (`check_heartbeats.sh`). A ratchet permits a new escape hatch as
# long as an old one leaves; an allowlist does not. Every surviving site must be named in
# `scripts/option_escapes_allowlist.txt` together with its measured floor bracket and the mechanism that
# makes it irreducible. Anything else fails the build.
#
# Why an allowlist is defensible here: the 2026-07/08 campaign took hand-written `maxHeartbeats` from
# 638 to ZERO by diagnosing and fixing causes, and the survivors are all *generated* definitions with
# measured, understood mechanisms. Upstream Clean carries none in 44,603 lines and enforces that in
# review; this is the closest equivalent for a tree that must also carry compiler-generated AIR.
#
# Allowlist format (one entry per line, `#` comments and blank lines ignored):
#
#   <option>  <path>  <value>  <count>  <justification…>
#
# The key is (option, path, value) and the count must match EXACTLY — so adding a second site with the
# same value to an already-listed file fails, as does silently raising a listed value. Line numbers are
# deliberately not part of the key: they drift, and a drifting key trains people to edit the allowlist.
#
# Adding an entry requires a measured ladder recorded in the justification. Do not add one to make a
# build pass: see `docs/agents/perf-findings.md` §12 (extract over opaque arguments; check what the
# extraction can still see), which is how every removed site was removed.
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
  grep -rn "set_option $opt " SP1Clean SP1CleanTest --include='*.lean' 2>/dev/null \
    | sed -E "s|^([^:]+):[0-9]+:.*set_option $opt ([0-9]+).*|$opt \1 \2|"
done | sort | uniq -c | awk '{print $2, $3, $4, $1}' | sort > "$tmp_actual"

# Allowlist: strip comments/blank lines, keep the first four fields.
grep -vE '^\s*(#|$)' "$allow" | awk '{print $1, $2, $3, $4}' | sort > "$tmp_allow"

if ! diff -u "$tmp_allow" "$tmp_actual" > /tmp/.option_escapes_diff 2>&1; then
  echo "FAIL: elaboration-budget escape hatches do not match the allowlist." >&2
  echo "      '-' = allowlisted but absent (ratchet DOWN — delete the allowlist entry)." >&2
  echo "      '+' = present but NOT allowlisted (a new or raised ceiling — this is the failure)." >&2
  echo >&2
  sed -n '3,$p' /tmp/.option_escapes_diff >&2
  echo >&2
  echo "      Fold the blowup instead of adding an entry — docs/agents/perf-findings.md §12:" >&2
  echo "      extract over OPAQUE arguments, and check what the extraction can still see." >&2
  echo "      If a site is genuinely irreducible, add it to $allow WITH a measured ladder." >&2
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "check_option_escapes: FAILED" >&2
  exit 1
fi

total=$(awk '{s+=$4} END {print s+0}' "$tmp_actual")
echo "check_option_escapes: PASS ($total allowlisted site(s), 0 unlisted)"
