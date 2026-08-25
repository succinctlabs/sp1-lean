#!/usr/bin/env bash
# Gate the single-source-of-truth invariant for SP1's concrete KoalaBear characteristic.
# Production and test/export code must import Model/SP1Field.lean; a local alias or repeated
# decimal literal would recreate two notions of the field and let their facts drift apart.

set -euo pipefail
cd "$(dirname "$0")/.."

owner="SP1Clean/Model/SP1Field.lean"
hits="$(rg -l '(^|[[:space:]])(abbrev|def)[[:space:]]+SP1Prime|2130706433' \
  SP1Clean SP1CleanTest scripts -g '*.lean' || true)"

if [[ "$hits" != "$owner" ]]; then
  echo "FAIL: SP1Prime and its decimal characteristic must occur only in $owner"
  if [[ -n "$hits" ]]; then
    echo "$hits"
  else
    echo "no owner declaration found"
  fi
  exit 1
fi

echo "SP1 field singleton OK: $owner is the sole Lean owner"
