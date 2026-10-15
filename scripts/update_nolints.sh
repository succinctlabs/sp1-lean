#!/usr/bin/env bash
# Regenerate scripts/nolints.json — the environment-linter burn-down list (AGENTS.md § Linters).
#
# Batteries' `runLinter --update` rewrites the file with the findings of ONE root module and stops
# at the first root that has any, so a package with several roots has to run it per root and merge.
# This script does that for the four hand-written roots and writes the sorted union. Needs the
# full build (`lake build SP1Clean ToClean ToMathlib ToPolyFun`) first; `--no-build` refuses to
# build missing oleans rather than silently building them.
#
# Usage: scripts/update_nolints.sh            (from anywhere; exit 0 = file regenerated)
set -uo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp scripts/nolints.json "$tmp/original.json"
for root in SP1Clean ToClean ToMathlib ToPolyFun; do
  cp "$tmp/original.json" scripts/nolints.json
  lake exe runLinter --no-build --update "$root" > "$tmp/$root.log" 2>&1
  status=$?
  # 0 = no findings (the file is now `[]`), 1 = findings written; anything else is a real failure.
  if [ "$status" -gt 1 ]; then
    echo "FAIL: runLinter --update $root exited $status:"; tail -20 "$tmp/$root.log"; exit "$status"
  fi
  cp scripts/nolints.json "$tmp/$root.json"
done
python3 - "$tmp" <<'PYEOF'
import json, sys
tmp = sys.argv[1]
entries = set()
for root in ["SP1Clean", "ToClean", "ToMathlib", "ToPolyFun"]:
    for linter, decl in json.load(open(f"{tmp}/{root}.json")):
        entries.add((linter, decl))
merged = sorted(entries)
with open("scripts/nolints.json", "w") as f:
    f.write("[" + ",\n ".join(json.dumps([l, d], ensure_ascii=False) for l, d in merged) + "]\n")
from collections import Counter
print(f"scripts/nolints.json: {len(merged)} entries", dict(Counter(l for l, _ in merged)))
PYEOF
