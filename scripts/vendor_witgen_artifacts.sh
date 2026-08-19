#!/usr/bin/env bash
# vendor_witgen_artifacts.sh — sync the witness-generation export into the SP1 tree.
#
# The SP1-side conformance check (`crates/core/compiler/conformance-check/`)
# checks the vendored artifacts against the live prover's `generate_trace` output, so
# the vendored tree must be an exact copy of this repo's committed `export/witgen/`
# (25 `<Chip>.witgen.json` + 25 `<Chip>.rowmap.json` + 25 `<Chip>.manifest.json` +
# `index.json`).
#
# The exported artifacts deliberately embed no revisions (byte-stability is what lets
# CI diff them against fresh exports); attribution for the vendored copy lives in a
# `provenance.json` sidecar written HERE, at vendoring time — the sp1-lean commit, the
# Clean pin, and the wire version — so the SP1 tree can always say which verified
# state produced its copy. The sidecar sits next to (not inside) the artifact files
# and is excluded from the --check byte comparison.
#
# Modes:
#   default   copy export/witgen/ into $SP1_DIR/crates/core/compiler/testdata/lean-witgen/
#             and stamp provenance.json (run from a clean sp1-lean tree, since the
#             stamped commit must describe the artifacts).
#   --check   require the vendored artifact files to be byte-identical to the local
#             export; never writes. Exit 1 on drift.
#
# Usage: SP1_DIR=../sp1 scripts/vendor_witgen_artifacts.sh [--check]   (from the repo root)
set -uo pipefail
cd "$(dirname "$0")/.."

CHECK=0
for arg in "$@"; do
  case "$arg" in
    --check) CHECK=1 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

SP1_DIR="${SP1_DIR:-../sp1}"
DEST="$SP1_DIR/crates/core/compiler/testdata/lean-witgen"

if [[ "$CHECK" == "1" ]]; then
  if [[ ! -d "$DEST" ]]; then
    echo "FAIL: $DEST does not exist" >&2
    exit 1
  fi
  fail=0
  for f in export/witgen/*.json; do
    base="$(basename "$f")"
    if ! cmp -s "$f" "$DEST/$base"; then
      echo "FAIL: $DEST/$base differs from export/witgen/$base" >&2
      fail=1
    fi
  done
  for f in "$DEST"/*.json; do
    base="$(basename "$f")"
    [[ "$base" == "provenance.json" ]] && continue
    if [[ ! -f "export/witgen/$base" ]]; then
      echo "FAIL: $DEST/$base has no counterpart in export/witgen/" >&2
      fail=1
    fi
  done
  if [[ "$fail" == "1" ]]; then exit 1; fi
  echo "PASS: vendored artifacts are byte-identical to export/witgen/"
  exit 0
fi

if [[ -n "$(git status --porcelain export/witgen/)" ]]; then
  echo "FAIL: export/witgen/ has uncommitted changes; the stamped commit must describe the artifacts" >&2
  exit 1
fi

SP1LEAN_COMMIT=$(git rev-parse HEAD)
CLEAN_REV=$(python3 -c "
import json
pkgs = {p['name']: p for p in json.load(open('lake-manifest.json'))['packages']}
print(pkgs['Clean']['rev'])
")
mkdir -p "$DEST"
rm -f "$DEST"/*.json
cp export/witgen/*.json "$DEST/"
python3 - "$DEST" "$SP1LEAN_COMMIT" "$CLEAN_REV" <<'EOF'
import json, sys
dest, commit, clean = sys.argv[1], sys.argv[2], sys.argv[3]
prov = {
    "wireVersion": 1,
    "sp1LeanCommit": commit,
    "cleanRev": clean,
    "source": "sp1-lean export/witgen (byte-identical; scripts/vendor_witgen_artifacts.sh)",
}
with open(f"{dest}/provenance.json", "w") as f:
    json.dump(prov, f, indent=2)
    f.write("\n")
EOF
echo "Vendored $(ls "$DEST" | wc -l | tr -d ' ') files into $DEST (inspect + commit in the sp1 tree)"
