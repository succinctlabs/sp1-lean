#!/usr/bin/env bash
# update_sp1_dumps.sh — sole writer for the committed SP1 trace dumps.
#
# The committed `export/sp1dump/` tree (25 `<Chip>.dump.json` files + `index.json`) is
# the SP1-side conformance anchor: deterministic per-chip event batteries plus the FULL
# padded `generate_trace` row matrix, produced by the `chip_traces` binary committed on
# the pinned extraction branch (`crates/core/compiler/src/bin/chip_traces.rs`). The
# Lean fixture generator (`scripts/witgenExport.lean --testdata`) recomputes every event
# row from these dumps and fails closed on any cell mismatch, so the dumps are the
# ground truth the witgen differential is anchored to.
#
# Provenance discipline mirrors `update_extracted.py`: `$SP1_DIR` must be a CLEAN
# checkout of exactly `SP1_PINNED_COMMIT` (read from `update_extracted.py` — the single
# source of truth, cross-checked against `index.json` by `scripts/check_pins.sh`), so a
# committed dump is always reproducible from the pin. The dumper is deterministic
# (fixed LCG seed, no timestamps): regeneration at the pin is byte-identical.
#
# Modes:
#   default   regenerate into a temp dir, then install over `export/sp1dump/`
#             (inspect and commit the delta).
#   --check   regenerate into a temp dir and require byte-identity with the committed
#             tree; exit 1 on drift. Never writes into the repo.
#
# Usage: SP1_DIR=../sp1 scripts/update_sp1_dumps.sh [--check]   (from the repo root)
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
PIN=$(python3 -c "
import re
src = open('update_extracted.py').read()
print(re.search(r'SP1_PINNED_COMMIT = \"([0-9a-f]{40})\"', src).group(1))
")
if [[ -z "$PIN" ]]; then
  echo "FAIL: could not read SP1_PINNED_COMMIT from update_extracted.py" >&2
  exit 1
fi

# -- pin + cleanliness fence (fail-closed, before any cargo run) ------------------------
ACTUAL=$(git -C "$SP1_DIR" rev-parse HEAD 2>/dev/null)
if [[ "$ACTUAL" != "$PIN" ]]; then
  echo "FAIL: $SP1_DIR is at ${ACTUAL:-<no git>}, expected pinned extraction commit $PIN" >&2
  exit 1
fi
DIRTY=$(git -C "$SP1_DIR" status --porcelain=v1 | grep -v '^??' || true)
if [[ -n "$DIRTY" ]]; then
  echo "FAIL: $SP1_DIR has uncommitted changes (dumps must be reproducible from the pin):" >&2
  echo "$DIRTY" >&2
  exit 1
fi

# -- regenerate into a temp dir ---------------------------------------------------------
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

echo "Running chip_traces --all at pin $PIN ..."
(cd "$SP1_DIR" && cargo run --release -p sp1-constraint-compiler --bin chip_traces -- \
    --all --out "$TMP") || { echo "FAIL: chip_traces run failed" >&2; exit 1; }

# index.json: schema + provenance + chip list (sorted by the dumper's stable order = ls).
python3 - "$TMP" "$PIN" <<'EOF'
import json, os, sys
out_dir, pin = sys.argv[1], sys.argv[2]
chips = sorted(f[: -len(".dump.json")] for f in os.listdir(out_dir) if f.endswith(".dump.json"))
if len(chips) != 25:
    raise SystemExit(f"FAIL: expected 25 chip dumps, found {len(chips)}")
for chip in chips:
    with open(os.path.join(out_dir, f"{chip}.dump.json")) as f:
        dump = json.load(f)
    for key in ("schemaVersion", "chip", "mode", "width", "height", "events", "rows"):
        if key not in dump:
            raise SystemExit(f"FAIL: {chip}.dump.json missing key '{key}'")
    if dump["chip"] != chip:
        raise SystemExit(f"FAIL: {chip}.dump.json declares chip '{dump['chip']}'")
    if len(dump["rows"]) != dump["height"] or any(len(r) != dump["width"] for r in dump["rows"]):
        raise SystemExit(f"FAIL: {chip}.dump.json rows do not match width x height")
index = {"schemaVersion": 1, "sp1Commit": pin, "chips": chips}
with open(os.path.join(out_dir, "index.json"), "w") as f:
    json.dump(index, f, indent=2)
    f.write("\n")
print(f"Validated {len(chips)} dumps; wrote index.json")
EOF
[[ $? -eq 0 ]] || exit 1

# -- install or diff --------------------------------------------------------------------
if [[ "$CHECK" == "1" ]]; then
  if ! diff -r "$TMP" export/sp1dump >/dev/null 2>&1; then
    echo "FAIL: committed export/sp1dump/ differs from a fresh regeneration at the pin:" >&2
    diff -rq "$TMP" export/sp1dump >&2 || true
    exit 1
  fi
  echo "PASS: export/sp1dump/ is byte-identical to a fresh regeneration at pin $PIN"
else
  rm -rf export/sp1dump
  mkdir -p export/sp1dump
  cp "$TMP"/*.json export/sp1dump/
  echo "Installed $(ls export/sp1dump | wc -l | tr -d ' ') files into export/sp1dump/ (inspect + commit)"
fi
