#!/usr/bin/env bash
# check_witgen_export.sh — structural gate for the committed witness-generation export.
#
# The committed `export/witgen/` tree (25 `<Chip>.witgen.json` payloads + 25
# `<Chip>.manifest.json` manifests + `index.json`) is the wire-format artifact the Rust
# reference interpreter (`rust/witgen-interp/`) consumes; `scripts/witgenExport.lean`
# is its only writer. This gate keeps the committed tree well-formed and internally
# consistent, and (in `--regen` mode) byte-identical to a fresh export.
#
# The committed `export/testdata/` tree (25 `<Chip>.trace.json` differential fixtures —
# the same writer, `--testdata` mode) is validated alongside: parseable, 25 files,
# per-row input widths match the manifest `inputWidth` and witness lengths match
# `localLength`.
#
# The committed `export/sp1dump/` tree (25 `<Chip>.dump.json` SP1 trace dumps +
# `index.json`; sole writer `scripts/update_sp1_dumps.sh`) is validated structurally
# too: parseable, 25 dumps, rows match the declared width x height, index consistent.
# Its `sp1Commit` pin is cross-checked by `scripts/check_pins.sh`, and byte-level
# reproducibility by `update_sp1_dumps.sh --check` (needs the pinned sp1 checkout).
#
# Modes:
#   default          structural validation only (no Lean toolchain needed): every file
#                    parses, wireVersion == 1, 25 payload/manifest pairs + index,
#                    manifest localLength matches its payload, file stems match names,
#                    index rows match the manifests, files end in a newline; testdata
#                    fixtures consistent with the manifests. Enforcing from day one —
#                    committed artifacts must always parse. Exit 1 on any failure.
#   --regen          additionally regenerate both trees into a temp dir with
#                    `scripts/witgenExport.lean` (needs `lake build SP1CleanTest`
#                    first) and require byte-identical trees. Validates the FRESH
#                    output structurally before diffing, because `lake env lean`
#                    exits 0 on a Lean stack overflow.
#   --regen --update install the fresh export over `export/` instead of failing on
#                    drift (inspect and commit the delta).
#
# Callers: `scripts/run_audit.sh` (A0 hygiene block) and
# `.github/workflows/lean_action_ci.yml` (the `guards` job runs the structural mode;
# the `test` job runs `--regen` after `lake test`, when the oleans are warm).
#
# Usage: scripts/check_witgen_export.sh [--regen [--update]]   (from the repo root)
set -uo pipefail
cd "$(dirname "$0")/.."

REGEN=0
UPDATE=0
for arg in "$@"; do
  case "$arg" in
    --regen) REGEN=1 ;;
    --update) UPDATE=1 ;;
    *) echo "unknown flag: $arg" >&2; exit 2 ;;
  esac
done

validate() {
  python3 - "$1" <<'EOF'
import json, sys, os
d = sys.argv[1]
fail = []
def err(msg): fail.append(msg)
if not os.path.isdir(d):
    print(f"FAIL: {d} does not exist", file=sys.stderr); sys.exit(1)
files = sorted(os.listdir(d))
payloads = [f for f in files if f.endswith(".witgen.json")]
manifests = [f for f in files if f.endswith(".manifest.json")]
rowmaps = [f for f in files if f.endswith(".rowmap.json")]
if len(payloads) != 25: err(f"expected 25 *.witgen.json, found {len(payloads)}")
if len(manifests) != 25: err(f"expected 25 *.manifest.json, found {len(manifests)}")
if len(rowmaps) != 25: err(f"expected 25 *.rowmap.json, found {len(rowmaps)}")
if "index.json" not in files: err("index.json missing")
extras = set(files) - set(payloads) - set(manifests) - set(rowmaps) - {"index.json"}
if extras: err(f"unexpected files: {sorted(extras)}")
def load(name):
    path = os.path.join(d, name)
    raw = open(path, "rb").read()
    if not raw.endswith(b"\n"): err(f"{name}: missing trailing newline")
    try:
        return json.loads(raw)
    except Exception as e:
        err(f"{name}: parse error: {e}"); return None
data = {name: load(name) for name in payloads + manifests + rowmaps + (["index.json"] if "index.json" in files else [])}
for p in payloads:
    stem = p[:-len(".witgen.json")]
    pj = data.get(p); mj = data.get(f"{stem}.manifest.json")
    if pj is None: continue
    if pj.get("version") != 1: err(f"{p}: version != 1")
    if not isinstance(pj.get("operations"), list): err(f"{p}: operations not a list")
    if mj is None:
        err(f"{stem}: manifest missing"); continue
    if mj.get("wireVersion") != 1: err(f"{stem}.manifest.json: wireVersion != 1")
    if mj.get("name") != stem: err(f"{stem}.manifest.json: name != file stem")
    if mj.get("witgenFile") != p: err(f"{stem}.manifest.json: witgenFile mismatch")
    if mj.get("localLength") != pj.get("localLength"):
        err(f"{stem}: manifest localLength {mj.get('localLength')} != payload {pj.get('localLength')}")
for f in rowmaps:
    stem = f[:-len(".rowmap.json")]
    rj = data.get(f)
    if rj is None: continue
    if rj.get("wireVersion") != 1: err(f"{f}: wireVersion != 1")
    if rj.get("name") != stem: err(f"{f}: name != file stem")
    row = rj.get("row")
    if not isinstance(row, list) or rj.get("rustWidth") != len(row):
        err(f"{f}: rustWidth != len(row)")
idx = data.get("index.json")
if idx is not None:
    if idx.get("wireVersion") != 1: err("index.json: wireVersion != 1")
    chips = idx.get("chips") or []
    if len(chips) != 25: err(f"index.json: expected 25 chips, found {len(chips)}")
    names = {c.get("name") for c in chips}
    stems = {p[:-len('.witgen.json')] for p in payloads}
    if names != stems: err(f"index.json chips != payload stems: {sorted(names ^ stems)}")
    for c in chips:
        mj = data.get(f"{c.get('name')}.manifest.json")
        if mj is None: continue
        for k in ("inputWidth", "localLength"):
            if c.get(k) != mj.get(k):
                err(f"index.json {c.get('name')}: {k} {c.get(k)} != manifest {mj.get(k)}")
if fail:
    for m in fail: print(f"FAIL: {m}", file=sys.stderr)
    sys.exit(1)
print(f"check_witgen_export: {d} structurally clean (25 payloads + 25 manifests + index).")
EOF
}

validate_testdata() {
  python3 - "$1" "$2" <<'EOF'
import json, sys, os
td, wg = sys.argv[1], sys.argv[2]
fail = []
def err(msg): fail.append(msg)
if not os.path.isdir(td):
    print(f"FAIL: {td} does not exist", file=sys.stderr); sys.exit(1)
files = sorted(os.listdir(td))
fixtures = [f for f in files if f.endswith(".trace.json")]
if len(fixtures) != 25: err(f"expected 25 *.trace.json, found {len(fixtures)}")
extras = set(files) - set(fixtures)
if extras: err(f"unexpected files: {sorted(extras)}")
for f in fixtures:
    stem = f[:-len(".trace.json")]
    raw = open(os.path.join(td, f), "rb").read()
    if not raw.endswith(b"\n"): err(f"{f}: missing trailing newline")
    try:
        d = json.loads(raw)
    except Exception as e:
        err(f"{f}: parse error: {e}"); continue
    if d.get("wireVersion") != 1: err(f"{f}: wireVersion != 1")
    if d.get("chip") != stem: err(f"{f}: chip != file stem")
    try:
        m = json.load(open(os.path.join(wg, f"{stem}.manifest.json")))
    except Exception:
        err(f"{f}: no matching manifest"); continue
    if d.get("inputWidth") != m.get("inputWidth"):
        err(f"{f}: inputWidth {d.get('inputWidth')} != manifest {m.get('inputWidth')}")
    if d.get("localLength") != m.get("localLength"):
        err(f"{f}: localLength {d.get('localLength')} != manifest {m.get('localLength')}")
    rows = d.get("rows") or []
    if not rows: err(f"{f}: no rows")
    for i, r in enumerate(rows):
        if len(r.get("inputs", [])) != m.get("inputWidth"):
            err(f"{f} row {i}: inputs length != inputWidth"); break
        if len(r.get("expectedWitness", [])) != m.get("localLength"):
            err(f"{f} row {i}: expectedWitness length != localLength"); break
        if r.get("kind") not in ("event", "padding", "synthetic"):
            err(f"{f} row {i}: bad kind {r.get('kind')}"); break
if fail:
    for m in fail: print(f"FAIL: {m}", file=sys.stderr)
    sys.exit(1)
print(f"check_witgen_export: {td} structurally clean (25 fixtures, rows consistent with manifests).")
EOF
}

validate_sp1dump() {
  python3 - "$1" <<'EOF'
import json, sys, os
sd = sys.argv[1]
fail = []
def err(msg): fail.append(msg)
if not os.path.isdir(sd):
    print(f"FAIL: {sd} does not exist", file=sys.stderr); sys.exit(1)
files = sorted(os.listdir(sd))
dumps = [f for f in files if f.endswith(".dump.json")]
if len(dumps) != 25: err(f"expected 25 *.dump.json, found {len(dumps)}")
if set(files) - set(dumps) != {"index.json"}:
    err(f"unexpected files: {sorted(set(files) - set(dumps) - {'index.json'})}")
try:
    index = json.load(open(os.path.join(sd, "index.json")))
    if index.get("schemaVersion") != 1: err("index.json: schemaVersion != 1")
    if index.get("chips") != sorted(f[:-len(".dump.json")] for f in dumps):
        err("index.json: chips list != dump file stems")
except Exception as e:
    err(f"index.json: parse error: {e}")
for f in dumps:
    stem = f[:-len(".dump.json")]
    raw = open(os.path.join(sd, f), "rb").read()
    if not raw.endswith(b"\n"): err(f"{f}: missing trailing newline")
    try:
        d = json.loads(raw)
    except Exception as e:
        err(f"{f}: parse error: {e}"); continue
    if d.get("schemaVersion") != 1: err(f"{f}: schemaVersion != 1")
    if d.get("chip") != stem: err(f"{f}: chip != file stem")
    rows = d.get("rows") or []
    if len(rows) != d.get("height"): err(f"{f}: rows != height"); continue
    if any(len(r) != d.get("width") for r in rows): err(f"{f}: a row's length != width")
    if not d.get("events"): err(f"{f}: no events")
if fail:
    for m in fail: print(f"FAIL: {m}", file=sys.stderr)
    sys.exit(1)
print(f"check_witgen_export: {sd} structurally clean (25 dumps, rows match width x height).")
EOF
}

if ! validate "export/witgen"; then
  echo "FAIL: committed export/witgen is not structurally clean; regenerate with" >&2
  echo "  WITGEN_ARGS= lake env lean scripts/witgenExport.lean" >&2
  exit 1
fi
if ! validate_testdata "export/testdata" "export/witgen"; then
  echo "FAIL: committed export/testdata is not structurally clean; regenerate with" >&2
  echo "  WITGEN_ARGS=--testdata lake env lean scripts/witgenExport.lean" >&2
  exit 1
fi
if ! validate_sp1dump "export/sp1dump"; then
  echo "FAIL: committed export/sp1dump is not structurally clean; regenerate with" >&2
  echo "  SP1_DIR=../sp1 scripts/update_sp1_dumps.sh" >&2
  exit 1
fi

if [[ "$REGEN" == "0" ]]; then
  exit 0
fi

if [[ ! -f .lake/build/lib/lean/SP1CleanTest/Exportable.olean ]]; then
  echo "FAIL(--regen): SP1CleanTest oleans missing. Run: lake build SP1CleanTest" >&2
  exit 1
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
if ! WITGEN_ARGS="--out $tmp" lake env lean scripts/witgenExport.lean >/dev/null; then
  echo "FAIL(--regen): exporter run failed" >&2
  exit 1
fi
if ! WITGEN_ARGS="--testdata --out $tmp" lake env lean scripts/witgenExport.lean >/dev/null; then
  echo "FAIL(--regen): exporter testdata run failed" >&2
  exit 1
fi
# Validate the FRESH trees first — `lake env lean` exits 0 on stack overflow, so the
# exit codes above prove nothing by themselves.
if ! validate "$tmp/witgen"; then
  echo "FAIL(--regen): fresh export is not structurally clean (exporter bug or partial run)" >&2
  exit 1
fi
if ! validate_testdata "$tmp/testdata" "$tmp/witgen"; then
  echo "FAIL(--regen): fresh testdata is not structurally clean (exporter bug or partial run)" >&2
  exit 1
fi
if diff -rq "export/witgen" "$tmp/witgen" >/dev/null \
    && diff -rq "export/testdata" "$tmp/testdata" >/dev/null; then
  echo "check_witgen_export (--regen): committed export matches a fresh regeneration byte-for-byte."
  exit 0
fi
if [[ "$UPDATE" == "1" ]]; then
  rm -rf export/witgen export/testdata
  mkdir -p export
  cp -R "$tmp/witgen" export/witgen
  cp -R "$tmp/testdata" export/testdata
  echo "check_witgen_export (--regen --update): installed the fresh export (inspect and commit the delta)."
  exit 0
fi
echo "FAIL(--regen): committed export drifted from a fresh regeneration:" >&2
{ diff -rq "export/witgen" "$tmp/witgen"; diff -rq "export/testdata" "$tmp/testdata"; } | head -20 >&2
echo "(inspect the drift; if intended, rerun with --regen --update and commit)" >&2
exit 1
