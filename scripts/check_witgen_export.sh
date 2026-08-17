#!/usr/bin/env bash
# check_witgen_export.sh — structural gate for the committed witness-generation export.
#
# The committed `export/witgen/` tree (25 `<Chip>.witgen.json` payloads + 25
# `<Chip>.manifest.json` manifests + `index.json`) is the wire-format artifact the Rust
# reference interpreter (`rust/witgen-interp/`) consumes; `scripts/witgenExport.lean`
# is its only writer. This gate keeps the committed tree well-formed and internally
# consistent, and (in `--regen` mode) byte-identical to a fresh export.
#
# Modes:
#   default          structural validation only (no Lean toolchain needed): every file
#                    parses, wireVersion == 1, 25 payload/manifest pairs + index,
#                    manifest localLength matches its payload, file stems match names,
#                    index rows match the manifests, files end in a newline. Enforcing
#                    from day one — committed artifacts must always parse. Exit 1 on
#                    any failure.
#   --regen          additionally regenerate into a temp dir with
#                    `scripts/witgenExport.lean` (needs `lake build
#                    SP1CleanTest.Exportable` first) and require a byte-identical tree.
#                    Validates the FRESH output structurally before diffing, because
#                    `lake env lean` exits 0 on a Lean stack overflow.
#   --regen --update install the fresh export over `export/witgen/` instead of failing
#                    on drift (inspect and commit the delta).
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
if len(payloads) != 25: err(f"expected 25 *.witgen.json, found {len(payloads)}")
if len(manifests) != 25: err(f"expected 25 *.manifest.json, found {len(manifests)}")
if "index.json" not in files: err("index.json missing")
extras = set(files) - set(payloads) - set(manifests) - {"index.json"}
if extras: err(f"unexpected files: {sorted(extras)}")
def load(name):
    path = os.path.join(d, name)
    raw = open(path, "rb").read()
    if not raw.endswith(b"\n"): err(f"{name}: missing trailing newline")
    try:
        return json.loads(raw)
    except Exception as e:
        err(f"{name}: parse error: {e}"); return None
data = {name: load(name) for name in payloads + manifests + (["index.json"] if "index.json" in files else [])}
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

if ! validate "export/witgen"; then
  echo "FAIL: committed export/witgen is not structurally clean; regenerate with" >&2
  echo "  WITGEN_ARGS= lake env lean scripts/witgenExport.lean" >&2
  exit 1
fi

if [[ "$REGEN" == "0" ]]; then
  exit 0
fi

if [[ ! -f .lake/build/lib/lean/SP1CleanTest/Exportable.olean ]]; then
  echo "FAIL(--regen): SP1CleanTest.Exportable oleans missing. Run: lake build SP1CleanTest.Exportable" >&2
  exit 1
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
if ! WITGEN_ARGS="--out $tmp" lake env lean scripts/witgenExport.lean >/dev/null; then
  echo "FAIL(--regen): exporter run failed" >&2
  exit 1
fi
# Validate the FRESH tree first — `lake env lean` exits 0 on stack overflow, so the
# exit code above proves nothing by itself.
if ! validate "$tmp/witgen"; then
  echo "FAIL(--regen): fresh export is not structurally clean (exporter bug or partial run)" >&2
  exit 1
fi
if diff -rq "export/witgen" "$tmp/witgen" >/dev/null; then
  echo "check_witgen_export (--regen): committed export matches a fresh regeneration byte-for-byte."
  exit 0
fi
if [[ "$UPDATE" == "1" ]]; then
  rm -rf export/witgen
  mkdir -p export
  cp -R "$tmp/witgen" export/witgen
  echo "check_witgen_export (--regen --update): installed the fresh export (inspect and commit the delta)."
  exit 0
fi
echo "FAIL(--regen): committed export drifted from a fresh regeneration:" >&2
diff -rq "export/witgen" "$tmp/witgen" | head -20 >&2
echo "(inspect the drift; if intended, rerun with --regen --update and commit)" >&2
exit 1
