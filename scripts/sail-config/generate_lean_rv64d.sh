#!/usr/bin/env bash
# Regenerate the LeanRV64D model from pinned sources + the SP1 platform config, and verify the
# result against the in-tree copy. The model is the repository's `LeanRV64D/` + `LeanRV64D.lean`,
# an AUTO-GENERATED library that is never hand-edited: generator output from the pins below plus
# `sp1_rv64d_cfg.json`. See docs/agents/sail-model-provenance.md.
#
# Modes:
#   --deps         one-time: create the opam switch and build the pinned sail compiler
#   --stock        generate with the stock rv64d config; diff vs the opencompl base snapshot
#   --sp1          generate with the SP1 config; diff vs the base (four sites expected) AND the
#                  in-tree copy (the gate: regeneration must be idempotent)
#   --install      generate with the SP1 config and write the in-tree copy (then commit it and
#                  refresh the fingerprints in scripts/provenance.json)
#   --make-config  regenerate scripts/sail-config/sp1_rv64d_cfg.json (base config ⊕ overlay)
#
# Requires: opam, cmake, z3, python3, git. Work tree defaults to ~/.cache/sp1-sail-gen (override
# with SAIL_GEN_DIR). Generation takes ~10 minutes after the one-time --deps (~20-40 minutes).
# CI runs --make-config/--sp1/--stock on every generator, config, or model-tree change and monthly
# (.github/workflows/sail-regen.yml); scripts/check_pins.py checks the in-tree copy's hash
# against scripts/provenance.json.
#
# Generator inputs and output fingerprints are owned by scripts/provenance.json.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
MODE="${1:?usage: generate_lean_rv64d.sh --deps | --stock | --sp1 | --install | --make-config}"
case "$MODE" in
  --deps|--stock|--sp1|--install|--make-config) ;;
  *) echo "unknown mode: $MODE" >&2; exit 2 ;;
esac
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
read -r SAIL_SHA SAIL_RISCV_SHA OCAML_VERSION BASE_SNAPSHOT < <(
  python3 - "$REPO_ROOT/scripts/provenance.json" <<'PYPROVENANCE'
import json, sys
sail = json.load(open(sys.argv[1]))["sail"]
print(*(sail[key] for key in ("compilerRevision", "modelRevision", "ocamlVersion", "baseSnapshot")))
PYPROVENANCE
)
WORK="${SAIL_GEN_DIR:-$HOME/.cache/sp1-sail-gen}"
SWITCH=sail-gen
export OPAMYES=1

mkdir -p "$WORK"; cd "$WORK"
[ -d sail ] || git clone --quiet https://github.com/rems-project/sail
[ -d sail-riscv ] || git clone --quiet https://github.com/riscv/sail-riscv
git -C sail fetch --quiet origin "$SAIL_SHA" 2>/dev/null || true
git -C sail-riscv fetch --quiet origin "$SAIL_RISCV_SHA" 2>/dev/null || true
git -C sail checkout --quiet "$SAIL_SHA"
git -C sail-riscv checkout --quiet "$SAIL_RISCV_SHA"

if [ "$MODE" = --deps ]; then
  opam switch list --short | grep -qx "$SWITCH" || opam switch create "$SWITCH" "$OCAML_VERSION"
  eval "$(opam env --switch=$SWITCH --set-switch)"
  opam update >/dev/null
  (cd sail && opam install . --deps-only --yes)
  (cd sail && make install)
  sail --version
  exit 0
fi

eval "$(opam env --switch=$SWITCH --set-switch)"
command -v sail >/dev/null || { echo "run --deps first"; exit 1; }
echo "sail: $(sail --version)"

# Configure (writes the stock build/config/rv64d_v256_e64.json from config/config.json.in).
cmake -S sail-riscv -B sail-riscv/build -DCMAKE_BUILD_TYPE=RelWithDebInfo >/dev/null
CFG=sail-riscv/build/config/rv64d_v256_e64.json

if [ "$MODE" = --make-config ]; then
  # The generated config carries //-comments; strip them before merging, and write via a temp
  # file so a failure never leaves a blank config.
  python3 - "$CFG" "$HERE/sp1-overlay.json" "$HERE/sp1_rv64d_cfg.json" <<'PYEOF'
import json, os, re, sys
def load_jsonc(path):
    text = re.sub(r"^\s*//.*$", "", open(path).read(), flags=re.M)
    return json.loads(text)
def deep_merge(base, overlay):
    for key, value in overlay.items():
        if isinstance(value, dict) and isinstance(base.get(key), dict):
            deep_merge(base[key], value)
        else:
            base[key] = value
    return base
base, overlay, out = sys.argv[1:4]
merged = deep_merge(load_jsonc(base), load_jsonc(overlay))
tmp = out + ".tmp"
with open(tmp, "w") as f:
    json.dump(merged, f, indent=2, sort_keys=True)
    f.write("\n")
os.replace(tmp, out)
PYEOF
  echo "wrote sp1_rv64d_cfg.json (sha256 $(shasum -a 256 "$HERE/sp1_rv64d_cfg.json" | cut -d' ' -f1))"
  exit 0
fi

if [ "$MODE" = --sp1 ] || [ "$MODE" = --install ]; then
  [ -f "$HERE/sp1_rv64d_cfg.json" ] || { echo "missing sp1_rv64d_cfg.json — run --make-config"; exit 1; }
  cp "$HERE/sp1_rv64d_cfg.json" "$CFG"
fi

# Build the Lean model; the hash guard catches a cmake re-configure clobbering the SP1 config.
H0=$(shasum -a 256 "$CFG" | cut -d' ' -f1)
cmake --build sail-riscv/build --target generated_lean_rv64d
H1=$(shasum -a 256 "$CFG" | cut -d' ' -f1)
[ "$H0" = "$H1" ] || { echo "FAIL: cmake regenerated the config mid-build"; exit 1; }

OUT=sail-riscv/build/model/Lean_RV64D
[ -d ref ] || git clone --quiet https://github.com/opencompl/sail-riscv-lean ref
git -C ref fetch --quiet origin
# Repo furniture the nightly adds around the generated tree.
EXCLUDES=(-x README.md -x report.py -x build_log.txt -x .github -x .gitignore -x .lake
          -x lake-manifest.json -x lakefile.toml -x lean-toolchain -x README.md.template -x .git)

verdict=0
diff_against() { # rev label
  git -C ref checkout --quiet "$1"
  echo "=== diff vs $2 ($1) ==="
  if diff -ru "${EXCLUDES[@]}" ref "$OUT"; then
    echo "=== IDENTICAL vs $2 ==="
  else
    echo "=== DIFFERS vs $2 (see above) ==="
    return 1
  fi
}

# The in-tree copy: exactly the generated library, nothing else.
diff_in_tree() {
  echo "=== diff vs the in-tree copy ($REPO_ROOT/LeanRV64D) ==="
  if diff -ru "$REPO_ROOT/LeanRV64D" "$OUT/LeanRV64D" && diff -u "$REPO_ROOT/LeanRV64D.lean" "$OUT/LeanRV64D.lean"; then
    echo "=== IDENTICAL vs the in-tree copy ==="
  else
    echo "=== DIFFERS vs the in-tree copy (see above) ==="
    return 1
  fi
}

case "$MODE" in
  --stock)
    diff_against "$BASE_SNAPSHOT" "opencompl base" || verdict=1 ;;
  --sp1)
    # Four generated value sites vs the base are EXPECTED; identity vs the in-tree copy is the
    # gate (regeneration is idempotent).
    diff_against "$BASE_SNAPSHOT" "opencompl base (four value sites expected)" || true
    diff_in_tree || verdict=1 ;;
  --install)
    diff_against "$BASE_SNAPSHOT" "opencompl base (four value sites expected)" || true
    rm -rf "$REPO_ROOT/LeanRV64D"
    cp -R "$OUT/LeanRV64D" "$REPO_ROOT/LeanRV64D"
    cp "$OUT/LeanRV64D.lean" "$REPO_ROOT/LeanRV64D.lean"
    echo "=== INSTALLED the generated model into $REPO_ROOT (commit it; refresh scripts/provenance.json) ===" ;;
esac
echo "config sha256: $H1"
exit "$verdict"
