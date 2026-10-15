#!/usr/bin/env bash
# Reproduce the release audit against current built library oleans.
# Pin/source/model gates run in the main scope. Compiled-library trust policy runs in
# both scopes; detailed reports go only to .lake/build/trust/, never tracked snapshots.
# Usage: scripts/run_audit.sh [--main-only|--test-only]
# Build SP1Clean/To* before main, and SP1CleanTest before test. The no-flag default runs both.

set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
run_main=1
run_test=1
for arg in "$@"; do
  case "$arg" in
    --update)
      echo "--update is retired: trust reports are build artifacts, not committed snapshots." >&2
      echo "Review explicit trust-policy changes in scripts/trust_policy.json; no auto-approval is available." >&2
      exit 2 ;;
    --main-only) run_test=0 ;;
    --test-only) run_main=0 ;;
    *) echo "unknown flag: $arg (usage: run_audit.sh [--main-only|--test-only])"; exit 2 ;;
  esac
done
if [ "$run_main" -eq 0 ] && [ "$run_test" -eq 0 ]; then
  echo "--main-only and --test-only cannot be combined"
  exit 2
fi

if [ "$run_main" -eq 1 ]; then

echo "== A0 pins =="
echo "sp1-lean:  $(git rev-parse HEAD)"
echo "toolchain: $(cat lean-toolchain)"
# The dependency graph is fully determined by lake-manifest.json (every pin is an immutable git
# rev; scripts/check_pins.py gates that below). Record it, and — when the package checkout is
# present — gate that what is on disk is what the manifest says.
python3 - <<'EOF' || fail=1
import json, subprocess, sys
ok = True
for p in json.load(open("lake-manifest.json"))["packages"]:
    if p.get("inherited", False):
        continue
    name, rev = p["name"], p.get("rev", "<none>")
    line = f"{name + ':':11}{rev}"
    try:
        head = subprocess.run(["git", "-C", f".lake/packages/{name}", "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True).stdout.strip()
        if head != rev:
            line += f"  MISMATCH: .lake checkout at {head}"
            ok = False
    except Exception:
        line += "  (not checked out)"
    print(line)
if not ok:
    print("FAIL: a .lake package checkout disagrees with lake-manifest.json")
    sys.exit(1)
EOF
# Optional context: the SP1 semantic checkout, when present as a sibling (informational only —
# the audited semantic revision itself is pinned in SP1Clean/FormalModel/CoreProfile.lean).
SP1_DIR="${SP1_DIR:-../sp1}"
if git -C "$SP1_DIR" rev-parse HEAD >/dev/null 2>&1; then
  echo "sp1 (informational): $(git -C "$SP1_DIR" rev-parse HEAD) ($(git -C "$SP1_DIR" describe --tags 2>/dev/null), branch $(git -C "$SP1_DIR" branch --show-current))"
fi

echo
echo "== A1 recorded-pin cross-checks (gate) =="
if scripts/check_pins.py; then
  :
else
  echo "FAIL: a recorded pin value disagrees with the build graph (see above)"; fail=1
fi

echo
echo "== A1 root-index completeness (gate) =="
if scripts/check_root_index.sh; then
  :
else
  echo "FAIL: SP1Clean.lean is out of sync with the modules on disk (see above)"; fail=1
fi

echo
echo "== A1 maintained documentation (gate) =="
if python3 scripts/check_current_docs.py; then
  :
else
  echo "FAIL: maintained documentation or module docstrings drifted (see above)"; fail=1
fi

echo
echo "== A1 layering contract (gate) =="
if scripts/check_layering.sh; then
  :
else
  echo "FAIL: the layering contract is violated (see above)"; fail=1
fi

echo
echo "== A1 SP1 field singleton (gate) =="
if scripts/check_sp1_field_singleton.sh; then
  :
else
  echo "FAIL: SP1's concrete field has more than one Lean owner"; fail=1
fi

echo
echo "== A1 shared relation vocabulary (gate) =="
if scripts/check_shared_vocabulary.sh; then
  :
else
  echo "FAIL: soundness/completeness vocabulary has duplicate owners"; fail=1
fi

echo
echo "== A1 25-chip release surface (gate) =="
if python3 scripts/check_release_surface.py; then
  :
else
  echo "FAIL: the instruction-chip audit inventory is incomplete (see above)"; fail=1
fi

echo
echo "== A1 compiled capstone contract (gate) =="
# This harness requires current library oleans. Trust-policy compliance does not establish
# the intended theorem statement: review semantic-contract changes separately.
if python3 scripts/check_capstone_contract.py --no-build; then
  :
else
  echo "FAIL: capstone target type or definition dependencies changed"; fail=1
fi

echo
echo "== A2 proof-deferral inventory (gate: none) =="
# Both `sorry` and start-of-proof `stop` introduce `sorryAx`; neither is permitted in the main
# library. Conditional theorem hypotheses and relation parameters are audited at the statement
# boundary instead of being disguised as proof deferrals.
sorry_re='(^[[:space:]]*sorry[[:space:]]*$)|(:=[[:space:]]*sorry)|(=>[[:space:]]*sorry)|(^[[:space:]]*stop([[:space:]]|$))'
actual=$(grep -rlE "$sorry_re" SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest --include='*.lean' | sort)
grep -rnE "$sorry_re" SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest --include='*.lean'
if [ -z "$actual" ]; then
  echo "PASS: no proof deferrals"
else
  echo "FAIL: proof deferral(s) found"; fail=1
fi

echo
echo "== A2 axiom declarations (gate: none in project proof/test libraries) =="
if grep -rnE '^[[:space:]]*axiom[[:space:]]' SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest --include='*.lean'; then
  echo "FAIL: unexpected axiom declaration(s) above"; fail=1
else
  echo "PASS: no axiom declarations"
fi

echo
echo "== A2 skipKernelTC guard (gate: none in SP1Clean/) =="
if scripts/check_no_skipkerneltc.sh; then
  echo "PASS: no skipKernelTC usage"
else
  echo "FAIL: skipKernelTC reintroduced (see above)"; fail=1
fi

echo
echo "== A2 native_decide guard (gate: none in SP1Clean/) =="
if scripts/check_no_native_decide.sh; then
  echo "PASS: no native_decide in the main library"
else
  echo "FAIL: native_decide in SP1Clean/ (see above)"; fail=1
fi

echo
echo "== A2 witness-generation escape-hatch gate (enforced — the witgen cutover is complete) =="
if scripts/check_no_witness_native.sh --enforce | tail -1; then
  :
else
  echo "FAIL: witness-generation escape hatch reintroduced"
  fail=1
fi

echo
echo "== A2 independent SP1 witness inputs (gate) =="
# The full CI phase separately generates native artifacts and runs their Rust comparison.
if python3 scripts/check_witgen_export.py --source-only; then
  :
else
  echo "FAIL: independent SP1 witness inputs are invalid (see above)"; fail=1
fi

echo
echo "== A2 elaboration-budget escape-hatch gate (allowlist, not a budget) =="
if scripts/check_option_escapes.sh; then
  echo "PASS: every maxHeartbeats/maxRecDepth site is allowlisted with a measured ladder"
else
  echo "FAIL: unlisted or raised elaboration-budget override — fold instead (see above)"; fail=1
fi

fi  # run_main (A0-A2)

echo
echo "== A3 compiled-library trust policy =="
if [ "$run_main" -eq 1 ]; then
  python3 scripts/check_trust.py --scope main || fail=1
fi
if [ "$run_test" -eq 1 ]; then
  python3 scripts/check_release_surface.py --native || fail=1
  python3 scripts/check_trust.py --scope test || fail=1
fi

echo
[ "$fail" -eq 0 ] && echo "== AUDIT PASS ==" || echo "== AUDIT FAIL =="
exit "$fail"
