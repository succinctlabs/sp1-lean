#!/usr/bin/env bash
# The reproducible audit harness behind `docs/release-audit.md` / `docs/snapshots/axiom-ledger.md`.
#
# Runs, in order: (A0) pin record, (A1) recorded-pin cross-checks + root-index + report-citation
# gates, (A2) sorry/axiom text inventory with gates, (A3) the authoritative `#print axioms` census
# over the released theorem set (via `scripts/gen_axiom_probe.py`), split into two scopes so each
# probe elaborates against exactly the oleans its build target produces:
#   main — `scripts/axiom_probe.lean`      vs `docs/snapshots/axiom-census.txt`      (needs `lake build SP1Clean`)
#   test — `scripts/axiom_probe_test.lean` vs `docs/snapshots/axiom-census-test.txt` (needs `lake test`)
# Both scopes gate that no released declaration carries `sorryAx`; the main scope additionally
# gates that no compiler-trusted proof constant (native_decide) appears at all. Run on a green
# tree. Exit 0 = all gates pass, and the tree is left untouched.
#
# Usage: scripts/run_audit.sh              (repo root; both scopes; ~3-5 min, dominated by probes)
#        scripts/run_audit.sh --main-only  (A0-A2 + the main census; what the CI `audit` job runs —
#                                           no SP1CleanTest oleans required)
#        scripts/run_audit.sh --test-only  (just the test census; the CI `test` job runs this
#                                           after `lake test`)
#        scripts/run_audit.sh --update     (additionally rewrite the census snapshot(s) for the
#                                           scope(s) run — use after an intended census change,
#                                           then commit the diff)

set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
update=0
run_main=1
run_test=1
for arg in "$@"; do
  case "$arg" in
    --update) update=1 ;;
    --main-only) run_test=0 ;;
    --test-only) run_main=0 ;;
    *) echo "unknown flag: $arg (usage: run_audit.sh [--update] [--main-only|--test-only])"; exit 2 ;;
  esac
done

# A0-A2 are pin/source-policy gates over the main library; the test-only mode (the CI `test`
# job's census step) skips straight to its census scope.
if [ "$run_main" -eq 1 ]; then

echo "== A0 pins =="
echo "sp1-lean:  $(git rev-parse HEAD)"
echo "toolchain: $(cat lean-toolchain)"
# The dependency graph is fully determined by lake-manifest.json (every pin is an immutable git
# rev; scripts/check_pins.sh gates that below). Record it, and — when the package checkout is
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
if scripts/check_pins.sh; then
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
echo "== A1 report citations (gate) =="
if scripts/check_report_citations.sh; then
  :
else
  echo "FAIL: a documented citation does not resolve (see above)"; fail=1
fi

echo
echo "== A2 proof-deferral inventory (gate: none) =="
# Both `sorry` and start-of-proof `stop` introduce `sorryAx`; neither is permitted in the main
# library. Conditional theorem hypotheses and relation parameters are audited at the statement
# boundary instead of being disguised as proof deferrals.
sorry_re='(^[[:space:]]*sorry[[:space:]]*$)|(:=[[:space:]]*sorry)|(=>[[:space:]]*sorry)|(^[[:space:]]*stop([[:space:]]|$))'
actual=$(grep -rlE "$sorry_re" SP1Clean --include='*.lean' | sort)
grep -rnE "$sorry_re" SP1Clean --include='*.lean'
if [ -z "$actual" ]; then
  echo "PASS: no proof deferrals"
else
  echo "FAIL: proof deferral(s) found"; fail=1
fi

echo
echo "== A2 axiom declarations (gate: none in SP1Clean/) =="
if grep -rnE '^[[:space:]]*axiom[[:space:]]' SP1Clean --include='*.lean'; then
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
echo "native_decide occurrences in SP1CleanTest/ (disclosed — the witness/trace conformance battery,"
echo "the sole sanctioned native_decide; trusts the compiler via generated ._native.native_decide.ax_* constants, confined off the main library):"
grep -rn 'native_decide' SP1CleanTest --include='*.lean' | wc -l

echo
echo "== A2 elaboration-budget escape-hatch gate (allowlist, not a budget) =="
if scripts/check_option_escapes.sh; then
  echo "PASS: every maxHeartbeats/maxRecDepth site is allowlisted with a measured ladder"
else
  echo "FAIL: unlisted or raised elaboration-budget override — fold instead (see above)"; fail=1
fi

fi  # run_main (A0-A2)

echo
echo "== A3 axiom census (the authoritative oracle) =="
python3 scripts/gen_axiom_probe.py || { echo "FAIL: probe generation"; exit 1; }

# One census scope: elaborate a probe file, gate its entries, diff against its committed
# snapshot ignoring only the two `#`-comment header lines (commit stamp + date). A pass leaves
# the tree untouched; a drift is a FAIL unless --update. With --update the fresh census (and
# its current-commit stamp) is always installed — a content-identical restamp is hygienic and
# records the verifying commit.
census_scope() {
  local scope="$1" probe="$2" census="$3"
  echo
  echo "-- census scope: $scope ($probe vs $census) --"
  local fresh
  fresh=$(mktemp)
  {
    echo "# Raw #print axioms census ($scope scope) — generated by scripts/run_audit.sh"
    echo "# sp1-lean $(git rev-parse HEAD) · $(date -u +%Y-%m-%d)"
    lake env lean "$probe"
  } > "$fresh" 2>&1
  if grep -q "error" "$fresh"; then
    echo "FAIL: probe elaboration errors:"; grep "error" "$fresh"; fail=1
  fi

  python3 - "$fresh" "$probe" "$scope" <<'EOF' || fail=1
import re, sys
text = open(sys.argv[1]).read()
probe, scope = sys.argv[2], sys.argv[3]
entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
print(f"census entries ({scope}): {len(entries)}")
expected = sum(1 for line in open(probe) if line.startswith("#print axioms "))
if len(entries) != expected:
    print(f"FAIL: parsed {len(entries)} census entries for {expected} generated probes")
    sys.exit(1)
buckets = {}
for fqn, axs in entries:
    key = frozenset(a.strip() for a in axs.split(",") if a.strip())
    buckets.setdefault(key, []).append(fqn)
print("bucket sizes:")
for key, fqns in sorted(buckets.items(), key=lambda kv: -len(kv[1])):
    print(f"  [{len(fqns):3}] {{{', '.join(sorted(key))}}}")
bad = [f for f, axs in entries if "sorryAx" in axs]
if bad:
    print("FAIL: unexpected sorryAx carriers:", *bad, sep="\n  "); sys.exit(1)
print("PASS: no probed declaration carries sorryAx")
compiler_trust = [
    fqn for fqn, axioms in entries
    if ("native_decide" in axioms or "Lean.ofReduceBool" in axioms or
        "Lean.trustCompiler" in axioms)
]
if scope == "main":
    # The main library carries no native_decide at all (CI-gated at the source level too);
    # a compiler-trusted constant here means the quarantine failed.
    if compiler_trust:
        print("FAIL: compiler-trusted proof constants escaped into the main library:",
              *compiler_trust, sep="\n  ")
        sys.exit(1)
    print("PASS: no compiler-trusted proof constant in the main-library census")
else:
    # The test scope exists to DISCLOSE the compiler-trusted anchors, not to forbid them.
    print(f"disclosed: {len(compiler_trust)}/{len(entries)} test anchors carry "
          "compiler-trust axioms (native_decide)")
    trusted = set(compiler_trust)
    for fqn, _ in entries:
        if fqn not in trusted:
            print(f"  note: {fqn} carries no compiler-trust axiom (proved without native_decide)")
EOF

  if [ ! -f "$census" ]; then
    if [ "$update" -eq 1 ]; then
      cp "$fresh" "$census"
      echo "UPDATED: $census created from this run — inspect and commit"
    else
      echo "FAIL: committed snapshot $census does not exist (run with --update to create it)"
      fail=1
    fi
    rm -f "$fresh"
    return
  fi
  if diff -q <(grep -v '^#' "$census") <(grep -v '^#' "$fresh") >/dev/null 2>&1; then
    echo "PASS: census matches the committed snapshot ($census)"
    if [ "$update" -eq 1 ]; then
      cp "$fresh" "$census"
      echo "UPDATED: $census restamped from this run (content unchanged)"
    fi
  else
    if [ "$update" -eq 1 ]; then
      cp "$fresh" "$census"
      echo "UPDATED: $census rewritten from this run — inspect and commit the diff"
    else
      echo "FAIL: census drifted from the committed snapshot:"
      diff <(grep -v '^#' "$census") <(grep -v '^#' "$fresh") | head -40
      echo "(inspect the drift; if intended, rerun with --update and commit)"
      fail=1
    fi
  fi
  rm -f "$fresh"
}

if [ "$run_main" -eq 1 ]; then
  census_scope "main" scripts/axiom_probe.lean docs/snapshots/axiom-census.txt
fi
if [ "$run_test" -eq 1 ]; then
  census_scope "test" scripts/axiom_probe_test.lean docs/snapshots/axiom-census-test.txt
fi

echo
[ "$fail" -eq 0 ] && echo "== AUDIT PASS ==" || echo "== AUDIT FAIL =="
exit "$fail"
