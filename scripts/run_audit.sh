#!/usr/bin/env bash
# The reproducible audit harness behind `docs/release-audit.md` / `docs/snapshots/axiom-ledger.md`.
#
# Runs, in order: (A0) pin record, (A1) recorded-pin cross-checks + root-index + report-citation
# gates, (A2) sorry/axiom text inventory with gates, (A3) the authoritative `#print axioms` census
# over the released theorem set (via `scripts/gen_axiom_probe.py` → `scripts/axiom_probe.lean`),
# compared against the committed `docs/snapshots/axiom-census.txt` and gating that no released
# declaration carries `sorryAx`. Run on a green tree (`lake build SP1Clean` first). Exit 0 = all
# gates pass, and the tree is left untouched.
#
# Usage: scripts/run_audit.sh            (from the repo root; ~3-5 min, dominated by the probe run)
#        scripts/run_audit.sh --update   (additionally rewrite docs/snapshots/axiom-census.txt —
#                                         use after an intended census change, then commit the diff)

set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
update=0
[ "${1:-}" = "--update" ] && update=1

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
echo "the sole sanctioned native_decide; adds Lean.ofReduceBool/trustCompiler, confined off the main library):"
grep -rn 'native_decide' SP1CleanTest --include='*.lean' | wc -l

echo
echo "== A2 elaboration-budget escape-hatch gate (allowlist, not a budget) =="
if scripts/check_option_escapes.sh; then
  echo "PASS: every maxHeartbeats/maxRecDepth site is allowlisted with a measured ladder"
else
  echo "FAIL: unlisted or raised elaboration-budget override — fold instead (see above)"; fail=1
fi

echo
echo "== A3 axiom census (the authoritative oracle) =="
python3 scripts/gen_axiom_probe.py || { echo "FAIL: probe generation"; exit 1; }
census=docs/snapshots/axiom-census.txt
fresh=$(mktemp)
{
  echo "# Raw #print axioms census — generated by scripts/run_audit.sh"
  echo "# sp1-lean $(git rev-parse HEAD) · $(date -u +%Y-%m-%d)"
  lake env lean scripts/axiom_probe.lean
} > "$fresh" 2>&1
if grep -q "error" "$fresh"; then
  echo "FAIL: probe elaboration errors:"; grep "error" "$fresh"; fail=1
fi

python3 - "$fresh" <<'EOF' || fail=1
import re, sys
text = open(sys.argv[1]).read()
entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
print(f"census entries: {len(entries)}")
expected = sum(
    1 for line in open("scripts/axiom_probe.lean")
    if line.startswith("#print axioms ")
)
if len(entries) != expected:
    print(f"FAIL: parsed {len(entries)} census entries for {expected} generated probes")
    sys.exit(1)
allowed = set()
bad = [f for f, axs in entries if "sorryAx" in axs and f not in allowed]
buckets = {}
for fqn, axs in entries:
    key = frozenset(a.strip() for a in axs.split(",") if a.strip())
    buckets.setdefault(key, []).append(fqn)
print("bucket sizes:")
for key, fqns in sorted(buckets.items(), key=lambda kv: -len(kv[1])):
    print(f"  [{len(fqns):3}] {{{', '.join(sorted(key))}}}")
if bad:
    print("FAIL: unexpected sorryAx carriers:", *bad, sep="\n  "); sys.exit(1)
count = sum(1 for _, axioms in entries if "sorryAx" in axioms)
if count:
    print(f"FAIL: {count} probed declaration(s) still carry sorryAx"); sys.exit(1)
main_compiler_trust = [
    fqn for fqn, axioms in entries
    if ("native_decide" in axioms or "Lean.ofReduceBool" in axioms or
        "Lean.trustCompiler" in axioms)
    and not (fqn.startswith("SP1Clean.WitnessTests.") or
             fqn.startswith("SP1Clean.TraceGenTests."))
]
if main_compiler_trust:
    print("FAIL: compiler-trusted proof constants escaped the test library:",
          *main_compiler_trust, sep="\n  ")
    sys.exit(1)
print("PASS: no probed declaration carries sorryAx")
print("PASS: compiler-trusted proof constants are confined to SP1CleanTest")
EOF

# Compare against the committed snapshot, ignoring only the two `#`-comment header lines
# (commit stamp + date). A pass leaves the tree untouched; a drift is a FAIL unless --update.
# With --update the fresh census (and its current-commit stamp) is always installed — a
# content-identical restamp is hygienic and records the verifying commit.
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

echo
[ "$fail" -eq 0 ] && echo "== AUDIT PASS ==" || echo "== AUDIT FAIL =="
exit "$fail"
