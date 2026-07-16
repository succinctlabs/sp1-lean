#!/usr/bin/env bash
# The reproducible audit harness behind `docs/release-audit.md` / `docs/snapshots/axiom-ledger.md`.
#
# Runs, in order: (A0) pin record, (A2) sorry/axiom text inventory with gates, (A3) the
# authoritative `#print axioms` census over the released theorem set (via
# `scripts/gen_axiom_probe.py` → `scripts/axiom_probe.lean`), writing the raw census to
# `docs/snapshots/axiom-census.txt` and gating that `sorryAx` is reachable only from the
# known-debt set. Run on a green tree (`lake build SP1Clean` first). Exit 0 = all gates pass.
#
# Usage: scripts/run_audit.sh   (from the repo root; ~3-5 min, dominated by the probe run)

set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

echo "== A0 pins =="
echo "sp1-lean:  $(git rev-parse HEAD)"
echo "toolchain: $(cat lean-toolchain)"
SP1_DIR="${SP1_DIR:-../sp1}"
echo "sp1:       $(git -C "$SP1_DIR" rev-parse HEAD) ($(git -C "$SP1_DIR" describe --tags 2>/dev/null), branch $(git -C "$SP1_DIR" branch --show-current))"
CLEAN_DIR="${CLEAN_DIR:-../clean}"
SAIL_RISCV_DIR="${SAIL_RISCV_DIR:-../sail-riscv-lean}"
RISCV_DIR="${RISCV_DIR:-../riscv-lean}"
LEAN_SAIL_DIR="${LEAN_SAIL_DIR:-../lean-sail}"
echo "Clean:     $(git -C "$CLEAN_DIR" rev-parse HEAD 2>/dev/null || echo '<missing>')"
echo "LeanRV64D: $(git -C "$SAIL_RISCV_DIR" rev-parse HEAD 2>/dev/null || echo '<missing>')"
echo "RISCV:     $(git -C "$RISCV_DIR" rev-parse HEAD 2>/dev/null || echo '<missing>')"
echo "Sail:      $(git -C "$LEAN_SAIL_DIR" rev-parse HEAD 2>/dev/null || echo '<missing>')"
echo "PolyFun:   $(git -C .lake/packages/PolyFun rev-parse HEAD 2>/dev/null || echo '<missing>')"

echo
echo "== A2 proof-deferral inventory (gate: exactly the known-debt set) =="
# The known direct proof-holes — both `sorry` and start-of-proof `stop` (`stop` discards the
# following tactic block and closes via `sorryAx`, so it is a deferral just like `sorry` and must
# be tracked here). Update this list (and the docs) when one is closed.
#   · SP1Ensemble        — `sp1_decoded_rows_sound` (structural typed-decode seam)
#   · Branch/Shift{Left,Right}Chip/Formal — completeness (Lean-4.30/4.31 `whnf` regression;
#     MulChip completeness was restored 2026-07-16 via the recorded normalization pattern)
#   · DivRemChip/Completeness/Driver — completeness (same blowup; `stop`)
#   · AIR                  — `supportedCore_orderedRows_dynamic` (the per-row dynamic grounding seam;
#     `supported_core_witness_grounding` and `supported_core_native_sound` are its proved consumers)
#   · DivRemChip/Formal — one explicit `evidenceSoundness` seam from the generated whole-chip
#     constraints to the isolated four-family evidence contract, plus the requirements-lawfulness
#     record field. The unused top-level State exposure was retired, closing its former structural
#     admission; the former nine per-op proofs were retired rather than retained as dead debt.
expected_sorries="$(cat <<'LIST'
SP1Clean/Proofs/Chips/ShiftLeftChip/Formal.lean
SP1Clean/Proofs/Chips/ShiftRightChip/Formal.lean
SP1Clean/Proofs/Chips/BranchChip/Formal.lean
SP1Clean/Proofs/Chips/DivRemChip/Completeness/Driver.lean
SP1Clean/Proofs/Chips/DivRemChip/Formal.lean
SP1Clean/Soundness/AIR.lean
SP1Clean/Soundness/SP1Ensemble.lean
LIST
)"
sorry_re='(^[[:space:]]*sorry[[:space:]]*$)|(:=[[:space:]]*sorry)|(=>[[:space:]]*sorry)|(^[[:space:]]*stop([[:space:]]|$))'
actual=$(grep -rlE "$sorry_re" SP1Clean --include='*.lean' | sort)
grep -rnE "$sorry_re" SP1Clean --include='*.lean'
n_exp=$(echo "$expected_sorries" | grep -c .)
if [ "$actual" = "$(echo "$expected_sorries" | sort)" ]; then
  echo "PASS: proof-deferral files = expected $n_exp (4 completeness + 1 DivRem contract file + 2 capstone seams)"
else
  echo "FAIL: proof-deferral inventory drifted from the documented set"; fail=1
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
echo "== A3 axiom census (the authoritative oracle) =="
python3 scripts/gen_axiom_probe.py || { echo "FAIL: probe generation"; exit 1; }
census=docs/snapshots/axiom-census.txt
{
  echo "# Raw #print axioms census — generated by scripts/run_audit.sh"
  echo "# sp1-lean $(git rev-parse HEAD) · $(date -u +%Y-%m-%d)"
  lake env lean scripts/axiom_probe.lean
} > "$census" 2>&1
if grep -q "error" "$census"; then
  echo "FAIL: probe elaboration errors:"; grep "error" "$census"; fail=1
fi

python3 - "$census" <<'EOF' || fail=1
import re, sys
text = open(sys.argv[1]).read()
entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
print(f"census entries: {len(entries)}")
# Declarations allowed to (transitively) carry sorryAx: the five deferred completeness proofs,
# DivRem's evidence/channel-law seams, the two machine-grounding seams, and the circuit/registry/
# capstone structures that embed or consume them.  `#print axioms` is intentionally structural:
# a `GeneralFormalCircuit` retains its completeness field even when a soundness theorem never
# projects that field.
#
# *** DIVREM WHOLE-CHIP CONFORMANCE. *** The obsolete 9-way per-op circuit proofs were retired.
# `DivRemChip.evidenceSoundness` is now the single stronger seam from the generated chip row to four
# isolated quotient/remainder evidence families; `contractSoundness` and public `soundness` are proved
# from that interface and inherit its sorryAx. This remains a genuine soundness gap, but its statement
# now exposes selection, edge cases, arithmetic evidence, and final output routing explicitly.
# *** STALE-SNAPSHOT RECONCILIATION (2026-07-12, C1/Move-2 audit run). *** Re-homing the decode globs to
# `Model/Semantics/Decode.lean` regenerated the census against the *current* tree for the first time since
# the 4.30 migration, surfacing two disclosed-debt carriers the previous (stale) snapshot never showed:
#   · `MulChip.completeness` — the 4.30 Mul-completeness stub (already in the A2 `expected_sorries` set; the
#     sibling of the already-allowed `DivRemChip.completeness`).
#   · `sp1_finishedChannel_guarantees` — a capstone-chain member (sibling of the already-allowed
#     balanced-trail ensemble) that consumes the chip soundness/completeness and so
#     inherits their sorryAx.
# Neither is a Move-2 regression: the decode redefinition + collapsed producers + hoists are verified
# axiom-clean (zero sorryAx). Both are consequences of the pre-existing Mul-completeness + DivRem-soundness
# stops; disclosed here and in the docs.
#
# The registry/coverage declarations below project from the single `supportedChips` descriptor.  That
# descriptor deliberately bundles each route with its `ChipKind` and Clean `Component`, so Lean's axiom
# dependency analysis sees the admitted DivRem circuit even in name/length projections.  This is
# transitive structure-field contamination, not an additional proof admission; retaining the unified
# descriptor prevents the circuit registry and routing census from drifting apart.
allowed = {
    "SP1Clean.DivRemChip.completeness",
    "SP1Clean.BranchChip.completeness", "SP1Clean.BranchChip.circuit",
    "SP1Clean.ShiftLeftChip.completeness", "SP1Clean.ShiftLeftChip.circuit",
    "SP1Clean.ShiftRightChip.completeness", "SP1Clean.ShiftRightChip.circuit",
    "SP1Clean.Soundness.sp1_finishedChannel_guarantees",
    # DivRem whole-chip evidence extraction seam + its public consequences:
    "SP1Clean.DivRemChip.evidenceSoundness", "SP1Clean.DivRemChip.contractSoundness",
    "SP1Clean.DivRemChip.soundness", "SP1Clean.DivRemChip.circuit",
    "SP1Clean.Soundness.sp1_decoded_rows_sound",
    "SP1Clean.Soundness.sp1_gatedExecution_prereqs",
    "SP1Clean.Soundness.sp1Tables", "SP1Clean.Soundness.sp1Tables_length",
    "SP1Clean.Soundness.sp1Ensemble", "SP1Clean.Soundness.sp1ProviderTables",
    "SP1Clean.Soundness.sp1ProviderTables_length",
    "SP1Clean.Soundness.balancedStateTrailFormalEnsemble",
    "SP1Clean.Soundness.balanced_state_trail_soundness",
    "SP1Clean.Soundness.supportedCore_orderedRows_dynamic",
    "SP1Clean.Soundness.supported_core_witness_grounding",
    "SP1Clean.Soundness.supported_core_native_sound",
    "SP1Clean.Soundness.Target.sp1_target_soundness",
    "SP1Clean.Soundness.allChipKinds", "SP1Clean.Soundness.allChipKinds_length",
    "SP1Clean.Soundness.allChipKinds_migrated",
    "SP1Clean.Soundness.covered_iff_routed",
    "SP1Clean.Soundness.reachable_subset_wired",
    "SP1Clean.Soundness.wired_subset_reachable",
    "SP1Clean.Soundness.coverage_kinds_eq_registry",
    "SP1Clean.Soundness.coverage_length",
}
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
print(f"PASS: sorryAx confined to the known-debt set "
      f"({sum(1 for f, a in entries if 'sorryAx' in a)} carriers, all allowed)")
EOF

echo
[ "$fail" -eq 0 ] && echo "== AUDIT PASS ==" || echo "== AUDIT FAIL =="
exit "$fail"
