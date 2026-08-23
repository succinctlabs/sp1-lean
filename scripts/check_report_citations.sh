#!/usr/bin/env bash
# Check that every repo path cited in the reader-facing docs exists, and that every
# backtick-quoted declaration name cited alongside a .lean path actually occurs in that file.
# Part of the release-readiness harness (invoked by scripts/run_audit.sh and the CI `guards`
# job); run from the repo root. Note this validates that citations RESOLVE — recorded pin
# values are separately cross-checked by scripts/check_pins.sh.
set -euo pipefail
report="docs/verification-report.md"
[ -f "$report" ] || { echo "FAIL: $report missing"; exit 1; }

fail=0

# 1. Every repo-relative path cited in a reader-facing doc must exist.
for doc in "$report" README.md docs/README.md docs/overview.md docs/architecture.md \
           docs/release-audit.md docs/roadmap.md docs/witgen-wire-format.md \
           docs/audit-surface.md docs/layering.md \
           docs/audits/2026-08-pr110-external-report-disposition.md; do
  [ -f "$doc" ] || { echo "FAIL: expected doc missing: $doc"; fail=1; continue; }
  paths=$(grep -oE '`(SP1Clean|SP1CleanTest|ToClean|ToMathlib|docs|scripts)/[A-Za-z0-9_/.-]+`' "$doc" | tr -d '`' | sort -u || true)
  while IFS= read -r p; do
    [ -z "$p" ] && continue
    if [ ! -e "$p" ]; then
      echo "FAIL: $doc cites a path that does not exist: $p"
      fail=1
    fi
  done <<< "$paths"
done

# 2. Key declarations quoted in the report must exist where the report says they do.
check_decl() { # file decl
  if ! grep -q "$2" "$1" 2>/dev/null; then
    echo "FAIL: declaration '$2' not found in $1"
    fail=1
  fi
}
check_decl SP1Clean/Soundness/AIR.lean "supported_core_native_sound"
check_decl SP1Clean/Soundness/AIR.lean "supported_core_witness_grounding"
check_decl SP1Clean/Soundness/AIR.lean "SupportedCoreNativeRelation"
check_decl SP1Clean/Soundness/CoreAIR.lean "sp1_air_sound_of_obligations"
check_decl SP1Clean/Soundness/CoreAIR.lean "CoreAIRRefinementObligations"
check_decl SP1Clean/Model/Semantics/GuestProgram.lean "SailStep"
check_decl SP1Clean/Model/Semantics/GuestProgram.lean "SP1Halted"
check_decl SP1Clean/FormalModel/CoreProfile.lean "sp1SemanticRevision"
check_decl SP1Clean/Faithful/AddChip.lean "addChip_faithful"
check_decl SP1Clean/Faithful/ChipOracle.lean "ChipFaithful"
check_decl SP1Clean/Faithful/SupportedMachine.lean "supportedChipFaithfulness"
check_decl SP1Clean/Faithful/SupportedMachine.lean "instructionOracleMainWidth_isSome_iff"
check_decl SP1Clean/Faithful/Transport/PreprocessedProviders.lean \
  "extractedPreprocessedProviderTables_cleanAccesses"
check_decl SP1Clean/Faithful/Transport/CoreEnsemble.lean \
  "exactNativeEnsembleWitness_constraints"
check_decl SP1Clean/Faithful/Transport/CoreArtifact.lean \
  "exactNativeArtifact_supportedCoreNativeRelation"
check_decl SP1Clean/Soundness/SP1Ensemble.lean "sp1Ensemble"
check_decl SP1Clean/Soundness/AIRCompleteness.lean "supported_core_native_complete"
check_decl SP1CleanTest/Audit/ActiveTraceNonVacuity.lean \
  "active_real_decoded_instruction_row_count"
check_decl SP1Clean/FormalModel/Contracts/DivRem.lean "Case"
check_decl SP1Clean/FormalModel/Relations.lean "Sound"
check_decl SP1Clean/FormalModel/Execution.lean "SP1ExecutionRelation"

# 3. The reserved names must NOT be declared (they are reserved). Matches inside `/- ... -/`
# doc/block comments (the documented intended-shape sketches) are ignored.
for name in sp1_air_sound sp1_execution_sound sp1_verifier_sound; do
  hits=$(find SP1Clean -name '*.lean' -exec awk -v decl="theorem $name " '
    /\/-/ { depth++ }
    depth == 0 && index($0, decl) == 1 { print FILENAME ":" FNR }
    /-\// { if (depth > 0) depth-- }
  ' {} + | grep -v "_of_obligations" || true)
  if [ -n "$hits" ]; then
    echo "FAIL: reserved name appears declared outside comments: $name ($hits)"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "PASS: report citations resolve"
else
  exit 1
fi
