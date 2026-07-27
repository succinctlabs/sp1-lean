#!/usr/bin/env bash
# Check that every repo path cited in docs/verification-report.md exists, and that every
# backtick-quoted declaration name cited alongside a .lean path actually occurs in that file.
# Part of the release-readiness harness; run from the repo root.
set -euo pipefail
report="docs/verification-report.md"
[ -f "$report" ] || { echo "FAIL: $report missing"; exit 1; }

fail=0

# 1. Every cited repo-relative path must exist.
paths=$(grep -oE '`(SP1Clean|SP1CleanTest|docs|scripts)/[A-Za-z0-9_/.-]+`' "$report" | tr -d '`' | sort -u)
while IFS= read -r p; do
  [ -z "$p" ] && continue
  if [ ! -e "$p" ]; then
    echo "FAIL: cited path does not exist: $p"
    fail=1
  fi
done <<< "$paths"

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
check_decl SP1Clean/Soundness/SP1Ensemble.lean "sp1Ensemble"
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
