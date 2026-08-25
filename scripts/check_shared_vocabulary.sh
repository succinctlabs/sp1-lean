#!/usr/bin/env bash
# Keep the relation vocabulary genuinely shared across soundness and completeness.

set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

check_owner() {
  local name="$1"
  local owner="$2"
  local hits
  hits="$(rg -l "^[[:space:]]*(abbrev|def|structure|inductive)[[:space:]]+${name}([[:space:]{(:]|$)" \
    SP1Clean SP1CleanTest -g '*.lean' || true)"
  if [[ "$hits" != "$owner" ]]; then
    echo "FAIL: $name must be declared only in $owner"
    if [[ -n "$hits" ]]; then
      echo "$hits"
    else
      echo "no declaration found"
    fi
    fail=1
  fi
}

check_absent() {
  local name="$1"
  local hits
  hits="$(rg -n "^[[:space:]]*(abbrev|def|structure|inductive)[[:space:]]+${name}([[:space:]{(:]|$)" \
    SP1Clean SP1CleanTest -g '*.lean' || true)"
  if [[ -n "$hits" ]]; then
    echo "FAIL: retired duplicate declaration $name has returned"
    echo "$hits"
    fail=1
  fi
}

check_owner SupportedCoreStatement SP1Clean/FormalModel/Execution.lean
check_owner ConfiguredDecode SP1Clean/Model/Semantics/GuestProgram.lean
check_owner WithinOrdinaryRowLimit SP1Clean/FormalModel/CoreProfile.lean
check_owner SP1TransitionView SP1Clean/Model/Semantics/TransitionView.lean
check_owner SupportedSP1Transition SP1Clean/FormalModel/SupportedShard.lean
check_owner SyscallMsg SP1Clean/Model/BusMessages.lean

check_absent SupportedOrdinaryShardStatement
check_absent ConfiguredDecodeStable
check_absent WithinCoreShardLimit
check_absent WithinCoreNativeRowLimit
check_absent SupportedDecodedTransition
check_absent syscallCoreInteractions
check_absent memoryLocalInteractions

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "Shared vocabulary OK: statement, decode, transition, syscall message, support, and capacity each have one owner"
