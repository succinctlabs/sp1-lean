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
    echo "FAIL: retired direction-specific declaration $name has returned"
    echo "$hits"
    fail=1
  fi
}

check_owner SupportedCoreStatement SP1Clean/FormalModel/Execution.lean
check_owner ConfiguredDecode SP1Clean/Model/Semantics/GuestProgram.lean
check_owner WithinOrdinaryRowLimit SP1Clean/FormalModel/CoreProfile.lean

check_absent SupportedOrdinaryShardStatement
check_absent ConfiguredDecodeStable
check_absent WithinCoreShardLimit
check_absent WithinCoreNativeRowLimit

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "Shared vocabulary OK: statement, decode, and capacity each have one owner"
