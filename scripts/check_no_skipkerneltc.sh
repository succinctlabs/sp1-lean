#!/usr/bin/env bash
# Gate: no `set_option (debug.)skipKernelTC` anywhere in the Lean source tree.
#
# `skipKernelTC` bypasses the kernel's type-check re-run — the trust anchor for an
# axiom-clean proof. It was a last-resort escape used while proving the bit-shift chips;
# the last site was removed 2026-06-18 and replaced by abstract-`BitVec` helper bridges
# (see `docs/agents/proof-patterns.md` §"Bit-shift chip soundness", the `2^64` bullet).
# This gate keeps it out for good.
#
# Scope is `SP1Clean/**/*.lean` only — `docs/` legitimately *mentions* the token
# ("…NOT `skipKernelTC`"), so scanning the source tree avoids those false positives.
# There are zero legitimate uses in source, so any case-insensitive hit fails the gate.
#
# Used by `scripts/run_audit.sh` (A2 gate) and `.github/workflows/lean_action_ci.yml`
# (the lightweight `guards` job). Exit 0 = clean, 1 = reintroduced.
#
# Usage: scripts/check_no_skipkerneltc.sh   (from the repo root)

set -uo pipefail
cd "$(dirname "$0")/.."

if grep -rniE 'skipKernelTC' SP1Clean ToClean ToMathlib --include='*.lean' 2>/dev/null; then
  echo "FAIL: skipKernelTC reintroduced in SP1Clean/ (see lines above)." >&2
  echo "      Fix the kernel error by factoring the expensive compute into an abstract-BitVec" >&2
  echo "      helper proved once over variables (the srl_toNat/sra_toNat pattern) — do NOT" >&2
  echo "      bypass the kernel. See docs/agents/proof-patterns.md." >&2
  exit 1
fi
exit 0
