#!/usr/bin/env bash
# Gate: no `native_decide` anywhere in the main `SP1Clean/` library.
#
# `native_decide` discharges a goal by running compiled code, so it trusts the **entire Lean
# compiler** (surfaced in the census as generated `._native.native_decide.ax_*` compiler-trust
# constants — formerly the named `Lean.ofReduceBool`/`Lean.trustCompiler` axioms) rather than just the
# kernel — the same reason mathlib bans it from its main library. No released theorem may acquire
# compiler-trust constants this way: pure chip/AIR theorems normally retain only the logical
# baseline, while Sail-facing capstones separately disclose their generated platform-hook and
# `bv_decide` footprint. `native_decide` is confined to the top-level `SP1CleanTest` test library,
# which imports `SP1Clean` but is never imported by it.
#
# Scope is every released main source library: `SP1Clean/`, `ToClean/`, and `ToMathlib/`.
# `SP1CleanTest/` is the sanctioned home, while `docs/` and `scripts/` legitimately mention the
# token. There are zero legitimate main-library uses, so any case-insensitive hit fails the gate.
#
# Used by `scripts/run_audit.sh` (A2 gate) and `.github/workflows/lean_action_ci.yml`
# (the lightweight `guards` job). Exit 0 = clean, 1 = reintroduced.
#
# Usage: scripts/check_no_native_decide.sh   (from the repo root)

set -uo pipefail
cd "$(dirname "$0")/.."

if grep -rniE 'native_decide' SP1Clean ToClean ToMathlib --include='*.lean' 2>/dev/null; then
  echo "FAIL: native_decide found in a released main source library (see lines above)." >&2
  echo "      native_decide trusts the whole compiler (generated ._native compiler-trust constants) — it must not appear" >&2
  echo "      in the main library. Move the check into the SP1CleanTest test library (run by" >&2
  echo "      'lake test'), or prove the goal in the kernel (decide / a real proof) instead." >&2
  exit 1
fi
exit 0
