#!/usr/bin/env bash
# Gate: no witness-generation escape hatches anywhere in the main `SP1Clean/` library.
#
# Clean's witness IR has exactly one non-exportable constructor — `WitgenIR.native`, an arbitrary
# Lean closure `ProverEnvironment F → Vector F m`. Its entry points (`witnessNative`,
# `witnessVectorNative`, the closure-valued hint inputs `UnconstrainedNative`/`UnconstrainedDepNative`,
# and raw `.witness m (.native …)` operation payloads) keep a circuit runnable in Lean but reject
# `#assert_exportable`/`#witgen_json`, so the witness generator can never be serialized for a proving
# backend. The witgen-cutover campaign removes every such site; this gate keeps them out afterwards.
#
# Scope is `SP1Clean/**/*.lean` only — `SP1CleanTest/`, `docs/`, and `scripts/` legitimately mention
# the tokens (conformance harness plumbing, prose, this script). The grep is token-targeted: a bare
# `\.native` would false-positive on "Clean-native" prose in doc-comments.
#
# Modes:
#   default    — report-only: prints any hits and the running total, always exits 0.
#                (The cutover waves use this to watch the count fall.)
#   --enforce  — blocking: any hit exits 1. Flipped on by `run_audit.sh` and the CI `guards`
#                job at cutover completion (wave W7).
#
# Usage: scripts/check_no_witness_native.sh [--enforce]   (from the repo root)

set -uo pipefail
cd "$(dirname "$0")/.."

ENFORCE=0
if [[ "${1:-}" == "--enforce" ]]; then
  ENFORCE=1
fi

PATTERN='witnessNative|witnessVectorNative|UnconstrainedNative|UnconstrainedDepNative|nativeValue|WitgenIR\.native|\.native[[:space:]]+fun|\.native[[:space:]]*\('

HITS=$(grep -rnE "$PATTERN" SP1Clean --include='*.lean' || true)

if [[ -z "$HITS" ]]; then
  echo "check_no_witness_native: clean (0 escape-hatch witness sites in SP1Clean/)."
  exit 0
fi

COUNT=$(printf '%s\n' "$HITS" | wc -l | tr -d ' ')
printf '%s\n' "$HITS"
if [[ "$ENFORCE" == "1" ]]; then
  echo "FAIL: $COUNT witness-generation escape-hatch site(s) found in SP1Clean/ (see lines above)." >&2
  echo "      The main library must stay on the exportable witness IR: witness / witnessProgram /" >&2
  echo "      witnessVectorProgram / witnessField / witnessVector with '.ir' payloads, and typed" >&2
  echo "      'Unconstrained*' (non-Native) hint inputs. Port the site per the recipe in" >&2
  echo "      docs/agents/porting-recipe.md instead of reintroducing a closure." >&2
  exit 1
fi
echo "check_no_witness_native (report-only): $COUNT escape-hatch witness site(s) remain in SP1Clean/."
exit 0
