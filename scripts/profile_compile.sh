#!/usr/bin/env bash
#
# profile_compile.sh — rank every hand-written module by its isolated elaboration cost.
#
# Method: after one warm `lake build` (so every dependency is a cached .olean), run
#   lean -Dprofiler=true -Dprofiler.threshold=50 [package flags] <file>
# on each module. Because deps load from cache, this isolates that file's own elaboration
# cost. We time it with /usr/bin/time -p — CPU (`user` + `sys`, the primary number: Lean
# elaborates proof bodies on parallel threads, so wall under-counts them) and wall — and capture
# the profiler breakdown to a per-file log, then scripts/profile_aggregate.py turns the logs into
# a ranking plus a per-category and per-pillar cost split (import, elaboration, simp, tactic
# execution, type checking, typeclass inference, interpretation, compilation, linting, ...).
#
# Caveats baked in:
#   - Lean can exit 0 on a stack overflow. Check diagnostics and the final profiler report as
#     well as the exit code; fail the sweep if any measurement is incomplete or unsuccessful.
#   - Runs sequentially: clean wall-clock numbers, and respects the repo's build-concurrency cap.
#   - A warm full build must precede the sweep, or early files pay to build their deps.
#   - `lake env` only sets environment variables; it applies neither `moreLeanArgs` nor the
#     package's `[leanOptions]`. The sweep therefore passes the package flags itself, read from
#     lakefile.toml by `scripts/lean_flags.py` (package options, plus a library's own for the
#     test and generated-model trees), so they cannot drift from the build.
#   - The Lake environment is captured once (`lake env` with no command) and `lean` is invoked
#     directly, so per-module wall time is Lean alone, without ~1 s of Lake startup per file.
#   - Numbers are per-module wall time of one `lean` process. Lean elaborates proof bodies
#     asynchronously, so the profiler's `blocked (unaccounted)` category is time the main thread
#     waited for those tasks; read it together with `simp`/`tactic execution`/`type checking`.
#     For a real parallel build's per-module times, feed its log to
#     `scripts/profile_aggregate.py --lake-log <log>` instead.
#
# Usage:
#   scripts/profile_compile.sh [PATH_PREFIX]
#     PATH_PREFIX  optional repo-relative path prefix to restrict the sweep
#                  (e.g. SP1Clean/Math/ or ToClean/).
#
# Env:
#   TREES=…        space-separated source trees to sweep
#                  (default: "SP1Clean ToClean ToMathlib ToPolyFun").
#                  Add SP1CleanTest to include the native_decide test library.
#   SKIP_BUILD=1   skip the warm build (use when the cache is already warm).
#   EXCLUDE_RE=…   optional grep -E pattern of module paths to skip.
#   OUTDIR=…       output directory (default .lake/profile, gitignored).
#   TOP=…          rows in the ranking tables (default 50).
#
# Outputs (under $OUTDIR):
#   <module>.log         full -Dprofiler stdout+stderr for each module
#   summary.tsv          cpu<TAB>wall<TAB>exit<TAB>module, sorted by CPU (the offender ranking);
#                        exit is nonzero for process failures or rejected profiler output
#   summary.md           the ranking as a markdown table with a totals/failures footer
#   measurements.jsonl   one JSON-Lines record per module (archival)
#   profile.md           ranking + category totals + per-pillar split (from profile_aggregate.py)
#   profile.json         the same data, machine-readable

set -u
set -o pipefail

cd "$(dirname "$0")/.." || exit 1
ROOT="$(pwd)"
OUTDIR="${OUTDIR:-$ROOT/.lake/profile}"
PREFIX="${1:-}"
TREES="${TREES:-SP1Clean ToClean ToMathlib ToPolyFun}"
TOP="${TOP:-50}"

# Package-level lean args (lakefile.toml `moreLeanArgs` + `[leanOptions]`), applied to every
# module; the test and generated-model libraries add their own (`lean_flags.py --lib`).
pkg_flags="$(python3 "$ROOT/scripts/lean_flags.py" --shell)" || exit 1
test_flags="$(python3 "$ROOT/scripts/lean_flags.py" --lib SP1CleanTest --shell)" || exit 1
model_flags="$(python3 "$ROOT/scripts/lean_flags.py" --lib LeanRV64D --shell)" || exit 1
PACKAGE_FLAGS=($pkg_flags); TEST_FLAGS=($test_flags); MODEL_FLAGS=($model_flags)

mkdir -p "$OUTDIR"
: > "$OUTDIR/summary.tsv"
: > "$OUTDIR/measurements.jsonl"

# 1. Warm the olean cache. Abort the sweep if the build is broken — profiling a non-building
#    tree measures error-recovery, not steady-state elaboration. The default Lake target is
#    only the core, so warm the full library. Run solo; never stop another process here.
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo ">>> Warming cache: strict full build"
  if ! lake build --wfail --iofail SP1Clean SP1CleanTest ToClean ToMathlib ToPolyFun; then
    echo "!!! warm build failed — fix the build before profiling. Aborting." >&2
    exit 1
  fi
else
  echo ">>> SKIP_BUILD=1: assuming cache is warm"
fi

# 1b. Capture the Lake environment once (LEAN_PATH etc.) so each module runs `lean` directly.
lake_env="$(lake env)" || exit 1
while IFS= read -r line; do
  case "$line" in [A-Za-z_]*=*) export "$line" ;; esac
done <<< "$lake_env"
LEAN_BIN="${LEAN:-lean}"
command -v "$LEAN_BIN" >/dev/null 2>&1 || LEAN_BIN="$(lake env which lean 2>/dev/null || echo lean)"
echo ">>> lean: $("$LEAN_BIN" --version 2>/dev/null | head -1)"

# 2. Enumerate modules (deterministic order), optionally scoped by path prefix.
#    bash 3.2 has no `mapfile`, so stream from a temp list and count up front.
LISTFILE="$(mktemp)"
trap 'rm -f "$LISTFILE" "$LISTFILE.f"' EXIT
for tree in $TREES; do
  [ -d "$tree" ] && find "$tree" -name '*.lean'
done | sort > "$LISTFILE"
if [ -n "$PREFIX" ]; then
  grep "^$PREFIX" "$LISTFILE" > "$LISTFILE.f"; mv "$LISTFILE.f" "$LISTFILE"
fi
if [ -n "${EXCLUDE_RE:-}" ]; then
  grep -Ev "$EXCLUDE_RE" "$LISTFILE" > "$LISTFILE.f"; mv "$LISTFILE.f" "$LISTFILE"
fi
TOTAL="$(wc -l < "$LISTFILE" | tr -d ' ')"
if [ "$TOTAL" -eq 0 ]; then
  echo "!!! no modules selected (trees='$TREES' prefix='$PREFIX')" >&2
  exit 1
fi

echo ">>> Profiling ${TOTAL} modules (trees='${TREES}' prefix='${PREFIX}') -> $OUTDIR"
count=0
failed=0
while IFS= read -r f; do
  count=$((count + 1))

  # dotted module name, e.g. SP1Clean/Math/Word.lean -> SP1Clean.Math.Word
  module="${f%.lean}"
  module="${module//\//.}"
  log="$OUTDIR/${module}.log"
  timefile="$(mktemp)"

  # A library's own options replace the package's (Lake: the library wins on a key).
  case "$f" in
    SP1CleanTest/*) flags=("${TEST_FLAGS[@]}") ;;
    LeanRV64D/*|LeanRV64D.lean) flags=("${MODEL_FLAGS[@]}") ;;
    *) flags=("${PACKAGE_FLAGS[@]}") ;;
  esac

  printf '[%3d/%3d] %s ... ' "$count" "$TOTAL" "$module"

  # 3. Time the isolated elaboration. lean runs inside `sh -c` so ITS stdout+stderr (incl. the
  #    profiler breakdown) go to $log, while /usr/bin/time -p's own `real/user/sys` lines stay on
  #    the outer stderr -> $timefile. time -p exits with the wrapped command's status, so rc is
  #    lean's exit code. (Redirecting lean directly under time would capture time's output too.)
  /usr/bin/time -p sh -c \
    'log="$1"; lean="$2"; shift 2; "$lean" -Dprofiler=true -Dprofiler.threshold=50 "$@" > "$log" 2>&1' \
    _ "$log" "$LEAN_BIN" "${flags[@]}" "$f" 2> "$timefile"
  rc=$?
  if [ "$rc" -eq 0 ] && ! python3 "$ROOT/scripts/profile_aggregate.py" --check-log "$log"; then
    rc=1
  fi
  [ "$rc" -ne 0 ] && failed=1

  secs="$(awk '/^real/ {print $2}' "$timefile")"
  cpu="$(awk '/^user/ {u=$2} /^sys/ {s=$2} END {printf "%.2f", u + s}' "$timefile")"
  rm -f "$timefile"
  [ -z "$secs" ] && secs="0"
  [ -z "$cpu" ] && cpu="0"

  printf '%ss cpu, %ss wall (exit %d)\n' "$cpu" "$secs" "$rc"
  printf '%s\t%s\t%s\t%s\n' "$cpu" "$secs" "$rc" "$module" >> "$OUTDIR/summary.tsv"
  printf '{"metric": "compile//%s", "value": %s, "unit": "s", "wall": %s, "exit": %d}\n' \
    "$module" "$cpu" "$secs" "$rc" >> "$OUTDIR/measurements.jsonl"
done < "$LISTFILE"

# 4. Sort by CPU, slowest-first; that sorted file IS the canonical offender ranking.
sort -t$'\t' -k1,1 -rn "$OUTDIR/summary.tsv" -o "$OUTDIR/summary.tsv"

# 5. Render a markdown table + a totals/failures footer.
{
  echo "# Compile-time profile (isolated per module: CPU = user+sys, wall)"
  echo
  echo "| Rank | CPU s | Wall s | Exit | Module |"
  echo "| ---: | ---: | ---: | ---: | --- |"
  awk -F'\t' '{ printf "| %d | %.2f | %.2f | %d | \x60%s\x60 |\n", NR, $1, $2, $3, $4 }' "$OUTDIR/summary.tsv"
  echo
  awk -F'\t' '
    { total += $1; wall += $2; n++; if ($3 != 0) fails[$3"\t"$4]=1 }
    END {
      printf "**Total:** %.1fs CPU, %.1fs wall across %d modules (sequential; one lean per module).\n\n", total, wall, n
      nf = 0; for (k in fails) nf++
      if (nf > 0) {
        printf "**%d failed or incomplete measurement(s)** (see per-module logs):\n\n", nf
        for (k in fails) { split(k, a, "\t"); printf "- `%s` (exit %s)\n", a[2], a[1] }
      } else {
        print "All measurements completed without diagnostics."
      }
    }' "$OUTDIR/summary.tsv"
} > "$OUTDIR/summary.md"

# 6. Category and per-pillar split from the profiler logs.
python3 "$ROOT/scripts/profile_aggregate.py" --profile-dir "$OUTDIR" --top "$TOP" || exit 1

echo
echo ">>> Done. Ranking: $OUTDIR/summary.tsv  |  Split: $OUTDIR/profile.md  |  Logs: $OUTDIR/*.log"
echo ">>> Top 15:"
head -15 "$OUTDIR/summary.tsv" | awk -F'\t' '{ printf "  %7.2fs cpu %7.2fs wall  (exit %s)  %s\n", $1, $2, $3, $4 }'
exit "$failed"
