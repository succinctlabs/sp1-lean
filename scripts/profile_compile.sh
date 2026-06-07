#!/usr/bin/env bash
#
# profile_compile.sh — rank every SP1Clean module by wall-clock elaboration time.
#
# Method: after one warm `lake build` (so every dependency is a cached .olean), run
#   lake env lean -Dprofiler=true -Dprofiler.threshold=50 <file>
# on each module. Because deps load from cache, this isolates that file's own elaboration
# cost. We time it with /usr/bin/time -p and capture the profiler breakdown to a per-file log.
#
# Caveats baked in:
#   - `lake env lean` exits 0 even on a stack overflow, so we record exit codes explicitly and
#     surface any nonzero ones — a silent failure must not be misread as "fast".
#   - Runs sequentially: clean wall-clock numbers, and respects the repo's build-concurrency cap.
#   - A warm full build must precede the sweep, or early files pay to build their deps.
#
# Usage:
#   scripts/profile_compile.sh [PATH_PREFIX]
#     PATH_PREFIX  optional: only profile modules whose path starts with this (e.g. Operations/).
#
# Env:
#   SKIP_BUILD=1   skip the warm `lake build` (use when the cache is already warm).
#
# Outputs (under build/profile/):
#   <module>.log     full -Dprofiler stdout+stderr for each module
#   summary.tsv      seconds<TAB>exit<TAB>module, sorted slowest-first (the offender ranking)
#   summary.md       same data as a markdown table
#   measurements.jsonl   one JSON-Lines record per module (archival)

set -u
set -o pipefail

cd "$(dirname "$0")/.." || exit 1
ROOT="$(pwd)"
OUTDIR="$ROOT/build/profile"
PREFIX="${1:-}"

mkdir -p "$OUTDIR"
: > "$OUTDIR/summary.tsv"
: > "$OUTDIR/measurements.jsonl"

# 1. Warm the olean cache. Abort the sweep if the build is broken — profiling a non-building
#    tree measures error-recovery, not steady-state elaboration.
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo ">>> Warming cache: lake build SP1Clean"
  pkill -f "lake build" 2>/dev/null
  pkill -f "lake env lean" 2>/dev/null
  if ! lake build SP1Clean; then
    echo "!!! warm build failed — fix the build before profiling. Aborting." >&2
    exit 1
  fi
else
  echo ">>> SKIP_BUILD=1: assuming cache is warm"
fi

# 2. Enumerate modules (deterministic order), optionally scoped by path prefix.
#    bash 3.2 has no `mapfile`, so stream from a temp list and count up front.
LISTFILE="$(mktemp)"
find SP1Clean -name '*.lean' | sort > "$LISTFILE"
if [ -n "$PREFIX" ]; then
  grep "^SP1Clean/$PREFIX" "$LISTFILE" > "$LISTFILE.f" && mv "$LISTFILE.f" "$LISTFILE"
fi
TOTAL="$(wc -l < "$LISTFILE" | tr -d ' ')"

echo ">>> Profiling ${TOTAL} modules (prefix='${PREFIX}')"
count=0
while IFS= read -r f; do
  rel="${f#SP1Clean/}"
  count=$((count + 1))

  # dotted module name for logs/tables, e.g. Operations/MulOperation.lean -> Operations.MulOperation
  module="${rel%.lean}"
  module="${module//\//.}"
  log="$OUTDIR/${module}.log"
  timefile="$(mktemp)"

  printf '[%3d/%3d] %s ... ' "$count" "$TOTAL" "$module"

  # 3. Time the isolated elaboration. lean runs inside `sh -c` so ITS stdout+stderr (incl. the
  #    profiler breakdown) go to $log, while /usr/bin/time -p's own `real <sec>` line stays on
  #    the outer stderr -> $timefile. time -p exits with the wrapped command's status, so rc is
  #    lean's exit code. (Redirecting lean directly under time would capture time's output too.)
  /usr/bin/time -p sh -c \
    'lake env lean -Dprofiler=true -Dprofiler.threshold=50 "$1" > "$2" 2>&1' \
    _ "$f" "$log" 2> "$timefile"
  rc=$?

  secs="$(awk '/^real/ {print $2}' "$timefile")"
  rm -f "$timefile"
  [ -z "$secs" ] && secs="0"

  printf '%ss (exit %d)\n' "$secs" "$rc"
  printf '%s\t%s\t%s\n' "$secs" "$rc" "$module" >> "$OUTDIR/summary.tsv"
  printf '{"metric": "compile//%s", "value": %s, "unit": "s", "exit": %d}\n' \
    "$module" "$secs" "$rc" >> "$OUTDIR/measurements.jsonl"
done < "$LISTFILE"
rm -f "$LISTFILE"

# 4. Sort slowest-first; that sorted file IS the canonical offender ranking.
sort -t$'\t' -k1,1 -rn "$OUTDIR/summary.tsv" -o "$OUTDIR/summary.tsv"

# 5. Render a markdown table + a totals/failures footer.
{
  echo "# Compile-time profile (wall-clock elaboration, isolated per module)"
  echo
  echo "| Rank | Seconds | Exit | Module |"
  echo "| ---: | ---: | ---: | --- |"
  awk -F'\t' '{ printf "| %d | %.2f | %d | \x60%s\x60 |\n", NR, $1, $2, $3 }' "$OUTDIR/summary.tsv"
  echo
  awk -F'\t' '
    { total += $1; n++; if ($2 != 0) fails[$2"\t"$3]=1 }
    END {
      printf "**Total:** %.1fs across %d modules (sequential; no parallelism/kernel phase).\n\n", total, n
      nf = 0; for (k in fails) nf++
      if (nf > 0) {
        printf "**%d module(s) exited nonzero** (silent under `lake env lean` — investigate):\n\n", nf
        for (k in fails) { split(k, a, "\t"); printf "- `%s` (exit %s)\n", a[2], a[1] }
      } else {
        print "All modules exited 0."
      }
    }' "$OUTDIR/summary.tsv"
} > "$OUTDIR/summary.md"

echo
echo ">>> Done. Ranking: $OUTDIR/summary.tsv  |  Table: $OUTDIR/summary.md  |  Logs: $OUTDIR/*.log"
echo ">>> Top 15:"
head -15 "$OUTDIR/summary.tsv" | awk -F'\t' '{ printf "  %6.2fs  (exit %s)  %s\n", $1, $2, $3 }'
