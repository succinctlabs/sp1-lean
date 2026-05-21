# SP1-Lean compile-time bottleneck inventory — 2026-05-21

**Status: complete.** Per-file wall times on `dtumad/final-aggregation` at
HEAD `cf7ca82` (one day after the 2026-05-20 sweep at `9b49330`). The
intervening commits include `7d783cc perf improvements` and
`cf7ca82 break up an additional omega pain point`; the AbsHelper /
ProdHelper extraction landed in `a3af4f5` just before. This sweep
measures the impact of those changes and re-establishes the top-5
ranking.

**Headline:** four of the five slowest files are the DivRem opcode
cores. `MulOperation/Constraints` (the prior #1) is now #3. The
biggest perf win since 2026-05-20 is `DivRem/Common.lean`, which
dropped from **292.76 s → 10.07 s** (29×) via the helper extraction;
but the cost largely relocated into the per-opcode files, which
previously cascade-failed and so were unmeasured.

## Methodology

Identical to the 2026-05-20 sweep: `time lake env lean --profile <file>`
captures wall/user/sys/RSS without invalidating cached oleans. Per-file
`cumulative profiling times` summary is retained in
`.claude/profile_logs/<basename>.log`. Raw TSV is at
`.claude/perf_2026-05-21.tsv`. The sweep ran serially across 28
candidate files (top 19 from 2026-05-20 + the 5 DivRem opcode/Chip
files that cascade-failed last time + 2 new DivRem helpers + Soundness
+ DivRem/Constraints). Two files (`DivwRemw.lean`, `DivuwRemuw.lean`)
stack-overflowed at the default `--tstack=400000` and were retried at
`--tstack=4000000`; their reported walls are from the retry. DivRem/Common
also needed `--tstack=4000000`. Spot-check on the #2 file (DivRem.lean,
338.71 → 336.69 s on rerun, Δ −0.6%) confirms single-run variance is
well within ±10%.

## 1. Top 5 — the answer

| rank | file | wall_s | 2026-05-20 wall_s | Δ | dominant phases (cumulative; CPU-time, may exceed wall) |
|---:|---|---:|---:|---:|---|
| **1** | `SP1Chips/DivRem/DivwRemw.lean` | **595.95** | (cascade-failed) | n/a | typeclass inference 477s · instantiate metavars 388s · simp 264s · interpretation 101s · tactic execution 69s |
| **2** | `SP1Chips/DivRem/DivRem.lean` | **338.71** | (cascade-failed) | n/a | instantiate metavars 294s · simp 165s · typeclass inference 159s · tactic execution 49.6s · interpretation 33.4s |
| **3** | `SP1Operations/Operation/MulOperation/Constraints.lean` | **273.57** | 300.14 | **−9%** | tactic execution **252s** (92% of wall) · interpretation 56s · typeclass inference 15s · simp 14s · instantiate metavars 12s |
| **4** | `SP1Chips/DivRem/DivuRemu.lean` | **239.59** | (cascade-failed) | n/a | instantiate metavars 288s · simp 82.8s · typeclass inference 52.8s · tactic execution 45.5s · interpretation 4.3s |
| **5** | `SP1Chips/DivRem/DivuwRemuw.lean` | **216.34** | (cascade-failed) | n/a | instantiate metavars 296s · simp 58.6s · tactic execution 47.5s · typeclass inference 21.7s · interpretation 3.9s |

## 2. Top 10 — runners-up

| rank | file | wall_s | 2026-05-20 wall_s | Δ |
|---:|---|---:|---:|---:|
| 6 | `SP1Chips/ShiftRight/Common.lean` | 116.34 | 117.66 | −1% |
| 7 | `SP1Chips/ShiftLeft/Common.lean` | 96.70 | 97.65 | −1% |
| 8 | `SP1Chips/ShiftRight/Sraw.lean` (exit 1, linter) | 84.94 | 91.37 | −7% |
| 9 | `SP1Chips/ShiftRight/Sra.lean` | 59.90 | 64.27 | −7% |
| 10 | `SP1Chips/DivRem/Constraints.lean` | 48.91 | (not in sweep) | n/a |

## 3. Full per-file table

| file | wall_s | rss_MB | exit |
|---|---:|---:|---:|
| `SP1Chips/DivRem/DivwRemw.lean` | 595.95 | 8675 | 0 |
| `SP1Chips/DivRem/DivRem.lean` | 338.71 | 8046 | 0 |
| `SP1Operations/Operation/MulOperation/Constraints.lean` | 273.57 | 10647 | 0 |
| `SP1Chips/DivRem/DivuRemu.lean` | 239.59 | 8164 | 0 |
| `SP1Chips/DivRem/DivuwRemuw.lean` | 216.34 | 8247 | 0 |
| `SP1Chips/ShiftRight/Common.lean` | 116.34 | 7088 | 0 |
| `SP1Chips/ShiftLeft/Common.lean` | 96.70 | 6697 | 0 |
| `SP1Chips/ShiftRight/Sraw.lean` | 84.94 | 7401 | 1 |
| `SP1Chips/ShiftRight/Sra.lean` | 59.90 | 6898 | 0 |
| `SP1Chips/DivRem/Constraints.lean` | 48.91 | 10524 | 0 |
| `SP1Chips/ShiftRight/Srlw.lean` | 40.24 | 7050 | 1 |
| `SP1Chips/ShiftRight/Srl.lean` | 30.55 | 6674 | 0 |
| `SP1Chips/ShiftLeft/Sll.lean` | 25.98 | 6910 | 0 |
| `SP1Foundations/SailM.lean` | 22.43 | 7376 | 0 |
| `SP1Chips/DivRemChip.lean` | 20.20 | 7220 | 0 |
| `SP1Chips/Branch/Common.lean` | 15.43 | 6595 | 0 |
| `SP1Chips/MulChip.lean` | 14.29 | 7039 | 0 |
| `SP1Chips/DivRem/ProdHelper.lean` | 12.64 | 6645 | 0 |
| `SP1Chips/LoadX0Chip.lean` | 12.59 | 7139 | 0 |
| `SP1Chips/ShiftRightChip.lean` | 11.61 | 7237 | 0 |
| `SP1Chips/BranchChip.lean` | 11.18 | 6936 | 0 |
| `SP1Chips/ShiftLeftChip.lean` | 10.90 | 6956 | 0 |
| `SP1Foundations/Word.lean` | 10.63 | 6772 | 0 |
| `SP1Chips/DivRem/Common.lean` | 10.07 | 6903 | 0 |
| `SP1Chips/ShiftLeft/Sllw.lean` | 6.99 | 6652 | 0 |
| `SP1Foundations/MemChecks.lean` | 5.38 | 6563 | 0 |
| `SP1Chips/DivRem/AbsHelper.lean` | 3.56 | 6409 | 0 |
| `SP1Chips/Soundness.lean` | 3.45 | 6527 | 0 |

Sum of successful wall times across 28 files: **2602 s** (~43 min
single-threaded). The DivRem family alone is **1453 s** (56%);
removing `DivRem/Constraints.lean` (autogen, 49 s) and the small
helpers, the 4 opcode cores contribute **1390 s** (53% of the total).

## 4. Interpretation — where the work went

The dominant story is the DivRem extraction (`a3af4f5` → `cf7ca82`):

- **`DivRem/Common.lean`** previously ran at 292.76 s, dominated by
  `tactic execution 278s` (the wide-obtain heavy proofs in the family
  helpers). It is now **10.07 s** — the 29× drop comes from moving
  the heavy proof work out of Common and into per-opcode files.
- **The 4 DivRem opcode cores were cascade-failing on 2026-05-20** (their
  `Common.olean` was missing in `.lake/build`), so the prior sweep
  reported 0.47 s import failures, not real walls. The current sweep
  measures their real cost for the first time: **595 + 339 + 240 + 216
  = 1390 s combined**. Their cost shape (~290 s each of
  `instantiate metavars`) is markedly different from old `Common.lean`'s
  shape (tactic execution dominated), confirming the work was not just
  moved but restructured — the per-opcode files now do heavy generic
  lemma instantiation rather than direct wide-obtain destructuring.
- **`DivwRemw.lean` at 596 s is the new critical-path single file.**
  `typeclass inference 477s` (cumulative) is the standout signal — 1.7×
  larger than #2's TC-inference cost, suggesting a specific instance
  resolution bottleneck (likely in the `Fact (1 < 2^N)` / ring instance
  chain inside the `_w` variant's `BitVec 32 → BitVec 64` lifting).

Outside the DivRem family, the picture matches 2026-05-20:

- **`MulOperation/Constraints.lean`** dropped 9% (300 → 274 s) but is
  still dominated by `tactic execution 252s` — the 5 wide-obtain
  chains in `spec.{mul,mulh,mulhu,mulhsu,mulw}` documented in the
  2026-05-20 §1 fix recommendation have **not** been refactored. This
  remains the single highest-leverage fix outside the DivRem family.
- **`ShiftRight/Common`, `ShiftLeft/Common`, `Sraw`, `Sra`, `Srlw`, `Srl`,
  `Sll`** all moved within ±1–8% — no structural change. The two
  exit-1 files (Sraw, Srlw) still trip the same linter
  warning→error escalation on discarded stdout.
- **`BranchChip.lean`** held at 11.18 s — the 10× drop documented in
  the 2026-05-20 §1 surprise persists.

## 5. Regressions

None > 10%. The largest single regression in the cohort is
`ShiftLeft/Common` at +0% (within noise). The fast-fail removals that
exposed real costs (4 DivRem opcode files) are not regressions —
they're previously-unmeasured work surfaced by the build-state fix.

## 6. Open issues (carried over from 2026-05-20)

- **`ShiftRight/Sraw.lean` and `Srlw.lean` exit 1** at the end of a
  full elaboration. Profile data is complete, so the wall time is
  meaningful, but the non-zero exit suggests a linter is being
  promoted to error against discarded stdout. Worth a targeted look
  — capture stderr cleanly, identify the offending warning, decide
  whether to fix-or-disable. Not on the critical path for the top-5
  question.
- **DivRem files need `--tstack=4000000`.** Three of the eight DivRem
  files in this sweep overflow at the project-default `--tstack=400000`.
  Bumping the lakefile default (and clearing the per-decl
  `set_option debug.skipKernelTC` and skip pragmas where they were
  acting as workarounds) is worth scoping separately. See 2026-05-20 §7.3.

## 7. Reproducing this sweep

`./.claude/perf_2026-05-21.sh` runs the 28-file candidate sweep
serially (~28 min wall). The script is a thin wrapper around
`/usr/bin/time lake env lean --profile`. It does **not** invalidate
cached oleans; safe to run against a green build state. Two stack-overflow
retries and the spot-check were appended manually
(`.claude/perf_2026-05-21_retry.tsv`).
