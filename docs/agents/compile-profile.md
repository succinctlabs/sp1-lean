# Compile-time profile — SP1Clean

Per-module wall-clock elaboration profile of the whole library, with per-tactic attribution for the
worst offenders and the common threads behind them. Measured June 2026 (Lean v4.28.0, warm olean cache).

> **Snapshot.** These are point-in-time numbers; treat them as a historical baseline, not current truth.
> Re-run `scripts/profile_compile.sh` to refresh.

> **Recent optimizations (nlinarith dedup + `tauto` outliers).** The repeated
> per-limb `.val`/bound `nlinarith` goals in the `srl_/sll_within_byte_shift*` variants were factored
> into `Operations/ShiftBounds.lean` (proved once, applied by `exact`), and the three `Faithful/` `tauto`
> outliers were swapped to `itauto`. Measured isolated `lake env lean` times (no profiler overhead) after
> the change: **ShiftRightMath 110s→44s, ShiftLeftCore 49s→32s, AddressOperation 37s→9s,
> LtOperationUnsigned 18s→6s, LtOperationSigned 13s→4s** (~227s→~94s across the five). All five stay
> axiom-clean; ShiftRightMath's ceiling dropped 100M→8M. The figures in the tables below are the
> pre-optimization profiler snapshot and are kept for reference.

## How to re-run

```sh
scripts/profile_compile.sh            # whole library (warm-builds first, then sweeps)
SKIP_BUILD=1 scripts/profile_compile.sh            # cache already warm
SKIP_BUILD=1 scripts/profile_compile.sh Operations/  # scope to one subdir
```

Outputs land in `build/profile/`:
- `summary.tsv` — `seconds⇥exit⇥module`, sorted slowest-first (the canonical offender ranking)
- `summary.md` — same as a markdown table + totals/failures footer
- `<module>.log` — the full `-Dprofiler=true` breakdown for each module
- `measurements.jsonl` — one archival JSON-Lines record per module

## Method & caveats

After one warm `lake build`, each module is re-elaborated in isolation with
`lake env lean -Dprofiler=true -Dprofiler.threshold=50 <file>`. Every dependency loads from its cached
`.olean`, so the timing isolates **that one file's** elaboration. Read the numbers with three caveats:

1. **Import tax is a sweep artifact.** Each isolated run re-pays ~0.8s to load imports (~**195s total**,
   ~12% of the sweep). In a real parallel `lake build` that cost is shared/amortized. It dominates the
   cheap files but is <1% of the expensive ones — so the **ranking of expensive files is accurate**, but
   absolute seconds for sub-3s files are mostly fixed tax, not real work.
2. **Profiler sums over-count.** `-Dprofiler` lines are nested/cumulative (a child tactic's time rolls up
   into its parent), so summing all `took` lines exceeds wall-clock (MulOperation: ~510s of lines vs 163s
   wall). The per-category percentages below are **dominance signals among leaf tactics**, not an additive
   budget.
3. **`lake env lean` exits 0 even on a stack overflow.** The script records exit codes explicitly; this
   run had **0 nonzero exits** across all 220 modules.

## Headline numbers

- **220 modules, ~1640s total** (sequential, isolated). Mean 7.5s, **median 2.4s**, p95 25.7s, max 163s.
- Heavily skewed: **139/220 modules elaborate in <3s** (≈ import + linter floor). The top 13 files
  account for **~890s — more than half the whole sweep.**
- The known Mul baseline reproduces (163s, top of the list, rw-dominated) — the method is sound.

### Time by subsystem

| Subsystem | Time | Files | Note |
| --- | ---: | ---: | --- |
| `Operations/` | 527s | 34 | the gadgets — nlinarith & rw-on-big-goals heavy |
| `Chips/` | 486s | 42 | chip soundness — simp & rw heavy |
| `Extracted/` | 334s | 55 | auto-gen constraint mirror — pure term elaboration + linter tax, no hand proofs |
| `Faithful/` | 178s | 53 | constraint anchors — mostly cheap, two `tauto` outliers |
| `Foundations/` | 50s | 15 | |
| `Readers/` | 36s | 9 | |
| `Soundness/` | 16s | 7 | |
| `Specs/` | 9s | 3 | |

## Top 25 offenders

| # | Time | Module | Lines | maxHB count | max HB | Dominant cost |
| ---: | ---: | --- | ---: | ---: | ---: | --- |
| 1 | 163s | `Operations.MulOperation` | 1929 | 8 | 40M | rw + type-checking + omega on giant goals |
| 2 | ~104s | `Chips.BranchChip` | 540 | 2 | 8M | `circuit_proof_start` whnf + setup bridges (six-way decision dispatch extracted to `Chips.BranchChip.Decision`, which compiles at default HB in ~3.5s) |
| 3 | 128s | `Chips.ShiftRightChip` | 2090 | 3 | 16M | simp + instantiate-metavars |
| 4 | 110s | `Operations.ShiftRightMath` | 2292 | 2 | 100M | **nlinarith/linarith** (114 calls) |
| 5 | 75s | `Extracted.MulOperation` | 609 | 2 | 8M | elaboration of monolithic extracted term + linter tax |
| 6 | 49s | `Operations.ShiftLeftCore` | 1649 | 16 | 4M | **nlinarith/linarith** (78 calls) |
| 7 | 49s | `Chips.ShiftLeftChip` | 693 | 2 | 4M | simp |
| 8 | 39s | `Extracted.ShiftRightChip` | 382 | 2 | 8M | elaboration of extracted term + linter tax |
| 9 | 37s | `Faithful.AddressOperation` | 62 | 1 | 4M | **one `tauto` = 16.4s** |
| 10 | 30s | `Operations.BitwiseU16Operation` | 632 | 2 | 2M | bvDecide + simp |
| 11 | 29s | `Extracted.ShiftLeftChip` | 309 | 2 | 8M | elaboration of extracted term + linter tax |
| 12 | 26s | `Operations.LtOperationSigned` | 388 | 4 | 4M | rw (rewriteSeq) + obtain |
| 13 | 23s | `Operations.LtOperationUnsigned` | 569 | 7 | 4M | rw (rewriteSeq) + tauto |
| 14 | 18s | `Faithful.LtOperationUnsigned` | 56 | 1 | 4M | (see thread D — small file, heavy tactic) |
| 15 | 15s | `Chips.StoreByteChip` | 387 | 2 | 16M | |
| 16 | 14s | `Operations.ShiftRightDispatch` | 1593 | 12 | 1M | |
| 17 | 14s | `Readers.ALUTypeReader` | 186 | 1 | 4M | |
| 18 | 13s | `Chips.JalrChip` | 375 | 2 | 2M | |
| 19 | 13s | `Foundations.SailWrap` | 450 | 1 | 10M | |
| 20 | 13s | `Faithful.LtOperationSigned` | 63 | 1 | 8M | |
| 21 | 12s | `Operations.AddrAddOperation` | 286 | 3 | 16M | |
| 22 | 12s | `Chips.LoadByteChip` | 379 | 2 | 16M | |
| 23 | 12s | `Extracted.BranchChip` | 212 | 2 | 8M | |
| 24 | 11s | `Operations.SubOperation.RawSpec` | 176 | 2 | 16M | |
| 25 | 11s | `Chips.LoadHalfChip` | 368 | 2 | 16M | |

## Common threads

Ranked by aggregate cost across the library.

### A. Proof tactics on monolithic constraint goals (the dominant theme)
Mul, Branch, Shift, and Lt all build one enormous goal (inline schoolbook columns / dispatch fan-out)
and then pay for it inside whatever tactic touches it — `rw`/`rewriteSeq` (Mul 130s cumulative, Branch
112s, Lt), `simp` (ShiftRightChip 34s, ShiftLeftChip 20s), `omega` + `type checking` + `typeclass
inference of CharP` (Mul). The tactic varies; the root cause is the same **giant-goal** shape first
documented for Mul in `mul-operation-learnings.md`. This is now confirmed to span the whole ALU
cluster, not just Mul.

### B. `nlinarith`/`linarith` is the single most concentrated hot spot
`Operations/ShiftRightMath` (110s) and `Operations/ShiftLeftCore` (49s) spend **~45% of profiled time in
nlinarith** — 114 and 78 nlinarith invocations respectively, individual calls running 1–7s and climbing
as the goal grows. Two files, ~**460s of cumulative nlinarith**. This is the highest-leverage single
target: replacing/▸ pre-shaping these `nlinarith` goals (explicit lemmas, `omega` where linear, smaller
sub-goals) would move the needle more than any other change.

### C. Fixed per-file tax: import + mathlib/batteries linters
Every file pays ~0.8s import **and** a recurring **linter-interpretation tax** — `TacticAnalysis`,
`UnusedTactic`, `UnreachableTactic`, `UnnecessarySeqFocus` each interpret per declaration (~0.1–0.6s/file;
on `Extracted.MulOperation` the linters + linting were the *heaviest* lines after import). For the 139
sub-3s files this tax **is** essentially their whole cost. Import (~195s) is a sweep artifact, but the
linter interpretation is paid in real builds too — disabling these linters for the auto-generated
`Extracted/` tree (which contains no hand proofs to lint) is low-risk, library-wide savings.

### D. Small files, heavy single tactics — size does *not* predict time
`Faithful/AddressOperation` is **62 lines but 37s — one `tauto` call alone is 16.4s**;
`Faithful/LtOperationUnsigned` is 56 lines / 18s. Conversely `Specs/Chip` (604 lines) is cheap. Line
count correlates weakly with elaboration time; the **dominant-tactic choice** dominates. The `tauto`
outliers are the cheapest wins available — a targeted replacement reclaims ~16s from one call.

### E. `Extracted/` mirror cost — elaboration of monolithic generated terms
The auto-generated constraint definitions cost ~**140s+ across `Extracted.MulOperation` (75s),
`Extracted.ShiftRightChip` (39s), `Extracted.ShiftLeftChip` (29s)** despite containing no hand proofs —
pure elaboration of one huge term plus the linter tax (thread C). Splitting the generated definitions
(or generating them in a form Lean elaborates incrementally) in `sp1-constraint-compiler` would cut this.

## Where to optimize first (by leverage)

1. ~~**`nlinarith` in ShiftRightMath + ShiftLeftCore** (thread B)~~ — **done.** Factored the
   repeated `.val`/bound goals into `Operations/ShiftBounds.lean`; ShiftRightMath 110s→44s, ShiftLeftCore
   49s→32s.
2. **Giant-goal shape in Mul/Branch/Shift/Lt** (thread A) — the structural fix (avoid building one
   monolithic goal) attacks the top 4 offenders at once. Largest absolute prize, largest effort. *Still open.*
3. ~~**`tauto` outliers** (thread D)~~ — **done.** `tauto`→`itauto` in `Faithful/AddressOperation`
   (37s→9s), `LtOperationUnsigned` (18s→6s), `LtOperationSigned` (13s→4s).
4. **Disable linters on `Extracted/`** (threads C+E) — library-wide, low-risk. *Still open.*

## Verification of this run

- Coverage: `summary.tsv` has **220 rows == `find SP1Clean -name '*.lean' | wc -l`**; no module dropped.
- Failures: **0 nonzero exits** (none silently misread as fast).
- Method sanity: MulOperation lands #1 at 163s, `rw`-dominated — reproduces the known ~180s baseline.
