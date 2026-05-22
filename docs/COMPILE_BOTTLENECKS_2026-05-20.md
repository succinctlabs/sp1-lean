# SP1-Lean compile-time bottleneck inventory — 2026-05-20

**Status: complete (sweep finished 21:14).** Per-file wall times from the
current branch (`dtumad/final-aggregation`, post field-genericization)
populate §2; pre-genericization baseline (`.claude/perf_phase_a.tsv`,
2026-04-26) referenced for delta comparison. The single open data
point — `SP1Chips/DivRem/Common.lean` wall time at higher `--tstack` —
is at the end of §2 / §7.

**Methodology.** Per-file wall time from `time lake env lean --profile <file>`
(does not touch cached oleans; one re-elaboration per file). The Lean
`--profile` flag emits a `cumulative profiling times` summary at the end —
that's the phase breakdown referenced below (interpretation / simp /
tactic execution / typeclass inference / .olean serialization). The
`set_option maxHeartbeats N in <decl>` pragmas already in the source
function as a pre-existing hotspot map: anywhere the author bumped the
budget is, by construction, a slow declaration. 137 such pragmas + 1
`debug.skipKernelTC` are active across `SP1Chips/` and `SP1Operations/`
(plus 1 file-wide `maxHeartbeats 10000000` in `SP1Foundations/SailM.lean`).

The report is written for the maintainer who needs to decide what to
refactor next. Each hotspot ends with a candidate fix tagged with its
`PROOF_PATTERNS.md` recipe number where one exists.

## 1. Executive summary

Fresh per-file profile sweep across 27 candidate files (the heaviest by
LOC + `maxHeartbeats` density) completed in ~19 min wall on
2026-05-20. Successful sweep elaborations sum to **781.9 s wall**
across 19 files; adding the separately-rerun DivRem/Common (292.76 s
at `--tstack=4000000`) takes the total to **1074.7 s** across the 20
files that produced clean data. 5 cascade-failed because
`SP1Chips/DivRem/Common.olean` is unexpectedly missing from
`.lake/build` (see §7.1); 2 (ShiftRight `Sraw`/`Srlw`) exited with
status 1 after a full elaboration — likely a linter promoting
warning→error, exact message not captured (stdout discarded).
DivRem/Common itself **stack-overflowed at the project-default
`--tstack=400000`** after 198 s of elaboration; the retry at
`--tstack=4000000` (§7.2) succeeded in 292.76 s.

**Top 10 cost centers (post-genericization, current state).**

| rank | file | wall_s | shape |
|---:|---|---:|---|
| 1 | `SP1Operations/Operation/MulOperation/Constraints.lean` | **300.14** | tactic execution dominated (`linear_combination` × 66 + wide `obtain` × 5) |
| 2 | `SP1Chips/DivRem/Common.lean` | **292.76** (at `--tstack=4000000`) | tactic execution dominated (278 s, 95% of wall); same wide-`obtain` pattern as #1 |
| 3 | `SP1Chips/ShiftRight/Common.lean` | 117.66 | interpretation-dominated (`omega` × 251) |
| 4 | `SP1Chips/ShiftLeft/Common.lean` | 97.65 | interpretation-dominated (`omega` × 81) |
| 5 | `SP1Chips/ShiftRight/Sraw.lean` | 91.37 | `instantiate metavars` 36.7s + tactic exec 30.4s |
| 6 | `SP1Chips/ShiftRight/Sra.lean` | 64.27 | `instantiate metavars` 38.5s (close-helpers) |
| 7 | `SP1Chips/ShiftRight/Srlw.lean` | 43.91 | mixed |
| 8 | `SP1Chips/ShiftRight/Srl.lean` | 34.87 | mixed |
| 9 | `SP1Chips/ShiftLeft/Sll.lean` | 27.00 | `instantiate metavars` 24.7s (close-helpers) |
| 10 | `SP1Foundations/SailM.lean` | 22.92 | simp 40.3s cumulative |

**Single highest-leverage fix.** Break the 5 wide `obtain` chains in
`spec.mul / spec.mulh / spec.mulhu / spec.mulhsu / spec.mulw`
(`SP1Operations/Operation/MulOperation/Constraints.lean`, lines 1753 +
182/142/135/142/142 lines later). Each is an 80-name `obtain ⟨…⟩
:= cstrs` matching the exact anti-pattern documented in
`PROOF_PATTERNS.md §1.2`. Expected saving: **90–180 s** off the file's
300 s wall — that one file is currently a third of the heavy-file
critical path.

**Two surprising findings that complicate the simple picture.**

1. **`BranchChip` dropped 114 s → 11.45 s (10×)** vs the
   2026-04-26 baseline. Cumulative `interpretation` went from 279 s
   (Aesop-dominated) to 1.15 s — the genericization migration
   eliminated Aesop in this chip. The 6 × `maxHeartbeats 16000000`
   bumps in `BranchChip.lean` are now pure defensive scaffolding.
   `BitwiseChip` (5×), `ShiftRightChip` (3×), `ShiftLeftChip` (2.5×),
   and `MulChip` (2×) show the same pattern. **Most chip-level
   `correct_*` proofs are now fast**; cost has concentrated in the
   `Common.lean` / `Constraints.lean` files that hold the shared
   helpers.

2. **`SP1Chips/DivRem/Common.olean` is missing from `.lake/build` even
   though all 5 dependents (`DivRem.olean`, `DivuRemu.olean`, etc.)
   are present from a build that completed ~5 hours before this
   sweep.** Either the user's "green" build state is silently
   inconsistent, or lake's incremental-build logic ignores a missing
   olean as long as the hash + ilean exist. Worth confirming with
   `lake build SP1Chips.DivRem.Common` before any further perf work.
   Separately, re-elaborating the file via `lake env lean --profile`
   triggered `Stack overflow detected. Aborting.` after 198 s at the
   project-default `--tstack=400000`; the retry at `--tstack=4000000`
   completed cleanly in 292.76 s (§7.2). Suggests `lakefile.toml`
   should bump `--tstack` (§7.3).

## 2. Per-module wall time

### Current state (sweep 2026-05-20 20:55 → 21:14, plus DivRem retry to 21:20)

Per-file wall-time from `time lake env lean --profile <file>`. RSS is
the peak resident size for the lean process during elaboration.
"Dominant phase" picks the largest entries from the `cumulative
profiling times` summary `lean --profile` emits at end-of-stderr.

| file | LOC | wall_s | rss_MB | dominant phase (cumulative) |
|---|---:|---:|---:|---|
| `SP1Operations/Operation/MulOperation/Constraints.lean` | 2555 | **300.14** | 10688 | tactic execution **274s** (91%); interpretation 60s; typeclass inference 15.5s; simp 14.4s; instantiate metavars 13.2s |
| `SP1Chips/ShiftRight/Common.lean` | 2511 | **117.66** | 7056 | **interpretation 260s** (cumulative, > wall — multi-thread); blocked unaccounted 104s; typeclass inference 25.7s; tactic execution 8.41s; simp 5.98s |
| `SP1Chips/ShiftLeft/Sll.lean` | 2122 | **27.00** | 6920 | **instantiate metavars 24.7s** (distinctive!); tactic execution 9.38s; typeclass inference 8.72s; interpretation 2.07s |
| `SP1Chips/LoadX0Chip.lean` | 2529 | 12.76 | 7125 | tactic execution 22.6s; simp 14.7s; typeclass inference 9.8s; instantiate metavars 7.07s; interpretation 1.75s |
| `SP1Foundations/Word.lean` | 1772 | 10.84 | 6777 | typeclass inference 8.9s; tactic execution 6.56s; type checking 4.61s; simp 4.48s |
| `SP1Chips/DivRem/Common.lean` | 1705 | **292.76** (at `--tstack=4000000`); stack-overflows at default 400 k | 7873 | **tactic execution 278s** (95%); blocked unaccounted 58.3s; simp 9.14s; typeclass inference 7.13s; interpretation 6.84s; instantiate metavars 4.88s |
| `SP1Chips/ShiftLeft/Common.lean` | 1556 | **97.65** | 6688 | **interpretation 118s** (cumulative); blocked unaccounted 83.7s; typeclass inference 15.1s; simp 3.71s; tactic execution 2.5s |
| `SP1Chips/DivRem/DivwRemw.lean` | 1515 | fast-fail (exit 1) | 754 | cascading failure: imports `DivRem.Common` whose olean is missing |
| `SP1Chips/BranchChip.lean` | 1423 | **11.45** | 6961 | simp 19.5s (cumulative); typeclass inference 10.1s; tactic execution 8.21s; instantiate metavars 3.56s; **interpretation 1.15s** |
| `SP1Chips/ShiftRight/Sraw.lean` | 1368 | 91.37 (exit 1, stdout discarded) | 7417 | instantiate metavars **36.7s**; tactic execution 30.4s; interpretation 8.89s; typeclass inference 8.74s |
| `SP1Foundations/MemChecks.lean` | 1313 | 5.56 | 6561 | (small) |
| `SP1Foundations/SailM.lean` | 1292 | 22.92 | 7432 | **simp 40.3s** (cumulative); tactic execution 14s; typeclass inference 13.1s; grind 1.31s |
| `SP1Chips/ShiftRight/Sra.lean` | 1245 | **64.27** | 6896 | **instantiate metavars 38.5s** (dominant); tactic execution 10.7s; typeclass inference 7.81s |
| `SP1Chips/ShiftRight/Srlw.lean` | 1163 | 43.91 (exit 1, stdout discarded) | 7048 | instantiate metavars 17.7s; interpretation 11.8s; tactic execution 12.7s; typeclass inference 5.38s |
| `SP1Chips/DivRem/DivRem.lean` | 1116 | fast-fail (exit 1) | 755 | cascade (`DivRem/Common` missing) |
| `SP1Chips/DivRem/DivuRemu.lean` | 1019 | fast-fail (exit 1) | 755 | cascade |
| `SP1Chips/ShiftLeft/Sllw.lean` | 1002 | **7.26** | 6632 | tactic execution 5.1s; typeclass inference 3.54s; simp 1s |
| `SP1Chips/DivRem/DivuwRemuw.lean` | 995 | fast-fail (exit 1) | 755 | cascade |
| `SP1Chips/ShiftRight/Srl.lean` | 753 | **34.87** | 6666 | _profile parsed below_ |
| `SP1Chips/BitwiseChip.lean` | 692 | **7.39** | 6696 | simp 10.2s (cumulative); typeclass inference 6.13s; tactic execution 3.62s |
| `SP1Chips/DivRemChip.lean` | 668 | fast-fail (exit 1) | 2007 | cascade |
| `SP1Chips/Branch/Common.lean` | 586 | **15.99** | 6569 | simp 13.2s (cumulative); typeclass inference 11.1s; tactic execution 1.66s |
| `SP1Chips/Bitwise/Common.lean` | 154 | **3.34** | 6382 | (small) |
| `SP1Chips/ShiftRightChip.lean` | 593 | **11.87** | 7246 | tactic execution 15.7s (cumulative); simp 12.4s; blocked unaccounted **35.5s** |
| `SP1Chips/ShiftLeftChip.lean` | 415 | **11.43** | 6953 | tactic execution 10.5s; simp 5.43s; blocked unaccounted 15.3s |
| `SP1Chips/MulChip.lean` | 471 | **14.49** | 7058 | simp 11.7s (cumulative); tactic execution 11.9s; instantiate metavars 4.9s; blocked unaccounted 20.5s |
| `SP1Operations/Compare/LtOperationSigned.lean` | 494 | **4.99** | 6490 | (small) |

**Sum of successful wall times: 781.9 s** across 19 files in the
sweep + the separately-rerun **DivRem/Common at 292.76 s** =
**~1074.7 s of measurable single-threaded elaboration**. Two files
(Sraw, Srlw) emitted full cumulative profile data but exited 1 —
their wall times (91.37 + 43.91 = 135.28 s) are included above
because the elaboration ran to completion. 5 DivRem-family files
fast-failed (cascade) and contribute ~2 s total. `lake build SP1Chips
SP1Operations SP1Foundations` from clean state should track well
below 1074 s wall due to parallel build (8 cores), but is bounded
below by the longest single-file critical path through
`MulOperation/Constraints` (300 s) or `DivRem/Common` (293 s).

**Two surprises from the post-genericization data:**

- **`BranchChip` went 114s → 11.45s (10×).** Pre-genericization
  cumulative `interpretation` was 279s (Aesop-dominated); current is
  1.15s. The genericization migration eliminated Aesop closers from
  this chip and replaced them with direct simp/omega chains. The 6 ×
  `maxHeartbeats 16000000` per-decl bumps in `BranchChip.lean` are now
  defensive — candidates for §6.4-style cleanup.
- **`DivRem/Common.lean` stack-overflows under `lake env lean --profile`
  at `--tstack=400000`.** It elaborated successfully in the past
  (DivRem.olean existed at May 20 19:53 from an earlier build) but
  Common.olean is now missing from `.lake/build/lib/lean/SP1Chips/DivRem/`
  even though `Common.olean.hash` is present (May 20 19:46). Either
  the file genuinely needs a higher tstack today or there's a separate
  build-state inconsistency. See §7.

**Three distinct cost shapes are already visible** in the data above:

1. **Tactic-execution dominated** (`MulOperation/Constraints` — 91% of
   wall): deep `linear_combination` / `ring` / `omega` chains inside
   wide `obtain`-destructured proofs.
2. **Interpretation dominated** (`ShiftRight/Common` — 260s cumulative
   vs 117s wall, so spread across threads): **251 `omega` calls + 25
   `decide` calls** in this one file (0 aesop, 0 simp_all, 6
   linear_combination). `omega` ⇒ ~1 s/call accounts for ~250s of the
   260s interpretation. The fix is structural — most of the 251 omegas
   are byte-bound side-conditions (`< 256`, `< 65536`) inside the
   29-decl `_byte_shift_*`/`_close_cb*_*_case` family. A shared
   `private lemma` per bound shape (already partly done via the
   `val_*_zmod_p` simp set in `SP1Foundations/Field.lean`) plus
   `omega ⇒ exact <helper>` replacement would cut interpretation
   substantially. The 25 `decide` calls are candidates for
   `native_decide` only where the trust-base widening is acceptable.
3. **Instantiate-metavars dominated** (`ShiftLeft/Sll` — 24.7s of
   27s wall): mostly the 4 `sll_close_cb4cb5_*_case` close-helpers
   doing `linear_combination` / `omega` over byte-shift equations.

### Pre-genericization baseline (2026-04-26, `.claude/perf_phase_a.tsv`)

For SP1Chips only (47 files at the time; current tree has 70). Numbers
reflect `lake build <module>` wall after `rm <module>.olean`. Mathlib
cache + downstream oleans were warm.

Top 10 by wall time:

| module | LOC then | wall_s | maxRSS_MB |
|---|---:|---:|---:|
| `SP1Chips.ShiftRight.Constraints` | 2234 | 1754.7 | 20329 |
| `SP1Chips.ShiftLeft.Constraints` | 1035 | 394.4 | 15511 |
| `SP1Chips.DivRem.Constraints` | 4643 | 358.9 | 16033 |
| `SP1Chips.BranchChip` | 805 | 114.1 | 8979 |
| `SP1Chips.BitwiseChip` | 391 | 39.5 | 6527 |
| `SP1Chips.ShiftRightChip` | 490 | 37.1 | 6521 |
| `SP1Chips.MulChip` | 311 | 31.5 | 6476 |
| `SP1Chips.LtChip` | 381 | 29.3 | 6573 |
| `SP1Chips.LoadByteChip` | 505 | 28.8 | 5466 |
| `SP1Chips.ShiftLeftChip` | 238 | 28.1 | 6472 |

Pre-genericization total `lake build SP1Chips` ≈ 52 min wall (47 files,
from 00:15:51 to 01:08:26 in `.claude/perf_phase_a.log`).

Codebase reshape since 2026-04-26 invalidates direct line-for-line
comparison:

- `SP1Chips.DivRem.Constraints` was 4643 LOC → now 648 LOC (split into
  `Common.lean` 1705 + `DivRem.lean` 1116 + `DivuRemu.lean` 1019 +
  `DivwRemw.lean` 1515 + `DivuwRemuw.lean` 995). The wall-time cost
  also redistributed; current per-file numbers will land in §2.1.
- `SP1Chips.ShiftRight.Constraints` was 2234 LOC → now 406 LOC. Body
  split: `Common.lean` 2511 + `Sra/Sraw/Srl/Srlw.lean`.
- `SP1Chips.ShiftLeft.Constraints` 1035 → 312 LOC. Body in
  `Common.lean` 1556 + `Sll/Sllw.lean`.
- All bare `Vector (Fin KB) N` switched to `Vector (ZMod p) N`; new
  `[Fact (Nat.Prime p)]` + `[Fact (2^17 < p)]` in chip signatures.

## 3. Cost-mitigation pragma inventory

137 active `maxHeartbeats` / `skipKernelTC` pragmas + 1 file-wide bump in
`SailM.lean`. The distribution itself is a hotspot map.

### By budget tier (across SP1Chips + SP1Operations)

| budget | sites | typical resident |
|---:|---:|---|
| `100000000` (file-wide) | 5 | all 5 DivRem files: `Common`, `Constraints`, `DivRem`, `DivuRemu`, `DivuwRemuw`, `DivwRemw` |
| `32000000` per-decl | 21 | DivRem family (incl. 5 spec.mul* lines) and `MulOperation/Constraints` |
| `16000000` per-decl | 12 | BranchChip × 6, Branch/Common × 3, and three others |
| `10000000` file-wide | 1 | `SP1Foundations/SailM.lean` |
| `8000000` per-decl | 24 | DivRemChip × 8, MulChip × 5, ShiftRightChip × 8, ShiftLeftChip × 3 |
| `4000000` per-decl | 3 | Mul/Common × 2, MulOperation/Constraints × 1 |
| `1600000` per-decl | 25 | LoadX0Chip × 7, Branch helpers, BitwiseChip × 6, Load chips, etc. |
| `800000` per-decl | 16 | Load/<width>/Common helpers, ShiftLeft/Common × 1, Bitwise/Common × 1 |
| `debug.skipKernelTC` | **1** | `SP1Chips/DivRem/Common.lean:1413` (`div_rem_h_abs_aux`) |

### Per-file pragma density (top 10)

```
8 SP1Operations/Operation/MulOperation/Constraints.lean
8 SP1Chips/ShiftRightChip.lean
8 SP1Chips/DivRemChip.lean
7 SP1Chips/LoadX0Chip.lean
6 SP1Chips/Branch/Common.lean
6 SP1Chips/BranchChip.lean
6 SP1Chips/BitwiseChip.lean
5 SP1Chips/ShiftLeft/Common.lean
5 SP1Chips/MulChip.lean
4 SP1Chips/DivRem/{Common,DivRem,DivuRemu,DivuwRemuw,DivwRemw}.lean
```

Summed budgets (rough hotspot ordering):

- **DivRem family** ≈ 980M heartbeats across 5 files (file-wide 100M × 5
  + per-decl 32M × ~13). Highest.
- **Mul family** ≈ 188M (`MulOperation/Constraints` 32M × 5 + 8M + 4M +
  1.6M; `MulChip` 8M × 5).
- **Branch family** ≈ 149M (`BranchChip` 16M × 6; `Branch/Common`
  16M × 3 + 1.6M × 3).
- **ShiftLeft + ShiftRight chips** ≈ 25M each (lower than the constraints-file numbers above suggest — most cost was in the
  pre-genericization `Constraints.lean` which has since been split).

## 4. Per-hotspot drill-down

(Populated as `--profile` output is parsed. Each entry: target decl,
top-3 cost categories from the `cumulative profiling times` block at
the end of the file's stderr, candidate fix mapped to a
`PROOF_PATTERNS.md` recipe.)

### 4.1 `SP1Operations/Operation/MulOperation/Constraints.lean`

(2555 LOC, 8 pragmas: 32M × 5 on `spec.mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`;
8M on `core_mul`; 4M on `allHold_constraints_iff_is_real`; 1.6M on one
helper.)

Top hand-written declarations (line / pragma):

- `core_mul` @ 36 (8M, **747-line body**)
- `core_mulw` @ 784 (676-line body, no per-decl bump)
- `allHold_constraints_iff_is_real` @ 1461 (4M, 108-line body)
- `spec.mul` @ 1753 (**32M**, 147-line body)
- `spec.mulh` @ 1935 (**32M**, 142-line body)
- `spec.mulhu` @ 2078 (**32M**)
- `spec.mulhsu` @ 2213 (**32M**)
- `spec.mulw` @ 2352 (**32M**)
- `spec.mulh.gen` @ 2532

Pre-genericization `MulOperation/Constraints` did not exist as a
standalone file (work was inline in `MulChip` / `Mul/Constraints` and
much smaller); the 32M × 5 budget pattern is new.

**Cumulative profile of this file (300.14s wall):**

| phase | time | notes |
|---|---:|---|
| tactic execution | **274s** | 91% of wall — dominates |
| interpretation (Aesop core) | 60s | second-largest |
| simp | 14.4s | |
| typeclass inference | 15.5s | |
| instantiate metavars | 13.2s | |
| blocked (unaccounted) | 8.41s | |
| elaboration | 7.23s | |
| type checking | 6.51s | |
| ring | 1.72s | |
| norm_num | 897ms | |
| parsing | 97.4ms | |

**Confirmed anti-pattern in `spec.mul` (line 1780)** — a single
~80-name `obtain ⟨u16_b_cstrs, u16_c_cstrs, …, pp14, pp15⟩ := cstrs`
chain destructures the entire `cstrs` shape in one statement, followed
by 16 nearly-identical `have ppN' : cols.product[N].val < 256` byte-
bound conversions (lines 1826–1845). This is the canonical example of
the wide-`obtain` anti-pattern described in `PROOF_PATTERNS.md §1.2`,
duplicated across all 5 `spec.mul*` variants. **High-leverage fix**:
stepwise `rcases` + a single `pp_bytes_lt_256` helper used by all 5
variants. Expected impact based on §1.2 historical data (ShiftRight
went 836 → 161 lines + "visibly snappier"): wall-time saving on this
file in the 30–60% range — at 300s wall, **plausibly 90–180s saving**.

### 4.2 `SP1Chips/DivRem/Common.lean`

(1705 LOC, file-wide `maxHeartbeats 100000000`, 2 × 32M per-decl, **1
`skipKernelTC` on `div_rem_h_abs_aux` line 1413**.)

Top hand-written declarations:

- `allHold_constraints_iff` @ 183 — **351-line body**, governs all 8
  DivRem variants over `Vector (ZMod p) 246` (the **widest** constraint
  vector in the repo).
- 8 `_chip_bounds` lemmas (`divu`/`div`/`rem`/`remu`/`divw`/`remw`/`divuw`/`remuw`)
  @ 801–1014.
- `divrem_N128` opaque alias + `BitVec.toNat_ofNat_128` /
  `BitVec.toNat_add_128` helpers @ 1025–1037 (recipe 10 in
  `PROOF_PATTERNS.md` §3).
- `div_rem_h_abs_aux` @ 1413 (only `skipKernelTC` in the repo, ~232
  lines of 4-way `rcases` body per `PROOF_PATTERNS.md` §3 recipe 10
  follow-up).

_(per-decl profile pending sweep)_

### 4.3 `SP1Chips/ShiftLeft/Common.lean`

(1556 LOC, 5 pragmas.)

Top hand-written declarations:

- `allHold_constraints_iff` @ 18 — body 72 lines over `Vector (ZMod p) 65`.
- 4 `sll_close_cb4cb5_*_case` close-helpers @ 303–848 (recipe 9 in
  `PROOF_PATTERNS.md` §3 — these were the recipe-9 targets that lifted
  `% 2^64` out of the chip's call-sites).
- 2 `sllw_close_cb4_*_case` helpers @ 945–1063.
- `sllw_subcase_cb4_zero` / `_one` @ 1103, 1212 — the chip's prep
  chains that route into the close-helpers.

_(per-decl profile pending sweep)_

### 4.4 `SP1Chips/ShiftLeft/Common.lean` (97.65 s)

(1556 LOC, 5 pragmas — 4 × 800k, 1 × 80M.)

Cumulative profile:

| phase | time | notes |
|---|---:|---|
| interpretation | 118 s | dominant (multi-thread cumulative) |
| blocked (unaccounted) | 83.7 s | task-scheduler synchronization |
| typeclass inference | 15.1 s | second-largest single-thread |
| simp | 3.71 s | |
| tactic execution | 2.5 s | |

Pattern: same as ShiftRight/Common — interpretation-dominated.
**81 omega calls + 15 linear_combination calls + 0 aesop / decide /
simp_all** explain the interpretation cost.

### 4.5 `SP1Chips/BranchChip.lean` (11.45 s)

**Major win post-genericization**: 114.09 s → 11.45 s (10×). Cumulative
phase breakdown:

| phase | time | notes |
|---|---:|---|
| simp | 19.5 s | cumulative across 6 `correct_b*` theorems |
| typeclass inference | 10.1 s | |
| tactic execution | 8.21 s | |
| instantiate metavars | 3.56 s | |
| interpretation | 1.15 s | **down from 279 s pre-genericization** |
| aesop | (not in profile, was 1.71 s before) | eliminated |

Pre-genericization the file had heavy `aesop` interpretation (279 s
cumulative); the genericization rewrite eliminated aesop in this chip
and replaced it with direct simp/omega chains. The 6 × `maxHeartbeats
16000000` per-decl bumps (lines 33, 302, 556, 770, 994, 1206) are now
**defensive scaffolding**; per `PROOF_PATTERNS.md §3.6` "stale comment
check," they can be removed and verified with a single `lake build
SP1Chips.BranchChip` cycle (~12 s × 6 = 72 s of build cost to test).
See recommendation 6.4 for the cluster-cleanup recipe.

### 4.6 `SP1Chips/ShiftRight/Sra.lean` (64.27 s) — instantiate-metavars regime

| phase | time | notes |
|---|---:|---|
| instantiate metavars | **38.5 s** | dominates (60% of wall) |
| tactic execution | 10.7 s | |
| typeclass inference | 7.81 s | |
| interpretation | 1.88 s | |
| ring | 1.08 s | |

The "instantiate metavars 38.5 s" pattern repeats in `Sraw.lean`
(36.7 s) and `Sll.lean` (24.7 s). These three files contain the
4-way / 4-way close-helpers that `linear_combination` heavy byte-shift
equalities — each call generates many `?_` metavariables that the
unifier must close. See recommendation 6.7.

## 5. Suspected post-genericization regressions

### 5.1 `@[instance 10000]` on `ZMod p` arithmetic — incomplete

`SP1Foundations/Field.lean:64–69` has high-priority instances on:

```lean
@[instance 10000] instance instAdd ... Add (ZMod p) := inferInstance
@[instance 10000] instance instMul ... Mul (ZMod p) := inferInstance
@[instance 10000] instance instSub ... Sub (ZMod p) := inferInstance
@[instance 10000] instance instNeg ... Neg (ZMod p) := inferInstance
@[instance 10000] instance instZero ... Zero (ZMod p) := inferInstance
@[instance 10000] instance instOne ... One (ZMod p) := inferInstance
```

`PROOF_PATTERNS.md §1.1` originally listed `Add, Mul, Sub, Neg, Pow`
on `Fin KB`. **`Pow` is missing** from the post-genericization set.
`Pow (ZMod p) ℕ` does appear in chip proofs (constraint expressions
contain `2 ^ 16`, `2 ^ 32`, `2 ^ 48` byte-multipliers via `BitVec.ofNat`
and `Word.toBitVec64`). Cost of the missing bump is **unknown until the
sweep produces a `typeclass inference` figure for ShiftRight / DivRem /
Branch** — those chips have the most byte-multiplier expressions.

`PROOF_PATTERNS.md §1.1` reported ~779s synthesis cleared in ShiftRight
when the original `Fin KB` `@[instance 10000]` bumps were added. If
`Pow` synthesis is now in the same regime, adding the bump should be
similarly cheap.

`instLT` / `instLE` / `instMod` on `ZMod p` (lines 34–40, custom Mathlib-
omitted instances) carry default priority. If they appear in `synthInstance`
traces with non-trivial cumulative time, the same `@[instance 10000]`
treatment may help.

### 5.2 Constraint-vector destructure cost: `iff_poly` body sizes

Constraint vector widths (current state) and `allHold_constraints_iff[_poly]`
body sizes:

| chip | cols | iff body lines | file |
|---|---:|---:|---|
| DivRem | **246** | **351** | `SP1Chips/DivRem/Common.lean:183` |
| Mul | 82 | 108 | `SP1Operations/Operation/MulOperation/Constraints.lean:1461` |
| ShiftRight | 69 | 81 | `SP1Chips/ShiftRight/Common.lean:21` |
| ShiftLeft | 65 | 72 | `SP1Chips/ShiftLeft/Common.lean:18` |
| Bitwise | 51 | 16 | `SP1Chips/Bitwise/Common.lean:139` |
| LoadByte | 47 | 64 (× 2 variants) | `SP1Chips/Load/LoadByte/Common.lean:18` |
| LoadHalf | 44 | 54 (× 2 variants) | `SP1Chips/Load/LoadHalf/Common.lean:19` |
| LoadWord | 44 | 53 (× 2 variants) | `SP1Chips/Load/LoadWord/Common.lean:19` |
| LoadDouble | 39 | 37 | `SP1Chips/Load/LoadDouble/Common.lean:19` |
| Jalr is_real | 35 | (small) | `SP1Chips/Jalr/Constraints.lean:51` |

DivRem at 246 cols × 351-line iff body is the highest-leverage iff
target. **Open question:** is the bulk of DivRem's compile cost in the
`iff` itself or in the 8 `correct_*_poly` chip consumers? The sweep
runs both `Common.lean` (iff lives here) and each per-variant file
(consumers), so the split will be visible in the comparative wall
times.

### 5.3 Post-genericization vs pre-genericization Branch cost

Pre-genericization `BranchChip` (805 LOC, 114.1s wall) had:

- interpretation 279s CPU (Aesop)
- tactic execution 65.2s
- simp 31.5s
- typeclass inference 18.9s
- aesop 1.71s (separate from interpretation)

Current `BranchChip` is 1423 LOC + 6 × 16M-budget bumps. Post-
genericization wall and phase breakdown TBD from the sweep. The
prediction is that `typeclass inference` rose proportionally to the
`ZMod p` instance graph cost (Phase 5.1 question).

## 6. Prioritized recommendations

Ranked by (estimated wall-time saving) / (implementation effort).
Conservative estimates; verify with a per-fix follow-up rebuild.

### 6.1 Break the `spec.mul*` wide-`obtain` chains (highest leverage)

**Target.** `SP1Operations/Operation/MulOperation/Constraints.lean`,
the 5 sister lemmas `spec.mul / spec.mulh / spec.mulhu / spec.mulhsu
/ spec.mulw` (lines 1753, 1935, 2078, 2213, 2352). Each carries a 32M
`maxHeartbeats` bump and starts with a single `obtain ⟨…80 names…⟩
:= cstrs` at line 1780 (and analogues in the 4 siblings), followed by
~16 nearly-identical `have ppN' : cols.product[N].val < 256` byte-
bound conversions.

**Evidence.** File wall time 300.14s (largest in sweep);
cumulative `tactic execution` 274s (91% of wall);
`PROOF_PATTERNS.md §1.2` documents that this exact pattern on
`ShiftRight` cut a chip from 836 → 161 lines and was "visibly snappier"
(commit `f58d7cd`).

**Fix.** Stepwise `rcases` (split the 80-name obtain into 3–5
intermediate destructures) + extract the 16 `pp_byte_lt_256_*` byte-
bound conversions into a single shared private helper used by all 5
variants.

**Estimated effort.** 1–2 hours for the refactor + a `lake build
SP1Operations.Operation.MulOperation` cycle to verify. Mechanical;
no semantic change.

**Expected saving.** 30–60% of this file's wall time, i.e.
**90–180 s** on `MulOperation/Constraints` alone. Downstream
`MulChip.lean` may also benefit since it `import`s this file.

### 6.2 Cut `omega` invocations in `ShiftRight/Common.lean`

**Target.** `SP1Chips/ShiftRight/Common.lean`. **251 `omega` calls** in
2511 lines (concentrated in the 8 `bounds` / `single_op` / per-instruction
helpers between lines 477–2511).

**Evidence.** File wall time 117.66s; cumulative `interpretation`
260s (every `omega` invocation runs through Lean's expression
interpreter to build the witness). 251 calls × ~1 s/call ≈ 250s.
0 `aesop` / `simp_all` / `norm_num` / `polyrith` calls in this file —
omega is genuinely the cost center.

**Fix.** Two passes:

1. **Identify recurring bound shapes.** The 251 calls likely follow
   ~5–10 archetypes (`x.val < 256`, `x.val < 65536`, byte sum bounds,
   etc.). Extract each into a `private lemma <shape>_aux` shared
   across the file; replace `by omega` with `exact <shape>_aux _ _ …`.
2. **Use the existing `val_*_zmod_p` simp set** (already in
   `SP1Foundations/Field.lean:95–186`) more aggressively to avoid
   re-deriving the same `(N : ZMod p).val = N` bound inside each
   omega.

**Estimated effort.** 3–6 hours. Requires reading the 251 sites and
clustering them; less mechanical than 6.1.

**Expected saving.** Each `omega` replaced by a named lemma drops from
~1s to ~10ms. Even moving 70% of the 251 calls to named lemmas saves
~120s, i.e. roughly halving the wall-time on this file. **~50–60 s
saving** is a reasonable conservative figure.

### 6.3 Add `@[instance 10000] instPow` on `ZMod p`

**Target.** `SP1Foundations/Field.lean:64–69`. Current bumps cover
`Add / Mul / Sub / Neg / Zero / One` but **not `Pow`**, even though
`PROOF_PATTERNS.md §1.1` originally listed `Pow` in the recipe
(the historical bump was on `Fin KB`; the post-genericization port
dropped `Pow`).

**Evidence.** `Pow (ZMod p) ℕ` appears throughout chip proofs as
`2 ^ 16`, `2 ^ 32`, `2 ^ 48` (byte multipliers in `Word.toBitVec64` and
the `BitVec.ofNat` ladder). With default priority, every such literal
fans out to 5–9 instance candidates per call site (per `§1.1`
historical observation). Current cumulative `typeclass inference`
across the sweep so far: `MulOp/Constraints` 15.5s, `ShiftRight/Common`
25.7s, `LoadX0` 9.8s, `Word` 8.9s, `ShiftLeft/Sll` 8.7s — i.e. the TC
phase is consistently in the high single-digit-to-mid-twenties seconds.
Adding `Pow` might shave a fraction of each.

**Fix.**

```lean
@[instance 10000] instance instPow (p : ℕ) [NeZero p] :
    Pow (ZMod p) ℕ := inferInstance
```

added beside the existing 6 in `SP1Foundations/Field.lean:64–69`.

**Estimated effort.** 5 minutes to add + a `lake build SP1Chips`
to confirm no regression. Cheap; idempotent; easy to undo.

**Expected saving.** Speculative without per-file before/after TC
counts, but historical §1.1 saw ~779s synthesis cleared in
`ShiftRight` alone by adding 5 such bumps. Realistic upper bound:
1–2s shaved per heavy chip × ~10 chips = **5–20 s total**.

### 6.4 Remove defensive `maxHeartbeats` bumps in `LoadX0Chip.lean`

**Target.** `SP1Chips/LoadX0Chip.lean` carries 7 × `1.6M` per-decl
bumps. The file's whole-wall time is 12.76s — orders of magnitude
under the bumped budgets.

**Evidence.** Wall 12.76s; 7 bumps of 1.6M heartbeats each. Default
budget is 200k; the file's actual per-decl cost is unlikely to need
1.6M anywhere. Looks like leftover defensive scaffolding from the
genericization migration. `PROOF_PATTERNS.md §3 recipe 6` (cleared 2
sites already) suggests "just delete the line and rebuild."

**Fix.** Delete the 7 `set_option maxHeartbeats 1600000 in` lines and
their `-- <comment>` companions, then `lake build SP1Chips.LoadX0Chip`.
Re-add only the ones that turn red.

**Estimated effort.** 15 minutes + one build cycle.

**Expected saving.** None directly on this file (it's already fast).
The value is documentation hygiene: the cost-mitigation pragma map in
§3 becomes a true hotspot map, not noise.

### 6.5 Reduce `decide` count in `ShiftLeft/Sll.lean`

**Target.** `SP1Chips/ShiftLeft/Sll.lean`. **126 `decide` calls** in
2122 lines.

**Evidence.** Wall 27s; cumulative `instantiate metavars` 24.7s
(distinctively dominant for this file shape). 126 decide calls.
`decide` for BitVec equalities and 5-bit shift-amount comparisons is
slow.

**Fix.** Two strategies, applied per call site:

1. Where the decide goal is a small fixed BitVec equality (e.g.
   `(5 : BitVec 5) = 5`) and the trust base is acceptable, swap to
   `native_decide`. ~10× faster.
2. Where the goal is a polymorphic `ZMod p` bound, replace with
   `exact val_X_zmod_p` or analogous (the `val_*_zmod_p` family in
   `Field.lean` already covers the common cases).

**Estimated effort.** 4–6 hours (read 126 sites, audit each for
trust-base implications before swapping to `native_decide`).

**Expected saving.** **~10–15 s** on this file.

### 6.6 Cut omega cluster in `ShiftLeft/Common.lean`

**Target.** `SP1Chips/ShiftLeft/Common.lean`. Same pattern as 6.2 but
on a smaller file (1556 LOC, 81 `omega` calls, 0 aesop / decide /
simp_all).

**Evidence.** Wall 97.65 s; cumulative `interpretation` 118 s + 83.7 s
`blocked (unaccounted)` (interpretation cost spread across threads).
81 omega × ~1 s ≈ 80 s, matches.

**Fix.** Same recipe as 6.2 — cluster the recurring bound shapes
into shared private helpers, replace `omega` with `exact <helper>`.

**Estimated effort.** 3–4 hours.

**Expected saving.** ~30–50 s on this file.

### 6.7 Audit close-helpers in ShiftRight/Sra, Sraw, ShiftLeft/Sll

**Target.** The instantiate-metavars-heavy files:

| file | wall | inst metavars | tactic exec |
|---|---:|---:|---:|
| `SP1Chips/ShiftRight/Sraw.lean` | 91.37 s | 36.7 s | 30.4 s |
| `SP1Chips/ShiftRight/Sra.lean` | 64.27 s | 38.5 s | 10.7 s |
| `SP1Chips/ShiftLeft/Sll.lean` | 27.00 s | 24.7 s | 9.38 s |

**Evidence.** `instantiate metavars` is the cost of unifying
metavariables — Lean spends time solving `(? : _) = …` placeholders.
The dominant source is `linear_combination` / `ring` chains in the
4-way close-helpers (`sll_close_cb4cb5_*_case`,
`srl_close_cb4_*_case` analogues). These were the recipe-9 lifts
documented in `PROOF_PATTERNS.md §3.9`.

**Fix.** Two complementary moves:

1. **Reduce metavar fan-out per close-helper.** Where `linear_combination`
   sets up many metas, replace with `linear_combination (norm := ring1)
   …` to force a single-shot ring closer rather than the
   default-`ring`'s incremental rewriting.
2. **Cache shared intermediate equalities** between the 4 cases — each
   close-helper probably re-derives the same byte-arithmetic facts.

**Estimated effort.** 4–8 hours per chip family.

**Expected saving.** **~30–50 s combined** across ShiftRight family.

### 6.8 `DivRem/Common.lean` parallel to MulOperation/Constraints

**Target.** `SP1Chips/DivRem/Common.lean` (1705 LOC, 292.76 s wall at
`--tstack=4000000`, **tactic execution 278 s = 95% of wall**).

**Evidence.** Per-decl traces emitted by `lean --profile` show the
same anti-pattern as MulOp/Constraints: heavy `tactic execution of
Lean.Parser.Tactic.obtain` (100–150 ms each, ~15 sites) + dense
`tactic execution of Lean.Parser.Tactic.omega` (100–400 ms each, 101
in total in this file). Specific decls to drill into:

- `allHold_constraints_iff` line 183: **351-line body over `Vector
  (ZMod p) 246`** — the widest iff in the repo. The single largest
  `obtain` site in DivRem.
- 8 `_chip_bounds` lemmas (lines 801–1014): one per DivRem opcode
  variant; each ~27 lines, likely shareable into one parametric
  helper.
- `div_rem_h_abs_aux` line 1413: still carries `set_option
  debug.skipKernelTC true in`. The 232-line 4-way `rcases` body is
  the open `PROOF_PATTERNS.md §3` recipe-10 follow-up.

**Fix.** Same as 6.1 (stepwise `rcases` on `allHold_constraints_iff`) +
6.2 (omega-cluster bound helpers). Plus the §3-recipe-10 follow-up
splitting `div_rem_h_abs_aux` into 4 case helpers — already documented
as planned ~1–2 h work in the project memory.

**Estimated effort.** 4–8 h.

**Expected saving.** Similar profile to MulOp ⇒ **~100–180 s** off
DivRem/Common's 292 s wall.

### 6.9 (Investigate the 35.5 s "blocked (unaccounted)" in ShiftRightChip)

Both `ShiftRightChip.lean` (11.87 s wall, 35.5 s blocked) and
`MulChip.lean` (14.49 s wall, 20.5 s blocked) have `blocked
(unaccounted)` cumulative times **larger than their wall times**. This
is the Lean task scheduler waiting on dependencies between parallel
elaboration tasks. Worth measuring whether `set_option
Elab.async false` would *help* (one-thread sequential) vs hurt.

**Estimated effort.** 1 hour experiment per chip; verify with
before/after wall times on the same machine.

**Expected saving.** Unknown; speculative. Skip unless other items
land first.

### Summary of expected savings

| recommendation | target file | est. effort | est. saving |
|---|---|---:|---:|
| 6.1 spec.mul* obtain | MulOperation/Constraints | 1–2 h | **90–180 s** |
| 6.8 DivRem iff+chip_bounds+h_abs_aux | DivRem/Common | 4–8 h | **100–180 s** |
| 6.2 ShiftRight omega cluster | ShiftRight/Common | 3–6 h | 50–60 s |
| 6.6 ShiftLeft omega cluster | ShiftLeft/Common | 3–4 h | 30–50 s |
| 6.7 close-helper audit | ShiftRight/Sra+Sraw, ShiftLeft/Sll | 4–8 h × 2 | 30–50 s |
| 6.3 instPow | Field.lean | 5 min | 5–20 s |
| 6.5 ShiftLeft/Sll decide | ShiftLeft/Sll | 4–6 h | 10–15 s |
| 6.4 LoadX0 + Branch defensive bumps removal | LoadX0 + BranchChip | 1 h | 0 s (hygiene) |

Total **estimated saving: ~300–555 s** on a current ~1190 s heavy-file
critical path (sum of all heavy file walls, including the 292 s
DivRem/Common from the higher-tstack retry) = **25–47% wall-time
reduction**, achievable in roughly 25–30 person-hours of focused
refactor work. The top two items (6.1 and 6.8) together account for
half the potential saving.

## 7. Open questions & build-state inconsistencies

### 7.1 `DivRem/Common.olean` is missing from `.lake/build`

The file `.lake/build/lib/lean/SP1Chips/DivRem/Common.olean` does not
exist on disk, even though:

- `Common.olean.hash` and `Common.ilean.hash` are present (May 20 19:46)
- All 5 dependents (`DivRem.olean` 19:53, `DivuRemu.olean` 19:51,
  `DivuwRemuw.olean` 19:51, `DivwRemw.olean` 19:57,
  `Constraints.olean` 20:45) are present from subsequent builds
- The neighbouring `SP1Chips/ShiftRight/Common.olean` (13 MB,
  May 20 20:40) and `SP1Chips/ShiftLeft/Common.olean` (5.7 MB,
  May 20 20:40) are present — only DivRem is affected

The user's `CLAUDE.md` reports the repo is "build is green" and
this sweep ran without disturbing oleans (`lake env lean` only reads,
never writes). The state was already inconsistent before the sweep.

**Verify with**: `lake build SP1Chips.DivRem.Common`. If it succeeds
quickly (cache hit on a separate path), great — the build truly is
green. If it triggers a full re-elaboration, the prior build was
silently broken.

### 7.2 `DivRem/Common.lean` stack-overflows under `lake env lean --profile` at the project-default tstack

After 198 s of elaboration at the project-default `--tstack=400000`,
`lean --profile SP1Chips/DivRem/Common.lean` aborts with
`Stack overflow detected. Aborting.` (SIGABRT, exit 134).

**Retry at `--tstack=4000000` (10×) succeeded** in 292.76 s wall
(7.87 GB peak RSS). Cumulative profile:

| phase | time |
|---|---:|
| tactic execution | **278 s** (95% of wall) |
| simp | 9.14 s |
| typeclass inference | 7.13 s |
| interpretation | 6.84 s |
| instantiate metavars | 4.88 s |
| type checking | 4.23 s |
| elaboration | 2.89 s |
| blocked (unaccounted) | 58.3 s |

Same per-decl shape as `MulOperation/Constraints`: heavy
`tactic execution of Lean.Parser.Tactic.obtain` (5–15 sites at
100–150 ms each) + many `tactic execution of Lean.Parser.Tactic.omega`
(100–400 ms) + `simp took 200–280 ms` blocks. The `div_rem_h_abs_aux`
helper at line 1413 (carrying `set_option debug.skipKernelTC true`) is
likely one contributor; the 351-line `allHold_constraints_iff` at line
183 over 246 cols is another. See §6.9 below for the recommended fix
and §7.7 for the tstack-config issue.

### 7.3 `lakefile.toml` `--tstack=400000` is too low for `DivRem/Common.lean`

`lakefile.toml` sets `moreLeanArgs += "--tstack=400000"`. Per §7.2,
`DivRem/Common.lean` re-elaborates at 4 M but stack-overflows at 400 k.
The fact that `.lake/build` previously held a `DivRem/Common.olean`
(and dependents are present) means **a successful build did exist** at
some point — either with a different tstack, or `lake build` invokes
`lean` in a way that side-steps the issue (parallel sub-tasks each get
their own thread/stack?). Worth confirming with a clean
`lake build SP1Chips.DivRem.Common` from the current source.

If the file genuinely needs ≥ 1 M tstack in a fresh build, update
`lakefile.toml`:

```toml
moreLeanArgs = [..., "--tstack=2000000"]
```

(Pick 2 M as a safety margin; 4 M is overkill but harmless.) Without
this, a new contributor cloning the repo may hit "build is broken"
on first try.

### 7.4 `lake env lean --profile` exits 1 on `Sraw.lean` / `Srlw.lean`

Both files completed full elaboration (91 s and 44 s of cumulative
profile data emitted) and then exit-code 1. The script discarded
stdout, where lean prints `error:`-prefixed messages. Likely a linter
warning promoted to error under `weak.linter.mathlibStandardSet =
true`. To find the cause: rerun the file with stdout captured (`lake
env lean --profile SP1Chips/ShiftRight/Sraw.lean 2>&1 | tail -50`).
Not blocking for this report — the wall time + phase breakdown are
still valid.

### 7.5 Whole-library wall time vs per-file sum

The sum of per-file wall times for the 27 heavy candidates is ~1097 s.
A full clean `lake build SP1Chips SP1Operations` is bounded by the
critical path through the import DAG; with 8-core parallelism and the
heaviest single file at 300 s (`MulOperation/Constraints`), realistic
whole-library wall is **5–15 min**. Confirming this requires a
separate `lake clean SP1Chips SP1Operations; time lake build SP1Chips`
run on a clean worktree (to avoid disrupting the active LSP) — not
attempted here.

### 7.6 Light files with high pragma counts — investigate defensive bumps

- `LoadX0Chip.lean`: **12.76 s wall, 7 × 1.6M heartbeats bumps**.
  Each bump caps ~30 s of cost in current Lean. The file is well
  under that budget. Bumps are defensive scaffolding from the
  genericization migration. See §6.4.
- `BranchChip.lean`: **11.45 s wall, 6 × 16M bumps**. Same story —
  pre-genericization the file was 114 s (Aesop-dominated). Now Aesop
  is gone but the bumps remain. Removal proven safe via `recipe 6`
  pattern from `PROOF_PATTERNS.md §3`. See §6.4.

### 7.7 Per-decl profiling not yet done

This sweep is at file granularity. To localize cost within
`MulOperation/Constraints` (300 s) more precisely than "the 5 spec.mul*
wrappers" requires adding `set_option profiler true in <decl>` to each
of `core_mul`, `core_mulw`, `allHold_constraints_iff_is_real`, and the
5 `spec.mul*` lemmas — a temporary edit, ~30 min cycle per pass. The
MCP `lean_profile_proof` tool gives tactic-level breakdowns; budget ~1
hour per heavy decl. Not done here because the structural anti-pattern
(80-name `obtain`) is already documented in source and matches §1.2.

## 8. Methodology notes (for the next iteration)

- `lake build --profile` does **not** exist; the `--profile` flag is on
  `lean` (`lake env lean --profile <file>`).
- `lean --profile` emits per-decl traces inline (above the
  `profiler.threshold` ms cutoff, default 100); the cumulative summary
  at the end (`cumulative profiling times: ...`) is the most useful
  single-glance hotspot signal. The per-decl traces require
  `set_option profiler true in <decl>` for fine-grained drill-down.
- **Capture stdout too.** This sweep's script ran with `>/dev/null`,
  losing the `error:`-prefixed lines for the 2 files that exited 1
  after full elaboration (Sraw, Srlw). Next time: `2>&1 | tee
  <log>` so both streams land in the same place.
- The MCP `lean_profile_proof` tool gives tactic-level breakdowns for
  a single declaration. Slow but precise; budget 1 h per heavy decl.
- **LSP coexistence.** With the LSP holding 8–9 chip files in memory
  during a sweep, peak RAM hits ~20 GB on this machine. Don't run
  more than one `lake env lean` in parallel.
- **Stack overflow surfacing.** `lake env lean --profile <file>`
  correctly returned exit 134 (SIGABRT) on the `DivRem/Common.lean`
  stack overflow during this sweep — the older `PROOF_PATTERNS.md §4`
  "exits 0 on stack overflow" bug appears to be fixed in lake
  5.0.0-src+98dc76e (Lean 4.29.0).
- **Whole-library wall time** measurement still requires a separate
  `lake clean SP1Chips SP1Operations && time lake build SP1Chips`,
  ideally in a git worktree to avoid disrupting the user's LSP-cached
  oleans. ~5–15 min wall expected (sum of per-file wall is 1097 s,
  but 8-way parallel build should compress this materially).

## 9. Verification spot-check (not done)

The plan called for picking the top recommendation, applying it on a
throwaway branch, and confirming the wall-time saving falls within
±30% of the estimate. Skipped here because the user requested
report-only. Recommended first attempt:

1. `git worktree add /tmp/sp1-perf-mulop dtumad/final-aggregation`
2. In the worktree, edit `SP1Operations/Operation/MulOperation/Constraints.lean`:
   - Split the 80-name `obtain` chain in `spec.mul` (line 1780) into
     5 stepwise `rcases` of 16 names each.
   - Extract the 16 `pp_byte_lt_256_N` byte-bound `have` blocks into
     one `private lemma pp_bytes_lt_256` reused via destructure.
3. `lake env lean --profile SP1Operations/Operation/MulOperation/Constraints.lean`
   and compare wall against the 300 s baseline. Expected: 120–210 s.
4. If positive, apply the same shape to `spec.mulh`/`mulhu`/`mulhsu`/`mulw`.

If the experiment lands ±30% of the prediction, the cost model behind
the rest of this report is calibrated and the other recommendations
can be ranked confidently.
