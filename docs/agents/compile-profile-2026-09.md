# Compile-time profile, 2026-09 (fork workstream A baseline)

Point-in-time measurement record for the compile-time investigation on the fork; not evergreen
documentation. Numbers here are the baseline every later build change is judged against. Regenerate
with the commands below rather than editing figures by hand.

## Method

Two complementary sources:

1. **A real parallel build.** The first cold CI build of fork PR #1 (workflow run `35459095386`,
   job `105939589524`, `ubuntu-latest`: 4 vCPU, 16 GB; toolchain v4.32.2; mathlib from
   `lake exe cache get`; everything else built from source). Harvested with
   `scripts/profile_aggregate.py --lake-log <job log> --out .lake/profile/ci-cold-4core`, which
   parses Lake's per-module `Built <module> (<N>s)` lines. Per-module times are the elaboration
   time Lake reports for that module inside a parallel build.
2. **Isolated per-module profiles.** `scripts/profile_compile.sh` (one `lean -Dprofiler=true` per
   module against a warm olean cache, sequential, with the package flags and the eight style-linter
   flags applied) and `scripts/profile_aggregate.py --profile-dir`, which splits each module's
   time into Lean's profiler categories (import, elaboration, simp, tactic execution, type
   checking, typeclass inference, codegen, linting, `blocked (unaccounted)` = the main thread
   waiting on asynchronously elaborated proof bodies). Machine: the maintainer's arm64 macOS host.

## Cold CI build: wall time and where the CPU goes

| Step | Duration |
|---|---|
| checkout + free disk space | 1 min 48 s |
| cache restore (miss, cold) | seconds |
| elan toolchain install | 11 s |
| `lake exe cache get` (mathlib) | 1 min 55 s |
| `lake build` (all three default targets, 4171 jobs) | **1 h 48 min** |
| cache save (`.lake/build` + non-mathlib packages) | 13 s |
| whole `build` job | 1 h 52 min |

Summed per-module elaboration time was 18,951 s (5.3 CPU-hours) over 1,161 built modules, so the
4-core runner reached a parallel speed-up of about 2.9. On the warm cache the downstream jobs took
3 min 34 s (`lint`) and 3 min 28 s (`audit`) including the mathlib cache download and the replayed
`lake build`; `test` (the `SP1CleanTest` battery, witgen regeneration, and test census) is the
long warm job.

| Modules | Total s | Mean | Median | p90 | p95 | Max |
|---:|---:|---:|---:|---:|---:|---:|
| 1161 | 18951.1 | 16.32 | 6.10 | 29.00 | 43.00 | 3930.00 |

### Per pillar

| Pillar | Modules | Seconds | Share |
|---|---:|---:|---:|
| `LeanRV64D` (generated Sail model) | 124 | 5255.1 | 27.7 % |
| `SP1Clean.Proofs` | 300 | 5128.4 | 27.1 % |
| `SP1Clean.Soundness` | 203 | 3276.0 | 17.3 % |
| `SP1Clean.Faithful` | 45 | 1372.8 | 7.2 % |
| `SP1Clean.Native` | 133 | 1120.9 | 5.9 % |
| `SP1Clean.Extracted` | 62 | 795.1 | 4.2 % |
| `SP1Clean.Model` | 88 | 679.9 | 3.6 % |
| `SP1Clean.FormalModel` | 64 | 466.4 | 2.5 % |
| `Clean` | 57 | 417.8 | 2.2 % |
| `SP1Clean.Composition` | 12 | 197.8 | 1.0 % |
| `ToClean` | 24 | 88.6 | 0.5 % |
| `SP1Clean.Math` | 10 | 56.9 | 0.3 % |
| `PolyFun`, `Sail`, `ToMathlib`, `RISCV`, other | 38 | 95.8 | 0.5 % |

The alignment-only pillars (`Faithful`, `Soundness`, `Composition`, the `Extracted` oracles, and
the `Proofs/Chips/*/{Bridge,Contracts}` and `Proofs/Sail`/`Proofs/Completeness` families) account
for well over half of the project's own CPU; the default-build split (workstream A2) moves them out
of PR CI.

### The generated Sail model

`LeanRV64D` costs 5,255 s, 27.7 % of the whole cold build, and one module dominates:

| Seconds | Module | Lines |
|---:|---|---:|
| 3930 | `LeanRV64D.RvfiDii` | 1,269 |
| 432 | `LeanRV64D.InstsEnd` | 72,378 |
| 160 | `LeanRV64D.ZicsrInsts` | 22,304 |
| 145 | `LeanRV64D.Defs` | 2,064 |
| 141 | `LeanRV64D.PlatformConfig` | 11,216 |

`RvfiDii` (the RVFI-DII trace interface) takes 3 s per line, about 100× the model's average, and
it cannot be dropped by import narrowing: `LeanRV64D.Step`, which defines `try_step`, imports it.
It is generated code from the pinned snapshot, so any fix lands in the generator configuration or
upstream, not in this tree. Its isolated local profile is recorded below.

### Top project modules (cold CI build)

| Seconds | Module |
|---:|---|
| 456 | `SP1Clean.Proofs.Sail.InstructionDecode.Families` |
| 395 | `SP1Clean.Soundness.Grounding.RTypeChips` |
| 366 | `SP1Clean.Extracted.SystemOracle.Global` |
| 172 | `SP1Clean.Soundness.GroundingAdapter` |
| 135 | `SP1Clean.Proofs.Sail.Advance` |
| 133 | `SP1Clean.Proofs.Chips.ShiftRightChip.Core` |
| 132 | `SP1Clean.Soundness.HostQueueCPUReplay` |
| 131 | `SP1Clean.Soundness.Grounding.MemoryChips` |
| 110 | `SP1Clean.Faithful.SyscallInstrsChip` |
| 108 | `SP1Clean.Composition.PreprocessedProviders` |
| 107 | `SP1Clean.Faithful.MulChip` |
| 97 | `SP1Clean.Soundness.SyscallWiring` |
| 90 | `SP1Clean.Proofs.Completeness.ProviderInteractions` |
| 89 | `SP1Clean.Proofs.Chips.DivRemChip.Evidence` |
| 85 | `SP1Clean.Model.Semantics.Decode` |
| 76 | `SP1Clean.Extracted.ChipOracle.DivRem` |
| 72 | `SP1Clean.Soundness.ChipContracts` |
| 71 | `SP1Clean.Faithful.BranchChip` |
| 62 | `SP1Clean.Proofs.Chips.MulChip.Formal` |
| 60 | `SP1Clean.Proofs.Chips.LoadWordChip.Formal` |
| 59 | `SP1Clean.Native.Operations.MulOperation.RawSpec` |
| 59 | `SP1Clean.Proofs.Chips.UTypeChip.Complete` |
| 58 | `SP1Clean.Proofs.Chips.LoadHalfChip.Formal` |
| 58 | `SP1Clean.Soundness.TypedState` |
| 57 | `SP1Clean.Proofs.Chips.StoreWordChip.Formal` |
| 56 | `SP1Clean.Extracted.SystemOracle.PublicValues` |
| 56 | `SP1Clean.Faithful.ALUTypeReader` |
| 55 | `SP1Clean.Proofs.Chips.LoadByteChip.Formal` |
| 55 | `SP1Clean.Faithful.LtChip` |
| 54 | `SP1Clean.Proofs.Operations.DivRemOperation.Core` |

The per-chip `Formal.lean` files cluster at 50–60 s and the per-chip `Bridge.lean` files at
8–10 s locally (the incremental-build logs), a shared fixed cost per chip family rather than one
outlier. The complete ranking is in `.lake/profile/ci-cold-4core.tsv` after re-harvesting.

## Isolated profiles of the hottest modules

Local arm64 macOS host, one `lean` process per module against a warm cache, package flags and the
eight style-linter flags applied (`-Dprofiler=true`). Category seconds are Lean's own accounting and
can exceed wall time because proof bodies elaborate on parallel threads; `blocked` is the main
thread waiting for them. The CI column is the same module in the cold 4-core build.

| Module | Local wall s | CI s | Dominant categories (s) |
|---|---:|---:|---|
| `Soundness/Grounding/RTypeChips` | 101.5 | 395 | type checking 98.0, blocked 97.8 |
| `Soundness/GroundingAdapter` | 70.9 | 172 | type checking 68.5 |
| `Extracted/SystemOracle/Global` | 61.2 | 366 | elaboration 53.4 |
| `Proofs/Sail/InstructionDecode/Families` | 41.6 | 456 | simp 305.0, typeclass inference 89.6, tactic execution 83.3, interpretation 18.7 |
| `Proofs/Chips/ShiftRightChip/Core` | 19.4 | 133 | interpretation 20.8, blocked 12.8, typeclass inference 8.5 |
| `Extracted/ChipOracle/DivRem` | 16.1 | 76 | elaboration 11.2 |
| `Proofs/Sail/Advance` | 14.3 | 135 | tactic execution 58.0, blocked 38.3 |
| `Model/SailWrap` | 6.3 | — | simp 13.1, typeclass inference 4.8 |
| `Proofs/Chips/LoadWordChip/Bridge` | 3.3 | — | import 1.2 |
| `Proofs/Chips/AddChip/Bridge` | 1.6 | — | import 1.2 |
| `LeanRV64D/RvfiDii` (generated) | 718.6 | 3930 | do element elaborator 671.0, typeclass inference 22.8, elaboration 12.9 |

What the split says, module by module:

- **`RTypeChips` and `GroundingAdapter` are kernel-bound.** Almost all of their time is `type
  checking`: the kernel re-checking large proof terms, the "kernel size cliff" that Clean's
  `doc/performance-problems.md` describes (`have`-bound terms are never pruned; composition depth
  counts). The lever is structural: state the per-chip grounding facts as standalone theorems over
  opaque variables so each is kernel-checked separately, and cut composition depth, not `simp only`.
- **`Global` is elaborator-bound** on the single 1,239-binding let-chain the Rust emitter cannot
  chunk; only the generator can change it. It has one importer and is alignment-only.
- **`InstructionDecode/Families` is `simp`-bound and highly parallel** (305 CPU-s of `simp` for
  42 s of wall), which is why it was the slowest project module on the 4-core runner. Candidate
  levers: `simp only` sets for the per-family decode lemmas, or `decide`-style closed evaluation.
- **`ShiftRightChip/Core` and `Advance` are tactic-interpretation-bound** (`bv_decide`/`omega`
  heavy) with substantial async waiting; term-intrinsic per the existing proof-patterns notes.
- **The per-chip `Bridge.lean` files are import-only** (1.2 s of import, nothing else): their
  8–10 s in incremental build logs was contention, not elaboration. They are not a lever.
- **`RvfiDii`** spends 671 of 719 s in the `do`-notation elaborator on a 1,269-line generated
  file. It is imported by `LeanRV64D.Step` (which defines `try_step`), so it cannot be dropped by
  import narrowing; the fix is in the generator or an upstream Lean issue about large `do` blocks,
  and it is the single biggest item in the cold build (21 % of all CPU).

The local-to-CI ratio is roughly 4–10× per module (a slower CPU plus four-way contention), so
CI wall time is dominated by the few kernel- and `simp`-bound modules above rather than by the
long tail: 79 % of modules elaborate in under 3 s locally.

## How to regenerate

```bash
# real-build baseline from a CI job log
gh api repos/dtumad/sp1-lean/actions/jobs/<job-id>/logs > .lake/profile/ci.log
python3 scripts/profile_aggregate.py --lake-log .lake/profile/ci.log --out .lake/profile/ci --top 40

# isolated per-module sweep (about two hours sequentially; run when the machine is idle)
SKIP_BUILD=1 scripts/profile_compile.sh            # all hand-written trees
SKIP_BUILD=1 scripts/profile_compile.sh SP1Clean/Soundness/   # one subtree
```
