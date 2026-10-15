# Build semantics: where the build time goes and what each second buys

Investigation date: 2026-09-20, on fork branch `dtumad/lakefile-modernization` at `cb2b891c`
(PR #19; toolchain v4.32.2). A point-in-time measurement record with verdicts, written for the
question "why are the build times so long, do they provide value, and how does the upstream-SP1
connection work — from the perspective of building our own thing first". Numbers here are not
maintained; regenerate them with the commands in § Reproduction. Verdicts are proposals for the
maintainer to decide per cluster, not decisions.

## Summary

1. **The build is wide, not deep.** In the local full build (1 132 modules, 14 cores) 995 modules
   take 1–10 s and account for half the time; only 18 finish under a second. Solo, every module pays
   a fixed **import floor of ≈ 1.0–1.2 s** (Mathlib's tactic closure 0.94 s / 2.6 GB resident; the
   Sail model adds 0.5 s / 1.2 GB), and `import` is the largest profiler category of the whole tree:
   1 063 s of the 2 871 s solo sweep (37 %). Under parallel builds that floor inflates most: the
   1–3 s band runs 2.3× slower on 14 local cores and 3.1× slower on the 4-vCPU CI runner than solo;
   the heavy modules inflate 1.8× and 5–6×.
2. **The cold PR-CI build is one generated file plus six minutes.** PR #19's `build` job took
   65 min: `LeanRV64D.RvfiDii` (3 308 s, 34 % of all CPU, the known Lean do-elaborator bug
   leanprover/lean4#13858) finished at minute 59 and the 201 Sail-dependent modules built in the
   last 6.5 min, after the other three cores had already finished every Sail-free module. Import
   narrowing cannot remove it — `GuestProgram` needs `try_step` from `Step.lean`, which imports
   `RvfiDii` for two lines inside a dead `if get_config_rvfi ()` branch — so the fix is the Lean
   one-liner (#13985), the Sail-backend `let _ : Unit :=` spelling, or the RVFI overlay (#6).
   Without it the same build is bounded by ≈ 6 400 CPU-s ÷ 4 ≈ 27–30 min.
3. **The claims and the cost do not line up.** The intended capstone (`Soundness/Shard/*`) has
   unfilled targets and a 48-module Model-only closure. The closed theorems are the retained
   55-table `supported_core_native_sound`, native completeness, the 25 `ChipFaithful` anchors and
   the frontier theorem `HostHintReadCPU.source_execution_with_memory`. Of the machine layer's
   1 845 s, ≈ 720 s feeds the retained theorem/completeness, ≈ 830 s is reached **only** by the
   frontier theorem, ≈ 125 s by nothing; of the chip layer's 2 398 s, 1 672 s is under the closed
   chip claims, 535 s frontier-only, 180 s reached by nothing. 73 modules are in no headline's
   import closure.
4. **The SP1 connection at the bottom is exactly 18 generated struct modules.** The proof of
   `supported_core_native_sound` uses constants from 18 `Extracted/` modules — the Rust-mirrored
   column structs the readers and nine operations use as circuit input types — and nothing else
   from `Extracted/`: no `asserts`/`interactions`, no `ChipOracle`, no `SystemOracle`. The import
   closure says otherwise (all 62, including the 4 269-line `SystemOracle/Global`) because
   `Soundness/SyscallRowSemantics` reuses `decodeSyscallRow` from `Faithful/CoreAIR`; that is a
   module-graph fact, not a proof fact. `AddOperation`/`SubOperation` already show the native
   alternative for the structs.
5. **The chip template is one third import.** The 275 chip-named modules cost 906 s solo, 305 s
   of it import; the small per-chip files (`Witgen`, `Complete`, `Bridge`, `Native/Chips/Defs`) are
   55–67 % import floor.

## Method and data

| Data set | What | Where |
|---|---|---|
| **local14** | `lake build SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest` on the maintainer's arm64 macOS host (14 cores, 36 GB), 4 225 jobs, 1 132 modules elaborated, 7 495 module-seconds. Per-module wall under 14-way parallelism. | session scratchpad `pr1/build2.log`; `scripts/build_semantics.py --out …/local14` |
| **ci4** | PR #19 `build` job (run 35533002399), `ubuntu-latest` 4 vCPU, cold cache, `lake build --wfail --iofail` of the default targets: 3 803 jobs, 711 modules elaborated, 9 709 module-seconds, 65 min wall (19:41:44–20:47:00 Z). | `gh api repos/dtumad/sp1-lean/actions/jobs/<build job>/logs` |
| **solo** | `SKIP_BUILD=1 scripts/profile_compile.sh` over all 1 004 hand-written + test modules, sequential, one `lean -Dprofiler=true` per module against warm oleans (≈ 1 h 10 min). Wall and Lean's category split per module. | `.lake/profile/sweep-2026-09-20/` (`summary.tsv`, `profile.json`, `profile.md`) |
| import floor | one-line files `import X` + `example : True := trivial`, solo, `-Dprofiler` `import` time and `/usr/bin/time -l` resident set. | scratchpad `hot/import_*.lean` |
| proof closure | a `lake env lean` script walking `getUsedConstants` transitively from a theorem and mapping constants to modules (`Environment.getModuleIdxFor?`). | scratchpad `hot/declclosure.lean` |
| claim map | import graph over the five source trees + `LeanRV64D/`, stratum from `scripts/layering.txt`, layer from the table in `scripts/build_semantics.py`, closures of thirteen headline modules. | `scripts/build_semantics.py` |

Layers (`scripts/build_semantics.py`, `LAYERS`): **L1 ISA semantics** (`Model/{Register,Sail*,RV64Semantics}`,
`Model/{Semantics,Core,Machine}/`, `Proofs/Sail/`, `Alignment/Chips/*/Bridge`); **L2 native
gadgets & chips** (`Math/`, the bus/field `Model/` files, `FormalModel/Contracts`, `Native/`,
`Proofs/Operations`, `Proofs/Chips`, `FormalModel/TraceGen`, `ToClean`/`ToMathlib`/`ToPolyFun`);
**L3 native machine** (`Soundness/`, `Proofs/Completeness`, `Alignment/Chips/*/Contracts`,
`FormalModel/{Shard*,Execution,…}`); **L4 SP1 alignment** (`Extracted/`, `Faithful/`, `Composition/`,
`Soundness/CoreAIR*`, `Soundness/SyscallRowSemantics`, `FormalModel/{CoreAIRRelation,CoreProfile,OpcodeTable}`);
**L5 tests**; **G** the generated Sail model.

## Where the time goes

### By layer

| Layer | Modules | local14 s | share | ci4 s (core build) | solo s | solo import s |
|---|---:|---:|---:|---:|---:|---:|
| L1 ISA semantics | 105 | 608 | 8.1 % | 526 | 254 | 108 |
| L2 native gadgets/chips | 468 | 2 398 | 32.0 % | 4 475 | 1 120 | 477 |
| L3 native machine | 261 | 1 845 | 24.6 % | 96 (RowView only) | 926 | 305 |
| L4 SP1 alignment | 125 | 855 | 11.4 % | 114 (the 26 core structs) | 421 | 119 |
| L5 tests | 49 | 305 | 4.1 % | — | 150 | 55 |
| G generated Sail model | 161 | 1 485 | 19.8 % | 4 499 | — | — |

Solo category split per layer (seconds; categories can exceed wall because proof bodies elaborate
on parallel threads; `blocked` is the main thread waiting for them):

| Layer | solo wall | import | elaboration | simp | tactic exec | interpretation | type checking | typeclass | blocked |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| L1 | 254 | 108 | 11 | 371 | 212 | 119 | 24 | 121 | 47 |
| L2 | 1 120 | 477 | 35 | 199 | 196 | 431 | 94 | 137 | 27 |
| L3 | 926 | 305 | 131 | 114 | 212 | 279 | 307 | 67 | 124 |
| L4 | 421 | 119 | 104 | 176 | 139 | 130 | 42 | 50 | 7 |
| L5 | 150 | 55 | 4 | 1 | 4 | 69 | 30 | 4 | 368 |
| all | 2 871 | 1 063 | 285 | 862 | 764 | 1 028 | 496 | 378 | 573 |

Reading: L2 (the chips) is import + tactic *interpretation* (`omega`/`decide`/`bv_decide`/
`linear_combination` running in the interpreter) + `simp`; L3 (the machine) is the only layer
where **kernel type checking** is a top category (307 s: `Grounding/RTypeChips` 95,
`GroundingAdapter` 68, `ChipContracts` 28, `HostQueueCPUReplay` 26, `SyscallWiring` 22 — the
"kernel size cliff" family); L1 is `simp`-bound through one file (`InstructionDecode/Families`,
304 s of `simp` for 41 s of wall); L4 is elaboration-bound on generated let-chains (`Global` 56 s)
and statement-size-bound in the faithfulness monoliths.

### Distribution: a wide band, not a few giants

| local14 band | modules | seconds | share |  | ci4 band | modules | seconds | share |
|---|---:|---:|---:|---|---|---:|---:|---:|
| ≥ 60 s | 6 | 1 649 | 22.0 % |  | ≥ 60 s | 9 | 4 486 | 46.2 % |
| 10–60 s | 113 | 2 054 | 27.4 % |  | 10–60 s | 108 | 2 702 | 27.8 % |
| 1–10 s | 995 | 3 779 | 50.4 % |  | 1–10 s | 588 | 2 517 | 25.9 % |
| < 1 s | 18 | 13 | 0.2 % |  | < 1 s | 6 | 5 | 0.1 % |

Cumulative (local14): top 1 = 14 %, top 10 = 25 %, top 50 = 38 %, top 200 = 58 %. Median 3.8 s,
p90 10 s. Solo: median 1.72 s, p90 5.0 s, 79 % of modules under 3 s.

### The import floor

Solo `import` time and resident set of a one-line file importing X:

| X | import | RSS |
|---|---:|---:|
| `Mathlib.Tactic.Ring` / `Linarith` / `NormNum` | 0.43–0.45 s | 1.2–1.3 GB |
| `Mathlib.Data.ZMod.Basic` | 0.51 s | 1.44 GB |
| `LeanRV64D` (whole generated model) / `LeanRV64D.Defs` | 0.49 s / 0.47 s | 1.2 GB |
| `Clean.Circuit.Basic` / `Clean.Circuit.Subcircuit` | 0.65 s / 0.81 s | 1.8 / 2.1 GB |
| `SP1Clean.Math.Word`, `ToClean.Tactic.GetElemFastPath` | 0.63 s | 1.8 GB |
| `Mathlib.Tactic` | 0.94 s | 2.6 GB |
| `SP1Clean.Native.Chips.AddChip.Defs` | 1.09 s | 2.95 GB |
| `SP1Clean.Model.SailWrap` / `Semantics.GuestProgram` / `Proofs.Sail.Advance` / `Soundness.SP1Ensemble` | 1.11–1.20 s | 2.95–3.1 GB |

Every module of ours pays the `Mathlib.Tactic` floor (28 files at the bottom of the DAG import it:
`Math/Gate.lean`, `Model/{Register,SailWrap,Opcode}.lean`, `Model/Machine/Schedule.lean`,
`ToMathlib/{General,BitVec}.lean`, 18 `Faithful/*` files, …), and every Sail-touching module pays
≈ 0.2 s and 0.4 GB more. 1 004 modules × ≈ 1.06 s = the 1 063 s import total of the sweep.

### Contention: the same modules in three settings

| solo band | n | solo s | local14 s | × | n (ci4) | solo s | ci4 s | × |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ≥ 60 s | 3 | 232 | 413 | 1.78 | 0 | — | — | — |
| 10–60 s | 21 | 392 | 720 | 1.84 | 4 | 61 | 367 | 5.97 |
| 3–10 s | 157 | 869 | 1 703 | 1.96 | 80 | 459 | 2 336 | 5.09 |
| 1–3 s | 777 | 1 343 | 3 091 | 2.30 | 462 | 774 | 2 425 | 3.13 |
| < 1 s | 46 | 34 | 74 | 2.17 | 38 | 27 | 76 | 2.80 |
| all | 1 004 | 2 871 | 6 001 | 2.09 | 584 | 1 321 | 5 204 | 3.94 |

Parallel builds inflate the small, import-dominated modules the most (memory bandwidth from
≈ 3 GB of mapped oleans per process); earlier "anomalies" are this effect —
`Soundness/CoreHaltExecution` is 1.78 s solo and 52 s in local14, the per-chip `Bridge` files are
1.2 s solo and 8–16 s in parallel logs.

### The chip template (N = 25 instruction chips + providers/host chips)

| file kind | n | solo s | of which import | local14 s |
|---|---:|---:|---:|---:|
| `Faithful/<Chip>` (L4) | 29 | 173 | 32 | 344 |
| `Proofs/Chips/*/Formal` (L2) | 39 | 172 | 43 | 404 |
| `Native/Chips/*/Defs` (L2) | 38 | 74 | 42 | 157 |
| `Proofs/Chips/*/Populate` (L2) | 21 | 65 | 23 | 128 |
| `Proofs/Chips/*/Soundness` (L2) | 7 | 56 | 7 | 90 |
| `Proofs/Chips/*/Evidence` (L2) | 6 | 54 | 7 | 101 |
| `Alignment/Chips/*/Bridge` (L1) | 25 | 52 | 29 | 184 |
| `Proofs/Chips/*/Complete` (L2) | 25 | 47 | 27 | 77 |
| `Proofs/Chips/*/Witgen` (L2) | 27 | 45 | 30 | 97 |
| `Alignment/Chips/*/Contracts` (L3) | 16 | 42 | 19 | 95 |
| all chip-named | 275 | 906 | 305 | 1 942 |

The heavy chips are content, not template: DivRem 292 s local14 (`Evidence` family 101,
`Populate` 67, `Completeness` 44), ShiftRight 167 (`Core` 36 — twelve `*_close_su16_*` arithmetic
lemmas), ShiftLeft 92, Mul 82; the ALU chips are 38–42 s each across all their files.

## What the build proves

### Claim map: import closure versus proof closure

| Headline | Status | Import closure (modules / local14 s) | Proof closure (modules) |
|---|---|---:|---:|
| `FormalModel/Shard`, `Soundness/Shard/{Contract,Machine}` — `Executes`, `SoundnessTarget`, `realizes`, `statement_iff_of_realizes` (the intended capstone) | targets unfilled | 174–181 / 1 670–1 692, of which G 124 / 1 485, L1 36, L2 13–17, L3 1–4 | — |
| `Soundness/AIR.lean` `supported_core_native_sound` (retained 55-table) | closed | 556 / 4 472 (G 124, L1 53, L2 236, L3 72, L4 71) | 226 `SP1Clean.*` + 115 `LeanRV64D.*`; `Extracted`: 18 struct modules; `Alignment`: 25 bridges |
| `Soundness/NativeCompleteness.lean` `supported_core_native_complete` (+ totality-conditional) | closed on `NativeTraceAdmissible`; `NativeShardTraceTotal` open | 647 / 4 810 | 283 + 115; `Extracted`: the same 18 |
| `Soundness/HostHintReadFinalSnapshot.lean` `HostHintReadCPU.source_execution_with_memory` (frontier) | closed, "does not establish `SoundnessTarget`" | 849 / 6 080 (L3 193, L2 361, L1 100) | 366 + 115; `Extracted`: 18 + `SystemOracle/SyscallInstrs` |
| `Faithful/SupportedMachine.lean` `supportedChipFaithfulness` (25 `ChipFaithful`) | closed | 465 / 3 661 (L4 91) | 215; `Extracted`: 45 (25 `ChipOracle` + 18 structs + DSL + immutable reader); 0 `Alignment`, 0 `LeanRV64D` |
| `Soundness/CoreAIR.lean` `sp1_air_sound_of_obligations` (exact upstream) | conditional, no constructed obligation bundle | 204 / 1 937 (L4 56 — all 12 `SystemOracle/*`) | — |
| `Composition/CoreArtifact.lean` `exactNativeArtifact_*` | conditional | 615 / 4 892 | — |

Every import closure contains the whole generated model (124 modules, 1 485 s local14): the three
direct importers of `LeanRV64D` (`Model/Register`, `Model/SailWrap`, `Model/Semantics/GuestProgram`)
import its root. The proof closures show the actual use: the native theorems use constants from
115 generated modules (the `execute_*` bodies through `try_step`); the faithfulness anchors use
none.

The retained theorem's import closure holds all 62 `Extracted/` modules (19 942 generated lines,
365 s local14, `SystemOracle/Global` 146 s of it) but its **proof** uses 18: `ALUTypeReader`,
`AddOperation`, `AddrAddOperation`, `AddressOperation`, `CPUState`, `ITypeReader`,
`IsEqualWordOperation`, `IsZeroOperation`, `IsZeroWordOperation`, `JTypeReader`,
`LtOperationSigned`, `LtOperationUnsigned`, `MemoryAccess`, `MulOperation`, `RTypeReader`,
`U16CompareOperation`, `U16MSBOperation`, `U16toU8OperationUnsafe` — the column structs. The rest
enters through one import edge: `Soundness/SyscallRowSemantics.lean` uses `Faithful.decodeSyscallRow`
(`Faithful/CoreAIR.lean:339`), and `Faithful/CoreAIR` imports every oracle.

### Verdicts by layer (local14 seconds; "core claims" = in the closure of AIR, NativeCompleteness or SupportedMachine)

| Layer | core claims | frontier-only | Shard-only | exact-only | reached by nothing |
|---|---:|---:|---:|---:|---:|
| L1 | 54 modules / 352 s (25 bridges 184, `Model/Semantics` 66, `Proofs/Sail` 45) | 26 / 170 (`Proofs/Sail/InstructionDecode*` 103, `Model/Core` 62) | 22 / 75 (`Model/Core`) | — | 3 / 10 |
| L2 | 294 / 1 672 (`Proofs/Chips` 1 008, `Native/Operations` 233, `Proofs/Operations` 128, `Native/Chips` 106) | 122 / 535 (host/hint/provider chips, 29 `FormalModel/Contracts`, 21 `Native/Operations`) | 6 / 11 (`ToClean`/`ToPolyFun`/`ToMathlib`) | — | 46 / 180 (`Proofs/Chips` 58, `Proofs/Operations` 53, `Native/Operations` 24) |
| L3 | 104 / 857 (`Grounding/` 274, `Proofs/Completeness` 99, `Alignment/Contracts` 95, `GroundingAdapter` 83, `ChipContracts` 55) | 125 / 844 (`HostHintRead*` 209, `HostQueue*`/`Host*` 194, `Core*` 96, `LocalCore*` 85, `HostLocalCore*` 76, `Syscall*` 53, provider ensembles 82) | 4 / 19 (`Soundness/Shard`, `FormalModel/Shard*`) | — | 28 / 125 (`NativeCore*` 55, `ProtectedLocalCoreExecution` 15, `SyscallTrail`, `FormalModel/TraceGen` 17, …) |
| L4 | 107 / 772 (`SystemOracle/*` 200 — import-only, see above; `ChipOracle/*` 105; `Faithful/*`) | — | — | 12 / 62 (`Composition/*`, the bump-table anchors) | 6 / 21 (`CoreAIR*`, `Composition/{Balance,CoreSystemSemantics}`, `OpcodeTable`) |

The L3 engine that the retained theorem and completeness share (`Grounding/*`, `GroundingAdapter`,
`ChipContracts`, `Typed*`, `SP1Ensemble`, `WitnessDecode`, the capstone files) is ≈ 720 s local14 /
≈ 360 s solo, three quarters of it kernel type checking. The frontier-only stack (≈ 830 s local14)
and the frontier-only L2 chips/contracts/operations (535 s) are the newer native-profile material
behind the unfilled `Soundness/Shard` facade. The 73 unreached modules cost 298 s local14.

## The SP1 connection, as it stands

What it consists of: (1) `update_extracted.py` runs SP1's constraint compiler at the pinned
revision and writes `Extracted/` — 24 flat struct/reader/operation modules, 25 `ChipOracle/<Chip>`
(the Rust row + complete `asserts`/`interactions`), 12 `SystemOracle/*` (flat `Vector F n` rows;
`Global` 241 columns / 216 asserts, `PublicValues`), the manifest and provenance; (2) `Faithful/`
proves the 25 `ChipFaithful` anchors (native row ↔ Rust row via `reconfigure`, same assertion
system and interaction multiset) plus `SupportedMachine`'s coverage certificate; (3) `Composition/`
and `Soundness/CoreAIR*` state the exact v6.4.0 relation and the transport to the native theorem
under a 12-field obligation bundle that nothing constructs; (4) the dump/witgen conformance
pipeline (`export/sp1dump/`, `scripts/witgenExport.lean --testdata`, the Rust differential) is the
runtime check.

How it leaks into "our thing": (a) the 42 L2 modules importing `Extracted/` use the Rust structs as
*input types* (`FormalModel/Contracts/{Readers,Operations,DivRemColumns,…}`, `Soundness/RowView`,
`Native/Readers/*`, nine `Native/Operations/*/{RawSpec,Populate}`) — a design choice made when the
readers were ported, not a proof need (`AddOperation`/`SubOperation` are native and faithful);
(b) the import edge `SyscallRowSemantics → Faithful/CoreAIR`; (c) `FormalModel/CoreProfile` and
`FormalModel/OpcodeTable` (SP1's manifest and opcode alphabet, `decide`-checked) sit at stratum 4.
Cost of L4 in local14: 855 s (11 %), of which the parts no closed theorem's proof uses:
`SystemOracle/*` 200 s, `Composition/*` 60 s, `CoreAIR*` 10 s.

## Hotspot mechanisms

| Module | solo / local14 / ci4 s | Layer, verdict | Mechanism | Fix sketch | Status |
|---|---|---|---|---|---|
| `LeanRV64D/RvfiDii` (generated) | 1 011 solo / 1 049 / 3 308 | G, critical path of PR CI | `print_rvfi_exec`: 18 consecutive `(pure (print_bits …))` statements; Lean's `DoElemCont.mkBindUnlessPure` elaborates the continuation twice per `pure`-unit statement (2ⁿ) — lean4#13858 | lean4#13985 (one line, unreviewed since June); Sail backend prints `let _ : Unit := e`; `backward.do.legacy` emission; RVFI overlay (#6) | measured (issue #6) |
| `Soundness/Grounding/RTypeChips` | 98 / 184 / — | L3 retained | kernel type checking 95 s: three chips × ~10-declaration template whose `rtypeTimestampContract` records are checked as one term (the kernel size cliff) | per-chip facts as standalone theorems over opaque variables; cut composition depth | estimate |
| `Soundness/GroundingAdapter` | 70 / 83 / — | L3 retained | type checking 68 s: 143-line `rowAligned_*` conjunctions | same | estimate |
| `Extracted/SystemOracle/Global` (generated) | 64 / 146 / — | L4, in no proof closure | elaboration 56 s on a 1 239-binding let-chain the Rust emitter cannot chunk | not needed by any closed theorem: cut the import edge (P5.3) and it leaves every native build; emitter chunking only if the exact relation is pursued | measured (proof closure) |
| `Proofs/Sail/InstructionDecode/Families` | 41 / 94 / — (456 in the 09-19 CI log) | L1 frontier-only | 62 lemmas each re-walk the 27 530-line `encdec_backwards` cascade (`conv_lhs => whnf` + an 11-way `first` ladder per step, depth 3–42); `simp` 304 CPU-s | one decoder-table characterisation proven once, per-family lemmas by lookup | estimate |
| `Soundness/ChipContracts` | 32 / 55 / — | L3 retained | type checking 28 s: 25-chip `groundingContracts` + 11 `*GroundingData` records | as RTypeChips | estimate |
| `Soundness/HostQueueCPUReplay`, `SyscallWiring`, `HostHintQueueBoundary`, `HostQueueCPUOrder` | 27, 23, 15, 13 solo | L3 frontier-only | type checking / AC-normalisation over concrete `sp1Ensemble` multisets | frontier verdict first (§ Proposals) | estimate |
| `Faithful/SyscallInstrsChip`, `MulChip`, `BranchChip` | 25, 20, — solo | L4 anchors | statement size: 16-sub-block interaction equations, 200–500-line monoliths | per-sub-block `circuit_norm` rfl-helpers | estimate |
| `Proofs/Chips/DivRemChip/Evidence` | 20 / 25 / 99 | L2 core | two `obtain`s over a 122-conjunct hypothesis (Clean pattern 7) | `have`-projections instead of `obtain` | estimate |
| `Proofs/Chips/ShiftRightChip/Core` | 20 / 36 / 123 | L2 core | interpretation 22 s: twelve `*_close_su16_*` case lemmas (`omega`/`nlinarith`/`2^64` literals) | shared bit-dispatch lemma | estimate |
| `Proofs/Sail/Advance` | 15 / 40 / — | L1 core | tactic execution 57 s: 27 × `unfold reg_idx_to_Register; split <;> decide` over the 180-constructor `Register`, 34 `rcases … <;> decide` | one `reg_idx_to_Register_ne` lemma table | estimate |
| `Model/Semantics/Decode` | 11 / 17 / 90 | L1 core | `simp` 37 s: 23 inversion lemmas with `cases op <;> cases op' <;> decide` (100 `decide`s per arm pair) | `DecidableEq`-table lemma per enum | estimate |
| `SP1CleanTest/Alignment/Core/{ExecutionPath,LocalCore}` | 30, 16 solo | L5 | `blocked` 57 / 135 s: `native_decide` batteries | alignment-only already | — |

## Proposals

Each carries the claim it touches and an expected saving labelled measured or estimate.

1. **Fix RvfiDii at its source** (upstream lean4#13985; or the Sail-backend `let _ : Unit :=`
   spelling; or #6's overlay). Touches no claim. Measured: PR-CI cold build 65 min → bounded by
   the remaining 6 400 CPU-s (≈ 27–30 min); local full build −1 000 s. The single largest lever
   in the tree.
2. **Cut the import edge `Soundness/SyscallRowSemantics → Faithful/CoreAIR`** by defining
   `decodeSyscallRow` below `Faithful/` (it decodes a syscall row; Model-level). Touches no proof
   (the proof closure already excludes the oracles). Measured by closure: 12 `SystemOracle/*`
   modules + `Faithful/CoreAIR` leave the native theorems' builds (−200 s local14, −146 s of it
   `Global`); the alignment workflow still builds them for the exact relation.
3. **L2 free of L4: native `Columns` for the readers and the nine operations**, Rust structs
   identified in `Faithful/` as `AddOperation`/`SubOperation` already are. Touches 42 modules'
   import lines and the reader/operation `Inputs` types; no theorem statement changes at the chip
   level (`Spec`s are semantic). Saving in seconds small (the 18 structs are 30 s local14);
   semantic: the default build stops depending on the extraction pipeline, `layering.txt` gets
   a rule L2 ↛ L4, `FormalModel/{CoreProfile,OpcodeTable}` move to L4. Estimate.
4. **Verdict-driven retirement/demotion** (user decision per cluster): the 73 unreached modules
   (298 s local14; `NativeCore*` chain, `SyscallExecution`, `Coverage`, `AluGeneration`,
   `FormalModel/{EventExecution,Verifier}`, host-chip `Populate` files consumed only by tests);
   the frontier-only stack (≈ 830 s L3 + 535 s L2 + 170 s L1 local14) either promoted into the
   capstone plan or parked behind a `SP1Native`-style target built on demand; the exact-relation
   stack (`SystemOracle` + `Composition` + `CoreAIR*`, ≈ 270 s) to an on-demand target if it is
   not being pursued. Measured by closure; the census consequences are listed per cluster in
   `scripts/build_semantics.py --out …/unreached.md`.
5. **The import floor**: narrow the 28 `import Mathlib.Tactic` sites at the bottom of the DAG to
   the tactics used (`Ring`, `Linarith`, `NormNum`, `IntervalCases`, `LinearCombination`, …).
   Measured floor: `Mathlib.Tactic` 0.94 s / 2.6 GB vs `Mathlib.Tactic.Ring` 0.43 s / 1.2 GB;
   × 1 004 modules → an estimated −300 s solo and a smaller resident set per process (less
   parallel inflation). Also: merge the smallest per-chip files (`Witgen`, `Complete` into
   `Formal`) where the file exists only to hold one declaration — 50 files × ≈ 1 s floor.
   Estimate.
6. **Kernel-cliff refactors** (`RTypeChips`, `GroundingAdapter`, `ChipContracts`, the frontier
   `HostQueue*`/`SyscallWiring`): standalone per-chip theorems over opaque variables. Only worth
   doing for clusters that survive proposal 4. Estimate −150 s solo.
7. **Decoder and register tables** (`Families`, `Decode`, `Advance`): prove the enumeration facts
   once (a decoder table, an opcode `DecidableEq` table, a `reg_idx_to_Register` lemma table) and
   make the per-family lemmas lookups. `Families` is frontier-only today; `Decode`/`Advance` are
   core. Estimate −60 s solo, −250 s ci4.
8. **Module system tier 2** (after Track U): not a cold-build lever (elaboration is the same) but
   the dev-loop one — a proof edit stops rebuilding importers. Separate campaign.

## The natural connection (design, no code)

The claim map says the tree has one intended statement and several retained ones. "Build our
thing first" is then: L1 + L2 + L3 exist to prove `Air.Flat.Realizes (sp1Machine …) ensemble …`
(`Soundness/Shard/Machine.lean`) — the native ensemble realizes our Sail-based machine; the
retained 55-table theorem is either re-derived as an instance of that statement or retired once
the targets are filled; L4 becomes a library that *imports* the core and provides (a) the 25
`ChipFaithful` transports (closed, Sail-free, cheap) and (b) the exact-upstream relation as a
transport along a refinement (`Realizes.transport`), which is the M5 shape of the RiscvAir plan
(#16). For that, the core must expose: the native `Columns`/`Inputs` types (proposal 3), the
machine vocabulary without SP1 tables (proposal 2), and a stable `Realizes` statement — nothing
else. The build then literally builds our thing first: `SP1Core` has no L4 module in its closure,
and the alignment workflow is the only place the Rust extraction is compiled.

## Reproduction

```bash
# tables from a Lake log (+ optional solo sweep categories)
python3 scripts/build_semantics.py --lake-log <lake build log> --out .lake/profile/bsem \
    [--profile-dir .lake/profile/sweep-2026-09-20]
# the solo sweep (≈ 1 h 10 min, machine idle)
SKIP_BUILD=1 TREES="SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest" \
    OUTDIR=.lake/profile/sweep-<date> scripts/profile_compile.sh
# a CI log
gh api repos/dtumad/sp1-lean/actions/jobs/<job id>/logs > ci.log
```
The proof-closure probe and the import-floor files are in the session scratchpad
(`hot/declclosure.lean`, `hot/import_*.lean`); both are ten-line scripts reproduced in the
tracking issue.
