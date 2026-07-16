<div align="center">

![SP1 Lean](./.github/assets/header.png)

Formal verification of SP1 Hypercube zkVM arithmetization

</div>

## Overview

This repository is a Lean 4 formalization of SP1's RISC-V AIR. It builds semantic chips in the
[Clean](https://github.com/Verified-zkEVM/clean) circuit DSL, relates each active chip row to one step
of the official RISC-V [Sail](https://github.com/riscv/sail-riscv) model, and anchors the Lean circuit
to constraints extracted from SP1's Rust implementation.

The intended verification stack has three deliberately separate claims:

1. `sp1_air_sound`: a valid full SP1 shard AIR witness yields the corresponding Sail execution segment;
2. `sp1_execution_sound`: an authenticated shard ledger composes from boot to the halting ECALL; and
3. `sp1_verifier_sound`: an ArkLib knowledge-sound verifier extracts such an AIR witness.

Only the supported native-Clean slice has a theorem today. The full upstream AIR and verifier names are
reserved for their actual relations; they are not aliases for the native ensemble.

## Current verification boundary

The current checkpoint (Lean 4.31) has:

- one descriptor for all 25 supported RV64IM instruction chips, from which the Clean ensemble, semantic
  registry, opcode coverage, and routing tables are projected;
- one uniform `ChipKind.advance` contract for every registered chip, proving that an active semantic row
  advances the generated LeanRV64D `try_step` semantics with the row's register, memory, and PC effect;
- deterministic typed decoding of all 25 circuit tables, ranked State-bus ordering, exact active-row
  coverage, PC/clock chaining, and globally grounded Program fetch/decode facts;
- a production timed-grounding layer and a typed adapter from each circuit's exact evaluated Clean
  interactions to Memory facts; Add is the first complete register-operand contract instance;
- complete whole-chip Rust AIR oracles and `ChipFaithful` proofs for Add and Sub; and
- executable whole-trace conformance batteries for 10 chips, isolated in `SP1CleanTest`.

The native semantic capstone is:

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound SupportedCoreNativeRelation
      (SupportedCoreLocalExecutionRelation model)
```

It concludes a shard-local official-Sail execution between public endpoints. It currently inherits one
named semantic admission, `supportedCore_orderedRows_dynamic`: the remaining proof must derive every
ordered row's live Memory operands, circuit assumptions, semantic `Spec`, and `advanceReady` facts from
the balanced buses and the evolving Sail state. RAM accesses, repeated touches of one location, state
bumps, and syscalls are outside the proved ordinary register-only grounding slice.

Other disclosed proof debt is intentionally kept distinct:

- `DivRemChip.evidenceSoundness` is the one chip-soundness seam, connecting the generated row to a proved
  four-family arithmetic/evidence contract;
- five chip completeness proofs are deferred after the 4.31 migration (`Branch`, `Mul`, `ShiftLeft`,
  `ShiftRight`, and `DivRem`);
- two DivRem channel-law packaging fields are deferred; and
- `sp1_decoded_rows_sound` remains only for the frozen, older Eulerian-trail path.

The audit gate currently permits exactly 10 syntactic deferral sites in eight files. See
[`docs/release-audit.md`](docs/release-audit.md) for the theorem/axiom census and
[`docs/roadmap.md`](docs/roadmap.md) for the dependency-ordered path forward.

## Architecture

The stable verification boundary is a whole SP1 chip, not a Rust helper operation. Rust operations and
Lean gadgets are complementary implementation devices and do not need matching internal structures.
For each migrated chip the intended chain is:

1. a semantic native Clean `GeneralFormalCircuit` and chip-level `Spec`;
2. a Sail bridge proving the chip's `Spec` implements the relevant instruction step;
3. a mechanically generated whole-chip oracle containing the Rust row, complete `assertZero` list, and
   all four interaction lists;
4. one explicit row reconfiguration and a `ChipFaithful` proof comparing the complete assertions and
   interaction multisets; and
5. executable populate/trace conformance against SP1's real Rust prover.

Operation gadgets and local lemmas remain useful inside chip proofs, but operation-level faithfulness and
the generated direct-to-circuit forms are migration debt. Add and Sub are the completed examples of the
new whole-chip boundary. DivRem is the complex-chip test case: its nine old per-operation proof bodies were
removed in favor of one isolated four-family semantic contract and one heavy chip-level conformance seam.

At machine level, the four buses are ordinary Clean channels with row-local guarantees only:

- State: structural `(clock, pc)` messages;
- Program: structurally valid decoded rows;
- Memory: structurally valid 64-bit values and timestamps; and
- Byte: byte/range-table membership.

Global execution, committed-ROM decode, and live-memory currency are theorems of the grounding engine,
not assumptions smuggled into channel guarantees.

## Repository layout

- `SP1Clean/Math/` — generic word, bit-vector, carry, and arithmetic lemmas.
- `SP1Clean/Model/` — Sail wrappers, bus messages/channels, program commitment, and native machine model.
- `SP1Clean/Extracted/` — generated Rust constraint/oracle artifacts; do not hand-edit.
- `SP1Clean/FormalModel/` — semantic chip contracts, witness relations, execution relations, and the
  dependency-free verifier boundary.
- `SP1Clean/Native/` — native Clean circuits and proof-oriented gadgets.
- `SP1Clean/Proofs/` — circuit soundness/completeness and Sail bridges.
- `SP1Clean/Faithful/` — Rust/Lean faithfulness anchors.
- `SP1Clean/Soundness/` — supported-machine registry, typed witness decode, bus grounding, and capstones.
- `SP1CleanTest/` — the separate `native_decide`-using witness/trace conformance library.
- `docs/` — architecture, honest-claim audit, roadmap, and contributor notes.

The root module `SP1Clean.lean` imports the complete main library.

## Build and audit

```bash
lake build SP1Clean   # main proof library
lake test             # witness and complete-trace conformance batteries
lake lint             # curated environment linters
scripts/run_audit.sh  # pins, forbidden-feature gates, deferral allowlist, axiom census
```

The current validated checkpoint passes all four commands. The audit emits 460 declaration probes, finds
no project `axiom` declarations, no `skipKernelTC`, and no `native_decide` in the main library. The
separate test library contains the sanctioned executable conformance checks.

## Toolchain and dependencies

| Dependency | Current source |
|---|---|
| Lean | `leanprover/lean4:v4.31.0` |
| mathlib | `v4.31.0` |
| Clean | local `../clean` 4.31 migration checkout |
| LeanRV64D | local `../sail-riscv-lean` at `793034f3` plus the disclosed SP1 platform delta |
| RISCV | local `../riscv-lean` at `e65c352a` |
| lean-sail | local `../lean-sail` at `79b4d085` |
| PolyFun | `502582b4`, used only for `DynSystem.Machine`/`Run` semantic packaging |

The local path dependencies are deliberate migration pins and must be restored to immutable published
git pins before release. Do not run bare `lake update`; see
[`docs/agents/lean-sail-notes.md`](docs/agents/lean-sail-notes.md).

Start with [`docs/overview.md`](docs/overview.md) for the current claim, then
[`docs/architecture.md`](docs/architecture.md) and [`docs/release-audit.md`](docs/release-audit.md).
