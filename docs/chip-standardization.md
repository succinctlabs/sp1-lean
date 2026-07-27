# Chip standardization — one per-row Sail contract

**Status: complete for the supported registry, 2026-07-16.** All 25 supported instruction chips expose
the same `ChipKind.advance` obligation, `allChipKinds_migrated` proves every registered value is present,
and the old `sailEquiv`/`reaches_sail` path has been removed.

## The interface

`Soundness/ChipRow.lean` defines a heterogeneous `ChipKind` with these machine-facing fields:

| Field | Meaning |
|---|---|
| `name` | SP1's `MachineAir::name()` identity |
| `Inputs`, `Cols` | dependent circuit input and committed-column types |
| `view` | the chip-independent State/Program/Memory/Byte and effect projection |
| `chipSpec` | the verified semantic circuit contract |
| `advanceReady` | chip-specific structural facts needed immediately before execution |
| `advance` | the uniform official-Sail transition proof |

The transition obligation has one shape for every chip:

```lean
is_real = 1 → chipSpec input cols data →
SailConfigured state → RomLoaded program state →
pc_matches_state_pull → ValueOperandsBound view state →
decodedInROM program program_row → advanceReady input cols program state →
∃ next, SailStep state next ∧ RowEffect program view state next
```

`advanceReady` is the explicit home for facts that are neither instruction semantics nor live operand
currency: reader passthrough, `rd`/`x0` routing, active variant selection, PC bounds, alignment, or
chip-specific memory conditions.

The field remains `Option (PLift ...)` because that representation enabled incremental migration. There is
no semantic fallback now: `allChipKinds_migrated` proves that every member of the registry is `some`, and
the generic dispatcher eliminates the option using registry membership. Making the structure field total
is a possible later cleanup, but is not necessary for soundness and should only be done if it materially
simplifies the descriptor.

## Row effects

`RowEffect` describes the three independent parts of the generated Sail state affected by one ordinary
instruction:

- the committed next PC;
- zero or one register write; and
- zero or one contiguous byte-addressed memory write.

Everything else is framed. The underlying `CommitEffect` distinguishes `.regWrite`, `.noWrite`, and
`.store`, which lets ALU, branch/`x0`, load, and store chips share the same target without pretending that
Sail's register map and byte memory are one object.

Reusable proofs in `Proofs/Sail/Advance.lean` cover the common execution ladders: straight-line writes,
jumps, branches, loads, stores, and the `x0` no-write path. Per-chip bridge files reduce their semantic
`Spec` and decode case to one of those cores.

## Decode and dispatch

Program decode is a global fact derived from the exact Program pull, provider table, committed program,
and channel balance. It is supplied to `advance` as `decodedInROM`; chips do not assume semantic truth in
their channel type.

The former non-injective opcode problems for Mul, LoadDouble, LoadX0, StoreDouble, and the two AluX0 Mul
cases are closed in the current 25/25 registry. The generated instruction committed by the Program row,
rather than an opcode-only inverse, pins the instruction seen by Sail.

`Soundness/SupportedMachine.lean` is the single source of truth for the circuit, `ChipKind`, opcode list,
and `rd` guard. `allChipKinds`, coverage, routing, and the ensemble's instruction tables are projections of
that descriptor. `LocalExecution.lean` dispatches a grounded row by its registered kind and invokes
`advance`; adding a chip does not add a new capstone case split.

## Relationship to the grounding engine

The original standardization campaign was motivated by an experiment where channels carried semantic
truth directly. That representation has been retired. The current four Clean channels carry only
row-local structural guarantees, while the timed/ranked grounding engine derives:

- an exhaustive ordered State path;
- committed Program decode;
- live Memory/register currency; and
- the `advanceReady` inputs.

All four are proved for the supported native witness. `TypedInteractions.lean` and
`TypedMemory.lean` transport facts from the exact evaluated circuit interactions, and the
registry-wide `ChipGroundingContracts` instances supply every chip's operand and readiness contract.

## Faithfulness boundary

The `advance` proof establishes semantic conformance of the native chip. It does not by itself prove that
the native chip is SP1's Rust AIR. The independent whole-chip `ChipFaithful` layer compares the complete
assertion system and all four interaction multisets through one explicit row reconfiguration. All 25
supported instruction chips now have that final anchor; remaining operation/fragment anchors are
transitional implementation evidence.

## References

- `SP1Clean/Soundness/ChipRow.lean` — `ChipKind`, `ChipRow`.
- `SP1Clean/Soundness/SupportedMachine.lean` — the 25-chip descriptor.
- `SP1Clean/Soundness/ChipRegistry.lean` — registry projection and 25/25 migration theorem.
- `SP1Clean/Proofs/Sail/Advance.lean` — shared Sail execution cores.
- `SP1Clean/Soundness/LocalExecution.lean` — generic row dispatcher and Sail-chain construction.
- `SP1Clean/Soundness/TypedMemory.lean` and `SP1Clean/Soundness/ChipContracts.lean` — generic transport
  and the registry-wide grounding contracts.
- [`architecture.md`](architecture.md) and [`roadmap.md`](roadmap.md) — whole-machine context.
