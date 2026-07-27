# Architecture consolidation checkpoint

This is the current checkpoint for the July 2026 consolidation proposal. The detailed live plan is
[`../roadmap.md`](../roadmap.md); the original proposal remains a historical design record.

## Landed

- `Math/`, `Model/`, `FormalModel/`, `Native/`, `Proofs/`, `Faithful/`, and `Soundness/` have distinct
  ownership.
- Direct Rust-to-Clean circuit generation is removed. Extraction is list-only.
- Semantic contracts are separated from circuit and proof files.
- `SupportedMachine` is the single 25-chip descriptor registry.
- Every registered chip has native soundness/completeness and a Sail bridge.
- Every registered chip has a whole-chip `ChipFaithful` proof.
- `Faithful/SupportedMachine.lean` ties those proofs to the exact upstream instruction profile.
- Deterministic row decoding, ranked/timed grounding, and `supported_core_native_sound` are closed.
- The legacy unconditional decoded-row admission is removed.
- The exact 34-table execution and 6-table memory-boundary relations are present and pin-guarded.
- COMMIT-row correctness is separated from program-level all-eight-row coverage.
- The audit requires zero proof deferrals and zero `sorryAx` carriers.

## Current public theorem boundary

Closed:

```text
SupportedCoreNativeRelation
  → SupportedCoreLocalExecutionRelation
```

Conditional only:

```text
CoreAIR.Current.Relation
  + CoreAIRRefinementObligations
  → SP1CoreShardExecutionRelation
```

The conditional declarations are named `sp1_air_refinement_of_obligations` and
`sp1_air_sound_of_obligations`. The unqualified names are reserved.

## Remaining consolidation

1. Build the registry-driven 25-table exact-to-native trace adapter.
2. Derive native provider/boundary/timestamp relations from the exact system and boundary tables.
3. Prove mixed ordinary/syscall event ordering and concrete handler contracts.
4. Instantiate `CoreAIRRefinementObligations`.
5. Retire operation-level faithfulness and witness artifacts when no generated oracle or test imports
   them.
6. Restore immutable published dependency pins before release.

No broader circuit architecture change is currently justified. The next work should extend the exact
system-table adapter and reuse the existing native capstone.
