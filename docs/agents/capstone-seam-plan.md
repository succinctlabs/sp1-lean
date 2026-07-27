# Native capstone closure record

This file used to track the open `supportedCore_orderedRows_dynamic` seam. That plan is complete.
The live next-step plan is [`../roadmap.md`](../roadmap.md).

## Closed result

`supported_core_native_sound` now proves:

```lean
WitnessRelation.Sound SupportedCoreNativeRelation
  (SupportedCoreLocalExecutionRelation model)
```

with no proof deferrals.

The closure included:

- deterministic decoding of all 25 instruction tables;
- exhaustive ranked State-bus ordering;
- Program-provider commitment and decode grounding;
- typed extraction of exact Memory pulls and pushes;
- per-location Memory frontier and repeated-touch reasoning;
- physical timestamp bounds and strict access ordering;
- all 25 `ChipGroundingContracts`;
- transport through aligned timed carriers;
- per-position chip assumptions, semantic Specs, routing, and readiness; and
- construction of the final Sail chain and public clock count.

The older `sp1_decoded_rows_sound` admission was removed. The legacy Eulerian-trail theorem remains only
as an explicitly conditional adapter taking `DecodedRowsSound`.

## Performance outcome

The ShiftRight/ShiftLeft and DivRem proof cliffs were resolved with folded helper boundaries and
`circuit_proof_start_core`, following Clean's performance guidance. No `skipKernelTC` or
main-library `native_decide` was introduced.

Exact whole-chip list faithfulness adds many localized heartbeat scopes. Their count is recorded by the
heartbeat ratchet; existing declarations were not given broader ceilings.

## What this result does not close

`SupportedCoreNativeRelation` still takes semantic provider/boundary and timestamp relations as source
conjuncts. The exact upstream Core theorem must derive those facts from Program, MemoryLocal,
MemoryBump, StateBump, Global, SyscallCore, SyscallInstrs, and the memory-boundary cluster.

Do not reopen the native capstone with a second execution engine. Reuse it through the 25
`ChipFaithful` proofs and prove an exact-system-table adapter, as specified in
[`../roadmap.md`](../roadmap.md).
