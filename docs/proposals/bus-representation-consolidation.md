# Design record: bus and shard representation consolidation

**Status: accepted and implemented, 2026-08-24.** Current architecture is documented in
[`architecture.md`](../architecture.md); the remaining work is in [`roadmap.md`](../roadmap.md).
This record preserves the diagnosis, the decisions, and the boundaries the implementation did not
collapse.

## Problem

The chip boundary correctly distinguishes four genuinely different objects: native Clean circuit,
semantic contract, extracted Rust oracle, and Sail step theorem. That discipline had spread into
the machine layer as a rule to define a new carrier for every view of an interaction or execution.
The result was the opposite of auditability:

- typed bus messages, Clean interactions, trace lookup lists, Rust-oriented accesses, and several
  per-bus `*Consistency` lists described overlapping multisets;
- soundness and completeness carried different instruction registries and different positional
  25-chip records;
- completeness assembled a hand-written 53-table list while soundness mapped a registry;
- several custom execution/trace forms had to be bridged before either direction could state the
  same semantic theorem; and
- translation lemmas substantially outnumbered the lemmas carrying the actual balance or execution
  mathematics.

The worst symptom was not proof length but drift. The dead Byte and Memory lookup shadows still used
pre-W11 polarity while the live circuits used the opposite direction. They were not consumed by a
capstone, so they did not make a released theorem unsound, but they made the repository tell two
different stories about the same buses.

## Accepted architecture

The consolidation adopts three rules.

### 1. Keep two bus primaries, not one and not many

The two proof directions require inequivalent information.

**Typed primary, for soundness.** Evaluated `TypedInteraction`s retain structured field-valued
messages. `producedMessages`/`consumedMessages` and the typed State, Program, and Memory modules use
this form to relate a circuit pull to the exact row state consumed by a Sail bridge.

**Computable primary, for completeness.** `LookupAccess`, `tableCleanAccesses`, and the generated
trace's full ledger retain natural payload arrays and centered signed-integer multiplicities. This
form supports provider recounting, per-key integer sums, and executable concrete-shard checks.

**One bridge.** `Interaction.toAccess` is the element-level projection. It is lifted table- and
ensemble-wide, then connected to Clean's field balance by `Model/BalanceBridge.lean`. A new third
native ledger is not allowed merely to make one proof convenient.

Clean orientation is canonical in both native views. The Rust oracle's opposite Memory/Program
polarity is a real extraction-boundary fact, so it has one named Rust-facing projection rather than
being erased: `tableRustOrientedAccesses`. The theorem
`tableNativeAccesses_perm_tableRustOrientedAccesses` proves the table-wide correspondence.

### 2. Give identities a proof-neutral owner

`InstructionChipId` owns the 25 identities and their order. `InstructionRouting` owns the pure
opcode/`x0` decision. `ProviderTableId` owns the 28 provider/boundary identities and native table
positions. Circuit-bearing soundness descriptors and completeness table builders are realizations
of these neutral IDs, not independent registries.

Dependent Rust row types are indexed by `InstructionChipId` through `ExtractedCols`; the extracted
witness exposes one total `forId` function. Constraint transport and ledger transport are pointwise
over that index and flattened in the canonical order.

### 3. Use one proof-free semantic execution carrier

`Machine.EventExecutionTrace` is the operational witness shared by both directions. Validity is
separate evidence, which keeps a future trace compiler executable. The ordinary fragment converts
directly to `SailChain`; the PolyFun prefix is a theorem view rather than a second stored model.

`Execution.SupportedOrdinaryShardExecutionRelation` is the exact semantic image of the 25 native
instruction chips: each transition carries official-Sail `Retire_Success` evidence as well as its
canonical route. Physical `DecodedInstructionRow` and `ChipRow` types remain codecs at the AIR
boundary. The compiler's field-free access schedules and State/Memory histories are deterministic
views of that same trace, not independently supplied timelines. Their physical agreement is proved
or retained as an explicit readiness seam rather than assumed through a parallel execution model.

## Implemented changes

### General proof and wiring cleanup

- Replaced the binary-only local derivation of `signedVal (-x) = -signedVal x` in
  `ChipLedger.lean` with the general `signedVal_neg` theorem.
- Imported and composed `ChipLedger` in `AIRCompleteness`. The structural capstone now derives the
  State and Memory hand-off permutations from its chain/regrouping premises; `hstate` and `hmemory`
  are no longer unexplained final inputs.
- Added the native-to-Rust orientation projection and proved its whole-table permutation against
  `tableNativeAccesses`.

### Dead-stratum retirement

A fresh import and declaration-use audit removed about **2,491 lines** from obsolete bus modules
and module halves:

- `Soundness/ByteConsistency.lean`;
- `Soundness/MemoryConsistency.lean`;
- `Soundness/MemoryIsU64.lean`;
- `Soundness/MemoryGlobal.lean`;
- `Soundness/ProgramProviderSpike.lean`;
- `Model/ChipAir.lean`;
- `Composition/ExactBalance.lean`; and
- the complete `StateConsistency.lean` and `ProgramConsistency.lean` modules after their five live
  access declarations moved to `Soundness/RowView.lean`.

The unused `TraceLookupConsistent`, `byteLedger`, and `programLedger` aliases were retired as well.
The deleted Memory/Byte material was both unreachable and stale: its polarity and gating no longer
matched the actual Clean readers. The live proof path now reads the interaction ledger that the
circuits really emit.

This deletion deliberately retained `StateAccess`/`stateAccess` and
`ProgramAccess`/`programAccess`/`ProgramAccess.toRow`. Those are normalized row-view vocabulary used
by all chip bridges, not a competing global bus model.

### Fail-closed channel classification

`kindOf` now names all four native channels explicitly. In particular,
`kindOf_eq_byte_iff` proves that a channel is classified as Byte exactly when its name is
`"SP1Byte"`. Unknown and extracted raw-channel names enter the reserved State compatibility bucket,
so adding a fifth channel cannot silently make it eligible for Byte provider closure.

The compatibility fallback is not permission to treat an unknown channel as State semantics. The
native ensemble continues to admit exactly the four registered channels; the fallback exists only
for the extracted raw-access vocabulary.

### Unified registries and assembly

- `Model/InstructionChipId.lean` defines the canonical 25-entry identity list.
- `Model/InstructionRouting.lean` defines the route and guard independently of circuit types.
- `Soundness/SupportedMachine.lean`, typed decoding, opcode coverage, faithfulness coverage, and
  native ensemble construction derive from that registry.
- `Model/ProviderTableId.lean` defines the complete provider/boundary table inventory, including
  all 17 Range widths.
- `Proofs/Completeness/Assembly.lean` maps `InstructionChipId.all` and `ProviderTableId.all` instead
  of maintaining a 53-entry literal.
- `Composition/Ensemble.lean` replaces the named 25-field extracted row structure with
  `ExtractedInstructionRows.forId`; assertions, accesses, transport, and validity are all indexed by
  the same ID.

The benefit is not merely fewer lines. The Lean types now force soundness, completeness, and exact
transport to agree on identity before a physical table can be assembled.

### Shared exact shard relation

`FormalModel/SupportedShard.lean` states the exact ordinary supported relation over
`EventExecutionTrace`. Every transition is an official normally retiring Sail step, follows the
eight-tick schedule, fetches from the committed program, and has a successful canonical route.

`supported_core_native_ordinary_sound` constructs that exact trace from an accepted native witness.
On the reverse path, `nativeTrace` is a total proof-independent compiler over the same
`EventExecutionTrace`, and `supported_core_native_functionalCompleteness` proves its full native
ensemble result on `SupportedCoreNativeAdmissibleExecutionRelation`.  The compiler retains each
source transition beside its generated event, so this boundary really is coupled to the supplied
execution.  The former abstract language certificate was removed because its map could ignore that
execution. Both directions now use `SupportedCoreOrdinaryShardExecutionRelation`, whose row count is
checked by the single `CoreProfile.WithinOrdinaryRowLimit` policy; the native side projects its
active-row count into that same policy. Public-language equality remains intentionally
conditional on `NativeTraceTotalOnSupportedCore`, the residual readiness/footprint theorem for the
deterministic compiler image.

## Boundaries intentionally not collapsed

### Field balance versus integer balance

Clean balances field multiplicities under a `length < p` guard. Native canonical closure now proves
Byte/Range/Program balance directly in that field representation, without a centered
`2 * multiplicity ≤ p` convention. Integer recount remains an explicit boundary for exact-Rust
transport in `Composition/`, where source contracts are stated over natural multiplicities. An
aggregate Range multiplicity is never treated as binary in either path.

### Provider closure versus temporal hand-off

Byte and Program close by recounting demand and supplying canonical provider rows. State and Memory
form temporal chains in which a token is consumed and recreated. They use one ledger carrier but
different proof principles; forcing both into list equality or a single closure predicate previously
obscured the argument.

### Rust orientation versus Clean orientation

The extracted Rust AIR sends on Memory/Program where the native Clean circuits pull. This fact
cannot be simplified away while whole-chip faithfulness is part of the trust story. It is isolated
at the named Rust-facing projection and should not leak into native completeness statements.

### Physical rows versus semantic events

The dependent output columns of a Clean chip are real physical data. They are not replaced by
semantic events. The consolidation removes duplicate *semantic* carriers and makes row decoding a
codec with proved projections. `rowInput_buildRow` handles generated inputs generically; chip
`Spec`s remain responsible for output facts such as control-flow `next_pc`.

## Remaining work

The consolidation subsequently enabled the verified construction now implemented in
`Proofs/Completeness/`: all 25 event projections, the chronological access scheduler, State/Memory
refresh placement, canonical provider closure, and the proof-independent `nativeTrace` map.  The
remaining work is no longer a missing compiler representation.  It is discharging the explicit
readiness groups: rich per-chip event contracts; State/Memory chronology and physical-row agreement;
literal-ledger polarity/servability; initial-Memory truth; Program row/configured-decode agreement;
and the actual interaction footprint on the intended bounded semantic domain. The capacity-aligned
soundness target and conditional correctness/language-equality API are now present; closing
`NativeTraceTotalOnSupportedCore` removes the last native-domain restriction.

All-25 exportable witness programs, SP1 trace dumps, and interpreter differentials remain valuable
conformance evidence, but they are separate from those semantic inverse lemmas and from exact-Rust
trace reconfiguration.

The exact v6.4.0 Core system-table refinement and the ArkLib verifier layers are separate. Nothing in
this consolidation turns the 53-table proof architecture into an unconditional exact-AIR or
cryptographic-verifier theorem.

## Regression rules

Future work should preserve these checkable invariants:

1. No new global `*Lookups`/`*Consistency` shadow may duplicate the actual Clean interaction ledger.
2. A new instruction or provider identity is added at its neutral registry first; table builders and
   proof-bearing realizations map that identity.
3. `EventExecutionTrace` remains the only proof-free operational trace carrier. New data needed for
   compilation should be a proved view, not a parallel chain; a normalized middle carrier must land
   together with executable projections from both sides.
4. Native statements use Clean interaction orientation. Rust dualization is explicit at the
   faithfulness boundary.
5. Unknown channel names cannot enter Byte or Program provider closure by default.
6. Native canonical-closure counts are interpreted directly in the field and must not regain the
   retired `2 * multiplicity ≤ p` restriction.  The separate exact-Rust transport may retain its
   named centered-integer recount bound.  Clean's actual per-channel interaction-count bound remains
   explicit through `NativeTraceFootprint.Fits`.
7. Registry or module changes must pass `scripts/check_root_index.sh`, `scripts/check_layering.sh`,
   the warning-free full build, tests, and the axiom census.

## Historical note

The original proposal estimated roughly a dozen interaction carriers, around three dozen bridges,
and about 2,400 removable lines. Only the line-removal result was measured precisely during
implementation; the carrier/bridge counts were directional survey estimates and should not be cited
as release metrics. The durable result is the architecture above: two bus primaries, one semantic
execution carrier, neutral identities, and explicit boundary projections.
