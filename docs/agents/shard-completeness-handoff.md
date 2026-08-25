# Handoff: one native shard model for soundness and completeness

**Audience: us, on another machine, with no context.** Updated 2026-08-25 after the
shared-vocabulary and capacity-alignment pass on `dtumad/provider-closure`.

Read [`overview.md`](../overview.md) and [`architecture.md`](../architecture.md) first. The design
record for this cleanup is
[`bus-representation-consolidation.md`](../proposals/bus-representation-consolidation.md).

## 1. Outcome

Soundness and completeness now share one public statement, one operational witness, one physical
native witness, one configured-decode predicate, and one numeric Core row-limit policy. The forward
theorem is closed for the deterministic compiler's admissible image; it no longer starts from an
existential or hand-assembled trace.

```text
                      supported_core_native_shard_sound
bounded native AIR  ------------------------------------------->  bounded ordinary shard
       ^                                                              |
       | supported_core_native_shard_functionalCompleteness           | nativeTrace
       |                                                              | (total, proof-independent)
       +------------ admissible restriction of that shard <-----------+
```

The shared target is `Execution.SupportedCoreOrdinaryShardExecutionRelation`, a restriction of
`Execution.SupportedOrdinaryShardExecutionRelation`. Its witness is the single
proof-free `Machine.EventExecutionTrace`; validity supplies the official event-step semantics,
normal retirement, the ordinary eight-tick schedule, public endpoints, committed-program boundary,
and a successful route through the canonical 25-chip profile for every transition. Its only added
policy is `CoreProfile.WithinOrdinaryRowLimit execution.steps`.

The released direction theorems are:

- `supported_core_native_ordinary_sound` is closed. Every witness accepted by
  `SupportedCoreNativeRelation` produces an exact supported ordinary event trace.
- `supported_core_native_shard_sound` is the capacity-aligned projection from
  `SupportedCoreNativeShardRelation` to the shared bounded semantic relation.
- `supported_core_native_functionalCompleteness` is closed from
  `SupportedCoreNativeAdmissibleExecutionRelation`.  Its map is literally the deterministic
  `nativeTrace statement execution`; it is independent of the proof of admissibility.
- `supported_core_native_shard_functionalCompleteness` maps the same source and same compiler into
  the capacity-aligned native relation.
- `supported_core_native_complete` is the existential projection of that functional theorem.
- `supported_core_native_shard_correct_of_totality` and its language-equality corollary show that
  `NativeTraceTotalOnSupportedCore` is the sole remaining native-domain condition.
- `sp1Ensemble_statement_of_supported_execution` exposes the underlying Clean
  `Ensemble.Statement` directly.

`SupportedCoreNativeAdmissibleExecutionRelation` is not a renamed AIR witness condition. It is a
`Relation.restrict` view of the shared bounded ordinary Sail relation, adding only the named
field-free compiler/readiness facts for that same execution and `NativeTraceFootprint.Fits` on the
actual emitted interactions. In particular it contains neither channel balance nor table
constraints; both are conclusions.

This closes whole-ensemble completeness for the honest deterministic compiler image. It does not
yet prove that every witness of the shared bounded ordinary relation lies in that image. Therefore
there is deliberately no unconditional `WitnessRelation.Correct` or public-language-equality
theorem: `NativeTraceTotalOnSupportedCore` must first derive readiness and the physical `< p`
footprint for every bounded semantic execution. Capacity alignment itself is no longer open.

The older `supported_core_native_sound` remains useful as the broader local-Sail target. The exact
ordinary theorem is the one completeness should use: its source excludes unsupported instructions
and host-handled syscalls by construction.

## 2. The shared formal model

Two layers are now explicit.

1. `Machine.EventExecutionTrace` is the only proof-free operational execution carrier. A valid
   ordinary trace converts directly to `SailChain`, and a valid trace also has a direct PolyFun
   prefix view. There is no second custom prefix or completeness-only instruction trace.
2. `DecodedInstructionRow`, `ChipRow`, and `RowView` are physical codecs for a Clean witness. They
   remain dependent and field-valued because that information is real at the AIR boundary; they are
   not an alternative execution semantics.

The compiler's field-free access schedules and State/Memory histories are derived views of the one
operational trace, not another execution witness.  Their agreement with built rows is either proved
in the dedicated agreement modules or remains an explicit `NativeTraceReady` field; they must not
be promoted into an independently supplied timeline.

`FormalModel/Execution.lean` owns the one `SupportedCoreStatement` used by both directions, while
`FormalModel/SupportedShard.lean` owns the exact semantic relation below `Soundness/`.
`Model/Semantics/GuestProgram.lean` similarly owns the one `ConfiguredDecode` predicate used by
both committed Program rows and supported transitions. `Model/Semantics/TransitionView.lean` now
owns the sole `SP1TransitionView`: pc, fetched word, decoded instruction, route key, selected
`InstructionChipId`, and the attempted canonical access plan. `SupportedSP1Transition` and the
deterministic compiler both retain that literal projection. Access-plan success remains optional in
the view because complete eight-byte RAM-cell materialization is a compiler-domain fact, not part
of ordinary Sail support. This is a certified view of the operational trace, not a second execution
semantics.

## 3. Registries and table identity

The former repeated 25- and 53-way literals have one neutral source of truth.

- `Model/InstructionChipId.lean` owns the 25 instruction identities and canonical order.
- `Model/InstructionRouting.lean` owns the pure opcode and `rd = x0` route.
- `Soundness/SupportedMachine.lean` realizes each identity with its verified `ChipKind` and Clean
  circuit. Opcode claims and guards are derived from the neutral route rather than stored again.
- `Model/ProviderTableId.lean` owns the six Byte providers, all 17 Range widths, Program,
  MemoryInit/MemoryFinalize, MemoryBump, and StateBump, plus their native table positions.

Both native ensemble construction and completeness assembly map these registries. The extracted
instruction witness is now an indexed dependent bundle,
`ExtractedInstructionRows.forId : (id : InstructionChipId) -> List (ExtractedCols p id)`, rather
than a hand-maintained structure with 25 named fields. Transport, constraints, and interaction
ledgers are pointwise over the same identity and flattened in `InstructionChipId.all` order.

This is a format invariant: adding or reordering a chip must change the neutral registry and then
break the proofs that expose the corresponding physical order. A new positional list elsewhere is
an architectural regression.

## 4. Bus and ledger model

There are exactly two primary representations because the two proof directions need different
information.

- **Typed soundness view:** evaluated `TypedInteraction`s retain structured
  `StateMsg`/`MemoryMsg`/`ProgramMsg` values. Grounding reads this view.
- **Computable completeness view:** `LookupAccess`, `tableCleanAccesses`, and the generated trace's
  full ledger retain natural payloads and centered signed-integer multiplicities. Recounting and
  executable conformance read this view.

`Interaction.toAccess` is the bridge. Clean orientation is canonical in the native library. The
opposite Memory/Program polarity of the Rust oracle is named by `tableRustOrientedAccesses`, with
`tableNativeAccesses_perm_tableRustOrientedAccesses` proving the whole-table correspondence. This
keeps the extracted orientation fact at one boundary rather than recreating a second native ledger.

Two further distinctions remain load-bearing:

- Clean proves balance in the field; completeness reasons about centered signed integers.
  `Model/BalanceBridge.lean` is therefore an essential representation boundary, not duplication.
- Byte/Program provider closure and State/Memory hand-off are different combinatorial mechanisms.
  Closure supplies aggregated demand per key; hand-off proves a token is consumed and recreated in
  order. They share the ledger carrier, not the proof principle.

The raw-channel classifier now fails closed for provider recounting. `kindOf` has an explicit Byte
case, `kindOf_eq_byte_iff` proves that only `"SP1Byte"` enters the Byte bucket, and unknown/raw names
use the reserved State compatibility bucket. A future fifth channel cannot silently become Byte
demand.

## 5. Deterministic compiler and closed assembly

The construction is split into narrow layers:

1. `TransitionView.lean` projects the official transition once; `InstructionEvent.lean` consumes
   that same view for all 25 routed instruction families. Events are dependent on
   `InstructionChipId`, so a row cannot be placed in the wrong table.
2. `AccessPlan.lean` extracts one field-free `RAM,C,B,A` access plan.  `AccessSchedule.lean` stamps
   it against one frontier and inserts register `MemoryBump` rows at 24-bit-window crossings.
3. `ExecutionCompiler.lean` folds the chronological `locatedTransitions`, retaining the source
   transition beside its compiled event and access schedule.  The table partition is a derived
   `EventBuckets.ofChronological` view. `compileLocatedTransitions?_exists_of_views` proves that
   this recursion introduces no further partiality, while
   `compileExecution?_exists_of_instructionEventsReady` derives every outer
   fetch/decode/image/route projection from the shared semantic relation.
4. `MemoryHistory.lean` and `StateHistory.lean` derive the two hand-off histories.
5. `NativeTraceCompiler.lean` builds the 25 instruction tables, Memory init/final, MemoryBump,
   StateBump, and the one public verifier boundary.  There is zero native instruction padding.
6. `CanonicalClosure.lean` reads the literal consumer ledger and constructs exactly the demanded
   Byte, Range, and Program providers.  `FieldClosure.lean` proves their balance directly in the
   field; the retired `2 * multiplicity <= p` restriction is absent.
7. `NativeCompleteness.lean` combines provider closure with State/Memory hand-off, derives every
   table's constraints and all four channel balances, and packages the functional capstone.

The `SupportedCoreTraceWitness` stores the public `SP1PublicIO` boundary once.  The witness public
input, State endpoint messages, semantic boundary, and completeness statement are all projections
of that value; the previous four duplicated clock/PC fields are gone.

The lower `AIRCompleteness.lean` theorem remains as a useful generated-trace assembly lemma, under
the unambiguous names `supported_core_generated_trace_*`.  It is no longer presented as semantic
execution completeness.

## 6. What was retired

A second import/declaration-use audit removed the obsolete parallel bus stratum: about 2,491 lines
from the retired modules and module halves, including the whole of

- `Soundness/{ByteConsistency,MemoryConsistency,MemoryIsU64,MemoryGlobal}.lean`;
- `Soundness/ProgramProviderSpike.lean`;
- `Model/ChipAir.lean`;
- `Composition/ExactBalance.lean`; and
- `Soundness/{StateConsistency,ProgramConsistency}.lean` after moving their five live access
  declarations to `Soundness/RowView.lean`.

The deletion also removed `TraceLookupConsistent` and the unused Byte/Program ledger aliases. The
retired Byte and Memory lookup shadows predated the W11 polarity change and contained claims that
did not match the live Clean interactions. They were unreachable from a capstone, so deleting them
removed misleading models without weakening a released theorem.

Do not recreate `*Consistency` lookup lists beside the actual Clean ledger. New row-facing access
vocabulary belongs in `RowView`; global arguments must use either the typed interaction view or the
computable ledger view above.

## 7. The remaining gap to a shared semantic language

The old abstract `SupportedCoreLanguageCompletenessCertificate` API was removed.  It admitted maps
that could ignore the supplied execution and therefore did not express compiler fidelity.  The live
boundary is the concrete `Execution.NativeCompilerReady` plus the small named invariants in
`NativeTraceReady`, all indexed by the actual output of `compileExecution`.

The all-25 compiler, bump placement, provider recount, public-boundary projection, capacity-aligned
soundness/completeness API, and final AIR map are implemented. What remains on the compiler side is
proving `NativeTraceTotalOnSupportedCore`: every residual `NativeTraceReady` group plus the emitted
footprint on `SupportedCoreOrdinaryShardExecutionRelation`:

- access-plan success (including complete source and target RAM cells for memory instructions),
  row-shape compiler success, and registry-wide validity of each generated per-chip event;
- State chronology/bump readiness and the built-instruction-row projection;
- canonical Memory addresses, record chronology, physical-ledger agreement, and initial-state
  genesis content;
- Byte consumer polarity and Byte/Program demand servability for the literal generated ledger;
- Program-row physical projection (decoder stability is already the shared `ConfiguredDecode`
  attached to `SP1TransitionView` by `SupportedSP1Transition` and carried by `decodedInROM`); and
- the actual emitted interaction count being below the field characteristic.

Some of these are deterministic representation lemmas and should leave the readiness bundle as
their agreement modules mature; others are genuine semantic source restrictions.  The API should
not describe only the latter while still assuming the former.

The last item is intentionally a footprint property, not a provider multiplicity convention.  The
first three are semantic inverse/refinement lemmas.  They must be proved from the official Sail
step or added as precise source-language restrictions; they must not be replaced with an
existential AIR witness.

Deriving those facts remains necessary. The former capacity mismatch is closed: the native and
semantic relations project their active-row/step counts into the single
`CoreProfile.WithinOrdinaryRowLimit` predicate, and bounded soundness is proved. Consequently
`supported_core_native_shard_correct_of_totality` and
`supported_core_native_shard_language_eq_of_totality` require exactly the totality theorem above.
Until it is closed, unconditional public-language equality would still be an overclaim even though
all 53 native tables and the verifier row are covered by the current completeness theorem.

## 8. Separate upstream and cryptographic boundaries

This handoff concerns the 53-table native proof architecture. It does not close the exact v6.4.0
34-table/6-table Rust AIR refinement bundle. `CoreAIRRefinementObligations` still has to derive the
native provider/boundary facts from the six Core system tables before unqualified `sp1_air_sound` is
available.

The first local semantic fan-out for that bundle now lives in
`Composition/CoreSystemSemantics.lean`: both bump transports expose their exact native decoded
inputs. `Channels.SyscallMsg` is the single typed nine-field tuple shared by `SyscallCoreView` and
the narrow `SyscallInstrsSyscallView`; exact-list membership theorems prove the former receives and
the latter sends that same carrier at their generated multiplicities. `MemoryLocalView` names all
twenty columns and its typed initial/final Memory records, and another membership theorem identifies
the exact generated Memory endpoints. The generated oracle lists remain the sole complete ledgers —
the semantic layer no longer hand-copies their four- and fourteen-interaction lists.

The SyscallCore and MemoryLocal assertion iff theorems still characterize their complete local
contracts, and `CoreAIR.System.localValid_of_relationFor` fans those facts out from exact execution
validity without exposing the relation's conjunction layout. These are local facts only. Global
meaning, raw Syscall transcript balance, the full SyscallInstrs row law, and the missing cross-table
range/order consequences remain obligations rather than being inferred from typed names.

It also does not prove cryptographic verifier completeness or soundness. ArkLib must authenticate
the extracted AIR witness and retain the probabilistic error bound. Do not turn either the compiler
certificate or the exact-AIR refinement bundle into an unconditional verifier claim.

## 9. Maintenance rules learned from the cleanup

- Search for a registry-wide theorem before writing a 25-chip sweep.
- Keep expensive circuit `Spec` values folded; use explicit rewrite lemmas across spellings.
- Use `rowInput_buildRow` for the generic input half of generated rows; use the chip's `Spec` only
  for output facts it genuinely determines.
- Do not infer push/pull polarity from Clean's guarantee/requirement lists. Polarity lives in the
  interaction multiplicity.
- Keep aggregate provider multiplicities out of binary-only lemmas.  Canonical closure now proves
  Byte/Range/Program balance directly in the field; only the actual interaction-list length must be
  below `p`.
- Run the root-index and layering gates after any registry or module move. The final campaign must
  still finish with a clean `lake build SP1Clean`, `lake test`, and the audit census.
