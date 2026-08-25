# Handoff: one native shard model for soundness and completeness

**Audience: us, on another machine, with no context.** Updated 2026-08-24 after the
bus-representation and shard-model consolidation on `dtumad/provider-closure`.

Read [`overview.md`](../overview.md) and [`architecture.md`](../architecture.md) first. The design
record for this cleanup is
[`bus-representation-consolidation.md`](../proposals/bus-representation-consolidation.md).

## 1. Outcome

Soundness and completeness now share one operational witness and one physical native witness.  The
forward theorem is closed for the exact image on which the deterministic compiler's semantic and
capacity obligations hold; it no longer starts from an existential or hand-assembled trace.

```text
                     supported_core_native_ordinary_sound
native Clean AIR  -------------------------------------------->  exact ordinary shard
     ^                                                               |
     | supported_core_native_functionalCompleteness                   | nativeTrace
     |                                                               | (total, proof-independent)
     +---------------- native admissible image <----------------------+
```

The exact target is `Execution.SupportedOrdinaryShardExecutionRelation`. Its witness is the single
proof-free `Machine.EventExecutionTrace`; validity supplies the official event-step semantics,
normal retirement, the ordinary eight-tick schedule, public endpoints, committed-program boundary,
and a successful route through the canonical 25-chip profile for every transition.

The released direction theorems are:

- `supported_core_native_ordinary_sound` is closed. Every witness accepted by
  `SupportedCoreNativeRelation` produces an exact supported ordinary event trace.
- `supported_core_native_functionalCompleteness` is closed from
  `SupportedCoreNativeAdmissibleExecutionRelation`.  Its map is literally the deterministic
  `nativeTrace statement execution`; it is independent of the proof of admissibility.
- `supported_core_native_complete` is the existential projection of that functional theorem.
- `sp1Ensemble_statement_of_supported_execution` exposes the underlying Clean
  `Ensemble.Statement` directly.

`SupportedCoreNativeAdmissibleExecutionRelation` is not a renamed AIR witness condition.  It is the
exact ordinary Sail relation, the pinned Core row budget, the named field-free compiler/readiness
facts for that same execution, and `NativeTraceFootprint.Fits` on the actual emitted interactions.
In particular it contains neither channel balance nor table constraints; both are conclusions.

This closes whole-ensemble completeness for the honest deterministic compiler image.  It does not
yet prove that every witness of the broader exact ordinary relation lies in that image.  Therefore
there is deliberately no unconditional `WitnessRelation.Correct` or public-language-equality
theorem: soundness targets the broader exact relation, while completeness currently has the
explicitly narrower admissible source. In particular, the broader relation is unbounded and cannot
yield `WithinCoreShardLimit` or the physical `< p` footprint merely by discharging readiness.

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

`FormalModel/SupportedShard.lean` owns the exact semantic relation below `Soundness/`, so both proof
directions can depend on it. Its `SupportedDecodedTransition` retains the decoded instruction and
selected `InstructionChipId` as evidence, not as another stored trace.  The deterministic compiler
retains each `LocatedTransition` beside its decoded instruction and generated event; this is a
certified view of the operational trace, not a second execution semantics.

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

1. `InstructionEvent.lean` compiles all 25 routed instruction families from the official decoded
   Sail transition.  Events are dependent on `InstructionChipId`, so a row cannot be placed in the
   wrong table.
2. `AccessPlan.lean` extracts one field-free `RAM,C,B,A` access plan.  `AccessSchedule.lean` stamps
   it against one frontier and inserts register `MemoryBump` rows at 24-bit-window crossings.
3. `ExecutionCompiler.lean` folds the chronological `locatedTransitions`, retaining the source
   transition beside its compiled event and access schedule.  The table partition is a derived
   `EventBuckets.ofChronological` view.
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

The all-25 compiler, bump placement, provider recount, public-boundary projection, and final AIR map
are implemented. What remains on the compiler side is proving every residual `NativeTraceReady`
group on the intended capacity-bounded subset of `SupportedOrdinaryShardExecutionRelation`:

- compiler success and registry-wide validity of each generated per-chip event;
- State chronology/bump readiness and the built-instruction-row projection;
- canonical Memory addresses, record chronology, physical-ledger agreement, and initial-state
  genesis content;
- Byte consumer polarity and Byte/Program demand servability for the literal generated ledger;
- Program-row projection plus stability of the decoder across the configured-state class required
  by `ProgTruth`; and
- the actual emitted interaction count being below the field characteristic.

Some of these are deterministic representation lemmas and should leave the readiness bundle as
their agreement modules mature; others are genuine semantic source restrictions.  The API should
not describe only the latter while still assuming the former.

The last item is intentionally a footprint property, not a provider multiplicity convention.  The
first three are semantic inverse/refinement lemmas.  They must be proved from the official Sail
step or added as precise source-language restrictions; they must not be replaced with an
existential AIR witness.

Deriving those facts remains necessary, but completeness cannot simply be widened to the current
unbounded exact relation: its Core row cap and physical `< p` premise have no counterpart in the
soundness conclusion. A `WitnessRelation.Correct` capstone therefore needs a shared
capacity-bounded semantic relation on both directions, or equivalent strengthening/weakening
lemmas that make the two domains coincide. Until then, public-language equality would be an
overclaim even though all 53 native tables and the verifier row are covered by the current theorem.

## 8. Separate upstream and cryptographic boundaries

This handoff concerns the 53-table native proof architecture. It does not close the exact v6.4.0
34-table/6-table Rust AIR refinement bundle. `CoreAIRRefinementObligations` still has to derive the
native provider/boundary facts from the six Core system tables before unqualified `sp1_air_sound` is
available.

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
