# Native resource contract

The concrete native facade uses data-only numeric limits. A limit is an explicit policy choice;
it is not evidence that the existing AIR enforces it or that every bounded execution compiles.
The capstone needs both directions against the same domain. Current implementation and PR status
belong to fork campaigns [#12](https://github.com/dtumad/sp1-lean/issues/12) and
[#16](https://github.com/dtumad/sp1-lean/issues/16).

## Ranges and representation

`AddressRange` owns lower/upper bounds, and `MemorySpan` owns requested byte intervals and their
eight-byte-cell cover. Byte membership is half-open. Span containment checks the full natural
sum before narrowing; an empty span may start at the upper endpoint, matching existing host
reads. It may not start below the lower bound or beyond the upper bound.

`NativeLayout.guestMemory = [2^16, 2^48)` is the SP1 PMA/guest-access instance.
`NativeLayout.sailMemory = [0, 2^48)` is the byte-key domain represented by a complete Sail
snapshot. These are distinct: an inaccessible byte can still be present in the memory map.
`HostMemoryPolicy.range` consumes the shared range; its `lower`/`upper` names are compatibility
projections, not additional stored bounds. Program-image checks use the same guest instance.
Other range values are meaningful for the generic arithmetic/host interface, not a claim that
arbitrary layouts have been proved against the fixed generated Sail model or SP1 chips.

The clock encoding has two 24-bit limbs. Every active native CPU row also has phase one modulo
eight: the shared `Native/Readers/CPUState.lean` circuit constrains `(clk_0_16 - 1) / 8` by a
13-bit range lookup. Ordinary instruction and host rows both use it. `TimeExtraction.cpuState_clock_phase`
derives the phase from that actual specification. Source validity and the broader Sail/host
execution relation do not imply it. The native profile therefore requires the phase explicitly;
empty/stopped identities do not. The generic scheduler needs only room for its four local offsets,
and its window lemmas retain phase-one compatibility wrappers. Sail permits misaligned
ordinary data accesses. The specific alignment imposed by native chip encodings is a separate
representability condition, not a Sail fault assumption.

## Quantities and proof ownership

All `ResourceLimits` fields are inclusive ceilings. The `native` preset records count budgets:
`2^24` elapsed ticks from pinned SP1 v6.4.0 `opts.rs`, `2^21` events, and `p-1` for the remaining
finite inventories. The preset does not assert that all ceilings can be saturated simultaneously;
construction must establish its complete expansion fits. It is not a theorem about the current
mixed AIR's accepted language. In particular, `p-1` is a field-count ceiling, not a proof that
all pointer/length encodings fit for an arbitrarily large characteristic. Fixed bit-width bounds
and combined persistent-allocation bounds remain separate checks. The exact-Core budget uses
the same named tick constant.

| Quantity | Measurement | Enforcement / construction owner |
|---|---|---|
| events, ticks | Actual event tape and 8/264-tick durations | Ordered CPU occurrences and public clock boundary; execution scheduler |
| readBytes | Requested host read bytes, counting both logical VERIFY buffers | Bound host requests and byte observations; `HostFootprint`/`HostReadPlan` |
| writeBytes | Actual emitted host bytes, including mandatory HINT_READ padding | Word/write inventory and permission checks; hint word construction |
| allocatedHints | Cumulative fresh hints, including hook replies, independently of later pops | Fresh-node inventory; persistent queue construction |
| liveHints, liveHintBytes | Maximum actual queue occupancy over complete prefixes | Queue head/state binding; interpreter and queue representation |
| requests | Peak complete request-list length, including incoming observations | Request-bound host tables; host interpreter |
| outputBytes | Accumulated public/stdout/stderr bytes | Complete host boundary and WRITE observations |
| boundaryBytes | Live nonzero RAM plus length-prefixed host payload and Sail output strings, maximized over boundaries | Complete source/target verifier; finite snapshot normalization |
| tableRows | Physical rows in each table, including providers/refresh/padding | Actual table inventory and all-table construction |
| channelOccurrences | Complete occurrence count in each registered channel | Clean ledger capacity and exact footprint accounting |

Numeric definitions do not close these rows. In particular the existing installed host inventory
omits WRITE/VERIFY, full target authentication remains open, and the legacy compiler accepts
ordinary executions only. These installation obligations belong to A4–A6. The resource work must
prove bounds for actual consumers and must not substitute a witness/readiness predicate for usage.

## Installed endpoint checks and remaining enforcement

`Native/Operations/ResourceBoundary.lean` implements a real verifier subcircuit checking the
source and supplied target's finite occupancy, natural elapsed ticks, and target PC/clock range.
Its clock equations bind that target clock to the actual outgoing State token.
`Soundness/ResourceEnsemble.lean` installs it over the current source-hint assembly and derives
actual elapsed-work bounds from raw constraints and balance. Every event consumes at least
eight ticks; this proves the native preset's event ceiling, including 264-tick host calls.
It does **not** enforce an arbitrarily tighter independent `events` ceiling.

`ToClean/Air/PublicVerifier.lean` preserves the literal tables and every existing channel ledger,
including order, repetitions and zero-multiplicity occurrences. Its fresh assertion channel
accounts for the endpoint checks. The installed statement is proved
equivalent to the original raw statement plus the exact endpoint checks. The semantic domain
proves these checks for completeness; no conservative expansion estimate is imposed here.
Stopped identities retain their original clock and need no active-event phase.

The enforcement obligations remain explicit:

| Remaining conclusion | Owner / required evidence |
|---|---|
| Supplied target occupancy equals actual outgoing occupancy | A4 complete target authentication; clock equality alone is insufficient |
| Every intermediate live queue/RAM/output/request peak fits | A4/A5 constrained resource accounting at actual prefixes |
| Arbitrary independent event/read/write/allocation ceilings | A4/A5 exact occurrence/cost accounting, including padded writes and both VERIFY observations |
| Fixed pointer/length widths and cumulative persistent allocation | A5 queue/request installation; individual field-count ceilings are insufficient |
| Whole `ExecutionPath.Encoded` derived from registered rows | Shared CPU phase is derived from its actual specification; A6 assembly must combine each ordinary chip's address/alignment facts with actual prefix decoding |
| Physical height and every channel's occurrence ceiling | Exact inventory accounting below; final A4/A5/A6 construction must prove its full expansion fits, and silent tables need explicit height bounds |

These are unproved implementation obligations, not additional capstone premises. The endpoint
checker regression deliberately accepts a boundary whose tape exceeds the padded-write budget:
it prevents an endpoint-only check from being mistaken for complete resource enforcement.

## Exact physical accounting

`ToClean/Air/Footprint.lean` measures the public verifier's operations and every physical table.
For each raw channel, `channelOccurrences` adds the verifier's occurrence count to each table's
height times its circuit's syntactic interaction width. `channelOccurrences_eq_length` proves
this is exactly the evaluated ledger length. Repeated keys, zero multiplicities, refreshes and
inactive padding all spend capacity. No deduplication or multiplicity filter is involved.
`PhysicalFits` checks every table height and every registered channel against numeric ceilings;
`ChannelCapacity` is precisely Clean's existing strict field-characteristic bound.

The retained ordinary compiler consumes `ChannelCapacity` in `NativeTraceAdmissible` and its
functional completeness proof. `Proofs/Completeness/PhysicalFootprint.lean` proves its exact
height and demand formulas from the existing event buckets and provider occurrence lists:
one row per instruction event or provider occurrence, one mandatory Halt padding row, an empty
ordinary SyscallInstrs table, and the separate public verifier ledger. Provider closure and refresh occurrences are
already in those lists. The resulting `physicalFits_iff` and `channelCapacity_iff` are exact
arithmetic equivalences; they do not replace the accepted language with an upper estimate.

`Soundness/ResourceFootprint.lean` applies the same accounting to the installed host assembly.
Raw balance gives the native `p-1` occurrence ceiling on **every registered channel**, including
host/boundary channels. Any table with a positive syntactic interaction width on a registered
channel inherits its native height bound. A silent table needs separate evidence. Installing
the endpoint checker preserves every physical row and existing channel ledger. Its three
assertions add exactly six occurrences on a fresh channel. Thus the installed witness fits
exactly when the base witness fits and the channel ceiling is at least six. The lifting theorem
keeps this equivalence explicit for arbitrary budgets; the native field bound covers this cost.

This is not yet a proof that the fixed semantic limits imply full mixed construction capacity.
Independent ceilings of `p-1` do not imply that the sum of provider, boundary, host and padding
costs is below `p`. A4/A5 must finish authenticating and enforcing the complete resource domain;
A6 must give the full mixed constructor's exact demand, including those installations, and
prove capacity against the same domain. If these limits are insufficient, the policy and its
actual enforcement must be reviewed together. Adding compiler success or a conservative
footprint bound as a capstone premise would not discharge this obligation.

## Representation and retirement

The only complete execution model is `ExecutionPath` over Sail/host/clock, with paired replay and
`ExecutionSnapshot` boundaries. New resource records measure it; they do not carry a second path.
`ExecutionResources` observes the existing replay, summing events/ticks/read/write/allocation work
and taking maxima for live resources. It includes both sides of each real step; empty identities
check their incoming occupancy separately. `resources_append` and `resources_split` prove the
arithmetic at complete semantic cuts. `ExecutionSnapshot.resources_realize` computes occupancy
without materializing dense Sail memory; `ByteMemory.supportBelow` removes zeros and shadowed
writes. Both state and tape usage are invariant under equivalent complete snapshots.

`nativeProfile` is fixed at the Shard and PolyFun target consumers. It requires width-aligned
ordinary LOAD/STORE spans and phase one modulo eight at each active CPU source. This phase implies
the low-clock window (`clock % 2^24 + 4 < 2^24`). Normal Sail retirement alone does not imply width alignment. Final PC/clock
fit their native encodings but need no subsequent fetch. The physical `tableRows` and
`channelOccurrences` ceilings have actual witness consumers through `PhysicalFits`; they are
not yet derived from `nativeProfile` for the full mixed constructor. Semantic measurements do
not stand in for that proof. `boundaryBytes` is a variable-payload measure, not a full Sail
serialization-size theorem: fixed public register/platform data and the final boundary circuit's
actual row cost remain part of A4/R5. No bounded-ensemble instance is claimed by these definitions. `MemorySnapshot` remains the provider view.
`HintQueue.Store` is a persistent implementation of semantic host queues, related by `Represents`.

| Compatibility surface | Replacement / removal condition |
|---|---|
| `EventExecutionTrace`, `CoreShardSemanticWitness` | Retain for ordinary/exact-Core consumers; migrate the mixed compiler to the complete path in A6. Delete only after retained exact/export consumers have adapters. |
| `InstructionPlanReady`, `NativeCompilerReady`, `NativeTraceReady` | Prove their applicable fields from semantics for retained APIs; no occurrence in the new domain. Remove wrappers once all relevant consumers use the derived results. The legacy `syscallFree` field cannot describe mixed execution. |
| Explicit numeric range checks in older chip/Sail lemmas | Retain encoding-specific statements, derive their range facts from `NativeLayout`; factor more generally only with a migrated consumer. |

`ExecutionMemory` proves presence and outside-domain framing along the existing Sail/host path,
including padded host writes, independently of AIR grounding. `ShardAccess` derives canonical
access projection at every ordinary position. `Proofs/Completeness/SemanticAccess.admissibleExecution_compile_at`
then derives event extraction, role ordering, valid refreshes and the outgoing frontier invariant
for all 25 routed families. The family lemmas inspect the existing router and constructors;
`instructionAccessSlots` only erases values from the canonical plan. No second instruction model
or path is introduced. The old readiness wrappers remain for legacy consumers; extraction
readiness is now derived, while per-chip event validity and all-table mixed assembly remain A6.

No whole-chip faithfulness anchor is retired by this work. Native range/resource strengthening
does not automatically become exact upstream SP1 refinement.
