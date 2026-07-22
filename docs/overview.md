# SP1 verification: current claim and audit guide

**Status: current checkpoint, 2026-07-22.** This document describes the implementation in this worktree.
The aspirational completed-state document is [`goal-overview.md`](goal-overview.md); the frozen pre-remediation
audit is under [`audits/2026-07-full-project/`](audits/2026-07-full-project/).

## 1. What this repository is trying to prove

SP1 represents RISC-V execution with a family of AIR tables. The long-term claim is that a proof accepted
by SP1's verifier corresponds to an execution of the committed program in the official RISC-V Sail model.
That sentence contains three different verification problems, kept separate here:

1. **AIR soundness:** a satisfying upstream SP1 shard witness yields a Sail execution segment;
2. **execution composition:** authenticated consecutive shards compose from boot to the halting ECALL; and
3. **verifier knowledge soundness:** an accepting cryptographic proof admits extraction of the AIR witness.

The project implements a substantial supported native-Clean slice and now also has the exact pinned
upstream table/public-value relation plus an auditable deterministic capstone interface. It does not yet
claim a closed full-upstream shard proof, boot-to-halt composition theorem, or ArkLib verifier theorem:
the new `sp1_air_sound` composition theorem still requires its explicit per-table refinement bundle and
the disclosed commit-row provenance premise.

The stable unit of verification is a whole SP1 chip. Rust operations and Lean gadgets are allowed to use
different internal decompositions; only the complete chip's assertions, interactions, populate behavior,
and semantic effect need to be pinned.

## 2. The theorem stack

The implemented native theorem is:

```lean
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound SupportedCoreNativeRelation
      (SupportedCoreLocalExecutionRelation model)
```

`SupportedCoreNativeRelation` combines:

- the algebraic relation of the 36-table Clean ensemble (`Constraints` plus balanced channels); and
- explicit semantic binding of provider/boundary tables to the committed program and a local initial Sail
  state, including per-location uniqueness of the memory-init genesis records
  (`MemoryInitProviderUnique`, 2026-07-16) — channel balance alone cannot exclude a duplicate genesis
  record whose stale twin a later pull could match; upstream this is SP1's global-interaction
  uniqueness argument.

The conclusion is a finite official-LeanRV64D execution segment between public shard endpoints. It is
deliberately local: reachability from canonical boot belongs to shard composition, not to a one-shard AIR
theorem.

The theorem's assembly is present, but it is not yet axiom-clean. It inherits the named
`supportedCore_orderedRows_dynamic` admission, which must prove that every exactly decoded and ordered
physical row obtains current Memory operands, circuit assumptions, its semantic chip `Spec`, and
`advanceReady` at the corresponding evolving Sail state.

The theorem names now separate implemented composition boundaries from closed results:

```lean
supported_core_air_sound  -- still reserved: native/extracted whole-chip faithfulness + native soundness
sp1_air_refinement        -- implemented composition from exact upstream rows, conditional on named proofs
sp1_air_sound             -- implemented existential corollary, with the same explicit open premises
sp1_execution_sound       -- authenticated shard composition from boot to halt
sp1_verifier_sound        -- ArkLib knowledge soundness, post-composed through sp1_air_sound
```

The source relation of `sp1_air_refinement` is not a placeholder. `CoreProfile` is pinned to semantic
revision `a630089d9ff484ec6f2feade8d0afbb1447eed11` and checks the runtime-extracted 34-table execution
cluster, 6-table memory-boundary cluster, table widths, and 160 public cells. `Faithful/CoreAIR.lean`
dispatches every complete generated assertion and interaction list. The capstone consumes only the
`.execution` cluster; the boundary cluster cannot masquerade as an execution witness.

`FormalModel/Verifier.lean` proves the dependency-free extraction/refinement combinator needed by the
future ArkLib adapter. It does not pretend that deterministic AIR refinement proves Fiat–Shamir,
commitment, query, LogUp/GKR, or extractor soundness. In particular, the AIR source relation asks for
exact equality of canonical natural interaction multiplicities. ArkLib must derive that non-wrapping
multiset fact, with appropriate bounds and its existing knowledge-error term, from the proof protocol.

## 3. The supported machine

`Soundness/SupportedMachine.lean` is the single descriptor for the 25 implemented RV64IM instruction
chips. Each entry owns:

- its verified Clean `GeneralFormalCircuit`;
- its semantic `ChipKind`;
- its SP1 opcode family; and
- its `rd == x0` routing guard.

The ensemble tables, semantic registry, coverage table, and routing projections are derived from this
descriptor, preventing independent lists from silently drifting. The supported slice covers the ordinary
integer ALU, control-flow, multiplication/division, load/store, and `x0` routing tables. Syscalls/HALT,
precompiles, traps, User-mode duplicate AIRs, recursion, and the full SP1 machine table set remain outside
the **native Clean descriptor**. They are not silently absent from the upstream relation: the baseline
exact cluster includes `SyscallCore`, `SyscallInstrs`, MemoryBump, StateBump, MemoryLocal, and Global.
Precompile clusters, user/mprotect clusters, and retention extensions are separate profile targets.

Every registered chip now supplies the same per-row transition contract:

```lean
advance : is_real = 1 → chipSpec → SailConfigured state → RomLoaded program state →
  pc_matches_row → live_operands_match_row → committed_decode → advanceReady →
  ∃ next, SailStep state next ∧ RowEffect program row state next
```

All 25 entries have `advance.isSome = true`, proved by `allChipKinds_migrated`. The old parallel
`sailEquiv`/`reaches_sail` interface has been retired. `RowEffect` records the next PC, at most one register
write, at most one contiguous memory write, and preservation of everything else.

`ChipKind.advance` remains `Option`-typed as a migration-era representation, but there is no fallback
semantic path: registry membership plus `allChipKinds_migrated` is what the local-execution dispatcher
uses.

## 4. The four structural buses

Chips communicate through ordinary Clean channels. Their guarantees contain only facts a row or provider
can prove locally:

| Bus | Message | Local guarantee | Global fact derived later |
|---|---|---|---|
| State | `(clock, pc)` edge | `True` | exhaustive time-ordered execution path |
| Program | decoded instruction row | structural `ProgramMsg.RowSpec` | equality with the committed ROM decode |
| Memory | location, timestamp, value | `MemoryMsg.isU64 ∧ MemoryMsg.ClkBound` | read currency / most-recent write |
| Byte | opcode and byte/range operands | `ByteRowSpec` | the local table fact is already semantic |

Execution reachability, ROM commitment, and Memory currency are not channel assumptions. Clean balance
provides algebraic equality of posted and consumed records; the machine grounding layer proves their
global interpretation.

## 5. From an ensemble witness to Sail execution

The new capstone path has these stages:

1. `WitnessDecode.lean` deterministically decodes all typed circuit tables. It cannot choose unrelated
   semantic rows or convenient casts.
2. `RankedGrounding.lean` upgrades balanced State edges to an exhaustive trail by proving strict clock-rank
   increase, ruling out disconnected balanced cycles.
3. Program-provider balance binds every active row's committed fetch to the committed program.
4. `LocalExecution.lean` consumes the ordered rows through their registered `advance` proofs to construct a
   genuine Sail chain.
5. `supported_core_witness_grounding` assembles exact row coverage, State ordering, PC walk, clock count,
   activity, registry membership, and Program decode.

The remaining dynamic step is deliberately narrow. `TypedInteractions.lean` preserves each exact evaluated
Clean interaction with its channel type. `TypedMemory.lean` turns active Memory pulls into timed facts and
live-register bindings. All 24 non-DivRem chips now carry their exact Memory closed forms
(`exposedMemoryInteractions` + `interactionsWith_memory_eq`), and `GroundingAdapter.lean` turns any
migrated chip's registered `advance` into the timed engine's per-row records; `ChipContracts.lean`
bundles those into `ChipGroundingContracts` and reduces the named seam to
`supportedCore_orderedRows_dynamic_of_contracts` (Add's instance `addChip_groundingContracts` proved).
`AlignedCarrier.lean` + `AlignsWith` reconcile the walk's aligned `RowFacts` carrier with the ordinary
one the chip contracts and consumers use.

The next scale-out work is to instantiate `ChipGroundingContracts` for the remaining 23 chips and build
the memory-channel balance stack, then extend the grounding induction to RAM, repeated touches of one
location, and the relevant scheduling cases. This is the direct path to closing
`supportedCore_orderedRows_dynamic`.

The old Eulerian `GatedVm`/`TargetVm` material remains as a frozen proved intermediate and historical proof
resource. Its `sp1_decoded_rows_sound` admission is not the semantic seam consumed by the new native
capstone.

The upstream capstone uses a parallel eventful decoder. Ordinary events must be real Sail steps and
advance 8 ticks; syscall events advance 264 ticks and satisfy the extracted row laws plus a caller-named
`SyscallHandler`. This parameter is intentional: Sail does not model SP1 host/precompile effects. A weak
handler yields a correspondingly weak theorem, so a production instantiation must prove that handler from
the relevant authenticated syscall/precompile tables. The current baseline does not claim precompile
semantics merely because it can decode an ECALL row.

## 6. One chip end to end

The completed target boundary for a chip has five artifacts:

1. a native semantic Clean circuit and chip `Spec`;
2. a Sail bridge from `Spec` to one instruction step;
3. an auto-generated whole-chip Rust oracle with the complete row, `assertZero` list, and four-bus
   interaction list;
4. a `ChipFaithful` theorem relating the native circuit and oracle through one explicit row
   reconfiguration; and
5. complete-trace populate conformance against Rust `generate_trace`.

Add and Sub implement this whole-chip boundary today. Their native rows no longer alias generated Rust
rows, and their proofs compare complete assertion systems and complete interaction multisets. The remaining
chips retain useful operation/fragment faithfulness anchors during migration, but those are not counted as
final whole-chip AIR faithfulness.

DivRem is the complex-chip contract pilot. Its old nine operation-shaped integration proofs were deleted.
`FormalModel/Contracts/DivRem.lean` defines four arithmetic families plus eight opcode-routing cases;
`Proofs/Chips/DivRemChip/Cases.lean` proves their arithmetic and exceptional behavior. The single admitted
`DivRemChip.evidenceSoundness` theorem is the remaining generated-row-to-evidence bridge.

## 7. Completeness and executable conformance

Per-chip completeness is the honest-prover direction of each Clean circuit, not the converse of the
whole-machine semantic relation. Four such proofs are deferred after the Lean/Clean 4.31 migration:
Branch, ShiftLeft, ShiftRight, and DivRem. These are lower priority than the remaining soundness seams
because they do not change what a satisfying row means.

Whole-machine completeness will require a trace-generatable execution relation, a verified trace generator,
provider construction, and global balance. It is acceptable to state that future result with an explicit
top-level completeness admission while the architecture stabilizes; Clean itself is not being forked to
hide the distinction.

Executable checks live in the separate `SP1CleanTest` library. Ten chips have complete unmasked trace
batteries derived from their circuits' witness closures and compared cell-for-cell with SP1's real
`generate_trace`, including padding and hint-driven flags. Transitional operation witness batteries remain
where still useful. These checks use `native_decide` and are therefore never imported by the main proof
library.

## 8. Current gaps and trust boundary

`scripts/run_audit.sh` currently gates exactly 9 direct deferral sites in seven files:

- four chip-completeness proofs;
- `DivRemChip.evidenceSoundness`;
- two DivRem circuit channel-law fields;
- the frozen-path `sp1_decoded_rows_sound`; and
- the live semantic seam `supportedCore_orderedRows_dynamic`.

The generated census contains 471 probes. Thirty-one declarations transitively carry `sorryAx`; this is
not 31 independent holes, because the supported-machine descriptor embeds complete circuit records and
therefore propagates admitted circuit fields into registry/ensemble projections. The allowlist names every
permitted carrier, and a new direct file or unexpected transitive carrier fails the audit.

The project has no local `axiom` declarations, no `skipKernelTC`, and no `native_decide` in `SP1Clean/`.
Selected `bv_decide` helper lemmas disclose their generated decision axioms. Sail execution theorems inherit
the generated model's platform axiom surface; that dependency trust base is reported rather than hidden.
Rust extraction and executable conformance remain external/toolchain trust boundaries.

The new exact-upstream layer adds open proof obligations without adding `sorry` sites:

- instantiate `CoreAIRRefinementObligations` from the generated lists, using the native chip proofs and
  the completed timed-grounding engine rather than restating the semantic target;
- discharge the temporary `CoreAIRSemanticAssumptions` fact that a newly asserted COMMIT or
  COMMIT_DEFERRED flag has all eight introducing rows; per-row operand equality is still proved separately;
- prove concrete syscall-handler refinements, and add precompile clusters only when their whole tables and
  handler effects are covered;
- prove the recursion/PCS bindings (preprocessed commitment, septic cumulative sums, deferred-proof
  authentication, and complete full-state shard stitching); and
- instantiate ArkLib's knowledge-sound extractor for the strengthened exact-multiplicity AIR relation.

Run:

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

For exact pins, theorem carriers, and risk classification, use
[`release-audit.md`](release-audit.md). For the implementation sequence, use
[`roadmap.md`](roadmap.md) and [`proposals/consolidation-progress.md`](proposals/consolidation-progress.md).
