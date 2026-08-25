# The audit surface

*Machine-checked by `scripts/check_audit_surface.sh` (run by `scripts/run_audit.sh` and the CI
`guards` job): every declaration named below must still exist at the file named beside it. Adding a
premise, or removing one, changes this table — that is the point.*

## Why this list exists, and why it is short

The external PR #110 review (§9) states the right criterion, and it is not "theorems versus lemmas".
For a closed theorem `T` in an environment with no `sorryAx` and no project axiom, write `Stmt(T)`
for the constants reachable from `T`'s **type** and `Prf(T)` for those reachable from its **value**.
Everything in `Prf(T) \ Stmt(T)` is a proof-only artefact: if it were wrong the kernel would have
rejected `T`. The entire risk of *proving the wrong thing* lives in `Stmt(T)` and in the ambient
instance context.

That is what makes auditing this repository tractable. The review measured the split for
`supported_core_native_sound`: 13,943 constants in the proof closure, 10,665 in the statement
closure, of which 7,487 are proof-typed (inert for meaning) — leaving **3,178 data/definition-typed
constants across 243 modules** as the real surface, and confirming the repository's own claim that
`FormalModel/Contracts/` is where it concentrates.

This file is the human-sized version: the definitions where a defect would be undetectable by the
kernel, each with the question it decides. Reading these, plus `FormalModel/Contracts/` and the 25
`Native/Chips/*/Defs.lean`, is reading the part that can be *wrong* rather than merely unproved.

## The claim itself

| Declaration | File | Question it decides |
|---|---|---|
| `WitnessRelation.Relation` | `SP1Clean/FormalModel/Relations.lean` | What a statement/witness relation is |
| `WitnessRelation.Sound` | `SP1Clean/FormalModel/Relations.lean` | Direction and shape of the soundness claim |
| `WitnessRelation.Complete` | `SP1Clean/FormalModel/Relations.lean` | Direction and shape of the completeness claim |
| `WitnessRelation.FunctionalCompleteness` | `SP1Clean/FormalModel/Relations.lean` | The proof-independent reverse witness map; no witness-preservation law is implicit |
| `WitnessRelation.Correct` | `SP1Clean/FormalModel/Relations.lean` | Both existential directions, hence public-language equality rather than witness inversion |
| `SupportedCoreNativeRelation` | `SP1Clean/Soundness/AIR.lean` | The hypothesis side: exactly two conjuncts |
| `supported_core_native_sound` | `SP1Clean/Soundness/AIR.lean` | The headline theorem |
| `supported_core_native_ordinary_sound` | `SP1Clean/Soundness/AIR.lean` | The native witness projected to the exact ordinary supported target |
| `SupportedCoreLocalExecutionRelation` | `SP1Clean/FormalModel/Execution.lean` | What the conclusion actually says |
| `SupportedOrdinaryShardExecutionRelation` | `SP1Clean/FormalModel/SupportedShard.lean` | The shared normal-retirement, 25-route semantic target |
| `SupportedDecodedTransition` | `SP1Clean/FormalModel/SupportedShard.lean` | What “supported” requires of each transition |
| `LocalSegmentMatchesBoundary` | `SP1Clean/FormalModel/Execution.lean` | How the conclusion is pinned to the public endpoints |

## Which machine is being verified

| Declaration | File | Question it decides |
|---|---|---|
| `sp1Ensemble` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 53-table native machine |
| `sp1Tables` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 25 instruction tables |
| `sp1ProviderTables` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 28 provider/boundary tables and their order |
| `sp1StateVerifierMain` | `SP1Clean/Soundness/SP1Ensemble.lean` | The boundary row, incl. its public-limb range checks |
| `SP1StateBoundary` | `SP1Clean/FormalModel/Contracts/PublicValues.lean` | What is public |
| `ChipKind` | `SP1Clean/Soundness/ChipRow.lean` | The per-chip interface (`chipSpec`, `advanceReady`, `view`, `advance`) — 25 registrations |
| `RowEffect` | `SP1Clean/Soundness/RowEffectDefs.lean` | What each row is proved to *do* |
| `ValueOperandsBound` | `SP1Clean/Soundness/RowEffectDefs.lean` | How a row's operands are tied to machine state |

## The assumed semantic boundary

`InitialBoundaryFacts` has **eleven** fields. The PR #110 review tabulated twelve named premises;
the twelfth, `MemoryPullTimestampHighBound`, is now *derived* from the produced side of the
capstone's own per-location Memory balance and no longer exists as a declaration.

| Declaration | File | Question it decides |
|---|---|---|
| `InitialBoundaryFacts` | `SP1Clean/Soundness/ProviderBindings.lean` | The eleven-field assumed boundary |
| `SemanticBoundaryBinding` | `SP1Clean/Soundness/ProviderBindings.lean` | How the boundary attaches to a witness |
| `ProgramProviderBound` | `SP1Clean/Soundness/ProviderBindings.lean` | Program-table content (assumed; §7.3 — needs C1) |
| `MemoryInitProviderBound` | `SP1Clean/Soundness/ProviderBindings.lean` | Memory-init content at the boundary |
| `MemoryInitProviderUnique` | `SP1Clean/Soundness/ProviderBindings.lean` | One init record per location — not derivable from balance |
| `MemoryFinalizeProviderUnique` | `SP1Clean/Soundness/ProviderBindings.lean` | One finalize pull per location — likewise |

Seven of the eleven follow from a configured initial state, a committed program, and a canonical
`ProverData` choice. Four need real construction: `programProvider`, `memoryProvider`, and the two
uniqueness fields. The uniqueness pair is the sharpest residual — Clean balance cannot force it,
upstream's mechanism is the MemoryGlobal strictly-increasing-address chain this ensemble omits, and
the premise is stated per `locOf` (8-byte cell) while that chain orders exact byte addresses. That
granularity gap is recorded on the definitions themselves.

## Whether the target is the real Sail model

| Declaration | File | Question it decides |
|---|---|---|
| `GuestProgram` | `SP1Clean/Model/Semantics/GuestProgram.lean` | What a "program" is, and its guards |
| `SailStep` | `SP1Clean/Model/Semantics/GuestProgram.lean` | One step of the real generated interpreter |
| `SailRetiresNormally` | `SP1Clean/Model/Semantics/GuestProgram.lean` | Excludes trap/illegal/wait exits by recording the official `Retire_Success` branch |
| `SailChain` | `SP1Clean/Model/Semantics/GuestProgram.lean` | A multi-step run |
| `SailConfigured` | `SP1Clean/Model/Semantics/GuestProgram.lean` | Which platform state is assumed (incl. the single RWX PMA region) |
| `SailCodeMemoryCompatible` | `SP1Clean/Model/Semantics/GuestProgram.lean` | The code/data separation contract — self-modifying code excluded by assumption |
| `SP1MachineModel` | `SP1Clean/Model/Machine/Execution.lean` | The clock model |
| `SP1MachineModel.UsesOrdinarySchedule` | `SP1Clean/Model/Machine/Execution.lean` | Which schedule the conclusion is quantified over |
| `decodedInROM` | `SP1Clean/Model/Semantics/Decode.lean` | The decode correspondence |
| `instrToProgramRow` | `SP1Clean/Model/Semantics/Decode.lean` | How a decoded instruction projects to a Program row |
| `Commit.progOf` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | How the program is bound to prover data |
| `Commit.CanonicalEncoding` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | The range/singleton conditions that make decoding canonical |
| `Commit.StatementFor` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | The committed-program statement |

## Faithfulness to Rust, and the transport

| Declaration | File | Question it decides |
|---|---|---|
| `ChipFaithful` | `SP1Clean/Faithful/ChipOracle.lean` | What "faithful to Rust" means |
| `ChipOracle` | `SP1Clean/Faithful/ChipOracle.lean` | The generated Rust side of the comparison |
| `FaithfulPropFor` | `SP1Clean/Faithful/SupportedMachine.lean` | That an anchor is bound to *its own* table's theorem |
| `CanonicalPreprocessedInventory` | `SP1Clean/Composition/PreprocessedProviders.lean` | Caller-supplied provider carriers + projected-key `Nodup` |
| `PreprocessedProviderContract` | `SP1Clean/Composition/PreprocessedProviders.lean` | Caller-supplied row-local provider semantics |
| `PreprocessedProviderRecountContract` | `SP1Clean/Composition/PreprocessedProviders.lean` | Coverage, nonpositivity, canonical capacity |
| `ExactNativeGlobalContract` | `SP1Clean/Composition/CoreArtifact.lean` | What the artifact still assumes globally |
| `CoreAIRRefinementObligations` | `SP1Clean/Soundness/CoreAIR.lean` | The 14-field exact-refinement bundle (`executionCase` open) |

## The completeness direction

| Declaration | File | Question it decides |
|---|---|---|
| `SupportedCoreTraceWitness` | `SP1Clean/Proofs/Completeness/Assembly.lean` | What a supplied trace is |
| `compileExecution` | `SP1Clean/Proofs/Completeness/ExecutionCompiler.lean` | The proof-independent chronological all-25 compiler |
| `nativeTrace` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The unique 53-table trace produced from a statement and execution |
| `NativeTraceReady` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The remaining named semantic/representation facts about that exact compiler output |
| `NativeStateRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The sole physical-row projection seam for State instruction accesses |
| `NativeMemoryRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The two physical-row projection seams for instruction and MemoryBump accesses |
| `NativeMemoryGenesis` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The field-free initial-memory fact, before any Clean provider representation |
| `NativeProgramRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The physical Program pulls' link to retained compiler decodes |
| `nativeTrace_stateAgreement` | `SP1Clean/Proofs/Completeness/NativeStateAgreement.lean` | State projection plus generated boundaries/bumps yields the complete State ledger |
| `nativeTrace_memoryLedgerPermHandoffChains` | `SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean` | Physical Memory tables regroup to the canonical per-location histories |
| `nativeTrace_memoryInitProviderBound` | `SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean` | Field-free Memory genesis grounds the generated init-provider rows |
| `nativeTrace_programProviderBound` | `SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean` | Retained decode agreement grounds the generated Program-provider rows |
| `NativeTraceReady.semanticBoundary` | `SP1Clean/Proofs/Completeness/NativeBoundaryAgreement.lean` | The derived Program/Memory provider facts joined with the exact semantic boundary |
| `SupportedCoreNativeAdmissibleExecutionRelation` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The honest semantic source on which the deterministic compiler is presently proved complete |
| `supported_core_native_functionalCompleteness` | `SP1Clean/Soundness/NativeCompleteness.lean` | The proof-independent semantic-execution-to-AIR witness map |
| `supported_core_native_complete` | `SP1Clean/Soundness/NativeCompleteness.lean` | Existential whole-ensemble completeness on the admissible image |
| `sp1Ensemble_statement_of_supported_execution` | `SP1Clean/Soundness/NativeCompleteness.lean` | The direct Clean `Ensemble.Statement` consequence |
| `anchorExecution_admissible` | `SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean` | A concrete boundary-only execution jointly inhabits every admissibility premise |
| `anchorExecution_yields_airWitness` | `SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean` | The functional capstone returns its literal compiled 53-table witness |
| `SupportedCoreGeneratedTraceRelation` | `SP1Clean/Soundness/AIRCompleteness.lean` | The lower generated-trace assembly boundary, kept distinct from semantic completeness |

Completeness now covers the deterministic compiler's full 53-table admissible image: all 25 instruction
families, refresh-aware StateBump/MemoryBump placement, canonical Byte/Range/Program closure, both
Memory boundary tables, the State verifier row, constraints, and all four channel balances.  It is
still narrower than the entire unbounded exact ordinary semantic relation. Its compiler domain needs
registry-wide event-validity, Memory-genesis, configured-state decode-stability, and interaction-
footprint theorems on the intended bounded source. A language-equality theorem additionally needs
soundness to target that same capacity-bounded relation. No abstract certificate or existential AIR
witness hides those facts, and no public-language equality is claimed.

## Outside this list

`EnsembleWitness.Constraints` and `BalancedChannels` decide what "the AIR is satisfied" means, but
they live upstream in Clean (`Clean/Air/FlatEnsemble.lean`, `Clean/Air/Balance.lean`) and are pinned
by the Clean dependency, not by this repository. The generated `Extracted/**Oracle**` column
structures, `asserts` and `interactions` lists are the Rust side of faithfulness; they are
auto-generated and gated by `update_extracted.py` plus the regeneration workflow, not audited by
hand. Both are named here so a reader knows they were considered and placed, not forgotten.
