#!/usr/bin/env python3
"""Generate the axiom-census probes: one `#print axioms` line per headline declaration.

Scans the SP1Clean tree for the released theorem set (chip soundness/completeness, Sail
bridges + `kind` registrations, faithfulness anchors, witness-conformance anchors, the
timed-grounding capstone layer, deterministic completeness agreement/non-vacuity headlines, and
the coverage guards), resolving each declaration's fully qualified name by tracking
`namespace`/`end` blocks. The probe is self-checking: a wrong FQN fails to elaborate, so a green
probe run certifies the census covers real declarations.

Two probe files are emitted, one per library, so each elaborates against exactly the
oleans its build target produces (the CI `audit` job builds only `SP1Clean`; the `test`
job additionally builds `SP1CleanTest` via `lake test`):

- `scripts/axiom_probe.lean` — the main library (`import SP1Clean` only);
- `scripts/axiom_probe_test.lean` — the `SP1CleanTest` conformance and executable
  audit anchors (the native_decide quarantine), importing each test module explicitly.

Usage: `python3 scripts/gen_axiom_probe.py` (from the repo root); then
`lake env lean scripts/axiom_probe.lean` / `... scripts/axiom_probe_test.lean`
(see `scripts/run_audit.sh`).
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_MAIN = ROOT / "scripts" / "axiom_probe.lean"
OUT_TEST = ROOT / "scripts" / "axiom_probe_test.lean"

# Release/audit headlines are deliberately one target per declaration.  Do not fold these into
# an alternation: target validation is per tuple, so a grouped regex would let one surviving theorem
# hide a renamed or deleted sibling.  This list is the fail-closed inventory for the source-backed
# preprocessing boundary, exact integer-balance transport, the native artifact, and deterministic
# semantic-execution completeness.
# Entries may name theorem or definition headlines; in particular functional-completeness maps are
# deliberately proof-independent definitions whose proof fields are retained by the structure.
EXACT_REQUIRED_THEOREMS = [
    # Source-backed canonical preprocessing inventory and its literal Clean ledger.
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "inventoryPreprocessedKeys_eq_inventoryRows"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "inventoryPreprocessedKeys_nodup"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalByteRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalRangeRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalProgramRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "extractedPreprocessedProviderTables_constraints"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "extractedPreprocessedProviderTables_cleanAccesses"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "skeleton_append_recountedPreprocessedProviderAccesses_balanced"),
    # Boundary/system providers and the exact provider segment.
    ("SP1Clean/Composition/MemoryBoundary.lean", "memoryGlobalInitMultiplicity_bool"),
    ("SP1Clean/Composition/MemoryBoundary.lean", "memoryGlobalFinalizeMultiplicity_bool"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "memoryBoundaryProviderContract_of_relation"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "extractedMemoryBoundaryTables_constraints"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "extractedMemoryBoundaryTables_activeAccesses"),
    ("SP1Clean/Composition/SystemTables.lean", "extractedBumpTables_constraints"),
    ("SP1Clean/Composition/SystemTables.lean", "extractedBumpTables_accesses"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_components"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_constraints"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTableBundle_constraints"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_cleanAccesses"),
    # Complete native table assembly, literal-ledger recount, and public semantic capstones.
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_init_u8Pair"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_final_u8Pair"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_limbBounds"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTables_components"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTableBundle_components"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTables_constraints"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeEnsembleWitness_verifierTable"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeEnsembleWitness_constraints"),
    ("SP1Clean/Composition/CoreEnsemble.lean",
     "exactNativeAllCleanAccesses_eq_interactions"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeAllCleanAccesses_perm"),
    ("SP1Clean/Composition/CoreEnsemble.lean",
     "exactNativeAllCleanAccesses_preprocessedBalance"),
    ("SP1Clean/Composition/CoreArtifact.lean",
     "exactNativeEnsembleWitness_preprocessedIntegerBalance"),
    ("SP1Clean/Composition/CoreArtifact.lean", "exactNativeEnsembleWitness_balancedChannels"),
    ("SP1Clean/Composition/CoreArtifact.lean",
     "exactNativeArtifact_supportedCoreNativeRelation"),
    ("SP1Clean/Composition/CoreArtifact.lean", "exactNativeArtifact_localExecution"),
    # The representation and semantic agreement seams used by the deterministic native compiler.
    # Keep these exact (rather than one alternation per file): deleting one side of an agreement
    # layer must fail generation even when a sibling theorem survives.
    ("SP1Clean/Proofs/Completeness/NativeStateAgreement.lean",
     "nativeTrace_stateAgreement"),
    ("SP1Clean/Proofs/Completeness/NativeStateAgreement.lean",
     "NativeTraceReady.stateLedgerPerm"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryLedgerPermHandoffChains"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "NativeTraceReady.memoryLedgerPerm"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryInitProviderUnique"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryFinalizeProviderUnique"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryInitProviderBound"),
    ("SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean",
     "nativeProgramKey_decodedInROM"),
    ("SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean",
     "nativeTrace_programProviderBound"),
    ("SP1Clean/Proofs/Completeness/NativeBoundaryAgreement.lean",
     "NativeTraceReady.semanticBoundary"),
    # Deterministic ordinary-execution -> native ensemble completeness.
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "supported_core_native_functionalCompleteness"),
    ("SP1Clean/Soundness/NativeCompleteness.lean", "supported_core_native_complete"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "sp1Ensemble_statement_of_supported_execution"),
    # Executable joint-premise regression for the exact admissible source and both capstones.
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_nativeTraceReady"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_admissible"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_yields_airWitness"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_yields_ensembleStatement"),
]

EXACT_REQUIRED_TARGETS = [
    (path, rf"(?:theorem|def)\s+({re.escape(name)})\b")
    for path, name in EXACT_REQUIRED_THEOREMS
]

# (glob, declaration-name regex) → collect matching theorems/defs with their namespace.
TARGETS = [
    ("SP1Clean/Proofs/Chips/*/Formal.lean",
     # Probe the bundled circuit as well as its named proof fields.  In particular, a deferred
     # channel-law field lives only inside `circuit`, and every deferred completeness proof is
     # retained transitively by that structure even when a soundness consumer never projects it.
     r"(?:theorem|def)\s+(soundness|completeness|contractSoundness|evidenceSoundness|circuit)\b"),
    # Branch isolates its heavy soundness/completeness proofs in `Core.lean`; `Formal.circuit`
    # retains both, but direct probes keep the audit ledger readable.
    ("SP1Clean/Proofs/Chips/BranchChip/Core.lean",
     r"theorem\s+(soundness|completeness)\b"),
    # DivRem keeps its heavyweight completeness driver outside `Formal.lean`; without this explicit
    # target the textual admission gate saw the `stop`, but the axiom census silently skipped the
    # declaration itself.
    ("SP1Clean/Proofs/Chips/DivRemChip/Completeness/Driver.lean",
     r"theorem\s+(completeness)\b"),
    # DivRem's isolated, circuit-independent contract and evidence layer is a first-class audit
    # surface: probe every named theorem rather than only the admitted whole-chip extraction seam.
    # Dotted capture: `theorem Unsigned64Evidence.total` must probe the theorem, not collapse to
    # the (already-probed) structure name at the first `.`.
    ("SP1Clean/FormalModel/Contracts/DivRem.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/DivRemChip/Cases.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"theorem\s+(correct_\w+|\w*reaches_sail\w*)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"def\s+(kind)\b"),
    ("SP1Clean/Faithful/*.lean", r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/DivRemChip/Exact.lean",
     r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/SupportedMachine.lean",
     r"(?:theorem|def)\s+(supportedChipFaithfulness\w*|"
     r"instructionOracleMainWidth|instructionOracleMainWidth_isSome_iff|"
     r"supportedInstructionMainWidths)\b"),
    # W6: the transport layer — the generic per-table transport and all three public theorem
    # families for each of its twenty-five instantiations, plus the aggregate identity that makes
    # the transported tables the ensemble's own.
    # These are the declarations that put `Faithful/` inside a live import closure.
    # buildRow_input_get / eval_var_buildRow_input_get moved down to Model/CleanLedger.lean in
    # 2026-08 (pure Clean Component/ProvableType vocabulary; the completeness layer needs them too).
    ("SP1Clean/Model/CleanLedger.lean",
     r"theorem\s+(buildRow_input_get|eval_var_buildRow_input_get)\b"),
    ("SP1Clean/Composition/Table.lean",
     r"theorem\s+(signedVal_eq_zero_iff|transportTable_constraints|"
     r"transportTable_accesses_perm|transportTable_spec)\b"),
    ("SP1Clean/Composition/Chips.lean",
     r"theorem\s+(\w+Chip_transportTable_(?:constraints|accesses|spec))\b"),
    ("SP1Clean/Composition/Ensemble.lean",
     r"theorem\s+(transported_map_component|transportedInstructionActiveAccesses_perm|"
     r"transported_constraints)\b"),
    ("SP1Clean/Composition/Extracted.lean",
     r"theorem\s+(extractedInstructionRows_valid|extracted_instructionTables_constraints)\b"),
    ("SP1Clean/Composition/Balance.lean",
     r"theorem\s+(signedSum_eq_sent_sub_received|signedSum_eq_zero)\b"),
    *EXACT_REQUIRED_TARGETS,
    ("SP1Clean/Soundness/CoreAIRSyscallFree.lean",
     r"theorem\s+(publicCommitOperand|deferredCommitOperand|publicCommitSetsFlag|"
     r"deferredCommitSetsFlag|syscallTranscript)\b"),
    # The real-row satisfiability battery: every named anchor (28 per-chip rows + the Spec-level
    # companions + the nonempty-assert-list guard) is census-visible so its native_decide trust is
    # disclosed per-declaration like the conformance anchors.
    ("SP1CleanTest/NonVacuityReal.lean", r"theorem\s+(\w+)\b"),
    # Independent audit regressions freeze the full native constraint checks and exact evaluated
    # bus footprints.  The active-trace declarations additionally keep the generated one-row trace,
    # its particular native witness, and the official-Sail consequence census-visible end to end.
    ("SP1CleanTest/Audit/*.lean",
     r"theorem\s+(constraints_hold|interactions_exact|program_projection|"
     r"bytePaddingTable_constraints|bytePaddingTable_busNeutral|"
     r"byteAggregateTable_constraints|byteAggregateTable_preservesMultiplicity|"
     r"rangeAggregateTable_constraints|rangeAggregateTable_preservesMultiplicity|"
     r"programAggregateTable_constraints|programAggregateTable_preservesMultiplicity|"
     r"byteAggregateTable_accesses|byteAggregateLedger_accesses|"
     r"byteAggregate_signedVal|byteAggregateLedger_integerBalanced|"
     r"byteAggregateLedger_balancedInteractions|"
     r"memoryInitTable_constraints|memoryInitTable_booleanBranches|"
     r"memoryFinalizeTable_constraints|memoryFinalizeTable_booleanBranches|"
     r"supportedCoreNativeRelation_nonvacuous|traceGeneratableRelation_nonvacuous|"
     r"anchorTrace_yields_airWitness|activeTrace_traceGeneratable|activeTrace_nativeRelation|"
     r"verifierBytePulls_asymmetricClockOrder|"
     r"active_instruction_count|active_decoded_instruction_row_count|"
     r"active_real_decoded_instruction_row_count|"
     r"activeTrace_yields_airWitness|activeTrace_yields_localExecution|"
     r"activeTrace_suppliesDemand|activeTrace_stateHandoff|activeTrace_memoryHandoff|"
     r"activePaddedTrace_stateHandoff|activePaddedTrace_stateHandoff_raw_false)\b"),
    # The W4 completeness layer's provider/ledger half: the built provider and verifier tables'
    # constraint theorems, and the generic push/pull balance bridge the W5 assembly consumes.
    ("SP1Clean/Proofs/Completeness/Providers.lean",
     r"(?:theorem|lemma)\s+(traceTable_constraints|"
     r"ByteEntry\.signedVal_multiplicity|RangeEntry\.signedVal_multiplicity|"
     r"RomEntry\.signedVal_multiplicity)\b"),
    ("SP1Clean/Proofs/Completeness/Ledger.lean",
     r"theorem\s+(balancedInteractions_of_signed_perm|balancedInteractions_of_flatMap_perm|"
     r"balanceOf_eq_pushed_sub_pulled)\b"),
    # The provider closure. The ledger-level balance theorem and the key-selection lemmas that make
    # its two side conditions structural rather than caller-supplied; plus the trace-level
    # instantiation and the two conservativeness results that pin the closure out of State/Memory.
    # The ledger-level half of the provider closure moved to Model/InteractionBus.lean in 2026-08
    # (its namespace already said so); the trace-level half stayed in Closure.lean.
    # Tier 1 of the provider closure: what one built provider row emits, in Clean orientation.
    ("SP1Clean/Proofs/Completeness/ProviderInteractions.lean",
     r"theorem\s+(interactions_eq_interactionsWith_of_onlyChannel|"
     r"u8Range_interactionsWith_byte|u8Range_buildRow_cleanAccesses|"
     r"msb_buildRow_result|msb_buildRow_cleanAccesses|"
     r"and_buildRow_result_val|and_buildRow_cleanAccesses|"
     r"or_buildRow_cleanAccesses|xor_buildRow_cleanAccesses|"
     r"ltu_buildRow_cleanAccesses|range_buildRow_cleanAccesses|"
     r"program_buildRow_cleanAccesses)\b"),
    # Tier 2: a whole provider table's ledger is exactly its occurrence list.
    # Tier 3: the provider lists a shard's demand determines, and the balance that follows.
    ("SP1Clean/Proofs/Completeness/ClosureRealization.lean",
     r"theorem\s+(family_ledger_eq|family_multiplicitySum|program_round|"
     r"closureRange_contribution|providerLedger_multiplicitySum|"
     r"fullLedger_multiplicitySum|byteProgram_balanced|"
     r"fullLedger_multiplicitySum_channel|channelLedger_isConsistentBalanced|"
     r"channelLedger_isConsistentBalanced_of_handoff)\b"),
    # The ensemble's own channel discipline, which the orientation bridge rests on.
    ("SP1Clean/Soundness/EnsembleChannels.lean",
     r"theorem\s+(sp1Tables_channels_subset|sp1ProviderTables_channels_subset|"
     r"sp1Ensemble_allTables_channels_subset|channel_eq_of_name_eq)\b"),
    # Phase 3: the clock bridge, the generator's shadow bookkeeping, and the ALU fold.
    ("SP1Clean/FormalModel/TraceGen/ClockBridge.lean",
     r"theorem\s+(ordinarySchedule_duration_eq|accessOffsets_ordered|"
     r"clockAt_ordinary_eq|clockAt_ordinary_mod)\b"),
    ("SP1Clean/FormalModel/TraceGen/GenState.lean",
     r"theorem\s+(initial_bounded|prevTs_lt|stepRType_bounded)\b"),
    ("SP1Clean/FormalModel/TraceGen/AluGenerator.lean",
     r"theorem\s+(aluEvents_wellFormed|witnessStep_wellFormed|"
     r"witnessEvents_wellFormed)\b"),
    ("SP1Clean/FormalModel/TraceGen/SailAlu.lean",
     r"theorem\s+(aluStepOfState_wellFormed|aluStepOfState_isSome|"
     r"aluStepsFrom_wellFormed|aluStepsFrom_length_le)\b"),
    ("SP1Clean/Proofs/Completeness/AluGeneration.lean",
     r"theorem\s+(aluEvents_addTable_constraints|aluEvents_addTable_guarantees|"
     r"aluEvents_subTable_constraints|sailRun_addTable_constraints|"
     r"sailRun_subTable_constraints|sailRun_rows_le)\b"),
    # Phase 2: the two system tables' rows are built from crossings, not supplied.
    ("SP1Clean/FormalModel/TraceGen/Bump.lean",
     r"theorem\s+(stateBump_spec|memoryBump_spec|stateBumpTraceInputs_spec|"
     r"memoryBumpTraceInputs_spec|stateBumpEvent_wellFormed_witness|"
     r"memoryBumpEvent_wellFormed_witness)\b"),
    ("SP1Clean/Proofs/Completeness/ProviderTables.lean",
     r"theorem\s+(u8Range_traceTable_cleanAccesses|msb_traceTable_cleanAccesses|"
     r"and_traceTable_cleanAccesses|or_traceTable_cleanAccesses|"
     r"xor_traceTable_cleanAccesses|ltu_traceTable_cleanAccesses|"
     r"range_traceTable_cleanAccesses|program_traceTable_cleanAccesses)\b"),
    # A1: a built instruction table's State ledger — registry-wide, no case split.
    ("SP1Clean/Proofs/Completeness/ChipLedger.lean",
     r"theorem\s+(supportedChip_table_mem_allTables|tableStateLedger_eq_nil|"
     r"tableStateLedger_eq_of_component|stateLedger_eq_flatMap|"
     r"busLedger_eq_channelLedger|stateLedger_eq_channelLedger|"
     r"memoryLedger_eq_channelLedger|active_stateLedger_eq|"
     r"stateLedger_perm_handoff|memoryLedger_eq|memoryLedger_perm_handoff|"
     r"stateLedger_perm_handoff_singleChain|hnonpos_of_consumersOnlyPull)\b"),
    ("SP1Clean/Soundness/EnsembleChannels.lean",
     r"theorem\s+(channel_eq_of_kindOf_eq|interactions_channel_eq_of_kindOf)\b"),
    # A0: the ledger decomposition a per-chip sweep peels with.
    ("SP1Clean/Model/CleanLedger.lean",
     r"theorem\s+(tablesCleanAccesses_cons|tableCleanAccesses_buildHinted|"
     r"tableCleanAccesses_filterKind)\b"),
    ("SP1Clean/Model/InteractionBus.lean",
     r"theorem\s+(multiplicitySum_append_closingAccesses|multiplicitySum_append_closing|"
     r"multiplicitySum_closingAccesses|mem_closingKeys_of_multiplicitySum_ne_zero|"
     r"multiplicitySum_closingAccesses_of_not_select|multiplicitySum_handoff|"
     r"multiplicitySum_of_perm_handoff|isConsistentBalanced_of_perm_handoff|"
     r"multiplicitySum_filterKind|chainLedger_perm_handoff|"
     r"multiplicitySum_chainLedger|active_append|active_flatMap_gatedPair|"
     r"handoff_append|multiChainLedger_perm_handoff|multiplicitySum_nonpos)\b"),
    ("SP1Clean/Proofs/Completeness/Closure.lean",
     r"theorem\s+(closingAccesses_balances|closingAccesses_not_preprocessed|"
     r"closingAccesses_state|closingAccesses_memory|"
     r"preprocessedProviderTables_eq|preprocessedProviderLedger_eq)\b"),
    # W5: the machine-level assembly and its completeness capstone. The assembly's constraint
    # theorem is the join of all 54 tables' own theorems (53 ensemble tables plus verifier), so a
    # regression anywhere in the
    # completeness layer surfaces here first.
    ("SP1Clean/Proofs/Completeness/Assembly.lean",
     r"theorem\s+(witness_constraints|tables_map_component)\b"),
    ("SP1Clean/Soundness/AIRCompleteness.lean",
     r"(?:theorem|def)\s+(supported_core_generated_trace_functionalCompleteness|"
     r"supported_core_generated_trace_complete|"
     r"sp1Ensemble_statement_of_generated_trace|"
     r"balancedOn_of_signed_perm|witness_balancedChannels|balancedOn_of_closure|"
     r"balancedOn_of_handoff|balanced_of_closure_and_handoff|"
     r"sp1Ensemble_statement_of_structural_balance)\b"),
    # The deterministic semantic-execution -> native-trace compiler and the final converse
    # capstone.  Keep the trace-map readiness lemmas separate from the stratum-10 channel join so
    # the census mirrors the architectural boundary.
    ("SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean",
     r"theorem\s+(nativeBaseTraceOfCompiled_wellFormed|"
     r"nativeInitialClock_encodable)\b"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     r"(?:theorem|def)\s+(supported_core_native_functionalCompleteness|"
     r"supported_core_native_complete|"
     r"sp1Ensemble_statement_of_supported_execution)\b"),
    # The W4 completeness layer: each chip's trace-table constraint/guarantee theorems and its
    # event-to-prover-assumptions discharge. Probed from the pilot onward so the rollout cannot
    # silently introduce a compiler-trusted or deferred step.
    ("SP1Clean/Proofs/Chips/*/Complete.lean",
     r"theorem\s+(traceTable_constraints|traceTable_guarantees|proverAssumptions_of_event)\b"),
    # The abstract walk/trail core (live — used by AIR + RankedGrounding).
    ("SP1Clean/Soundness/Walk.lean", r"theorem\s+(exists_trail)\b"),
    # The W3 generic engines: the goodness filter + self-loop cancellation (StateBump) and the
    # refresh elimination (MemoryBump). Keystones probed like Walk's `exists_trail`.
    ("SP1Clean/Soundness/GoodnessFilter.lean",
     r"theorem\s+(endpointBalanced_of_cancel_loops|good_of_endpointBalanced)\b"),
    ("SP1Clean/Soundness/RefreshElimination.lean", r"theorem\s+(eliminate)\b"),
    # The field⇒ℤ balance bridge (relocated in W11 Phase 5).
    ("SP1Clean/Model/BalanceBridge.lean",
     r"theorem\s+(isConsistentBalanced_of_intCast_zero|intCast_multiplicitySum_map_toAccess|"
     r"intCast_multiplicitySum_map_toAccess_eq_balanceOf|"
     r"isConsistentBalanced_of_balancedInteractions|"
     r"balancedInteractions_of_isConsistentBalanced)\b"),
    ("SP1Clean/Model/InteractionProjection.lean",
     r"lemma\s+(signedVal_natCast_of_twice_le)\b"),
    ("SP1Clean/Model/InteractionProjection.lean",
     r"theorem\s+(toAccess_pulledIfValue|toAccess_pushedIfValue)\b"),
    ("SP1Clean/Soundness/SP1Ensemble.lean",
     r"(?:theorem|def)\s+((?:sp1|balanced)\w*\??)(?=\s|\()"),
    ("SP1Clean/Soundness/AIR.lean",
     r"theorem\s+(statePullAlign8_of_stateWalk|"
     r"supportedCore_groundingObligations_of_constraints|"
     r"supportedCore_orderedRows_dynamic_of_obligations|"
     r"supportedCore_orderedRows_dynamic|supported_core_witness_grounding|"
     r"supported_core_native_grounding|supported_core_native_sound|"
     r"supported_core_native_ordinary_sound)\b"),
    # Exact v6.4.0 table/profile guards and the public ArkLib-facing Core AIR capstone.  These are
    # release headlines: adding a new capstone file must not silently leave it outside the census.
    ("SP1Clean/FormalModel/CoreProfile.lean",
     r"theorem\s+(checkedIn_semanticRevision|coreCluster_matchesExtracted|"
     r"coreClusterShapes_matchExtracted|memoryBoundaryCluster_matchesExtracted|"
     r"memoryBoundaryClusterShapes_matchExtracted|publicValuesWidth_matchesExtracted)\b"),
    # The opcode-alphabet cross-check: the hand-maintained `Model/Opcode.lean` mirror against the
    # extracted `Opcode` enum discriminant table (trust-gap F8 closure).
    ("SP1Clean/FormalModel/OpcodeTable.lean",
     r"theorem\s+(opcodeTable_matchesExtracted)\b"),
    ("SP1Clean/Faithful/CoreAIR.lean", r"theorem\s+(system_isCurrent)\b"),
    ("SP1Clean/Soundness/CoreAIR.lean",
     r"(?:theorem|def)\s+(sp1_air_refinement_of_obligations|sp1_air_sound_of_obligations)\b"),
    # The base execution relation deliberately excludes COMMIT-row existence. Probe the persistence,
    # terminal-digest, and optional program-contract theorems separately so a future output theorem
    # cannot hide an admission behind wrapper or verifying-key terminology.
    ("SP1Clean/FormalModel/Contracts/PublicValues.lean",
     r"theorem\s+(SP1PublicValues\.committedDigest_eq_last_of_flag)\b"),
    ("SP1Clean/FormalModel/Execution.lean",
     r"theorem\s+(finalCommitRowsMatch_of_layout|finalCommitRowsMatch_of_execution|"
     r"completeCommitDigestMatches_of_coveredExecution|commitCovered_of_standardWrapper|"
     r"commitCovered_of_commitCoveringVerifyingKey)\b"),
    ("SP1Clean/Soundness/TimedGrounding.lean", r"theorem\s+(walk)\b"),
    ("SP1Clean/Soundness/FinishedChannels.lean", r"theorem\s+(sp1_finishedChannel_guarantees)\b"),
    ("SP1Clean/Soundness/ChipRegistry.lean", r"(?:theorem|def)\s+(allChipKinds\w*)\b"),
    ("SP1Clean/Soundness/Coverage.lean",
     r"theorem\s+(coverage_kinds_eq_registry|coverage_length|covered_iff_routed|"
     r"wired_subset_reachable|reachable_subset_wired|routeOf_reaches_sail)\b"),
    ("SP1Clean/Soundness/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|sailConfigured_nonempty)\b"),
    # C1/Move-2: the decode projection, guards, ∃I∀s `decodedInROM`, its accessor, the 16 collapsed
    # `decodes<T>` producers, and the `instrToProgramRow(_inv)_*` inversions all live here (Model layer).
    ("SP1Clean/Model/Semantics/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|decodes[A-Z]\w*|instrToProgramRow\w*|"
     r"mulOpCanonical|loadWidthOK|storeWidthOK|mulOp_canonical_inj|"
     r"loadOpcode_\w+|storeOpcode_\w+)\b"),
    ("SP1Clean/Model/SailDecode.lean",
     r"theorem\s+(run_bind_ok_\w+|decode_\w+)\b"),
    ("SP1Clean/FormalModel/Trace/Witness.lean",
     r"(?:theorem|lemma)\s+(isInitialState_nonvacuous|cfgState_[\w?]+|mem_fullRegs)\b"),
]

NS_RE = re.compile(r"^namespace\s+([\w.]+)")
END_RE = re.compile(r"^end\b\s*([\w.]+)?")
SECTION_RE = re.compile(r"^section\b\s*([\w.]+)?")


def fqns_in(path: Path, decl_re: re.Pattern) -> list[str]:
    stack: list[tuple[str, str]] = []  # (kind, name) — kind ∈ {ns, sec}
    out = []
    comment_depth = 0
    for line in path.read_text().splitlines():
        if comment_depth > 0:
            comment_depth += line.count("/-") - line.count("-/")
            continue
        opens = line.count("/-") - line.count("-/")
        if opens > 0:
            comment_depth = opens
            continue
        if m := NS_RE.match(line):
            for part in m.group(1).split("."):
                stack.append(("ns", part))
        elif m := SECTION_RE.match(line):
            stack.append(("sec", m.group(1) or ""))
        elif m := END_RE.match(line):
            parts = (m.group(1) or "").split(".") if m.group(1) else [""]
            for part in reversed(parts):
                if stack and (stack[-1][1] == part or (stack[-1][0] == "sec" and not part)):
                    stack.pop()
        elif m := decl_re.search(line):
            stripped = line.lstrip()
            if not stripped.startswith("--") and not stripped.startswith("private "):
                ns = ".".join(p for k, p in stack if k == "ns")
                out.append(f"{ns}.{m.group(1)}" if ns else m.group(1))
    return out


def main() -> None:
    main_fqns: list[str] = []
    test_fqns: list[str] = []
    test_imports: list[str] = []  # `SP1CleanTest.*` modules, imported explicitly in the test probe
    seen_imports: set[str] = set()
    missing_targets: list[tuple[str, str]] = []
    for glob, pattern in TARGETS:
        decl_re = re.compile(pattern)
        target_count = 0
        for path in sorted(ROOT.glob(glob)):
            found = fqns_in(path, decl_re)
            if not found:
                continue
            target_count += len(found)
            # `import SP1Clean` (the umbrella) covers every main-library declaration, but NOT the
            # `SP1CleanTest` conformance anchors (that test library is not imported by the umbrella —
            # it is the native_decide quarantine). Those go to the separate test probe, importing
            # each module explicitly so its FQNs resolve there.
            rel = path.relative_to(ROOT)
            if rel.parts[0] != "SP1Clean":
                test_fqns.extend(found)
                mod = ".".join(rel.with_suffix("").parts)
                if mod not in seen_imports:
                    seen_imports.add(mod)
                    test_imports.append(mod)
            else:
                main_fqns.extend(found)
        if target_count == 0:
            missing_targets.append((glob, pattern))

    if missing_targets:
        print("FAIL: axiom-census target(s) matched no declarations:")
        for glob, pattern in missing_targets:
            print(f"  {glob}: {pattern}")
        raise SystemExit(1)

    def dedupe(fqns: list[str]) -> list[str]:
        seen, ordered = set(), []
        for f in fqns:
            if f not in seen:
                seen.add(f)
                ordered.append(f)
        return ordered

    main_ordered = dedupe(main_fqns)
    lines = ["import SP1Clean",
             "",
             "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
             "Main-library census probe (elaborates against the `SP1Clean` oleans only).",
             "Run via `lake env lean scripts/axiom_probe.lean` (see `scripts/run_audit.sh`). -/",
             ""]
    lines += [f"#print axioms {f}" for f in main_ordered]
    OUT_MAIN.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT_MAIN.relative_to(ROOT)} with {len(main_ordered)} probes")

    test_ordered = dedupe(test_fqns)
    lines = [f"import {m}" for m in test_imports]
    lines += ["",
              "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
              "Test-library census probe (the `SP1CleanTest` conformance anchors; requires the",
              "test-library oleans — run `lake test` first).",
              "Run via `lake env lean scripts/axiom_probe_test.lean` (see `scripts/run_audit.sh`). -/",
              ""]
    lines += [f"#print axioms {f}" for f in test_ordered]
    OUT_TEST.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT_TEST.relative_to(ROOT)} with {len(test_ordered)} probes")


if __name__ == "__main__":
    main()
