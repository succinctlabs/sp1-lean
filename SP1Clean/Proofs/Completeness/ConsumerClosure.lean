import SP1Clean.Proofs.Completeness.ChipLedger
import SP1Clean.Proofs.Completeness.CanonicalClosureWellFormed
import SP1Clean.Soundness.TypedProgram

/-!
# Closing the consumer-side provider obligations

The canonical Byte/Range/Program closure is computed from the literal evaluated Clean ledger.
This file discharges the Program-polarity half of its `ConsumersOnlyPull` premise uniformly from
generated-trace well-formedness.  The proof does not introduce a symbolic interaction shadow: it
filters `tableCleanAccesses`, identifies that filter with the typed view of the same evaluated
interactions, and then applies the registry-wide Program emission theorem.

Byte polarity remains an explicit, Byte-only premise.  Clean's channel bookkeeping does not record
interaction polarity, and the repository does not yet have a registry-wide Byte emission shape
analogous to `supportedChip_programEmissionShape`.  Naming just that residual fact avoids making a
caller resupply the already-derived Program half.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table)
open SP1Clean.Channels (programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance consumerClosureFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-- Filtering the literal Clean ledgers of a table list to one ensemble channel is exactly the
erasure of the typed view of those same evaluated interactions. -/
theorem tablesCleanAccesses_filterKind_eq_typed {Message : TypeMap} [ProvableType Message]
    (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (channel : Channel (ZMod p) Message)
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (hchannel : channel.toRaw ∈ (sp1Ensemble (p := p)).channels)
    (hcomponents : ∀ table ∈ tables,
      table.component ∈ (sp1Ensemble (p := p)).tables) :
    (tablesCleanAccesses tables data).filter (fun access => access.1 = K) =
      (tables.flatMap (typedTableInteractionsWith · data channel)).map
        (Interaction.toAccess ∘ TypedInteraction.raw) := by
  simp only [tablesCleanAccesses, List.filter_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun table tableMem => ?_
  rw [tableCleanAccesses_filterKind table data channel.toRaw K hkind
    (fun interaction interactionMem interactionKind =>
      interactions_channel_eq_of_kindOf table data (hcomponents table tableMem) channel.toRaw
        hchannel interaction interactionMem
        (interactionKind.trans hkind.symm))]
  rw [← typedTableInteractionsWith_raw]
  simp only [List.map_map]

/-- The skeleton contains only physical tables from the assembled witness. -/
theorem skeletonTable_component_mem (table : Table (ZMod p))
    (tableMem : table ∈ trace.skeletonTables) :
    table.component ∈ (sp1Ensemble (p := p)).tables := by
  apply Air.Flat.EnsembleWitness.mem_component_of_mem (witness := trace.witness)
  rw [trace.witness_tables]
  rw [skeletonTables, List.mem_append] at tableMem
  exact tableMem.elim List.mem_of_mem_take List.mem_of_mem_drop

/-- The memory-initialization provider does not name the Program channel. -/
theorem memoryInitProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryInit) trace.data programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉ [Channels.memoryChannel.toRaw]
  simp [Channels.programChannel_eq_memoryChannel_false]

/-- The memory-finalization provider does not name the Program channel. -/
theorem memoryFinalizeProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryFinalize) trace.data programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉ [Channels.memoryChannel.toRaw]
  simp [Channels.programChannel_eq_memoryChannel_false]

/-- The memory-bump provider does not name the Program channel. -/
theorem memoryBumpProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryBump) trace.data programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉
    [Channels.byteChannel.toRaw, Channels.memoryChannel.toRaw,
      Channels.memoryChannel.toRaw]
  simp [Channels.programChannel_eq_byteChannel_false,
    Channels.programChannel_eq_memoryChannel_false]

/-- The state-bump provider does not name the Program channel. -/
theorem stateBumpProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .stateBump) trace.data programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉
    [Channels.byteChannel.toRaw, Channels.stateChannel.toRaw]
  simp [Channels.programChannel_eq_byteChannel_false,
    Channels.programChannel_eq_stateChannel_false]

/-- **The compiler's `SyscallInstrs` table has no rows**, so it is silent on every channel.
`syscallInstrsTraceInputs` is `[]` by construction (`List Empty` in, empty list out), which is a
property of *this compiler's trace* rather than of the chip — the chip genuinely speaks on seven
buses. This is precisely the fact that stops holding when the compiler learns to emit syscall rows,
and it is why the syscall table can join the ensemble before the compiler can fill it. -/
theorem syscallInstrsInteractions_eq_nil {Message : TypeMap} [ProvableType Message]
    (channel : Channel (ZMod p) Message) :
    typedTableInteractionsWith (trace.providerTableFor .syscallInstrs) trace.data channel = [] := by
  rw [typedTableInteractionsWith,
    show (trace.providerTableFor (p := p) .syscallInstrs).table = [] from
      SyscallInstrsChip.traceTable_table _ _ _]
  rfl

/-- The non-preprocessed provider suffix's Program interactions are exactly the halt table's
gated ECALL fetch pulls (the four Memory/State system tables are Program-silent). -/
theorem providerSuffixProgramInteractions_eq :
    (trace.providerTables.drop preprocessedProviderTableCount).flatMap
      (typedTableInteractionsWith · trace.data programChannel) =
    typedTableInteractionsWith (trace.providerTableFor .halt) trace.data programChannel := by
  rw [providerTables_drop_preprocessed]
  simp only [List.flatMap_cons, List.flatMap_nil,
    trace.memoryInitProgramInteractions_eq_nil,
    trace.memoryFinalizeProgramInteractions_eq_nil,
    trace.memoryBumpProgramInteractions_eq_nil, trace.syscallInstrsInteractions_eq_nil,
    trace.stateBumpProgramInteractions_eq_nil, List.nil_append, List.append_nil]

/-- The actual public verifier has no Program access, independently of physical provider rows. -/
theorem verifierProgramLedger_eq_nil :
    trace.verifierLedger.filter (fun access => access.1 = InteractionKind.Program) = [] := by
  classical
  apply List.filter_eq_nil_iff.mpr
  intro access member selected
  obtain ⟨interaction, emitted, rfl⟩ := List.mem_map.mp member
  have declared : interaction.channel ∈ (sp1Ensemble (p := p)).channels := by
    obtain ⟨abstract, abstractMem, rfl⟩ := List.mem_map.mp emitted
    exact sp1Ensemble_verifier_channels_subset (List.mem_map.mpr ⟨abstract, abstractMem, rfl⟩)
  have kind : kindOf interaction.channel.name = InteractionKind.Program :=
    of_decide_eq_true selected
  have same : interaction.channel = programChannel.toRaw :=
    channel_eq_of_kindOf_eq declared (by simp [sp1Ensemble_channels]) kind
  have silent := congrArg (List.map TypedInteraction.raw)
    (witness_verifierProgramInteractions_eq_nil trace.witness)
  simp only [typedInteractionValuesWith_raw, List.map_nil] at silent
  have selectedMem : interaction ∈ (sp1Ensemble (p := p)).verifierOperations.interactionValuesWith
      programChannel.toRaw (Environment.fromInput trace.witness.publicInput trace.witness.data) := by
    rw [Operations.interactionValuesWith_eq_filter]
    exact List.mem_filter.mpr ⟨emitted, by simp only [same, decide_true]⟩
  rw [silent] at selectedMem
  exact List.not_mem_nil selectedMem

/-- Generated-trace well-formedness forces every Program access in the provider-free skeleton to
be disabled or a unit pull, hence to have nonpositive centered multiplicity. -/
theorem skeleton_program_mult_nonpos (wf : trace.WellFormed) {access : LookupAccess}
    (accessMem : access ∈ trace.skeletonLedger)
    (program : (LookupAccessList.keyOf access).1 = InteractionKind.Program) :
    LookupAccessList.multOf access ≤ 0 := by
  have constraints := trace.witness_constraints wf
  have filteredMem : access ∈
      trace.skeletonLedger.filter (fun item => item.1 = InteractionKind.Program) :=
    List.mem_filter.mpr ⟨accessMem, by simpa only [LookupAccessList.keyOf, decide_eq_true_eq]
      using program⟩
  rw [skeletonLedger, List.filter_append, trace.verifierProgramLedger_eq_nil, List.nil_append,
    tablesCleanAccesses_filterKind_eq_typed trace.skeletonTables trace.data programChannel
      InteractionKind.Program rfl (by simp [sp1Ensemble_channels])
      trace.skeletonTable_component_mem] at filteredMem
  obtain ⟨interaction, interactionMem, rfl⟩ := List.mem_map.mp filteredMem
  obtain ⟨table, tableMem, interactionMem⟩ := List.mem_flatMap.mp interactionMem
  rw [skeletonTables, List.mem_append] at tableMem
  rcases tableMem with instruction | suffix
  · have decodedMem : interaction ∈
        decodedWitnessInstructionInteractionsWith trace.witness.data trace.witness.tables
          programChannel := by
      rw [decodedWitnessInstructionInteractionsWith_eq_tables trace.witness programChannel,
        trace.witness_tables]
      exact List.mem_flatMap.mpr ⟨table, instruction, interactionMem⟩
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
    rcases decodedWitnessProgramInteractions_pullShape trace.witness constraints interaction
        decodedMem with disabled | pulled
    · change signedVal interaction.raw.mult ≤ 0
      change interaction.raw.mult = 0 at disabled
      rw [disabled, signedVal_is_real hp (Or.inl rfl), ZMod.val_zero]
      norm_num
    · change signedVal interaction.raw.mult ≤ 0
      change interaction.raw.mult = -1 at pulled
      rw [pulled, signedVal_neg_is_real hp (Or.inr rfl),
        ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
      norm_num
  · have suffixMem : interaction ∈
        (trace.providerTables.drop preprocessedProviderTableCount).flatMap
          (typedTableInteractionsWith · trace.data programChannel) := by
      rw [tables_drop_preprocessed] at suffix
      exact List.mem_flatMap.mpr ⟨table, suffix, interactionMem⟩
    rw [trace.providerSuffixProgramInteractions_eq] at suffixMem
    -- the halt table's Program interactions are gated pulls: mult ∈ {0, -1}
    rw [← trace.haltTable_witness, ← trace.witness_data, haltTable_typedProgram] at suffixMem
    obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp suffixMem
    rw [List.mem_singleton] at hmem
    subst hmem
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
    change signedVal (TypedInteraction.pulledIfValue programChannel
      (haltRow trace.witness.data row).is_real
      (HaltChip.programMessage (haltRow trace.witness.data row))).raw.mult ≤ 0
    rcases witness_haltRows_selectorBinary trace.witness
        (trace.witness_constraints wf) row rowMem with h0 | h1
    · rw [show (TypedInteraction.pulledIfValue programChannel
          (haltRow trace.witness.data row).is_real
          (HaltChip.programMessage (haltRow trace.witness.data row))).raw.mult =
          -(haltRow trace.witness.data row).is_real from rfl, h0, neg_zero,
        signedVal_is_real hp (Or.inl rfl), ZMod.val_zero]
      norm_num
    · rw [show (TypedInteraction.pulledIfValue programChannel
          (haltRow trace.witness.data row).is_real
          (HaltChip.programMessage (haltRow trace.witness.data row))).raw.mult =
          -(haltRow trace.witness.data row).is_real from rfl, h1,
        signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (by omega)]
      norm_num

/-- The one residual polarity fact: only Byte accesses in the provider-free *actual Clean ledger*
need to be supplied. -/
def ByteConsumersOnlyPull : Prop :=
  ∀ access ∈ trace.skeletonLedger,
    (LookupAccessList.keyOf access).1 = InteractionKind.Byte →
      LookupAccessList.multOf access ≤ 0

/-- `ConsumersOnlyPull` follows from generated-row well-formedness and the residual Byte-only
polarity fact; Program polarity is derived above from the 25-chip registry contract. -/
theorem consumersOnlyPull_of_byte (wf : trace.WellFormed)
    (bytePulls : trace.ByteConsumersOnlyPull) : ConsumersOnlyPull trace := by
  intro access accessMem selected
  have kind : (LookupAccessList.keyOf access).1 = InteractionKind.Byte ∨
      (LookupAccessList.keyOf access).1 = InteractionKind.Program := by
    cases kindEq : (LookupAccessList.keyOf access).1 <;>
      simp only [preprocessedKey] at selected <;> simp_all
  rcases kind with byte | program
  · exact bytePulls access accessMem byte
  · exact trace.skeleton_program_mult_nonpos wf accessMem program

end SupportedCoreTraceWitness

end SP1Clean.Soundness
