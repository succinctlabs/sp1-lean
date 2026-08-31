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
    (tables : List (Table (ZMod p))) (channel : Channel (ZMod p) Message)
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (hchannel : channel.toRaw ∈ (sp1Ensemble (p := p)).channels)
    (hcomponents : ∀ table ∈ tables,
      table.component ∈ (sp1Ensemble (p := p)).allTables) :
    (tablesCleanAccesses tables).filter (fun access => access.1 = K) =
      (tables.flatMap (typedTableInteractionsWith · channel)).map
        (Interaction.toAccess ∘ TypedInteraction.raw) := by
  simp only [tablesCleanAccesses, List.filter_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun table tableMem => ?_
  rw [tableCleanAccesses_filterKind table channel.toRaw K hkind
    (fun interaction interactionMem interactionKind =>
      interactions_channel_eq_of_kindOf table (hcomponents table tableMem) channel.toRaw
        hchannel interaction interactionMem
        (interactionKind.trans hkind.symm))]
  rw [← typedTableInteractionsWith_raw]
  simp only [List.map_map]

/-- Every provider-free skeleton table is one of the assembled witness's actual tables (including
the verifier row), hence carries a component from `sp1Ensemble`. -/
theorem skeletonTable_component_mem (table : Table (ZMod p))
    (tableMem : table ∈ trace.skeletonTables) :
    table.component ∈ (sp1Ensemble (p := p)).allTables := by
  rw [skeletonTables, List.mem_cons, List.mem_append] at tableMem
  rcases tableMem with rfl | tableMem | tableMem
  · rw [Air.Flat.Ensemble.allTables, List.mem_cons]
    exact Or.inl rfl
  · exact trace.allTables_component_mem table
      (by rw [Air.Flat.EnsembleWitness.allTables, List.mem_cons, trace.witness_tables]
          exact Or.inr (List.mem_of_mem_take tableMem))
  · exact trace.allTables_component_mem table
      (by rw [Air.Flat.EnsembleWitness.allTables, List.mem_cons, trace.witness_tables]
          exact Or.inr (List.mem_of_mem_drop tableMem))

/-- The memory-initialization provider does not name the Program channel. -/
theorem memoryInitProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryInit) programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉ [Channels.memoryChannel.toRaw]
  simp [Channels.programChannel_eq_memoryChannel_false]

/-- The memory-finalization provider does not name the Program channel. -/
theorem memoryFinalizeProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryFinalize) programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉ [Channels.memoryChannel.toRaw]
  simp [Channels.programChannel_eq_memoryChannel_false]

/-- The memory-bump provider does not name the Program channel. -/
theorem memoryBumpProgramInteractions_eq_nil :
    typedTableInteractionsWith (trace.providerTableFor .memoryBump) programChannel = [] := by
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
    typedTableInteractionsWith (trace.providerTableFor .stateBump) programChannel = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  change programChannel.toRaw ∉
    [Channels.byteChannel.toRaw, Channels.stateChannel.toRaw]
  simp [Channels.programChannel_eq_byteChannel_false,
    Channels.programChannel_eq_stateChannel_false]

/-- The non-preprocessed provider suffix's Program interactions are exactly the halt table's
gated ECALL fetch pulls (the four Memory/State system tables are Program-silent). -/
theorem providerSuffixProgramInteractions_eq :
    (trace.providerTables.drop preprocessedProviderTableCount).flatMap
      (typedTableInteractionsWith · programChannel) =
    typedTableInteractionsWith (trace.providerTableFor .halt) programChannel := by
  rw [providerTables_drop_preprocessed]
  simp only [List.flatMap_cons, List.flatMap_nil,
    trace.memoryInitProgramInteractions_eq_nil,
    trace.memoryFinalizeProgramInteractions_eq_nil,
    trace.memoryBumpProgramInteractions_eq_nil,
    trace.stateBumpProgramInteractions_eq_nil, List.nil_append, List.append_nil]

/-- The skeleton verifier table does not name the Program channel. -/
theorem skeletonVerifierProgramInteractions_eq_nil :
    typedTableInteractionsWith trace.skeletonVerifierTable programChannel = [] := by
  rw [skeletonVerifierTable, ← trace.witness_verifierTable]
  exact witness_verifierProgramInteractions_eq_nil trace.witness

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
  rw [skeletonLedger,
    tablesCleanAccesses_filterKind_eq_typed trace.skeletonTables programChannel
      InteractionKind.Program rfl (by simp [sp1Ensemble_channels])
      trace.skeletonTable_component_mem] at filteredMem
  obtain ⟨interaction, interactionMem, rfl⟩ := List.mem_map.mp filteredMem
  obtain ⟨table, tableMem, interactionMem⟩ := List.mem_flatMap.mp interactionMem
  rw [skeletonTables, List.mem_cons, List.mem_append] at tableMem
  rcases tableMem with verifier | instruction | suffix
  · subst table
    rw [trace.skeletonVerifierProgramInteractions_eq_nil] at interactionMem
    simp only [List.not_mem_nil] at interactionMem
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
          (typedTableInteractionsWith · programChannel) := by
      rw [tables_drop_preprocessed] at suffix
      exact List.mem_flatMap.mpr ⟨table, suffix, interactionMem⟩
    rw [trace.providerSuffixProgramInteractions_eq] at suffixMem
    -- the halt table's Program interactions are gated pulls: mult ∈ {0, -1}
    rw [← trace.haltTable_witness, haltTable_typedProgram] at suffixMem
    obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp suffixMem
    rw [List.mem_singleton] at hmem
    subst hmem
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
    change signedVal (TypedInteraction.pulledIfValue programChannel
      (haltRow (haltTable trace.witness) row).is_real
      (HaltChip.programMessage (haltRow (haltTable trace.witness) row))).raw.mult ≤ 0
    rcases witness_haltRows_selectorBinary trace.witness
        (trace.witness_constraints wf) row rowMem with h0 | h1
    · rw [show (TypedInteraction.pulledIfValue programChannel
          (haltRow (haltTable trace.witness) row).is_real
          (HaltChip.programMessage (haltRow (haltTable trace.witness) row))).raw.mult =
          -(haltRow (haltTable trace.witness) row).is_real from rfl, h0, neg_zero,
        signedVal_is_real hp (Or.inl rfl), ZMod.val_zero]
      norm_num
    · rw [show (TypedInteraction.pulledIfValue programChannel
          (haltRow (haltTable trace.witness) row).is_real
          (HaltChip.programMessage (haltRow (haltTable trace.witness) row))).raw.mult =
          -(haltRow (haltTable trace.witness) row).is_real from rfl, h1,
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
