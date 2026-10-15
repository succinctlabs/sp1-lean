import SP1Clean.Soundness.LocalCoreProgram

/-! # Physical instruction decoding in the local shard assembly

The assembly's instruction batch retains the exact physical rows and shared prover data. Its
decoder inherits raw constraints, finished-channel guarantees, and the actual interaction ledger.
Active instruction fetches therefore reach the checked image and Sail decoder through one public
statement. Table offsets and instruction cases remain inside this adapter.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The ordinary instruction batch, after the two inventories and the fixed ROM table. -/
def instructionTables {image : ProgramImage} {source : ExecutionSnapshot} (witness : EnsembleWitness (ensemble (p := p) image source)) :
    List (Table (ZMod p)) := (witness.tables.drop 7).take 25

theorem instructionTables_components {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (instructionTables witness).map (·.component) = sp1Tables := by
  rw [instructionTables, List.map_take, List.map_drop, witness.tables_map_component]
  change (sp1Tables (p := p) ++ (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)).take 25 = _
  rw [← sp1Tables_length (p := p), List.take_left]

theorem instructionTables_mem {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) {table : Table (ZMod p)}
    (member : table ∈ instructionTables witness) : table ∈ witness.tables :=
  List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem instructionTables_aligned {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    InstructionTablesAligned supportedChips (instructionTables witness) :=
  InstructionTablesAligned.of_components (instructionTables_components witness)

/-- Decode ordinary rows without replacing their physical witness cells. -/
noncomputable def instructionRows {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : List (DecodedInstructionRow p) :=
  decodeInstructionTables supportedChips (instructionTables witness)

theorem instructionRows_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints) :
    ∀ row ∈ instructionRows witness,
      row.chip.table.operations.ConstraintsHold (row.environment witness.data) :=
  constraints_of_mem_decodeInstructionTables witness.data (instructionTables_aligned witness)
    (fun table member => constraints table (instructionTables_mem witness member))

/-- Every evaluated decoded interaction is an interaction of the original combined witness. -/
theorem instructionRows_interaction_mem {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    {Message : TypeMap} [ProvableType Message] (channel : Channel (ZMod p) Message)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness)
    {interaction : Interaction (ZMod p)}
    (emitted : interaction ∈ row.chip.table.operations.interactionValuesWith channel.toRaw
      (row.environment witness.data)) :
    interaction ∈ witness.interactionsWith channel.toRaw := by
  rw [← row.interactionsWith_raw witness.data channel] at emitted
  obtain ⟨typed, typedMem, rfl⟩ := List.mem_map.mp emitted
  have batchMem : typed ∈ decodedInstructionInteractionsWith witness.data supportedChips
      (instructionTables witness) channel := List.mem_flatMap.mpr ⟨row, member, typedMem⟩
  rw [decodedInstructionInteractionsWith_eq_tables witness.data channel
    (instructionTables_aligned witness)] at batchMem
  obtain ⟨table, tableMem, typedMem⟩ := List.mem_flatMap.mp batchMem
  apply EnsembleWitness.mem_interactionsWith.mpr
  refine Or.inr ⟨table, instructionTables_mem witness tableMem, ?_⟩
  rw [← typedTableInteractionsWith_raw]
  exact List.mem_map_of_mem typedMem

/-- All ordinary rows receive the combined AIR's closed Byte and Program guarantees. -/
theorem instructionRows_finished_guarantees {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness) :
    row.chip.table.operations.ChannelGuarantees byteChannel.toRaw (row.environment witness.data) ∧
      row.chip.table.operations.ChannelGuarantees programChannel.toRaw (row.environment witness.data) := by
  have closed := finishedChannel_guarantees image source witness constraints balanced
  constructor
  · exact channelGuarantees_of_mem_decodeInstructionTables witness.data byteChannel.toRaw
      (instructionTables_aligned witness)
      (fun table tableMem => (closed.2 table (instructionTables_mem witness tableMem)).1) row member
  · exact channelGuarantees_of_mem_decodeInstructionTables witness.data programChannel.toRaw
      (instructionTables_aligned witness)
      (fun table tableMem => (closed.2 table (instructionTables_mem witness tableMem)).2) row member

/-- An active decoded instruction fetch belongs to the checked image and official Sail decoder.
The statement is independent of the instruction's chip and physical table position. -/
theorem instructionRows_program_committed_of_balance {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness)
    (active : (row.toChipRow witness.data).is_real = 1) :
    Target.committedInROM (image.toGuestProgram valid)
      (programAccess (row.toChipRow witness.data).view).toRow := by
  have chipMem := mem_chip_of_mem_decodeInstructionTables member
  have emitted := supportedChip_programEmissionShape row.chip chipMem witness.data row.physical
    (instructionRows_constraints witness constraints row member)
  let message := programMessageOfView (row.toChipRow witness.data).view
  let interaction := programChannel.pulledIfValue (row.toChipRow witness.data).is_real message
  have pullMem : interaction ∈ witness.interactionsWith programChannel.toRaw := by
    apply instructionRows_interaction_mem witness programChannel member
    rw [DecodedInstructionRow.environment, emitted]
    exact List.mem_singleton_self _
  exact program_pull_committed_of_balance valid witness constraints balanced message interaction pullMem
    (by change -(row.toChipRow witness.data).is_real = -1; rw [active]) rfl

/-- The complete local AIR authenticates every active ordinary fetch. -/
theorem instructionRows_program_committed {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ instructionRows witness)
    (active : (row.toChipRow witness.data).is_real = 1) :
    Target.committedInROM (image.toGuestProgram valid)
      (programAccess (row.toChipRow witness.data).view).toRow :=
  instructionRows_program_committed_of_balance valid witness constraints
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels])) member active

end SP1Clean.Soundness.LocalCore
