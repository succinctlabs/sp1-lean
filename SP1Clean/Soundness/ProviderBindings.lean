import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.TypedState
import SP1Clean.Model.Semantics.Truth
import SP1Clean.FormalModel.Execution

/-! # Semantic bindings for preprocessed and boundary tables

Clean channel balance proves that consumers match some provider contribution; it does not prove that
the provider is the committed program or the selected initial machine state.  These predicates state
that companion boundary honestly.  They are deliberately separate from raw AIR satisfaction and do
not contain an execution trajectory.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The provider-table indices in the stable 25-chip + 11-provider witness layout. -/
def programProviderIndex : ℕ := 33
def memoryInitProviderIndex : ℕ := 34
def memoryFinalizeProviderIndex : ℕ := 35

/-- The fixed SP1 ensemble layout always contains its Program-provider table. -/
theorem programProviderIndex_lt_tablesLength
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    programProviderIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [programProviderIndex, sp1Ensemble_tables, sp1Tables_length,
    sp1ProviderTables_length]

/-- The fixed SP1 ensemble layout always contains its Memory-init provider table. -/
theorem memoryInitProviderIndex_lt_tablesLength
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    memoryInitProviderIndex < witness.tables.length := by
  rw [← witness.same_length]
  simp [memoryInitProviderIndex, sp1Ensemble_tables, sp1Tables_length,
    sp1ProviderTables_length]

/-- The physical Program-provider table selected by the stable ensemble layout. -/
noncomputable def programProviderTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[programProviderIndex]'(programProviderIndex_lt_tablesLength witness)

/-- Optional indexing recovers the canonical Program-provider table. -/
theorem programProviderTable_getElem?
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables[programProviderIndex]? = some (programProviderTable witness) := by
  rw [List.getElem?_eq_getElem (programProviderIndex_lt_tablesLength witness)]
  rfl

/-- The physical Memory-init provider table selected by the stable ensemble layout. -/
noncomputable def memoryInitProviderTable
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Table (ZMod p) :=
  witness.tables[memoryInitProviderIndex]'(memoryInitProviderIndex_lt_tablesLength witness)

/-- Optional indexing recovers the canonical Memory-init provider table. -/
theorem memoryInitProviderTable_getElem?
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.tables[memoryInitProviderIndex]? = some (memoryInitProviderTable witness) := by
  rw [List.getElem?_eq_getElem (memoryInitProviderIndex_lt_tablesLength witness)]
  rfl

/-- The stable Memory-init witness position is the range-checking push circuit. -/
theorem memoryInitProviderTable_component
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (memoryInitProviderTable witness).component = ⟨MemoryProviderChip.circuit⟩ := by
  unfold memoryInitProviderTable
  have aligned := witness.same_circuits 34 (by
    simp [sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length])
  exact aligned.symm.trans (by rfl)

/-- The stable Memory-init table uses the ensemble's shared prover data. -/
theorem memoryInitProviderTable_data
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (memoryInitProviderTable witness).data = witness.data := by
  exact witness.same_data _ (List.getElem_mem
    (memoryInitProviderIndex_lt_tablesLength witness))

/-- The Memory-init circuit's own constraints prove every active push's channel requirement. -/
theorem memoryInitProviderTable_requirements
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    (memoryInitProviderTable witness).ChannelRequirements memoryChannel.toRaw := by
  let table := memoryInitProviderTable witness
  have tableConstraints : table.Constraints := constraints table
    (witness.mem_allTables_of_mem_tables
      (List.getElem_mem (memoryInitProviderIndex_lt_tablesLength witness)))
  have tableAssumptions : table.Assumptions := by
    intro row rowMem
    rw [show table.component = ⟨MemoryProviderChip.circuit⟩ from
      memoryInitProviderTable_component witness]
    trivial
  have tableGuarantees : table.Guarantees := by
    rw [Table.guarantees_iff_channelGuarantees]
    intro channel channelMem
    change channel ∈ table.component.circuit.channelsWithGuarantees at channelMem
    rw [show table.component = ⟨MemoryProviderChip.circuit⟩ from
      memoryInitProviderTable_component witness] at channelMem
    have noChannels : (MemoryProviderChip.circuit (p := p)).channelsWithGuarantees = [] := rfl
    rw [noChannels] at channelMem
    simp at channelMem
  exact table.channelRequirements_of_requirements
    (Table.weakSoundness tableAssumptions tableConstraints tableGuarantees).2

/-- Every active Program-provider contribution is a decode of the program committed in shared prover
data.  Zero-multiplicity padding rows impose no semantic condition. -/
noncomputable def ProgramProviderBound
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Prop :=
  ∀ interaction,
    ∀ member : interaction ∈
      (programProviderTable witness).interactionsWith programChannel.toRaw,
    interaction.mult ≠ 0 →
      ProgTruth (TypedInteraction.message
        { raw := interaction
          channel_eq := (programProviderTable witness).channel_eq_of_mem_interactionsWith member })
        witness.data

/-- One active memory-init contribution names the true initial content of its register or aligned
64-bit RAM cell, at a timestamp no later than the shard's initial State boundary. -/
def MemoryInitMessageBound (initial : SailState) (initialClock : ℕ)
    (message : MemoryMsg (ZMod p)) : Prop :=
  locContent initial (MemoryMsg.locOf message) = some (Word.toBitVec64 message.value) ∧
    MemoryMsg.timeNat message ≤ initialClock

/-- Every active Memory-init contribution is grounded in the selected local initial state.  Finalizer
rows are intentionally absent: their values are derived from the ordered memory frontier and balance. -/
noncomputable def MemoryInitProviderBound
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (initial : SailState) (initialClock : ℕ) : Prop :=
  ∀ interaction,
    ∀ member : interaction ∈
      (memoryInitProviderTable witness).interactionsWith memoryChannel.toRaw,
    interaction.mult ≠ 0 →
      MemoryInitMessageBound initial initialClock
        (TypedInteraction.message
          { raw := interaction
            channel_eq := (memoryInitProviderTable witness).channel_eq_of_mem_interactionsWith member })

/-- Every exact active Memory-init push is locally true at the selected shard boundary. The value
range comes from the provider circuit's proved requirement; only state content and initial timing
come from `MemoryInitProviderBound`. -/
theorem MemoryInitProviderBound.localMemTruth_of_mem_produced
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (initial : SailState) (initialClock : ℕ)
    (bound : MemoryInitProviderBound witness initial initialClock)
    (message : MemoryMsg (ZMod p))
    (member : message ∈ producedMessages
      (typedTableInteractionsWith (memoryInitProviderTable witness) memoryChannel)) :
    LocalMemTruth initial initialClock message := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  have isU64 := guarantee_of_mem_producedTableMessages
    (memoryInitProviderTable witness) memoryChannel hp
    (memoryInitProviderTable_requirements witness constraints) message member
  change MemoryMsg.isU64 message at isU64
  unfold producedMessages at member
  obtain ⟨interaction, interactionMem, messageEq⟩ := List.mem_map.mp member
  obtain ⟨typedMem, positive⟩ := List.mem_filter.mp interactionMem
  simp only [decide_eq_true_eq] at positive
  have rawMem : interaction.raw ∈
      (memoryInitProviderTable witness).interactionsWith memoryChannel.toRaw := by
    rw [← typedTableInteractionsWith_raw]
    exact List.mem_map_of_mem typedMem
  have multNonzero : interaction.raw.mult ≠ 0 := by
    intro multZero
    change signedVal interaction.raw.mult = 1 at positive
    rw [multZero] at positive
    simp [signedVal] at positive
  let rebound : TypedInteraction memoryChannel :=
    { raw := interaction.raw
      channel_eq := (memoryInitProviderTable witness).channel_eq_of_mem_interactionsWith rawMem }
  have semantic := bound interaction.raw rawMem multNonzero
  change MemoryInitMessageBound initial initialClock rebound.message at semantic
  have reboundEq : rebound = interaction := TypedInteraction.raw_injective rfl
  rw [reboundEq, messageEq] at semantic
  exact Semantics.localMemTruth_of_initial isU64 semantic.1 semantic.2

/-- Proof-only facts tying one selected initial Sail state to the public and provider boundary. -/
structure InitialBoundaryFacts
    (statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (initial : SailState) : Prop where
  programWellFormed : statement.program.WellFormed
  programCommitted : Commit.StatementFor witness.data statement.program
  initialPc : initial.regs.get? Register.PC = some
    (supportedPcBits statement.publicValues.init_pc0
      statement.publicValues.init_pc1 statement.publicValues.init_pc2)
  initialClock : Commit.initClkNat witness.data =
    Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low
  romLoaded : RomLoaded statement.program initial
  configured : SailConfigured initial
  programProvider : ProgramProviderBound witness
  memoryProvider : MemoryInitProviderBound witness initial (Commit.initClkNat witness.data)

/-- The selected public boundary is exactly the initial truth needed by shard-local timed grounding.
No boot or zero-register premise is introduced here. -/
theorem InitialBoundaryFacts.localStateTruth
    {statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))}
    {witness : EnsembleWitness (sp1Ensemble (p := p))} {initial : SailState}
    (boundary : InitialBoundaryFacts statement witness initial) :
    LocalStateTruth statement.program initial (Commit.initClkNat witness.data)
      (initialBoundaryStateMessage statement.publicValues) := by
  apply Semantics.localStateTruth_initial
  · simpa [initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using
      boundary.initialClock.symm
  · simpa [initialBoundaryStateMessage, Semantics.StateMsg.pcBits,
      Semantics.pcBits, supportedPcBits] using boundary.initialPc
  · exact boundary.romLoaded
  · exact boundary.configured

/-- The non-execution companion relation required by supported-core AIR soundness.  It fixes the
committed program, chooses the concrete state represented by the initial public boundary, and binds
the Program/Memory provider tables to those semantic objects. -/
def SemanticBoundaryBinding
    (statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Prop :=
  ∃ initial, InitialBoundaryFacts statement witness initial

end SP1Clean.Soundness
