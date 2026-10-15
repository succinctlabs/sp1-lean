import SP1Clean.Soundness.LocalCoreRows
import SP1Clean.Soundness.SystemStateRows

/-! # Physical State ledger of the local shard assembly

The mixed event inventory and the actual StateBump rows account for all State interactions.
Initialization, finalization, and lookup providers are State-silent. The verifier contributes
exactly the public final pull and initial push, so balance authenticates both endpoints.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow typedTableInteractions_nil byteProvider_channel_silent
  flatMap_split flatMap_filter_inactive pushesAt_flatMap pullsAt_flatMap verifier_state_interactions_of_values)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The actual active canonicalization rows, separate from instruction execution. -/
noncomputable def stateBumps {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : List (StateBumpChip.Inputs (ZMod p)) :=
  activeSystemRows (systemTable witness 1) (stateBumpRow witness.data) (·.is_real)

private theorem boundary_state_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (tables image source).take 6) :
    stateChannel.toRaw ∉ component.circuit.channels := by
  change component ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component) ++
    FinalMemoryEnsemble.inventory.views.map (·.component) at member
  rcases List.mem_append.mp member with initial | final
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
    intro used
    have subset := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id used
    simp [stateChannel, byteChannel, memoryChannel, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
      StaticTable.ofRows, Channel.toRaw] at subset
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
    intro used
    have subset := FinalMemoryEnsemble.view_channels_subset (p := p) id used
    simp only [List.mem_cons, List.not_mem_nil, or_false, stateChannel_eq_byteChannel_false,
      stateChannel_eq_memoryChannel_false, false_or] at subset
    exact (by decide : "SP1State" ≠ OrderedFinalProvider.channelName) (congrArg RawChannel.name subset)

private theorem boundaryTables_state_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take 6).flatMap (typedTableInteractionsWith · witness.data stateChannel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply typedTableInteractions_nil
  apply boundary_state_silent image source
  have mapped := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  exact mapped

private theorem byteTables_state_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    ((witness.tables.drop 32).take 23).flatMap (typedTableInteractionsWith · witness.data stateChannel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply typedTableInteractions_nil
  have mapped := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) member
  rw [List.map_take, List.map_drop, witness.tables_map_component] at mapped
  change table.component ∈ (sp1ProviderTables (p := p)).take 23 at mapped
  exact byteProvider_channel_silent table.component mapped stateChannel.toRaw
    (by simp [stateChannel_eq_byteChannel_false])

/-- The physical State interior contains exactly ordinary rows and the three State system tables. -/
theorem state_interiors {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    witness.tables.flatMap (typedTableInteractionsWith · witness.data stateChannel) =
      (instructionTables witness).flatMap (typedTableInteractionsWith · witness.data stateChannel) ++
        typedTableInteractionsWith (systemTable witness 1) witness.data stateChannel ++
        typedTableInteractionsWith (systemTable witness 2) witness.data stateChannel ++
        typedTableInteractionsWith (systemTable witness 3) witness.data stateChannel := by
  have length : witness.tables.length = 61 := by
    rw [← witness.same_length]; exact tables_length image source
  have programSilent : typedTableInteractionsWith (programTable witness) witness.data stateChannel = [] := by
    apply typedTableInteractions_nil
    rw [programTable_component]
    change (stateChannel (p := p)).toRaw ∉ [programChannel.toRaw]
    simp [stateChannel_eq_programChannel_false]
  have refreshSilent : typedTableInteractionsWith (systemTable witness 0) witness.data stateChannel = [] := by
    apply typedTableInteractions_nil
    rw [systemTable_component]
    change (stateChannel (p := p)).toRaw ∉ [byteChannel.toRaw, memoryChannel.toRaw, memoryChannel.toRaw]
    simp [stateChannel_eq_byteChannel_false, stateChannel_eq_memoryChannel_false]
  have head : witness.tables.drop 6 = programTable witness :: witness.tables.drop 7 := by
    rw [List.drop_eq_getElem_cons (by omega)]; rfl
  have registerSilent : typedTableInteractionsWith (registerMembershipTable witness) witness.data stateChannel = [] := by
    apply typedTableInteractions_nil
    rw [registerMembershipTable_component]
    change stateChannel.toRaw ∉ [source.sail.memorySnapshot.registerTable.channel.toRaw]
    simp [stateChannel, StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows, Channel.toRaw]
  have ramSilent : typedTableInteractionsWith (ramMembershipTable witness) witness.data stateChannel = [] := by
    apply typedTableInteractions_nil
    exact ramMembershipTable_silent witness stateChannel.toRaw (by simp [stateChannel, Channel.toRaw])
  have tail : witness.tables.drop 55 = [systemTable witness 0, systemTable witness 1,
      systemTable witness 2, systemTable witness 3, registerMembershipTable witness, ramMembershipTable witness] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_nil_of_le (by omega)]
    rfl
  have split := congrArg (List.flatMap (typedTableInteractionsWith · witness.data stateChannel))
    (List.take_append_drop 6 witness.tables)
  rw [List.flatMap_append, boundaryTables_state_silent, List.nil_append] at split
  rw [← split, head, List.flatMap_cons, programSilent, List.nil_append,
    flatMap_split witness.tables _ 7 25, flatMap_split witness.tables _ 32 23,
    byteTables_state_silent, List.nil_append, tail]
  simp only [List.flatMap_cons, List.flatMap_nil, ramSilent, refreshSilent, registerSilent, List.nil_append,
    List.append_nil, List.append_assoc, instructionTables]

/-- The combined verifier contributes exactly the final pull and initial push. -/
theorem verifier_state_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    typedInteractionValuesWith (ensemble image source).verifierOperations stateChannel
      (Environment.fromInput witness.publicInput witness.data) =
      [TypedInteraction.pulledIfValue stateChannel 1
        ⟨witness.publicInput.final_clk_high, witness.publicInput.final_clk_low,
          witness.publicInput.final_pc0, witness.publicInput.final_pc1,
          witness.publicInput.final_pc2⟩,
       TypedInteraction.pushedIfValue stateChannel 1
        ⟨witness.publicInput.init_clk_high, witness.publicInput.init_clk_low,
          witness.publicInput.init_pc0, witness.publicInput.init_pc1,
          witness.publicInput.init_pc2⟩] := by
  apply verifier_state_interactions_of_values witness
  change ((LocalSourceBoundary.checker image source).install (baseEnsemble image source)).verifierOperations.interactionValuesWith stateChannel.toRaw
    (Environment.fromInput witness.publicInput witness.data) = _
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _
    (by simp [baseEnsemble, sp1Ensemble_channels])]
  simp [baseEnsemble, boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
    Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.ofInteractions,
    sp1StateVerifierMain, OrderedBoundaryVerifier.main, Operations.interactionValuesWith,
    Operations.interactionsWith, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
    OrderedFinalProvider.channelName, stateChannel, byteChannel, exitChannel, circuit_norm]

private theorem instruction_state_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (instructionTables witness).flatMap (typedTableInteractionsWith · witness.data stateChannel) =
      (instructionRows witness).flatMap (fun row =>
        statePairInteractions (row.toChipRow witness.data).is_real (decodedStateEdge witness.data row)) := by
  rw [← decodedInstructionInteractionsWith_eq_tables witness.data stateChannel
    (instructionTables_aligned witness)]
  apply List.flatMap_congr
  intro row member
  exact row.stateInteractions_eq witness.data (supportedChip_stateEmissionShape row.chip
    (decodedInstructionRows_chip_mem (witness.tables.drop 7) member))

/-- All typed State interactions, including disabled pairs, are these physical row ledgers. -/
theorem state_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    typedEnsembleInteractionsWith witness stateChannel =
      statePairInteractions 1 (finalBoundaryStateMessage witness.publicInput,
        initialBoundaryStateMessage witness.publicInput) ++
      (instructionRows witness).flatMap (fun row =>
        statePairInteractions (row.toChipRow witness.data).is_real (decodedStateEdge witness.data row)) ++
      (systemTable witness 1).table.flatMap (fun physical =>
        let row := stateBumpRow witness.data physical
        statePairInteractions row.is_real (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)) ++
      (systemTable witness 2).table.flatMap (fun physical =>
        let row := haltRow witness.data physical
        statePairInteractions row.is_real (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row)) ++
      (systemTable witness 3).table.flatMap (fun physical =>
        let row := syscallInstrsRow witness.data physical
        statePairInteractions row.is_real (SyscallInstrsChip.statePulledMessage row,
          SyscallInstrsChip.statePushedMessage row)) := by
  rw [typedEnsembleInteractionsWith,
    verifier_state_interactions, state_interiors, instruction_state_interactions,
    stateBumpTable_typedState_of_component _ witness.data (systemTable_component witness 1),
    haltTable_typedState_of_component _ witness.data (systemTable_component witness 2),
    syscallInstrsTable_typedState_of_component _ witness.data (systemTable_component witness 3)]
  simp only [statePairInteractions, initialBoundaryStateMessage, finalBoundaryStateMessage,
    List.append_assoc]

private theorem instruction_selector_binary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints)
    (row : DecodedInstructionRow p) (member : row ∈ instructionRows witness) :
    (row.toChipRow witness.data).is_real = 0 ∨ (row.toChipRow witness.data).is_real = 1 :=
  supportedChip_selectorConstraintShape row.chip
    (decodedInstructionRows_chip_mem (witness.tables.drop 7) member) witness.data row.physical
    (instructionRows_constraints witness constraints row member)

/-- State selectors are signed units or zero throughout the combined witness. -/
theorem state_signedBinary_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness stateChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  rw [state_interactions]
  intro interaction member
  simp only [List.mem_append] at member
  rcases member with (((boundary | ordinary) | bump) | halt) | syscall
  · exact statePair_signed_binary 1 (Or.inr rfl) _ _ interaction boundary
  · exact statePairs_signedBinary _ _ _ (instruction_selector_binary witness constraints) interaction ordinary
  · exact statePairs_signedBinary _ _ _
      (stateBumpRow_binary _ witness.data (systemTable_component witness 1)
        (systemTable_constraints witness constraints 1)
        (byte _ (systemTable_mem witness 1)))
      interaction bump
  · exact statePairs_signedBinary _ _ _
      (haltRow_binary _ witness.data (systemTable_component witness 2) (systemTable_constraints witness constraints 2))
      interaction halt
  · exact statePairs_signedBinary _ _ _
      (syscallRow_binary _ witness.data (systemTable_component witness 3) (systemTable_constraints witness constraints 3))
      interaction syscall

private noncomputable def activeStateEdges {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :=
  (activeInstructionRows witness).map (decodedStateEdge witness.data) ++
    (stateBumps witness).map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)) ++
    (activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)).map
      (fun row => (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row)) ++
    (activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)).map
      (fun row => (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row))

private theorem activeStateEdges_balance {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness) :
    RankedGrounding.EndpointBalanced (↑(activeStateEdges witness)) id
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) := by
  classical
  have raw : BalancedInteractions ((typedEnsembleInteractionsWith witness stateChannel).map TypedInteraction.raw) := by
    rw [typedEnsembleInteractionsWith_raw]
    exact channels.state
  have pairs := Multiset.coe_eq_coe.mpr (producedMessages_perm_consumedMessages _ raw
    (state_signedBinary_of_byte witness constraints channels.byte))
  have ordinary := statePairs_projection _ _ (decodedStateEdge witness.data) (instruction_selector_binary witness constraints)
  have bump := statePairs_projection _ _ (fun physical =>
    let row := stateBumpRow witness.data physical
    (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)) (stateBumpRow_binary _ witness.data (systemTable_component witness 1)
    (systemTable_constraints witness constraints 1)
    (channels.byte _ (systemTable_mem witness 1)))
  have halt := statePairs_projection _ _ (fun physical =>
    let row := haltRow witness.data physical
    (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row))
    (haltRow_binary _ witness.data (systemTable_component witness 2) (systemTable_constraints witness constraints 2))
  have syscall := statePairs_projection _ _ (fun physical =>
    let row := syscallInstrsRow witness.data physical
    (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row))
    (syscallRow_binary _ witness.data (systemTable_component witness 3) (systemTable_constraints witness constraints 3))
  rw [state_interactions, producedMessages_append, producedMessages_append, producedMessages_append,
    producedMessages_append, consumedMessages_append, consumedMessages_append, consumedMessages_append,
    consumedMessages_append, ordinary.1, ordinary.2, bump.1, bump.2, halt.1, halt.2, syscall.1, syscall.2,
    statePairInteractions, producedMessages_statePair_one, consumedMessages_statePair_one] at pairs
  simpa only [RankedGrounding.EndpointBalanced, Multiset.map_coe, activeStateEdges,
    activeInstructionRows, stateBumps, activeSystemRows, List.filter_map,
    List.map_append, List.map_map, Function.comp_def, id_eq, List.singleton_append, List.cons_append, List.nil_append,
    ← Multiset.cons_coe] using pairs

/-- Complete raw State balance on the mixed row inventory and actual canonicalization rows. -/
theorem state_endpointBalanced_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness) :
    RankedGrounding.EndpointBalanced
      ((↑((executionRows witness).map (ExecutionRow.edge witness.data)) : Multiset _) +
        (↑((stateBumps witness).map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))) : Multiset _))
      id (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) := by
  have equal : (↑(activeStateEdges witness) : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p))) =
      (↑((executionRows witness).map (ExecutionRow.edge witness.data)) : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p))) +
        (↑((stateBumps witness).map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))) : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p))) := by
    simp only [activeStateEdges, executionRows, List.map_append, List.map_map,
      Function.comp_def, ExecutionRow.edge, ← Multiset.coe_add]
    ac_rfl
  rw [← equal]
  exact activeStateEdges_balance witness constraints channels

/-- Complete witnesses supply the Byte facts used to decode State multiplicities. -/
theorem state_signedBinary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness stateChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 :=
  state_signedBinary_of_byte witness constraints (orderingChannels_of_balanced witness constraints balanced).byte

/-- Complete witnesses supply the State/Byte interface used by endpoint accounting. -/
theorem state_endpointBalanced {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    RankedGrounding.EndpointBalanced
      ((↑((executionRows witness).map (NativeCore.ExecutionRow.edge witness.data)) : Multiset _) +
        (↑((stateBumps witness).map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))) : Multiset _))
      id (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) :=
  state_endpointBalanced_of_orderingChannels witness constraints (orderingChannels_of_balanced witness constraints balanced)

end SP1Clean.Soundness.LocalCore
