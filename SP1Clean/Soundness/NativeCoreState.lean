import SP1Clean.Soundness.NativeCoreRows
import SP1Clean.Soundness.SystemStateRows

/-! # Physical State ledger of the authenticated native core

The mixed event inventory and the actual StateBump rows account for all State interactions.
Initialization, finalization, and lookup providers are State-silent. The verifier contributes
exactly the public final pull and initial push, so balance authenticates both endpoints.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The actual active canonicalization rows, separate from instruction execution. -/
noncomputable def stateBumps {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : List (StateBumpChip.Inputs (ZMod p)) :=
  activeSystemRows (systemTable witness 1) (stateBumpRow witness.data) (·.is_real)

private theorem providerView_state_silent {Payload : TypeMap} [ProvableType Payload]
    (name : String) (distinct : name ≠ "SP1Byte") (notState : name ≠ "SP1State")
    (recordSpec : MemoryMsg (ZMod p) → Prop)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → recordSpec output)
    (canonical : ∀ record, recordSpec record → MemoryBoundary.CanonicalSpec record)
    (privateChannel : (OrderedBoundary.channel name).toRaw ∉ provider.channels)
    (silent : stateChannel.toRaw ∉ provider.channels) :
    stateChannel.toRaw ∉ (OrderedMemoryEnsemble.providerView name distinct recordSpec
      provider binds canonical privateChannel).component.circuit.channels := by
  change stateChannel.toRaw ∉ provider.channelsWithGuarantees ++
    [byteChannel.toRaw, (OrderedBoundary.channel name).toRaw, byteChannel.toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ++
    (provider.channelsWithRequirements ++ [(OrderedBoundary.channel name).toRaw])
  have separate : (stateChannel (p := p)).toRaw ≠ (OrderedBoundary.channel name).toRaw := by
    simp [stateChannel, OrderedBoundary.channel, Channel.toRaw, Ne.symm notState]
  simpa only [GeneralFormalCircuit.channels, List.mem_append, List.mem_cons,
    List.not_mem_nil, separate, stateChannel_eq_byteChannel_false, or_false,
    false_or] using silent

private theorem terminalView_state_silent (name : String) (distinct : name ≠ "SP1Byte")
    (notState : name ≠ "SP1State") : stateChannel.toRaw ∉
      (OrderedMemoryEnsemble.terminalView (p := p) name distinct).component.circuit.channels := by
  change stateChannel.toRaw ∉ [byteChannel.toRaw, (OrderedBoundary.channel name).toRaw] ++
    [(OrderedBoundary.channel name).toRaw]
  simp [stateChannel, OrderedBoundary.channel, byteChannel, Channel.toRaw, Ne.symm notState]

private theorem boundary_state_silent (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (InitialMemoryEnsemble.views image).map (·.component) ++
      FinalMemoryEnsemble.inventory.views.map (·.component)) :
    stateChannel.toRaw ∉ component.circuit.channels := by
  simp only [InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · apply providerView_state_silent _ _ (by decide)
    all_goals simp [GeneralFormalCircuit.channels, InitialRegisterProvider.circuit, circuit_norm,
      stateChannel, memoryChannel, OrderedBoundary.channel, OrderedInitialProvider.channelName]
  · apply providerView_state_silent _ _ (by decide)
    all_goals simp [GeneralFormalCircuit.channels, InitialRamProvider.circuit, circuit_norm,
      stateChannel, memoryChannel, byteChannel, OrderedBoundary.channel,
      OrderedInitialProvider.channelName]
  · exact terminalView_state_silent _ (by decide) (by decide)
  · apply providerView_state_silent _ _ (by decide)
    all_goals simp [GeneralFormalCircuit.channels, FinalRegisterProvider.circuit, circuit_norm,
      stateChannel, memoryChannel, OrderedBoundary.channel, OrderedFinalProvider.channelName]
  · apply providerView_state_silent _ _ (by decide)
    all_goals simp [GeneralFormalCircuit.channels, FinalRamProvider.circuit, circuit_norm,
      stateChannel, memoryChannel, byteChannel, OrderedBoundary.channel,
      OrderedFinalProvider.channelName]
  · exact terminalView_state_silent _ (by decide) (by decide)

private theorem boundaryTables_state_silent {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (witness.tables.take 6).flatMap (typedTableInteractionsWith · witness.data stateChannel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply typedTableInteractions_nil
  apply boundary_state_silent image
  have mapped := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  exact mapped

private theorem byteTables_state_silent {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
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
theorem state_interiors {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    witness.tables.flatMap (typedTableInteractionsWith · witness.data stateChannel) =
      (instructionTables witness).flatMap (typedTableInteractionsWith · witness.data stateChannel) ++
        typedTableInteractionsWith (systemTable witness 1) witness.data stateChannel ++
        typedTableInteractionsWith (systemTable witness 2) witness.data stateChannel ++
        typedTableInteractionsWith (systemTable witness 3) witness.data stateChannel := by
  have length : witness.tables.length = 60 := by
    rw [← witness.same_length]; exact tables_length image
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
  have ramSilent : typedTableInteractionsWith (ramMembershipTable witness) witness.data stateChannel = [] := by
    apply typedTableInteractions_nil
    exact ramMembershipTable_silent witness stateChannel.toRaw (by simp [stateChannel, Channel.toRaw])
  have tail : witness.tables.drop 55 = [systemTable witness 0, systemTable witness 1,
      systemTable witness 2, systemTable witness 3, ramMembershipTable witness] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_nil_of_le (by omega)]
    rfl
  have split := congrArg (List.flatMap (typedTableInteractionsWith · witness.data stateChannel))
    (List.take_append_drop 6 witness.tables)
  rw [List.flatMap_append, boundaryTables_state_silent, List.nil_append] at split
  rw [← split, head, List.flatMap_cons, programSilent, List.nil_append,
    flatMap_split witness.tables _ 7 25, flatMap_split witness.tables _ 32 23,
    byteTables_state_silent, List.nil_append, tail]
  simp only [List.flatMap_cons, List.flatMap_nil, ramSilent, refreshSilent, List.nil_append,
    List.append_nil, List.append_assoc, instructionTables]

private theorem verifierMain_stateInteractions (image : ProgramImage)
    (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((verifierMain image input).operations offset).interactionsWith stateChannel.toRaw =
      ((sp1StateVerifierMain input).operations offset).interactionsWith stateChannel.toRaw := by
  have silent (name : String) (different : name ≠ "SP1State") (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil
      (OrderedBoundaryVerifier.circuit (p := p) name
        OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).base
      stateChannel.toRaw () offset (by
        change stateChannel.toRaw ∉ [(OrderedBoundary.channel name).toRaw]
        simp [stateChannel, OrderedBoundary.channel, Channel.toRaw, Ne.symm different])
  have initial := silent OrderedInitialProvider.channelName (by decide)
  have final := silent OrderedFinalProvider.channelName (by decide)
  simp only [verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
    Operations.interactionsWith, OrderedBoundaryVerifier.circuit] at initial final ⊢
  simp only [List.filter_append, initial, final, List.append_nil, sp1StateVerifier]
  rfl

/-- The combined verifier contributes exactly the final pull and initial push. -/
theorem verifier_state_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    typedInteractionValuesWith (ensemble image).verifierOperations stateChannel
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
  rw [verifier_values_of_registered image _ stateChannel.toRaw
    (by simp [baseEnsemble, sp1Ensemble_channels])]
  change (verifierInteractions image).circuitOperations.interactionValuesWith stateChannel.toRaw _ = _
  simp only [Operations.interactionValuesWith_eq_map, Verifier.Program.circuitOperations,
    Verifier.Program.operations, Operations.interactionsWith, verifierInteractions_interactions,
    sp1StateVerifierProgram, Verifier.ofInteractions_interactions]
  exact congrArg (List.map (AbstractInteraction.eval
    (Environment.fromInput witness.publicInput witness.data)))
      (verifierMain_stateInteractions image (varFromOffset SP1PublicIO 0) 0)

private theorem instruction_state_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
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
theorem state_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
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

private theorem instruction_selector_binary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints)
    (row : DecodedInstructionRow p) (member : row ∈ instructionRows witness) :
    (row.toChipRow witness.data).is_real = 0 ∨ (row.toChipRow witness.data).is_real = 1 :=
  supportedChip_selectorConstraintShape row.chip
    (decodedInstructionRows_chip_mem (witness.tables.drop 7) member) witness.data row.physical
    (instructionRows_constraints witness constraints row member)

/-- State selectors are signed units or zero throughout the combined witness. -/
theorem state_signedBinary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
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
        (((finishedChannel_guarantees image witness constraints balanced).2) _ (systemTable_mem witness 1)).1)
      interaction bump
  · exact statePairs_signedBinary _ _ _
      (haltRow_binary _ witness.data (systemTable_component witness 2) (systemTable_constraints witness constraints 2))
      interaction halt
  · exact statePairs_signedBinary _ _ _
      (syscallRow_binary _ witness.data (systemTable_component witness 3) (systemTable_constraints witness constraints 3))
      interaction syscall

private noncomputable def activeStateEdges {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :=
  (activeInstructionRows witness).map (decodedStateEdge witness.data) ++
    (stateBumps witness).map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)) ++
    (activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real)).map
      (fun row => (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row)) ++
    (activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)).map
      (fun row => (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row))

private theorem activeStateEdges_balance {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    RankedGrounding.EndpointBalanced (↑(activeStateEdges witness)) id
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) := by
  classical
  have raw : BalancedInteractions ((typedEnsembleInteractionsWith witness stateChannel).map TypedInteraction.raw) := by
    rw [typedEnsembleInteractionsWith_raw]
    exact balanced _ (by simp [ensemble, baseEnsemble, sp1Ensemble_channels])
  have pairs := Multiset.coe_eq_coe.mpr (producedMessages_perm_consumedMessages _ raw
    (state_signedBinary witness constraints balanced))
  have ordinary := statePairs_projection _ _ (decodedStateEdge witness.data) (instruction_selector_binary witness constraints)
  have bump := statePairs_projection _ _ (fun physical =>
    let row := stateBumpRow witness.data physical
    (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)) (stateBumpRow_binary _ witness.data (systemTable_component witness 1)
    (systemTable_constraints witness constraints 1)
    (((finishedChannel_guarantees image witness constraints balanced).2) _ (systemTable_mem witness 1)).1)
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
theorem state_endpointBalanced {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
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
  exact activeStateEdges_balance witness constraints balanced

end SP1Clean.Soundness.NativeCore
