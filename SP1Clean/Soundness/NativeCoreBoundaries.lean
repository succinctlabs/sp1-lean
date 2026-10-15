import SP1Clean.Soundness.NativeCoreEnsemble
import ToClean.Air.EnsembleBuild

/-! # Authenticated boundaries from the combined native AIR

The initialization projection retains the physical tables and shared prover data verbatim.
Only its verifier is restricted to the private ordering channel. Local provider specifications
come from raw constraints and the combined Byte ledger, not caller-supplied semantic facts.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem initialView_spec (image : ProgramImage)
    (view : TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName))
    (member : view ∈ InitialMemoryEnsemble.views image) (env : Environment (ZMod p))
    (constraints : view.component.operations.ConstraintsHold env)
    (byte : view.component.operations.ChannelGuarantees byteChannel.toRaw env)
    (ram : view.component.operations.ChannelGuarantees
      (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw env) :
    view.component.Spec env := by
  have assumptions : view.component.CircuitAssumptions env := by
    simp only [InitialMemoryEnsemble.views, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  have channels : view.component.circuit.channelsWithGuarantees ⊆
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw] := by
    simp only [InitialMemoryEnsemble.views, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · change ((InitialMemoryRead.circuit (p := p) image.initialMemory).channelsWithGuarantees ++
        List.replicate 2 byteChannel.toRaw ++
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ++
        List.replicate 4 byteChannel.toRaw) ⊆ _
      simp only [InitialMemoryRead.circuit, InitialMemoryRead.circuitNamed_guarantees]
      generalize (byteChannel (p := p)).toRaw = byte,
        (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName).toRaw = control,
        (InitialMemoryLookup.membership (p := p) image.initialMemory (2 ^ 48)
          "sp1.native.initial_memory").channel.toRaw = ram
      simp only [List.subset_def, List.mem_append, List.mem_replicate, List.mem_flatten,
        List.mem_cons, List.not_mem_nil, or_false]
      aesop
    · change [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ⊆ _
      simp
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (view.component.inChannelsOrGuarantees env)]
  intro channel member
  rcases List.mem_cons.mp (channels member) with rfl | member
  · exact byte
  · rcases List.mem_cons.mp member with rfl | member
    · exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _
    · obtain rfl := List.mem_singleton.mp member
      exact ram

/-- A proof view of the actual combined table list, with just the initialization verifier.
No row or prover data is synthesized or replaced. -/
def initialWitness {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image)) :
    EnsembleWitness (InitialMemoryEnsemble.ensemble (p := p) image (afterInitialTables (p := p) image ++ [ramMembership image]) []
      (baseEnsemble image).unique_names) :=
  EnsembleWitness.ofTables _ witness.tables () witness.tables_map_component

/-- The Byte closure of the combined ensemble discharges every initial provider's local
assumptions. Other instruction/finalizer specifications are not required at this stage. -/
theorem initialTables_spec {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (initialWitness witness).tables.take (InitialMemoryEnsemble.views (p := p) image).length,
      table.Spec witness.data := by
  intro table member row rowMem
  have componentMem : table.component ∈ (InitialMemoryEnsemble.views (p := p) image).map (·.component) := by
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, (initialWitness witness).tables_map_component] at mapped
    simpa only [InitialMemoryEnsemble.ensemble, OrderedBoundaryEnsemble.ensemble,
      List.take_left', List.length_map] using mapped
  obtain ⟨view, viewMem, same⟩ := List.mem_map.mp componentMem
  have tableMem : table ∈ witness.tables := List.mem_of_mem_take member
  have byte := ((finishedChannel_guarantees image witness constraints balanced).2 table tableMem).1 row rowMem
  have ram := ram_guarantees_of_balance image witness constraints
    (balanced _ (by simp [ensemble, baseEnsemble])) table tableMem row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte ram checked ⊢
  exact initialView_spec image view viewMem _ checked byte ram

/-- Initial records decoded from the combined AIR have the actual checked image's boot value,
zero timestamp, and canonical location. The theorem accepts raw constraints and balance only. -/
theorem initial_records_authentic {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ InitialMemoryEnsemble.records (initialWitness witness), MemoryBoundary.InitialSpec image record :=
  (InitialMemoryEnsemble.inventory image).records_valid_of_tables (initialWitness witness)
    (initialTables_spec witness constraints balanced)

private theorem initialChannel_not_old :
    (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName).toRaw ∉
      (sp1Ensemble (p := p)).channels := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [sp1Ensemble_channels, OrderedBoundary.channel, OrderedInitialProvider.channelName,
    stateChannel, memoryChannel, programChannel, byteChannel, exitChannel,
    syscallChannel, publicValuesChannel, Channel.toRaw_name] at names

/-- The private initialization channel is owned only by its three inventory tables and verifier. -/
theorem afterInitialTables_silent (image : ProgramImage) :
    ∀ component ∈ afterInitialTables (p := p) image,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels :=
    fun used => initialChannel_not_old (sp1Ensemble_tables_channels_subset component member used)
  simp only [afterInitialTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((member | rfl) | member) | member
  · simp only [OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉
        [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
          byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
          memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
      simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
        memoryChannel, byteChannel, Channel.toRaw]
    · change (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉
        [byteChannel.toRaw, byteChannel.toRaw,
          (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
          byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
          memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
      simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
        memoryChannel, byteChannel, Channel.toRaw]
    · change (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉
        [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
          (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
      simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
        byteChannel, Channel.toRaw]
  · change (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ [programChannel.toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel, Channel.toRaw]
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

private theorem verifier_initial_interactions (image : ProgramImage) (env : Environment (ZMod p)) :
    (verifierInteractions image).circuitOperations.interactionValuesWith
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw env =
      [(OrderedBoundary.channel OrderedInitialProvider.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel OrderedInitialProvider.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have original : ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).interactionsWith
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw =
      [((OrderedBoundary.channel OrderedInitialProvider.channelName).pushed (const (OrderedMemoryEnsemble.startKey (p := p)))).toRaw,
       ((OrderedBoundary.channel OrderedInitialProvider.channelName).pulled (const (OrderedMemoryEnsemble.endKey (p := p)))).toRaw] := by
    simp [Operations.interactionsWith, verifierMain, GeneralFormalCircuit.toSubcircuit_interactions,
      sp1StateVerifier, sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      stateChannel, byteChannel, exitChannel, circuit_norm]
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations,
    Operations.interactionValuesWith, Operations.interactionsWith, verifierInteractions_interactions]
  change (((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).interactionsWith _).map _ = _
  rw [original]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]

/-- Restricting the public verifier to initialization preserves the exact private-channel ledger. -/
theorem initialWitness_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (initialWitness witness).interactionsWith (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw := by
  have different : bootChannel (p := p) image ≠
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw := by
    intro equal
    exact (VerifierChannel.fresh "sp1.native.boot" (baseEnsemble (p := p) image)).unregistered
      (show bootChannel image ∈ (baseEnsemble image).channels from equal.symm ▸ List.mem_cons_self ..)
  change _ = (verifierProgram image _).circuitOperations.interactionValuesWith _
    (Environment.fromInput witness.publicInput witness.data) ++ _
  rw [verifierProgram_values, Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil,
    verifier_initial_interactions]
  apply congrArg (fun front => front ++ witness.tableContext.interactionsWith
    (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw)
  change (OrderedBoundaryVerifier.verifierProgram _ _ _).circuitOperations.interactionValuesWith _ _ = _
  simp only [OrderedBoundaryVerifier.verifierProgram, Verifier.Program.circuitOperations,
    Verifier.Program.operations, Verifier.ofInteractions_values]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- Raw constraints and actual balance force a unique initial record per decoded register/RAM
location, including across the two different physical provider tables. -/
theorem initial_records_locations_nodup {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((InitialMemoryEnsemble.records (initialWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply (InitialMemoryEnsemble.inventory image).records_locations_nodup_of_tables
    (initialWitness witness) (fun component member => ?_) (initialTables_spec witness constraints balanced)
  · change BalancedInteractions ((initialWitness witness).interactionsWith _)
    rw [initialWitness_interactions]
    exact balanced _ (List.mem_append_left _ (List.mem_cons_self ..))
  · rcases List.mem_append.mp member with native | fixed
    · exact afterInitialTables_silent image component native
    · obtain rfl := List.mem_singleton.mp fixed
      change (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉
        [(InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw]
      simp [InitialMemoryLookup.membership, StaticTable.channel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName, Channel.toRaw]


omit [Fact (2 ^ 24 < p)] in
theorem component_spec_of_byte (component : Component (ZMod p))
    (channels : component.circuit.channelsWithGuarantees ⊆
      [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw])
    (env : Environment (ZMod p)) (assumptions : component.CircuitAssumptions env)
    (constraints : component.operations.ConstraintsHold env)
    (byte : component.operations.ChannelGuarantees byteChannel.toRaw env) : component.Spec env := by
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (component.inChannelsOrGuarantees env)]
  intro channel member
  have member := channels member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _
  · exact byte
  · exact Operations.channelGuarantees_of_trivial _ (by simp [exitChannel, Channel.toRaw]) _ _
  all_goals exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _

/-- The public start state is fixed to the image's entry and boot clock by the actual verifier,
and both public endpoints have canonical limbs. -/
theorem public_boot {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    witness.publicInput.LimbBounds ∧ witness.publicInput.BootFor image := by
  have boot := (boot_balanced_iff witness).mp
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have byte := (finishedChannel_guarantees image witness constraints balanced).1.1
  have sourceByte : ({ circuit := verifier image } : Component (ZMod p)).operations.ChannelGuarantees
      byteChannel.toRaw (Environment.fromInput witness.publicInput witness.data) := by
    intro interaction member selected
    apply byte interaction ?_ selected
    simp only [ensemble, Ensemble.verifierOperations, verifierProgram,
      Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.operations_bind,
      Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append,
      Operations.interactions_append, List.mem_append]
    left
    change interaction ∈ ((verifierInteractions image).main (varFromOffset SP1PublicIO 0)).circuitOperations.interactions
    rw [verifierInteractions_interactions]
    simpa only [Component.interactions_eq, Component.rowOperations, verifier, verifierMain,
      GeneralFormalCircuit.toSubcircuit_interactions, sp1StateVerifier,
      sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
      circuit_norm] using member
  have checked : ({ circuit := verifier image } : Component (ZMod p)).operations.ConstraintsHold
      (Environment.fromInput witness.publicInput witness.data) := by
    rw [Operations.ConstraintsHold, Component.constraints_eq, Component.lookups_eq]
    change (∀ expression ∈ ((verifierMain image (varFromOffset SP1PublicIO 0)).operations (size SP1PublicIO)).constraints,
      Expression.eval (Environment.fromInput witness.publicInput witness.data) expression = 0) ∧ _
    constructor
    · have checks := (verifierChecks_iff image (Environment.fromInput witness.publicInput witness.data)).mpr
        (by simpa only [ProvableType.eval_fromInput_varFromOffset_zero] using boot)
      simpa only [verifierMain_constraints] using checks
    · simp [Component.rowOperations, verifier, verifierMain, sp1StateVerifier, sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
        circuit_norm]
  have spec := component_spec_of_byte ({ circuit := verifier image } : Component (ZMod p))
    (List.Subset.refl _) _ (by trivial) checked sourceByte
  simpa only [Component.Spec, verifier, Component.rowInput, circuit_norm,
    ProvableType.valueFromOffset_zero_fromInput_eq] using spec

private theorem programIndex_bound {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : 6 < witness.tables.length := by
  rw [← witness.same_length]
  have := tables_length (p := p) image
  change 6 < (tables image).length
  omega

/-- The sole Program provider in the combined assembly. -/
def programTable {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image)) : Table (ZMod p) :=
  witness.tables[6]'(programIndex_bound witness)

theorem programTable_component {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (programTable witness).component = ({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)) :=
  (witness.same_circuits 6 (by change 6 < (tables image).length; rw [tables_length]; decide)).symm

/-- Every physical Program row is authenticated against this image's ROM and official Sail,
including zero-multiplicity rows. No provider-validity premise is supplied. -/
theorem program_row_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints)
    (row : Array (ZMod p)) (member : row ∈ (programTable witness).table) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg (({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)).rowInput
        (Environment.fromArray row witness.data)).toMessage) := by
  have checked := constraints (programTable witness) (List.getElem_mem (programIndex_bound witness)) row member
  rw [programTable_component witness] at checked
  exact DecodedProgramProvider.constraints_committed valid _ checked

/-- The authenticated initial inventory is exactly the physical Memory push list.
Together with authentication and uniqueness, this is the initialization interface for grounding. -/
theorem initial_memory_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (witness.tables.take 3).flatMap (·.interactionsWith witness.data memoryChannel.toRaw) =
      (InitialMemoryEnsemble.records (initialWitness witness)).map memoryChannel.pushedValue :=
  InitialMemoryEnsemble.memory_interactions_eq (initialWitness witness)

end SP1Clean.Soundness.NativeCore
