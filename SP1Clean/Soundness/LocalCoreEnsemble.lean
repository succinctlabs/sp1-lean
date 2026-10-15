import SP1Clean.Soundness.NativeCoreEnsemble
import SP1Clean.Soundness.SnapshotMemoryEnsemble
import SP1Clean.Native.Operations.LocalSourceBoundary

/-! # Native local-shard assembly with a checked complete source

This assembly installs source register/RAM tables alongside the existing finalizers, fixed ROM,
instructions, and providers. The verifier checks the finite program, supported decoding, complete
Sail platform configuration and register initialization, source ROM, and 48-bit source PC/clock.
It binds the public incoming State token to that actual PC and clock; outgoing fields are range
checked. A stopped source must retain the same clock at the public end, excluding active events
through strict State ordering while admitting identity segments. ROM is checked even at bytes
absent from the touched inventory.

Byte and Program closure follow from this assembly's own raw ledger. Source State truth and the
initial memory invariant are derived in `LocalCoreSourceGrounding`. The mixed host walk, complete
outgoing state, and witness composition remain open; this assembly is not yet an execution theorem.
Host state and Sail bookkeeping are retained source data, without a reset at a shard cut.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

def verifierMain (image : ProgramImage) (source : ExecutionSnapshot)
    (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← sp1StateVerifier input
  let _ ← LocalSourceBoundary.circuit image source input
  let _ ← OrderedBoundaryVerifier.circuit SnapshotMemoryEnsemble.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()
  let _ ← OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()

def verifier (image : ProgramImage) (source : ExecutionSnapshot) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := verifierMain image source
  Spec input _ _ := input.LimbBounds ∧ ExecutionSourceValid image source ∧
    input.SourceFor source ∧ input.PreservesStoppedClock source
  ProverAssumptions input data hint :=
    sp1StateVerifier.ProverAssumptions input data hint ∧ ExecutionSourceValid image source ∧
      input.SourceFor source ∧ input.PreservesStoppedClock source
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, LocalSourceBoundary.circuit,
      OrderedBoundaryVerifier.circuit]
    exact h_holds
  completeness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, LocalSourceBoundary.circuit,
      OrderedBoundaryVerifier.circuit]
    exact h_assumptions

/-- State and fixed ordering traffic share the existing certified verifier programs. -/
def boundaryVerifier : Verifier.Program (ZMod p) SP1PublicIO where
  main input := do
    sp1StateVerifierProgram.main input
    (OrderedBoundaryVerifier.verifierProgram SnapshotMemoryEnsemble.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).main ()
    (OrderedBoundaryVerifier.verifierProgram OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).main ()
  Spec input _ := input.LimbBounds
  soundness := by
    intro env guarantees
    simp only [Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.FullGuarantees,
      Operations.interactions_append, List.forall_mem_append] at guarantees
    exact sp1StateVerifierProgram.soundness env guarantees.1

/-- Every outgoing boundary requirement holds without an execution premise. -/
theorem boundaryVerifier_requirements (env : Environment (ZMod p)) :
    (boundaryVerifier (p := p)).circuitOperations.FullRequirements env := by
  simp [boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
    Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.ofInteractions,
    Verifier.Operations.circuitOperations, Verifier.Operations.interactions,
    Operations.FullRequirements,
    sp1StateVerifierMain, OrderedBoundaryVerifier.main, AbstractInteraction.Requirements,
    ChannelInteraction.toRaw, stateChannel, byteChannel, exitChannel,
    OrderedBoundary.channel, Channel.toRaw, circuit_norm]

/-- Native execution components followed by the source's fixed membership provider. -/
def afterSourceTables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  NativeCore.afterInitialTables image ++ [SnapshotMemoryEnsemble.registerMembership source.sail.memorySnapshot,
    SnapshotMemoryEnsemble.ramMembership source.sail.memorySnapshot]

def tables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component) ++ afterSourceTables image source

/-- Byte guarantees suffice for the State verifier's endpoint bounds; ordering traffic is structural. -/
theorem boundaryVerifier_limbBounds (input : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p))
    (byte : (boundaryVerifier (p := p)).circuitOperations.ChannelGuarantees byteChannel.toRaw
      (Environment.fromInput input data)) : input.LimbBounds := by
  have channels : (boundaryVerifier (p := p)).channelsWithGuarantees ⊆
      [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
        (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] := by
    intro channel member
    simpa [boundaryVerifier, sp1StateVerifierProgram, OrderedBoundaryVerifier.verifierProgram,
      OrderedBoundaryVerifier.main, Verifier.ofInteractions, circuit_norm] using member
  have guarantees : (boundaryVerifier (p := p)).circuitOperations.FullGuarantees
      (Environment.fromInput input data) := by
    rw [Operations.guarantees_iff _ _ _ (boundaryVerifier.operations.inChannelsOrGuaranteesFull _)]
    intro channel member
    have member := channels member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _
    · exact byte
    · exact Operations.channelGuarantees_of_trivial _ (by simp [exitChannel, Channel.toRaw]) _ _
    all_goals exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _
  simpa only [boundaryVerifier, ProvableType.eval_fromInput_varFromOffset_zero] using
    boundaryVerifier.soundness (Environment.fromInput input data) guarantees

/-- The physical inventory and existing boundary traffic, before installing source assertions. -/
def baseEnsemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source
  unique_names := by
    simp only [tables, afterSourceTables, List.map_append, List.map_cons, List.map_nil,
      SnapshotMemoryEnsemble.registerMembership, SnapshotMemoryEnsemble.ramMembership,
      InitialMemoryLookup.membership, StaticTable.component, StaticTable.provider,
      MemorySnapshot.registerTable, StaticTable.ofRows, InitialMemoryLookup.membership]
    exact of_decide_eq_true rfl
  channels := (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ::
    source.sail.memorySnapshot.registerTable.channel.toRaw :: (InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw :: sp1Ensemble.channels
  verifier := boundaryVerifier

/-- Install all eight source checks with the generic public-assertion adapter. -/
def ensemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO :=
  (LocalSourceBoundary.checker image source).install (baseEnsemble image source)

/-- The assertion channel is separated from registered names and all actual existing traffic. -/
def sourceChannel (image : ProgramImage) (source : ExecutionSnapshot) : RawChannel (ZMod p) :=
  (LocalSourceBoundary.checker image source).channel (baseEnsemble image source)

/-- Source-channel balance enforces the complete original contract and its occurrence bound. -/
theorem source_balanced_iff {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    witness.BalancedChannel (sourceChannel image source) ↔
      LocalSourceBoundary.Spec image source witness.publicInput := by
  apply Iff.trans ?_ ((LocalSourceBoundary.checker image source).program_balanced_iff
    (baseEnsemble image source) witness.publicInput witness.data |>.trans ?_)
  · exact (congrArg BalancedInteractions
      ((LocalSourceBoundary.checker image source).installed_check_interactions
        (ens := baseEnsemble image source) witness)).to_iff
  · rw [LocalSourceBoundary.checks_iff]
    exact and_iff_right (LocalSourceBoundary.count_bound image source)

/-- The installed public verifier proves every outgoing requirement locally. -/
theorem verifier_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (env : Environment (ZMod p)) :
    (ensemble (p := p) image source).verifierOperations.FullRequirements env := by
  change (boundaryVerifier.andThen ((LocalSourceBoundary.checker image source).program
    (baseEnsemble image source))).circuitOperations.FullRequirements env
  rw [Verifier.Program.andThen_requirements]
  exact ⟨boundaryVerifier_requirements env, Verifier.checkZeros_requirements _ _ _⟩

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).length = 61 := by
  simp [tables, afterSourceTables, SnapshotMemoryEnsemble.inventory, NativeCore.afterInitialTables,
    OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
    sp1Tables_length, sp1ProviderTables_length]

private theorem source_requirements (source : ExecutionSnapshot) (component : Component (ZMod p))
    (member : component ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw] := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [SnapshotMemoryEnsemble.registerView, SnapshotMemoryEnsemble.ramView,
      SnapshotMemoryEnsemble.terminalView, OrderedMemoryEnsemble.providerView,
      OrderedMemoryEnsemble.terminalView, OrderedMemoryProvider.circuit,
      OrderedBoundaryEnd.circuit, SnapshotRegisterProvider.circuit, SnapshotRamProvider.circuit]

private theorem component_finished_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
      source.sail.memorySnapshot.registerTable.channel.toRaw,
      (InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  simp only [ensemble, PublicVerifier.install, baseEnsemble, tables, List.mem_append] at member
  rcases member with member | member
  · exact absent (fun required => outside (by
      have used := source_requirements source component member required
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
      tauto))
  · rcases List.mem_append.mp member with native | fixed
    · exact NativeCore.afterInitialTables_finished_requirements image component native channel
        (fun inside => outside (List.mem_append_left _ inside)) env constraints
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with rfl | rfl
      all_goals
        apply absent
        intro used
        apply outside
        simp only [SnapshotMemoryEnsemble.registerMembership, SnapshotMemoryEnsemble.ramMembership,
          StaticTable.component, StaticTable.provider, List.mem_cons, List.not_mem_nil, or_false] at used ⊢
        tauto

/-- The local assembly supplies its own Byte and Program guarantees, including for both
source providers. No provider validity or memory-content premise is accepted here. -/
theorem finishedChannel_guarantees (image : ProgramImage) (source : ExecutionSnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw ∧
      (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data programChannel.toRaw) ∧
    ∀ table ∈ witness.tables,
      table.ChannelGuarantees witness.data byteChannel.toRaw ∧
        table.ChannelGuarantees witness.data programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (baseEnsemble (p := p) image source).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
        (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        source.sail.memorySnapshot.registerTable.channel.toRaw,
      (InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw]) :
      (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data channel ∧
        ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel := by
    apply witness.channelGuarantees_of_component_requirements channel constraints
      (balanced channel (List.mem_append_left _ member))
    · intro input data interaction emitted _
      exact verifier_requirements image source _ interaction emitted
    · exact fun component mem env holds =>
        component_finished_requirements image source component mem channel outside env holds
  have byte := closed byteChannel.toRaw (by simp [baseEnsemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, byteChannel, StaticTable.channel,
      MemorySnapshot.registerTable, StaticTable.ofRows, InitialMemoryLookup.membership])
  have program := closed programChannel.toRaw (by simp [baseEnsemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, programChannel, StaticTable.channel,
      MemorySnapshot.registerTable, StaticTable.ofRows, InitialMemoryLookup.membership])
  exact ⟨⟨byte.1, program.1⟩, fun table member => ⟨(byte.2 table member), (program.2 table member)⟩⟩

/-- Program guarantees use only this channel's balance, so host extensions can retain their
complete Memory ledger while reusing the fixed program provider. -/
theorem program_guarantees_of_balance (image : ProgramImage) (source : ExecutionSnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw) :
    (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data programChannel.toRaw ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data programChannel.toRaw := by
  apply witness.channelGuarantees_of_component_requirements programChannel.toRaw constraints balanced
  · intro input data interaction emitted _
    exact verifier_requirements image source _ interaction emitted
  · exact fun component mem env holds => component_finished_requirements image source component mem
      programChannel.toRaw (by simp [circuit_norm, OrderedBoundary.channel,
        SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, programChannel,
        StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows, InitialMemoryLookup.membership]) env holds

/-- Fixed register rows discharge every provider requirement. Channel balance then authenticates
the sparse source requests against those rows, using the witness's canonical prover data. -/
theorem membership_guarantees_of_balance (image : ProgramImage) (source : ExecutionSnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (channel : RawChannel (ZMod p))
    (known : channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot)
    (balanced : witness.BalancedChannel channel) :
    (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data
        channel ∧
      ∀ table ∈ witness.tables,
        table.ChannelGuarantees witness.data channel := by
  let : channel.Consistent := by
    rcases List.mem_cons.mp known with rfl | known
    · infer_instance
    · obtain rfl := List.mem_singleton.mp known
      infer_instance
  apply witness.channelGuarantees_of_requirements _ balanced
  · intro interaction emitted _
    exact verifier_requirements image source _ interaction emitted
  · intro table member
    have location := EnsembleWitness.mem_component_of_mem member
    simp only [ensemble, PublicVerifier.install, baseEnsemble, tables, afterSourceTables,
      List.mem_append] at location
    rcases location with sourceTable | native | fixed
    · intro row rowMember
      apply Operations.requirements_of_not_mem _ _ _
        (table.component.inChannelsOrRequirements_of_constraints _
          (constraints table member row rowMember))
      intro required
      have used := source_requirements source table.component sourceTable required
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl
      all_goals simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows,
        memoryChannel, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
        Channel.toRaw] at used
    · intro row rowMember
      apply NativeCore.afterInitialTables_finished_requirements image table.component native _ ?_
        _ (constraints table member row rowMember)
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl
      all_goals simp [StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows,
        stateChannel, memoryChannel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName,
        OrderedFinalProvider.channelName, Channel.toRaw]
    · have assumptions : table.Assumptions witness.data := by
        intro row _
        rcases List.mem_cons.mp fixed with fixed | fixed
        · rw [fixed]; trivial
        · rw [List.mem_singleton.mp fixed]; trivial
      intro row rowMember interaction emitted _
      exact (table.component.weakSoundness_of_no_guarantees (by
          rcases List.mem_cons.mp fixed with fixed | fixed
          · rw [fixed]; rfl
          · rw [List.mem_singleton.mp fixed]; rfl)
        (table.circuitAssumptions (witness.data_consistent table member) assumptions row rowMember)
        (constraints table member row rowMember)).2 interaction emitted

/-- Exactly the channel facts used by chronology, including the installed public source checks.
Byte guarantees may be transported from a larger ensemble without projecting its Byte
multiplicities or its Memory effects. -/
structure OrderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : Prop where
  verifierByte : (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw
  byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw
  sourceChecks : witness.BalancedChannel (sourceChannel image source)
  state : witness.BalancedChannel stateChannel.toRaw

/-- A static local-component interface for deriving Byte guarantees in a larger assembly. -/
theorem component_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  apply component_finished_requirements image source component member byteChannel.toRaw ?_ env constraints
  simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
    OrderedFinalProvider.channelName, byteChannel, StaticTable.channel,
    MemorySnapshot.registerTable, StaticTable.ofRows, InitialMemoryLookup.membership]

/-- The local assembly derives the ordering interface from its Byte, State, and source-check ledgers. -/
theorem orderingChannels_of_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints)
    (byte : witness.BalancedChannel byteChannel.toRaw) (state : witness.BalancedChannel stateChannel.toRaw)
    (sourceChecks : witness.BalancedChannel (sourceChannel image source)) : OrderingChannels witness := by
  have closed : (ensemble image source).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw ∧
      ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw := by
    apply witness.channelGuarantees_of_component_requirements byteChannel.toRaw constraints byte
    · intro input data interaction emitted _
      exact verifier_requirements image source _ interaction emitted
    · exact fun component member env checked => component_byte_requirements image source component member env checked
  exact ⟨closed.1, closed.2, sourceChecks, state⟩

/-- Existing complete witnesses supply the smaller chronology interface. -/
theorem orderingChannels_of_balanced {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) : OrderingChannels witness :=
  orderingChannels_of_constraints witness constraints
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels]))
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels]))
    (balanced _ (List.mem_append_right _ (List.mem_singleton_self _)))

end SP1Clean.Soundness.LocalCore
