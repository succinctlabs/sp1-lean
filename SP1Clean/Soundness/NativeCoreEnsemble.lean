import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.InitialMemoryEnsemble
import SP1Clean.Soundness.FinalMemoryEnsemble
import SP1Clean.Alignment.Chips.DecodedProgramProvider.Bridge
import SP1Clean.FormalModel.Contracts.NativeCoreBoundary
import ToClean.Air.VerifierChannel
import ToClean.Circuit.SubcircuitProjection

/-! # Image-authenticated native core assembly

This assembly replaces the legacy Program and memory-boundary providers with the fixed decoded
ROM and the ordered register/RAM inventories. The verifier fixes boot PC/time and both private
ordering boundaries. Its five public boot assertions use a fresh check channel, with exactly
ten occurrences and no additional physical table. Byte/Program closure uses the combined ledger.
Connecting this assembly to mixed-row timed grounding and the complete host environment remains separate work;
this module does not claim an execution theorem for the assembly.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

def verifierMain (image : ProgramImage) (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← sp1StateVerifier input
  assertZero input.init_clk_high
  assertZero (input.init_clk_low - 1)
  assertZero (input.init_pc0 - .const (bitVecToWord image.entry)[0])
  assertZero (input.init_pc1 - .const (bitVecToWord image.entry)[1])
  assertZero (input.init_pc2 - .const (bitVecToWord image.entry)[2])
  let _ ← OrderedBoundaryVerifier.circuit OrderedInitialProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()
  let _ ← OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()

def verifier (image : ProgramImage) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := verifierMain image
  Spec input _ _ := input.LimbBounds ∧ input.BootFor image
  ProverAssumptions input data hint :=
    sp1StateVerifier.ProverAssumptions input data hint ∧ input.BootFor image
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, SP1PublicIO.BootFor,
      OrderedBoundaryVerifier.circuit]
    simpa only [sub_eq_zero] using h_holds
  completeness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, SP1PublicIO.BootFor,
      OrderedBoundaryVerifier.circuit]
    simpa only [sub_eq_zero] using h_assumptions

/-- The remaining core components, after the initialization inventory. -/
def afterInitialTables (image : ProgramImage) : List (Component (ZMod p)) :=
  FinalMemoryEnsemble.inventory.views.map (·.component) ++
    [{ circuit := DecodedProgramProvider.circuit image }] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

/-- Fixed intervals authenticate boot RAM requests through the same channel as local snapshots. -/
def ramMembership (image : ProgramImage) : Component (ZMod p) :=
  (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").component

/-- Both memory inventories precede ordinary instructions; the order is an assembly detail.
The legacy unauthenticated Program/init/final providers are absent. -/
def tables (image : ProgramImage) : List (Component (ZMod p)) :=
  (InitialMemoryEnsemble.views image).map (·.component) ++ (afterInitialTables image ++ [ramMembership image])

/-- The boot verifier retains exactly its five public assertions. -/
theorem verifierMain_constraints (image : ProgramImage) (input : Var SP1PublicIO (ZMod p))
    (offset : ℕ) :
    ((verifierMain image input).operations offset).constraints =
      [input.init_clk_high, input.init_clk_low - 1,
        input.init_pc0 - .const (bitVecToWord image.entry)[0],
        input.init_pc1 - .const (bitVecToWord image.entry)[1],
        input.init_pc2 - .const (bitVecToWord image.entry)[2]] := by
  simp [verifierMain, sp1StateVerifier,
    sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main, circuit_norm]

private theorem verifierInteractions_admitted (image : ProgramImage) (input : Var SP1PublicIO (ZMod p)) :
    ∀ interaction ∈ ((verifierMain image input).operations 0).interactions, ∀ env,
      if interaction.assumeGuarantees then interaction.Requirements env else interaction.Guarantees env := by
  intro interaction member env
  simp only [verifierMain, GeneralFormalCircuit.toSubcircuit_interactions,
    sp1StateVerifier, sp1StateVerifierMain, OrderedBoundaryVerifier.circuit,
    OrderedBoundaryVerifier.main, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AbstractInteraction.Requirements, AbstractInteraction.Guarantees,
      ChannelInteraction.toRaw, stateChannel, byteChannel, exitChannel,
      OrderedBoundary.channel, Channel.toRaw, circuit_norm]

/-- Literal source interactions, admitted through Clean's verifier operations. -/
def verifierInteractions (image : ProgramImage) : Verifier.Program (ZMod p) SP1PublicIO where
  main input := Verifier.ofInteractions ((verifierMain image input).operations 0).interactions
    (verifierInteractions_admitted image input)

theorem verifierInteractions_interactions (image : ProgramImage) (input : Var SP1PublicIO (ZMod p)) :
    ((verifierInteractions image).main input).circuitOperations.interactions =
      ((verifierMain image input).operations 0).interactions :=
  Verifier.ofInteractions_interactions _ (verifierInteractions_admitted image input)

/-- Enforce the original boot contract using the existing public-assertion adapter. -/
def verifierProgram (image : ProgramImage) (checkName : String) :
    Verifier.Program (ZMod p) SP1PublicIO where
  main input := do
    (verifierInteractions image).main input
    Verifier.checkZeros checkName ((verifierMain image input).operations 0).constraints
  Spec input _ := input.LimbBounds ∧ input.BootFor image
  soundness := by
    intro env guarantees
    simp only [Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.FullGuarantees,
      Operations.interactions_append, List.forall_mem_append] at guarantees
    have original : ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).FullGuarantees env := by
      have imported := guarantees.1
      change ((verifierInteractions image).main (varFromOffset SP1PublicIO 0)).circuitOperations.FullGuarantees env at imported
      simpa only [Operations.FullGuarantees, verifierInteractions_interactions] using imported
    have checks := (Verifier.checkZeros_guarantees checkName _ env).mp guarantees.2
    have checked : ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).ConstraintsHold env := by
      refine ⟨checks, ?_⟩
      simp [verifierMain, sp1StateVerifier,
        sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main, circuit_norm]
    exact ((verifier image).original_full_soundness 0 env (varFromOffset SP1PublicIO 0)
      trivial checked original).1

/-- Original boundary pushes and assertion checks prove all verifier requirements locally. -/
theorem verifierProgram_requirements (image : ProgramImage) (checkName : String)
    (env : Environment (ZMod p)) :
    (verifierProgram (p := p) image checkName).circuitOperations.FullRequirements env := by
  change ((verifierInteractions image).main (varFromOffset SP1PublicIO 0) >>= fun _ =>
    Verifier.checkZeros checkName
      ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).constraints).circuitOperations.FullRequirements env
  simp only [Verifier.circuitOperations, Verifier.operations_bind,
    Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append,
    Operations.FullRequirements, Operations.interactions_append, List.forall_mem_append]
  constructor
  · change ((verifierInteractions image).main (varFromOffset SP1PublicIO 0)).circuitOperations.FullRequirements env
    rw [Operations.FullRequirements, verifierInteractions_interactions]
    simp [verifierMain, GeneralFormalCircuit.toSubcircuit_interactions, sp1StateVerifier,
      sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
      AbstractInteraction.Requirements, ChannelInteraction.toRaw, stateChannel, byteChannel,
      exitChannel, OrderedBoundary.channel, Channel.toRaw, circuit_norm]
  · exact Verifier.checkZeros_requirements _ _ _

/-- The public verifier retains every original occurrence and appends only its assertion checks. -/
theorem verifierProgram_values (image : ProgramImage) (checkName : String)
    (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    (verifierProgram image checkName).circuitOperations.interactionValuesWith channel env =
      (verifierInteractions image).circuitOperations.interactionValuesWith channel env ++
        (Verifier.checkZeros checkName
          ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).constraints
          ).circuitOperations.interactionValuesWith channel env := by
  simp only [verifierProgram, Verifier.Program.circuitOperations, Verifier.Program.operations,
    Verifier.operations_bind, Verifier.Operations.circuitOperations, Verifier.Operations.interactions,
    List.map_append, Operations.interactionValuesWith, Operations.interactionsWith,
    Operations.interactions_append, List.filter_append]

/-- The source circuit's literal assertions are exactly the public boot contract. -/
theorem verifierChecks_iff (image : ProgramImage) (env : Environment (ZMod p)) :
    (∀ expression ∈ ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).constraints,
      Expression.eval env expression = 0) ↔
      (Eval.eval env (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p))).BootFor image := by
  simp [verifierMain_constraints, SP1PublicIO.BootFor, circuit_norm, sub_eq_zero]

/-- The original physical inventory and boundary traffic, before adding boot assertion checks. -/
def baseEnsemble (image : ProgramImage) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image
  unique_names := by exact of_decide_eq_true rfl
  channels := (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ::
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ::
    (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw :: sp1Ensemble.channels
  verifier := verifierInteractions image

/-- The boot assertions have a channel disjoint from all registered and actual traffic. -/
def bootChannel (image : ProgramImage) : RawChannel (ZMod p) :=
  VerifierChannel.channel "sp1.native.boot" (baseEnsemble image)

def ensemble (image : ProgramImage) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image
  unique_names := (baseEnsemble image).unique_names
  channels := (baseEnsemble image).channels ++ [bootChannel image]
  verifier := verifierProgram image (VerifierChannel.channelName "sp1.native.boot" (baseEnsemble (p := p) image))

/-- Boot assertions preserve the complete verifier ledger on every registered base channel. -/
theorem verifier_values_of_registered (image : ProgramImage) (env : Environment (ZMod p))
    (channel : RawChannel (ZMod p)) (registered : channel ∈ (baseEnsemble image).channels) :
    (ensemble image).verifierOperations.interactionValuesWith channel env =
      (baseEnsemble image).verifierOperations.interactionValuesWith channel env := by
  have different : bootChannel (p := p) image ≠ channel := by
    intro same
    apply (VerifierChannel.fresh "sp1.native.boot" (baseEnsemble (p := p) image)).unregistered
    change bootChannel image ∈ (baseEnsemble image).channels
    rwa [same]
  change (verifierProgram image _).circuitOperations.interactionValuesWith channel env = _
  rw [verifierProgram_values, Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil]
  rfl

/-- No old verifier or physical row can contribute to the fresh boot channel. -/
theorem boot_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    witness.interactionsWith (bootChannel image) =
      (Verifier.checkZeros (VerifierChannel.channelName "sp1.native.boot" (baseEnsemble (p := p) image))
        ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).constraints
        ).circuitOperations.interactionValuesWith (bootChannel image)
          (Environment.fromInput witness.publicInput witness.data) := by
  have fresh := VerifierChannel.fresh "sp1.native.boot" (baseEnsemble (p := p) image)
  have physical : witness.tableContext.interactionsWith (bootChannel image) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply List.flatMap_eq_nil_iff.mpr
    intro row _
    exact fresh.tables table.component
      (EnsembleWitness.mem_component_of_mem (witness := witness) member) _
  change (verifierProgram image _).circuitOperations.interactionValuesWith (bootChannel image)
    (Environment.fromInput witness.publicInput witness.data) ++ _ = _
  rw [verifierProgram_values, show (verifierInteractions image).circuitOperations.interactionValuesWith
      (bootChannel image) (Environment.fromInput witness.publicInput witness.data) = [] from fresh.verifier _,
    List.nil_append, physical, List.append_nil]

/-- Five assertions always contribute ten occurrences, including checks whose value is zero. -/
theorem boot_interactions_length {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (witness.interactionsWith (bootChannel image)).length = 10 := by
  rw [boot_interactions]
  simp only [bootChannel, VerifierChannel.channel]
  rw [Verifier.checkZeros_values, verifierMain_constraints]
  simp

/-- Boot-channel balance is exactly the original public boot contract. The field bound already
pays for all ten assertion occurrences; no caller-supplied readiness or count premise is needed. -/
theorem boot_balanced_iff {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    witness.BalancedChannel (bootChannel image) ↔ witness.publicInput.BootFor image := by
  rw [EnsembleWitness.BalancedChannel, boot_interactions]
  change BalancedInteractions ((Verifier.checkZeros
    (VerifierChannel.channelName "sp1.native.boot" (baseEnsemble (p := p) image))
    ((verifierMain image (varFromOffset SP1PublicIO 0)).operations 0).constraints
    ).circuitOperations.interactionValuesWith (Verifier.zeroChannel _).toRaw
      (Environment.fromInput witness.publicInput witness.data)) ↔ _
  rw [Verifier.checkZeros_balanced_iff]
  have bound : 2 * ((verifierMain (p := p) image (varFromOffset SP1PublicIO 0)).operations 0).constraints.length <
      ringChar (ZMod p) := by
    simp only [verifierMain_constraints, List.length_cons, List.length_nil, ZMod.ringChar_zmod_n]
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  simp only [bound, true_or, true_and, verifierChecks_iff,
    ProvableType.eval_fromInput_varFromOffset_zero]

theorem tables_length (image : ProgramImage) : (tables (p := p) image).length = 60 := by
  simp [tables, afterInitialTables, InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, sp1Tables_length, sp1ProviderTables_length]

private theorem boundary_requirements (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (InitialMemoryEnsemble.views image).map (·.component) ++
      FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] := by
  simp only [InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    simp [InitialMemoryEnsemble.registerView, InitialMemoryEnsemble.ramView,
      InitialMemoryEnsemble.providerView, InitialMemoryEnsemble.terminalView,
      FinalMemoryEnsemble.viewFor, FinalMemoryEnsemble.registerView, FinalMemoryEnsemble.ramView,
      OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
      OrderedMemoryProvider.circuit, OrderedBoundaryEnd.circuit,
      InitialRegisterProvider.circuit, InitialRamProvider.circuit,
      FinalRegisterProvider.circuit, FinalRamProvider.circuit]

/-- The shared instruction/finalizer/provider suffix closes Byte and Program requirements.
This proof is independent of the choice of source inventory and boot/local verifier. -/
theorem afterInitialTables_finished_requirements (image : ProgramImage)
    (component : Component (ZMod p)) (member : component ∈ afterInitialTables (p := p) image)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :=
    sp1_component_finished_requirements component member channel
      (fun mem => outside (by simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢; tauto))
      env constraints
  simp only [afterInitialTables, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at member
  rcases member with ((member | rfl) | member) | member
  · exact absent (fun required => outside (List.mem_cons_of_mem _
      (boundary_requirements image component (List.mem_append_right _ member) required)))
  · have required := (Component.weakSoundness_of_no_guarantees
      ({ circuit := DecodedProgramProvider.circuit image } : Component (ZMod p)) rfl (by trivial) constraints).2
    exact fun interaction emitted _ => required interaction emitted
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

/-- New boundary tables preserve closure of Byte/Program: their only outgoing nontrivial
requirements are Memory. The fixed Program provider proves its own requirements. -/
private theorem component_finished_requirements (image : ProgramImage)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image).tables)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
      (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  simp only [ensemble, tables, List.mem_append] at member
  rcases member with member | member | fixed
  · exact absent (fun required => outside (List.mem_cons_of_mem _
      (by
        have used := boundary_requirements image component (List.mem_append_left _ member) required
        simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
        tauto)))
  · exact afterInitialTables_finished_requirements image component member channel (fun inside => outside (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
      tauto)) env constraints

  · obtain rfl := List.mem_singleton.mp fixed
    apply absent
    change channel ∉ [(InitialMemoryLookup.membership image.initialMemory (2 ^ 48)
      "sp1.native.initial_memory").channel.toRaw]
    intro used
    apply outside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
    tauto

/-- Byte and Program guarantees hold for the public verifier and every physical table. -/
theorem finishedChannel_guarantees (image : ProgramImage)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((ensemble image).VerifierChannelGuarantees witness.publicInput witness.data byteChannel.toRaw ∧
      (ensemble image).VerifierChannelGuarantees witness.publicInput witness.data programChannel.toRaw) ∧
    ∀ table ∈ witness.tables,
      table.ChannelGuarantees witness.data byteChannel.toRaw ∧
        table.ChannelGuarantees witness.data programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (baseEnsemble (p := p) image).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw]) :
      (ensemble image).VerifierChannelGuarantees witness.publicInput witness.data channel ∧
        ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data channel := by
    apply witness.channelGuarantees_of_component_requirements channel constraints
      (balanced channel (List.mem_append_left _ member))
    · intro input data interaction emitted _
      exact verifierProgram_requirements image _ _ interaction emitted
    · exact fun component mem env holds =>
        component_finished_requirements image component mem channel outside env holds
  have byte := closed byteChannel.toRaw (by simp [baseEnsemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, OrderedInitialProvider.channelName,
      OrderedFinalProvider.channelName, byteChannel])
  have program := closed programChannel.toRaw (by simp [baseEnsemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, OrderedInitialProvider.channelName,
      OrderedFinalProvider.channelName, programChannel])
  exact ⟨⟨byte.1, program.1⟩, fun table member => ⟨byte.2 table member, program.2 table member⟩⟩

/-- Boot membership is derived from fixed columns and the assembly's own RAM ledger. -/
theorem ram_guarantees_of_balance (image : ProgramImage)
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel
      (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data
      (InitialMemoryLookup.membership image.initialMemory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw := by
  apply (witness.channelGuarantees_of_requirements _ balanced ?_ ?_).2
  · intro interaction emitted _
    exact verifierProgram_requirements image (bootChannel image).name _ interaction emitted
  · intro table member
    have location := EnsembleWitness.mem_component_of_mem member
    simp only [ensemble, tables, List.mem_append, List.mem_singleton] at location
    rcases location with initial | native | fixed
    · intro row rowMember
      apply Operations.requirements_of_not_mem _ _ _
        (table.component.inChannelsOrRequirements_of_constraints _ (constraints table member row rowMember))
      intro required
      have used := boundary_requirements image table.component (List.mem_append_left _ initial) required
      simp [StaticTable.channel, InitialMemoryLookup.membership, memoryChannel,
        OrderedBoundary.channel, OrderedInitialProvider.channelName,
        OrderedFinalProvider.channelName, Channel.toRaw] at used
    · intro row rowMember
      apply afterInitialTables_finished_requirements image table.component native _ ?_
        _ (constraints table member row rowMember)
      simp [StaticTable.channel, InitialMemoryLookup.membership,
        stateChannel, memoryChannel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName, OrderedFinalProvider.channelName, Channel.toRaw]
    · have assumptions : table.Assumptions witness.data := by
        intro row _
        rw [fixed]
        trivial
      intro row rowMember interaction emitted _
      exact (table.component.weakSoundness_of_no_guarantees (by rw [fixed]; rfl)
        (table.circuitAssumptions (witness.data_consistent table member) assumptions row rowMember)
        (constraints table member row rowMember)).2 interaction emitted

end SP1Clean.Soundness.NativeCore
