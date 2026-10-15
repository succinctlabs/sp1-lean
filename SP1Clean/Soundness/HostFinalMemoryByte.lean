import SP1Clean.Soundness.HostFinalMemory

/-! # Byte closure of the actual host/target assembly

Target RAM checks share the existing provider ledger. Their local contracts are established
before projecting to the earlier host proof views. The only interface parameter describes
the installed resource circuits; no witness validity, target agreement or grounding is assumed.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalByteLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalByteClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem not_required (component : Component (ZMod p))
    (quiet : (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = false)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _ (component.inChannelsOrRequirements_of_constraints env checked)
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = true at present
  rw [quiet] at present
  contradiction

private theorem checks_silent (target : MemorySnapshot) (channel : RawChannel (ZMod p))
    (quiet : (FinalMemoryChecks.checkTables (p := p) target).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true) :
    ∀ component ∈ FinalMemoryChecks.checkTables target, channel ∉ component.circuit.channels := by
  intro component member used
  have silent := List.all_eq_true.mp quiet component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

/-- The target consumers have a proved static host-resource interface. -/
theorem targetInterface (target : MemorySnapshot)
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    (interface : HostHintReadLocal.ExtensionInterface others resources) :
    HostHintReadLocal.ExtensionInterface others (resources ++ FinalMemoryChecks.checkTables target) := by
  apply interface.appendResources
  · constructor
    · intro component member env checked
      simp only [FinalMemoryChecks.checkTables, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact not_required _ (by rfl) env checked
    · exact checks_silent target stateChannel.toRaw (by rfl)
  · exact checks_silent target HostCallChip.channel.toRaw (by rfl)
  · exact checks_silent target HintReadWordChip.stateChannel.toRaw (by rfl)

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}

/-- Every Byte provider proves its own requirement in the complete installed component inventory. -/
theorem component_byte_requirements (interface : HostHintReadLocal.ExtensionInterface others resources)
    (component : Component (ZMod p))
    (member : component ∈ (ensemble image source target final bankFinal others resources channels names).tables)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  simp only [ensemble, ClosedVerifier.install, withReceipts, withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, base, HostHintQueueBoundary.ensemble,
    HaltPadding.install] at member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · rcases List.mem_or_eq_of_mem_set member with member | rfl
    · rcases List.mem_or_eq_of_mem_set member with member | rfl
      · exact HostLocalCore.component_byte_requirements image source _
          (HostHintReadLocal.auxiliaryInterface (targetInterface target interface)) component
          member env checked
      · exact not_required _ (by rfl) env checked
    · exact not_required _ (by rfl) env checked
  · exact not_required _ (by rfl) env checked

private theorem verifier_requirements (env : Environment (ZMod p)) :
    (ensemble image source target final bankFinal others resources channels names).verifierOperations.FullRequirements env := by
  change ((withReceipts image source target final bankFinal others resources channels names).verifier.andThen
    ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).program
      (withReceipts image source target final bankFinal others resources channels names))).circuitOperations.FullRequirements env
  rw [Verifier.Program.andThen_requirements]
  constructor
  · change ((HostHintReadLocal.ensemble image source others
      (resources ++ FinalMemoryChecks.checkTables target) channels names).verifier.andThen
        ((HostHintQueueBoundary.boundary source final bankFinal).program _)).circuitOperations.FullRequirements env
    rw [Verifier.Program.andThen_requirements]
    constructor
    · exact HostLocalCore.verifier_requirements env
    · apply ClosedVerifier.program_requirements
      simp only [ClosedVerifier.operations, HostHintQueueBoundary.boundary, HostBoundary.closed,
        HostBoundary.circuit, HostBoundary.main, circuit_norm,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [HostHintQueueBoundary.circuit,
        HostHintQueueBoundary.main, HostCommitEndpoint.circuit, HostCommitEndpoint.main,
        HostCommitBoundary.verifier, HostCommitBoundary.verifierMain,
        HostExitBoundary.circuit, HostExitBoundary.main, HostHintQueue.stateChannel,
        HostCommitChip.stateChannel, HostExitBoundary.channel, Channel.toRaw,
        GeneralFormalCircuit.toSubcircuit_interactions, AbstractInteraction.Requirements,
        ChannelInteraction.toRaw, or_imp, forall_and, circuit_norm]
  · apply ClosedVerifier.program_requirements
    simp [ClosedVerifier.operations, FinalMemoryChangeBoundary.closed,
      FinalMemoryChangeBoundary.circuit, FinalMemoryChangeBoundary.raw_interactions,
      Operations.FullRequirements, FinalMemoryChange.channel, circuit_norm]

/-- Actual full-assembly Byte balance supplies guarantees for every physical table, including
the newly installed target RAM consumer. The verifier supplies its own outgoing requirements. -/
theorem byte_guarantees
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (interface : HostHintReadLocal.ExtensionInterface others resources)
    (checked : witness.Constraints) (balanced : witness.BalancedChannel byteChannel.toRaw) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw := by
  apply (witness.channelGuarantees_of_component_requirements byteChannel.toRaw checked balanced
    ?_ (component_byte_requirements interface)).2
  intro input data interaction emitted _
  exact verifier_requirements _ interaction emitted

/-- Raw acceptance supplies the existing host proof view with authentic Byte facts.
No Byte consumer or provider is discarded in obtaining this result. -/
theorem baseWitness_byte_of_accepted
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names))
    (interface : HostHintReadLocal.ExtensionInterface others resources)
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (baseWitness witness).tables, table.ChannelGuarantees (baseWitness witness).data byteChannel.toRaw := by
  apply baseWitness_byte witness (byte_guarantees witness interface checked (balanced _ ?_))
  simp [ensemble, ClosedVerifier.install, withReceipts, withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
    base, HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble,
    HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
    HostLocalCore.baseEnsemble, ClosedVerifier.withInteractions, LocalCore.baseEnsemble,
    sp1Ensemble_channels]

end SP1Clean.Soundness.HostFinalMemory
