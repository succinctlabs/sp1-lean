import SP1Clean.Soundness.HostFinalMemoryView

/-! # Private Memory receipts in the physical host ledger

The old host components are silent on the five boundary protocols. This is a static
property of registered circuits. Selecting the seven boundary tables therefore preserves
these ledgers exactly, while their Byte guarantees still come from the full assembly.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalLedgerLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalLedgerClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The only protocols introduced by complete outgoing Memory validation. -/
def privateChannels (target : MemorySnapshot) : List (RawChannel (ZMod p)) :=
  [(FinalMemoryValue.channel false).toRaw, (FinalMemoryValue.channel true).toRaw,
   FinalMemoryChange.channel.toRaw, (FinalRegisterValue.membership target).channel.toRaw,
   (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw]

/-- Installed handlers/resources keep the final-memory receipt protocols private. -/
def PrivateInterface (target : MemorySnapshot) (others : List (HostLocalHandoff.Receiver (p := p)))
    (resources : List (Component (ZMod p))) : Prop :=
  ∀ channel ∈ privateChannels (p := p) target, ∀ component ∈ others.map (·.component) ++ resources,
    channel ∉ component.circuit.channels

omit [Fact (2 ^ 25 < p)] in
private theorem silent_of_names (component : Component (ZMod p)) (channel : RawChannel (ZMod p))
    (quiet : (component.circuit.channels.map RawChannel.name).contains channel.name = false) :
    channel ∉ component.circuit.channels := by
  intro member
  have used := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  rw [quiet] at used
  contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}

private theorem private_not_local (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p) target) :
    channel ∉ (LocalCore.baseEnsemble (p := p) image source).channels := by
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;>
    intro member <;>
    have names := List.mem_map_of_mem (f := RawChannel.name) member <;>
    simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      FinalMemoryValue.channel, FinalMemoryChange.channel, FinalRegisterValue.membership, StaticTable.channel, InitialMemoryLookup.membership,
      stateChannel, memoryChannel, byteChannel, programChannel, exitChannel, syscallChannel,
      publicValuesChannel, MemorySnapshot.registerTable,
      StaticTable.ofRows, Channel.toRaw] at names

private def fixedAdditions (image : ProgramImage) : List (Component (ZMod p)) :=
  [{ circuit := ProtectedStore.byte }, { circuit := ProtectedStore.half }, { circuit := ProtectedStore.word }, { circuit := ProtectedStore.double },
   { circuit := WritePermissionProvider.circuit image }, HostCallLedger.producer,
   HostHintReadHandoff.receiver.component] ++ HostHintReadHandoff.wordResources

private theorem additions_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p) target)
    (component : Component (ZMod p)) (member : component ∈ fixedAdditions (p := p) image) :
    channel ∉ component.circuit.channels := by
  apply silent_of_names
  have quiet : (fixedAdditions (p := p) image).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true := by
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
    rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;> rfl
  simpa using List.all_eq_true.mp quiet component member

/-- Receipt freshness follows from the existing core inventory and the installed resource interface. -/
theorem beforeChecks_private (interface : PrivateInterface target others resources)
    (channel : RawChannel (ZMod p)) (privateChannel : channel ∈ privateChannels (p := p) target) :
    ∀ component ∈ beforeChecks image source others resources, channel ∉ component.circuit.channels := by
  intro component member
  change component ∈ (ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer ++ _ at member
  rcases List.mem_append.mp member with core | auxiliary
  · rcases List.mem_or_eq_of_mem_set core with retained | rfl
    · rcases List.mem_append.mp retained with stores | permission
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
          · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
            · rcases List.mem_or_eq_of_mem_set stores with old | rfl
              · exact fun used => private_not_local channel privateChannel
                  (LocalCore.component_channels_subset image source component
                    old used)
              · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
            · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
          · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
        · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
      · obtain rfl := List.mem_singleton.mp permission
        exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
    · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
  · change component ∈ (HostHintReadHandoff.receiver :: others).map (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
        (HostHintReadHandoff.wordResources ++ resources) at auxiliary
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at auxiliary
    rcases auxiliary with rfl | other | word | resource
    · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
    · exact interface channel privateChannel component (List.mem_append_left _ other)
    · exact additions_private (image := image) channel privateChannel component (List.mem_append_right _ word)
    · exact interface channel privateChannel component (List.mem_append_right _ resource)

/-- The legacy padding restriction introduces no receipt-channel occurrence. -/
theorem padding_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p) target) :
    channel ∉ HaltPaddingChip.component.circuit.channels := by
  apply silent_of_names
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The currently installed six-call registry and fixed hint/bank resources satisfy receipt privacy. -/
theorem source_privacy (target : MemorySnapshot) (hints : List Bytes) :
    PrivateInterface target (HostCallReceivers.available (p := p)) (HostHintReadLocal.sourceResources hints) := by
  intro channel privateChannel component member
  apply silent_of_names
  have quiet : ((HostCallReceivers.available (p := p)).map
      (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
      HostHintReadLocal.sourceResources hints).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true := by
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
    rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;> rfl
  simpa using List.all_eq_true.mp quiet component member

/-- The target validators register all five private protocols before verifier installation. -/
private theorem check_channels (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p) target) :
    channel ∈ (FinalMemoryChecks.checkTables (p := p) target).flatMap (·.circuit.channels) := by
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;>
    simp [FinalMemoryChecks.checkTables, FinalRegisterCheck.circuit, FinalRamCheck.circuit,
      StaticTable.component, StaticTable.provider, circuit_norm]

/-- Queue, bank and CPU verifier boundaries emit nothing on the Memory receipt protocols.
Fresh assertion channels are separated using the registered target-validator inventory. -/
theorem base_verifier_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p) target) (env : Environment (ZMod p)) :
    (base image source target final bankFinal others resources channels names).verifierOperations.interactionValuesWith
      channel env = [] := by
  let original := HostHintReadLocal.ensemble image source others
    (resources ++ FinalMemoryChecks.checkTables target) channels names
  have declared : channel ∈ (HostLocalCore.baseEnsemble image source
      ((HostHintReadHandoff.receiver :: others).map (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
        (HostHintReadHandoff.wordResources ++ (resources ++ FinalMemoryChecks.checkTables target)))
      ((HintReadWordChip.stateChannel.toRaw ::
        ((HostHintReadHandoff.receiver :: others).map (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
          (HostHintReadHandoff.wordResources ++ (resources ++ FinalMemoryChecks.checkTables target))).flatMap
            (fun component : Component (ZMod p) => component.circuit.channels)) ++ channels) names).channels := by
    have used := check_channels (target := target) channel privateChannel
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_cons_of_mem
    rw [List.flatMap_append, List.flatMap_append, List.flatMap_append]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ used))
  have registered : channel ∈ original.channels := List.mem_append_left _ declared
  change ((HostHintQueueBoundary.boundary source final bankFinal).install original).verifierOperations.interactionValuesWith
    channel env = []
  rw [ClosedVerifier.install_verifier_interactions_of_mem _ original env channel registered]
  have quiet : original.verifierOperations.interactionValuesWith channel env = [] := by
    change ((LocalSourceBoundary.checker image source).install _).verifierOperations.interactionValuesWith channel env = []
    rw [PublicVerifier.install_verifier_interactions_of_mem _ _ env channel declared]
    exact LocalCore.boundaryVerifier_silent image source channel (private_not_local channel privateChannel) env
  have boundaryQuiet : channel ∉ (HostHintQueueBoundary.boundary source final bankFinal).circuit.channels := by
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
    rcases privateChannel with rfl | rfl | rfl | rfl | rfl <;>
      apply HostHintQueueBoundary.boundary_silent <;>
      simp [FinalMemoryValue.channel, FinalMemoryChange.channel, FinalRegisterValue.membership, StaticTable.channel, InitialMemoryLookup.membership, HostHintQueue.stateChannel,
        HostCommitChip.stateChannel, HostExitBoundary.channel, Channel.toRaw]
  have empty := (HostHintQueueBoundary.boundary source final bankFinal).singleton.interactionsWith_nil_of_channel_not_mem
    (data := env.data) boundaryQuiet
  rw [ClosedVerifier.singleton_interactions] at empty
  rw [quiet, empty, List.append_nil]

end SP1Clean.Soundness.HostFinalMemory
