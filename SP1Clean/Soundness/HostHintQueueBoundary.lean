import SP1Clean.Native.Operations.HostBoundary
import SP1Clean.Soundness.HostHintReadLocalQueue
import SP1Clean.Soundness.HostCommitEnsemble
import SP1Clean.Soundness.HaltPadding

/-! # Installing queue and commitment-bank boundaries in the local verifier

The witness retains every physical instruction, handler, and resource table. Its verifier runs
queue, bank, and terminal boundaries exactly once. Projection removes those verifier emissions
without adding a table or changing canonical data; only channels unused by the boundary retain
balance. Queue ordering accounts explicitly for the verifier's two endpoint occurrences.
The final cursor, outgoing bank words, and optional exit are instance parameters. Other fields of
`bankFinal` remain unused. Active HALT uses the syscall handler; the legacy table is padding only.
Complete outgoing snapshot agreement and dynamic allocation history remain separate proofs.
-/

namespace SP1Clean.Soundness.HostHintQueueBoundary

open Circuit Air.Flat Model.Core HostHintQueue HostHintReadLocal HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance boundaryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

abbrev boundary (source : ExecutionSnapshot) (final : State (ZMod p)) (bankFinal : HostState) :=
  SP1Clean.HostBoundary.closed source.host.io.hints final
    (fun deferred => HostCommitEnsemble.sourceValues deferred source.host)
    (fun deferred => HostCommitEnsemble.sourceValues deferred bankFinal)
    source.host.exitCode bankFinal.exitCode

private def haltSlot (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) :
    TableSlot (HostLocalCore.tables image source auxiliary) HaltPaddingChip.original where
  index := ⟨57, by rw [HostLocalCore.tables_length]; omega⟩
  component_eq := by
    rw [HostLocalCore.core_component image source auxiliary ⟨57, by decide⟩, if_neg (by decide)]
    rfl

def ensemble (image : ProgramImage) (source : ExecutionSnapshot) (final : State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : ((HostLocalCore.tables image source
      ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup) :
    Ensemble (ZMod p) SP1PublicIO :=
  HaltPadding.install
    ((boundary source final bankFinal).install (HostHintReadLocal.ensemble image source others resources channels names))
    (haltSlot image source _)

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup}

/-- Erase only the legacy zero-selector assertion; every physical row and channel survives. -/
def underlying (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names)) :
    EnsembleWitness ((boundary source final bankFinal).install
      (HostHintReadLocal.ensemble image source others resources channels names)) :=
  HaltPadding.project witness

private theorem underlying_data
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names)) :
    (underlying witness).data = witness.data := HaltPadding.project_data witness

/-- Retain the physical inventory while removing the installed verifier boundary. -/
def projected (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names)) :
    EnsembleWitness (HostHintReadLocal.ensemble image source others resources channels names) :=
  (boundary source final bankFinal).project (underlying witness)

@[simp] theorem projected_data
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names)) :
    (projected witness).data = witness.data := by
  rw [projected, ClosedVerifier.project_data]
  exact underlying_data witness

@[simp] theorem projected_publicInput
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names)) :
    (projected witness).publicInput = witness.publicInput := by
  simp only [projected, ClosedVerifier.project_publicInput, underlying]
  exact HaltPadding.project_publicInput witness

/-- Physical tables following the padding-only slot are unchanged; no verifier table is appended. -/
theorem projected_drop
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (count : ℕ) (after : 57 < count) :
    (projected witness).tables.drop count = witness.tables.drop count :=
  HaltPadding.drop_tables witness count after

theorem projected_constraints
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (constraints : witness.Constraints) : (projected witness).Constraints :=
  ((boundary source final bankFinal).project_constraints (underlying witness)).mp
    (HaltPadding.constraints witness constraints)

/-- Only channels without boundary emissions retain balance under physical projection. -/
theorem projected_balancedChannel
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) (channel : RawChannel (ZMod p))
    (registered : channel ∈ (HostHintReadLocal.ensemble image source others resources channels names).channels)
    (silent : channel ∉ (boundary source final bankFinal).circuit.channels) :
    (projected witness).BalancedChannel channel :=
  (boundary source final bankFinal).project_balancedChannel (underlying witness) channel registered silent
    (HaltPadding.balanced witness balanced channel (List.mem_append_left _ (List.mem_append_left _ registered)))

/-- Boundary assertions follow from their fresh check channel, not physical row constraints. -/
theorem boundary_checks
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) : (boundary source final bankFinal).Checks witness.data := by
  have checked := ((boundary source final bankFinal).balanced_iff (underlying witness)).mp
    (HaltPadding.balanced witness balanced)
  simpa only [underlying_data] using checked.2.2

theorem source_binding
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) :
    (SP1Clean.HostHintQueueBoundary.initial (p := p) source.host.io.hints).Binds
      (HintQueue.ofList source.host.io.hints).1 source.host.io.hints := by
  apply SP1Clean.HostHintQueueBoundary.initial_binds
  have raw := boundary_checks witness balanced
  unfold ClosedVerifier.Checks ClosedVerifier.operations at raw
  rw [HostBoundary.closed_main] at raw
  exact SP1Clean.HostBoundary.source_bound _ _ _ _ _ _ _ _ raw

omit [Fact (2 ^ 25 < p)] in
/-- The boundary uses queue, bank, and terminal state, with no record or CPU/word-cursor edge. -/
theorem boundary_silent (channel : RawChannel (ZMod p)) (different : channel ≠ stateChannel.toRaw) :
    channel ≠ (HostCommitChip.stateChannel false).toRaw →
    channel ≠ (HostCommitChip.stateChannel true).toRaw →
    channel ≠ HostExitBoundary.channel.toRaw →
    channel ∉ (boundary source final bankFinal).circuit.channels := by
  intro commit deferred terminal
  simp only [boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm,
    List.mem_cons, List.not_mem_nil, different, commit, deferred, terminal, or_self, not_false_eq_true]

/-- The complete HostCall handoff is unchanged by the queue, bank and exit endpoints. -/
theorem projected_hostCall_balancedChannel
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) :
    (projected witness).BalancedChannel HostCallChip.channel.toRaw := by
  apply projected_balancedChannel witness balanced
  · exact List.mem_append_left _ (List.mem_cons_self ..)
  · exact boundary_silent _
      (by simp [HostCallChip.channel, stateChannel, Channel.toRaw])
      (by simp [HostCallChip.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [HostCallChip.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [HostCallChip.channel, HostExitBoundary.channel, Channel.toRaw])

/-- Per-call word cursors have no traffic in the queue, bank or terminal boundary. -/
theorem projected_cursor_balancedChannel
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) :
    (projected witness).BalancedChannel HintReadWordChip.stateChannel.toRaw := by
  apply projected_balancedChannel witness balanced
  · simp [HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble,
      PublicVerifier.install, HostLocalCore.baseEnsemble]
  · exact boundary_silent _
      (by simp [HintReadWordChip.stateChannel, stateChannel, Channel.toRaw])
      (by simp [HintReadWordChip.stateChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [HintReadWordChip.stateChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [HintReadWordChip.stateChannel, HostExitBoundary.channel, Channel.toRaw])

/-- Write permissions are untouched by queue, bank and terminal endpoint traffic. -/
theorem projected_permission_balancedChannel
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) :
    (projected witness).BalancedChannel WritePermissionProvider.channel.toRaw := by
  apply projected_balancedChannel witness balanced
  · simp [HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble,
      PublicVerifier.install, HostLocalCore.baseEnsemble]
  · exact boundary_silent _
      (by simp [WritePermissionProvider.channel, stateChannel, Channel.toRaw])
      (by simp [WritePermissionProvider.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [WritePermissionProvider.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [WritePermissionProvider.channel, HostExitBoundary.channel, Channel.toRaw])

private theorem boundary_core_silent (channel : RawChannel (ZMod p))
    (registered : channel ∈ (LocalCore.baseEnsemble image source).channels) :
    channel ∉ (boundary source final bankFinal).circuit.channels := by
  have checked : (LocalCore.baseEnsemble (p := p) image source).channels.all
      (fun core => !((boundary source final bankFinal).circuit.channels.map RawChannel.name).contains core.name) = true := by
    simp only [LocalCore.baseEnsemble, List.all_cons, StaticTable.channel, InitialMemoryLookup.membership,
      MemorySnapshot.registerTable, StaticTable.ofRows]
    rfl
  intro used
  have absent := List.all_eq_true.mp checked channel registered
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
  exact Bool.noConfusion absent

/-- Core channels, including Memory and its private ordering ledgers, have no host-boundary traffic. -/
theorem projected_core_balancedChannel
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) (channel : RawChannel (ZMod p))
    (registered : channel ∈ (LocalCore.baseEnsemble image source).channels) :
    (projected witness).BalancedChannel channel := by
  apply projected_balancedChannel witness balanced channel
  · exact List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ registered)))
  · exact boundary_core_silent channel registered

/-- Authentication uses only the byte, node and word ledgers, all untouched by the boundary. -/
theorem record_channels
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (balanced : witness.BalancedChannels) : RecordChannels (projected witness) := by
  refine ⟨projected_balancedChannel witness balanced _ ?_ ?_,
    projected_balancedChannel witness balanced _ ?_ ?_, projected_balancedChannel witness balanced _ ?_ ?_⟩
  · simp [HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
      HostLocalCore.baseEnsemble, LocalCore.baseEnsemble, sp1Ensemble_channels]
  · exact boundary_silent _ (by simp [Channels.byteChannel, stateChannel, Channel.toRaw])
      (by simp [Channels.byteChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [Channels.byteChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [Channels.byteChannel, HostExitBoundary.channel, Channel.toRaw])
  · apply auxiliary_channel_registered image source others resources channels HostHintReadCoverage.handler
      (by simp [receiver])
    simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]
  · exact boundary_silent _ (by simp [nodeChannel, stateChannel, Channel.toRaw])
      (by simp [nodeChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [nodeChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [nodeChannel, HostExitBoundary.channel, Channel.toRaw])
  · apply auxiliary_channel_registered image source others resources channels HostHintReadCoverage.handler
      (by simp [receiver])
    simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]
  · exact boundary_silent _ (by simp [wordChannel, stateChannel, Channel.toRaw])
      (by simp [wordChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [wordChannel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [wordChannel, HostExitBoundary.channel, Channel.toRaw])

omit [Fact (2 ^ 25 < p)] in
private theorem boundary_checker_silent (base : Ensemble (ZMod p) SP1PublicIO) :
    (LocalSourceBoundary.checker image source).channel base ∉
      (boundary source final bankFinal).circuit.channels := by
  apply boundary_silent
  all_goals
    intro same
    have heads := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList[4]?) same
    dsimp only [PublicVerifier.channel, VerifierChannel.channel, Verifier.zeroChannel,
      Channel.toRaw, VerifierChannel.channelName] at heads
    rw [String.toList_append] at heads
    simp [LocalSourceBoundary.checker, stateChannel, HostCommitChip.stateChannel, HostExitBoundary.channel] at heads

/-- Source authentication and CPU chronology survive removal of the host-only endpoints. -/
theorem projected_orderingChannels
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (interface : ExtensionInterface others resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    LocalCore.OrderingChannels (HostLocalCore.localWitness (projected witness)) := by
  have byte := HostLocalCore.byte_guarantees (projected witness) (auxiliaryInterface interface)
    (projected_constraints witness constraints) (record_channels witness balanced).byte
  apply HostLocalCore.orderingChannels_of_guarantees (projected witness) (auxiliaryInterface interface) byte.1 byte.2
  · apply projected_balancedChannel witness balanced
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact boundary_checker_silent _
  · exact projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])

/-- Separate actual verifier emissions from the physical projection, preserving every occurrence.
The singleton is only a local ledger representation evaluated at the original canonical data. -/
theorem interactions_split
    (witness : EnsembleWitness (ensemble image source final bankFinal others resources channels names))
    (channel : RawChannel (ZMod p))
    (registered : channel ∈ (HostHintReadLocal.ensemble image source others resources channels names).channels ++
      (boundary source final bankFinal).circuit.channels) :
    (witness.interactionsWith channel).Perm ((projected witness).interactionsWith channel ++
      (boundary source final bankFinal).singleton.interactionsWith witness.data channel) := by
  have different : (boundary source final bankFinal).channel
      (HostHintReadLocal.ensemble image source others resources channels names) ≠ channel := by
    intro same
    exact (boundary source final bankFinal).channel_not_mem _ (same ▸ registered)
  have split := (boundary source final bankFinal).interactionView_interactions_perm (underlying witness) channel
  rw [(boundary source final bankFinal).interactionView_interactions _ _ different, underlying_data] at split
  exact (List.Perm.of_eq (HaltPadding.interactions witness channel).symm).trans split

variable {availableNames : ((HostLocalCore.tables image source
    ((receiver :: HostCallReceivers.available).map (·.component) ++ (wordResources ++ resources))).map
      (·.circuit.name)).Nodup}

theorem extraTables_eq
    (witness : EnsembleWitness (ensemble image source final bankFinal HostCallReceivers.available resources channels availableNames)) :
    extraTables (projected witness) = witness.tables.drop 85 := by
  change (((projected witness).tables.drop 62).drop 21).drop 2 = _
  rw [List.drop_drop, List.drop_drop]
  exact projected_drop witness 85 (by decide)

/-- The complete queue ledger includes the verifier's endpoints and each physical handler row. -/
theorem queue_balanced
    (witness : EnsembleWitness (ensemble image source final bankFinal HostCallReceivers.available resources channels availableNames))
    (silent : ∀ component ∈ resources, stateChannel.toRaw ∉ component.circuit.channels)
    (balanced : witness.BalancedChannels) :
    BalancedInteractions ([stateChannel.pushedValue (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints),
      stateChannel.pulledValue final] ++
      (queueTables (projected witness)).flatMap (·.interactionsWith witness.data stateChannel.toRaw)) := by
  have registered := auxiliary_channel_registered image source HostCallReceivers.available resources channels
    (names := availableNames) HostHintReadCoverage.handler (by simp [receiver]) stateChannel.toRaw
    (by simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm])
  have ledger := balancedInteractions_of_perm
    (balanced stateChannel.toRaw (List.mem_append_left _ (List.mem_append_left _ registered)))
    (interactions_split witness stateChannel.toRaw (List.mem_append_left _ registered))
  have extra : (extraTables (projected witness)).flatMap (·.interactionsWith (projected witness).data stateChannel.toRaw) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    apply silent table.component
    rw [← extraTables_components (projected witness)]
    exact List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [queue_interactions, extra, List.append_nil, projected_data,
    ClosedVerifier.singleton_interactions, ClosedVerifier.operations, HostBoundary.closed_main,
    SP1Clean.HostBoundary.queue_values] at ledger
  exact balancedInteractions_of_perm ledger (List.perm_append_comm ..)

/-- Every actual queue-handler row lies on the uniquely anchored path. Record authentication
is retained for dynamic providers; this version covers resources without additional queue edges. -/
theorem queue_ordered
    (witness : EnsembleWitness (ensemble image source final bankFinal HostCallReceivers.available resources channels availableNames))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (store : HintQueue.Store) (authenticated : RecordAuthentication (projected witness) store)
    (silent : ∀ component ∈ resources, stateChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ path : List (HostQueueOrder.Row (p := p)),
      path.Perm (TransitionView.readIndexedRows HostQueueOrder.indices (queueTables (projected witness)) witness.data) ∧
      Walk.IsWalk HostQueueOrder.edge (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) final path := by
  have ordered := HostQueueOrder.ordered _ (projected witness).data (queueTables_aligned (projected witness))
    (queue_specs (projected witness) interface store authenticated (projected_constraints witness constraints)
      (record_channels witness balanced)) _ final
    (by simpa only [projected_data] using queue_balanced witness silent balanced)
  simpa only [projected_data] using ordered

/-- The actual fixed provider tables authenticate immutable records, without a verifier resource. -/
theorem source_authentication
    (witness : EnsembleWitness (ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) :
    RecordAuthentication (projected witness) (HintQueue.ofList source.host.io.hints).1 :=
  source_record_authentication (projected witness) _ (.refl _) (projected_constraints witness constraints)

/-- The source/HINT_LEN/HINT_READ registration needs no record-authentication or endpoint premise.
This is a token-path theorem; semantic replay is established in `HostHintQueueHistory`. -/
theorem source_queue_ordered
    (witness : EnsembleWitness (ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ path : List (HostQueueOrder.Row (p := p)),
      path.Perm (TransitionView.readIndexedRows HostQueueOrder.indices (queueTables (projected witness)) witness.data) ∧
      Walk.IsWalk HostQueueOrder.edge (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) final path := by
  apply queue_ordered witness (source_interface source.host.io.hints) (HintQueue.ofList source.host.io.hints).1
    _ _ constraints balanced
  · exact source_authentication witness constraints
  · intro component member used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    simp only [sourceResources, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> change false = true at present <;> exact Bool.noConfusion present

end SP1Clean.Soundness.HostHintQueueBoundary
