import SP1Clean.Soundness.HostQueueCallProjection
import SP1Clean.Soundness.HostHintReadBanks
import ToClean.Air.UnitBalance

/-! # Terminal receipts in the installed host ledger

The canonical ledger authenticates the optional outgoing exit. Only the HALT receiver
produces a receipt; its full call remains tied to the instruction inventory by HostCall balance.
Disabled endpoint pulls remain in the original interaction-count bound.
-/

namespace SP1Clean.Soundness.HostTerminalLedger

open Circuit Air.Flat Channels Model.Core HostHintReadLocal HostQueueCallProjection

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance terminalLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Select the complete exit word from a HALT call. -/
def receipt? (message : HostCallChip.Message (ZMod p)) : Option (Word (ZMod p)) :=
  if Word.toBitVec64 message.code = 0 then some message.arg1 else none

omit [Fact (2 ^ 25 < p)] in
private theorem values_silent (component : Component (ZMod p)) (env : Environment (ZMod p))
    (silent : HostExitBoundary.channel.toRaw ∉ component.circuit.channels) :
    component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env = [] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
    InteractionRecovery.interactionsWith_main_eq_nil _ _ _ _ silent, List.map_nil]

private theorem control_values (receiver : HostLocalHandoff.Receiver (p := p))
    (member : receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (env : Environment (ZMod p)) (constraints : receiver.component.operations.ConstraintsHold env)
    (bytes : receiver.component.operations.ChannelGuarantees byteChannel.toRaw env) :
    receiver.component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env =
      ((receipt? (receiver.message env)).toList.map HostExitBoundary.channel.pushedValue) := by
  change receiver ∈ ([HostCallReceivers.halt, HostCallReceivers.enter] ++
    (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
    (List.ofFn fun slot => HostCallReceivers.commit true slot)) at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at member
  rcases member with ((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩
  · have valid := HostHaltChip.component_spec_of_byte env constraints bytes
    change HostHaltChip.Spec (valueFromOffset HostHaltChip.Inputs 0 env) at valid
    rw [HostCallReceivers.halt_message]
    have arg (input : Var HostHaltChip.Inputs (ZMod p)) :
        eval env input.call.arg1 = (eval env input).call.arg1 := by
      rcases input with ⟨⟨_, _, _, _, _, _, _⟩, _⟩
      simp only [circuit_norm]
    have zero : Word.toBitVec64 (0 : Word (ZMod p)) = 0 := by simp [Word.toBitVec64, Word.toNat]
    rw [receipt?, valid.1, zero, if_pos rfl]
    simp only [Option.toList_some, List.map_cons, List.map_nil]
    simp only [HostCallReceivers.halt, Operations.interactionValuesWith, Component.interactionsWith_eq]
    exact (HostHaltChip.terminal_values _ _ env).trans (by
      rw [arg, eval_varFromOffset_valueFromOffset])
  · have valid := HostEnterChip.component_spec_of_constraints env constraints
    change HostEnterChip.Spec (valueFromOffset HostEnterChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.enter (p := p)).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.enter_message]
    have three : (3 : ZMod p).val = 3 :=
      ZMod.val_natCast_of_lt (show (3 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1, HostEnterChip.codeWord, Word.toBitVec64, Word.toNat, three]
  · have valid := HostCommitBank.view_spec_of_byte false (some slot) env constraints bytes
    change HostCommitChip.Spec false slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.commit (p := p) false slot).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.commit_message]
    have sixteen : (16 : ZMod p).val = 16 :=
      ZMod.val_natCast_of_lt (show (16 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1.1, HostCommitChip.codeWord, Word.toBitVec64, Word.toNat, sixteen]
  · have valid := HostCommitBank.view_spec_of_byte true (some slot) env constraints bytes
    change HostCommitChip.Spec true slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.commit (p := p) true slot).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.commit_message]
    have twentySix : (26 : ZMod p).val = 26 :=
      ZMod.val_natCast_of_lt (show (26 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1.1, HostCommitChip.codeWord, Word.toBitVec64, Word.toNat, twentySix]

omit [Fact (2 ^ 25 < p)] in
private theorem receiver_values (receivers : List (HostLocalHandoff.Receiver (p := p)))
    (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component) receivers tables)
    (select : HostCallChip.Message (ZMod p) → Option (Word (ZMod p)))
    (rowValues : ∀ receiver ∈ receivers, ∀ env,
      receiver.component.operations.ConstraintsHold env →
      receiver.component.operations.ChannelGuarantees byteChannel.toRaw env →
      receiver.component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env =
        ((select (receiver.message env)).toList.map HostExitBoundary.channel.pushedValue))
    (constraints : ∀ table ∈ tables, table.Constraints data)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees data byteChannel.toRaw) :
    tables.flatMap (·.interactionsWith data HostExitBoundary.channel.toRaw) =
      ((ReceiverView.messages receivers tables data).filterMap select).map HostExitBoundary.channel.pushedValue := by
  induction aligned with
  | nil => rfl
  | @cons receiver table receivers tables same aligned ih =>
      rw [ReceiverView.messages_cons, List.filterMap_append, List.map_append, List.flatMap_cons]
      congr 1
      · simp only [Table.interactionsWith, ReceiverView.tableMessages, List.filterMap_map,
          List.map_filterMap, Function.comp_def]
        rw [List.filterMap_eq_flatMap_toList]
        apply List.flatMap_congr
        intro physical member
        rw [← same, rowValues receiver (List.mem_cons_self ..)]
        · exact (Option.toList_map ..).symm
        · rw [same]; exact constraints table (List.mem_cons_self ..) physical member
        · rw [same]; exact bytes table (List.mem_cons_self ..) physical member
      · exact ih (fun receiver member => rowValues receiver (List.mem_cons_of_mem _ member))
          (fun table member => constraints table (List.mem_cons_of_mem _ member))
          (fun table member => bytes table (List.mem_cons_of_mem _ member))

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

private theorem controls_interactions
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel byteChannel.toRaw) :
    (controlTables witness).flatMap (·.interactionsWith witness.data HostExitBoundary.channel.toRaw) =
      ((ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18)
        (controlTables witness) witness.data).filterMap receipt?).map HostExitBoundary.channel.pushedValue := by
  have aligned := ReceiverView.aligned_of_map_eq ((HostCallReceivers.available (p := p)).take 18)
    (controlTables witness) (by
      simp only [controlTables, List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
        List.map_cons, List.drop_succ_cons, List.drop_zero])
  exact receiver_values _ _ witness.data aligned receipt? (fun receiver member => control_values receiver member)
    (fun table present => constraints table (controlTables_mem witness table present))
    (fun table present => byte_guarantees witness interface constraints balanced table
      (controlTables_mem witness table present))

omit [Fact (2 ^ 25 < p)] in
private theorem receipt_none_of_queue (message : HostCallChip.Message (ZMod p))
    (event : HintQueue.Event) (selected : project message = some event) : receipt? message = none := by
  have nonzero : Word.toBitVec64 message.code ≠ 0 := by
    intro zero
    simp only [project, zero, queueCallEvent?, SyscallKind.code, BitVec.reduceEq, ↓reduceIte] at selected
    contradiction
  exact if_neg nonzero

private theorem queue_receipt (row : HostQueueOrder.Row (p := p))
    (valid : (HostQueueOrder.view row.1).component.Spec row.2) :
    receipt? (HostQueueCPUOrder.call row) = none :=
  receipt_none_of_queue _ _ (queue_projection row valid).2

private theorem filterMap_right {α β : Type*} (select : α → Option β)
    (all front back : List α) (permutation : all.Perm (front ++ back))
    (silent : ∀ value ∈ front, select value = none) :
    (all.filterMap select).Perm (back.filterMap select) := by
  have selected := permutation.filterMap select
  rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr silent, List.nil_append] at selected
  exact selected

private theorem calls_receipts
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data) :
    ((HostLocalHandoff.calls witness).filterMap receipt?).Perm
      ((ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18)
        (controlTables witness) witness.data).filterMap receipt?) := by
  apply filterMap_right receipt? _ _ _ (calls_split witness)
  intro message member
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
  exact queue_receipt row
    (HostQueueOrder.rows_spec _ witness.data (queueTables_aligned witness) specs row rowMem)

variable {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}

private theorem auxiliary_controls
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.tables.drop 62).flatMap (·.interactionsWith witness.data HostExitBoundary.channel.toRaw) =
      (controlTables (HostHintQueueBoundary.projected witness)).flatMap
        (·.interactionsWith witness.data HostExitBoundary.channel.toRaw) := by
  have silent : ∀ table ∈ (witness.tables.drop 62).take 1 ++ (witness.tables.drop 62).drop 19,
      table.interactionsWith witness.data HostExitBoundary.channel.toRaw = [] := by
    have mapped := HostTableRegistry.auxiliary_components witness
    have checked : (((HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.available).map
        (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
          (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints)).take 1 ++
        ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map
          (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
          (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints)).drop 19).all
        (fun component => !(component.circuit.channels.map RawChannel.name).contains
          (HostExitBoundary.channel (p := p)).toRaw.name) = true := rfl
    intro table member
    have present := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    simp only [List.map_append, List.map_take, List.map_drop, mapped] at present
    apply table.interactionsWith_nil_of_channel_not_mem
    intro used
    have absent := List.all_eq_true.mp checked table.component present
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
    contradiction
  have first : ((witness.tables.drop 62).take 1).flatMap (·.interactionsWith witness.data HostExitBoundary.channel.toRaw) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun table member => silent table (List.mem_append_left _ member))
  have last : ((witness.tables.drop 62).drop 19).flatMap (·.interactionsWith witness.data HostExitBoundary.channel.toRaw) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun table member => silent table (List.mem_append_right _ member))
  have split := congrArg (List.flatMap (fun table : Table (ZMod p) =>
    table.interactionsWith witness.data HostExitBoundary.channel.toRaw)) (List.take_append_drop 1 (witness.tables.drop 62))
  have tail := congrArg (List.flatMap (fun table : Table (ZMod p) =>
    table.interactionsWith witness.data HostExitBoundary.channel.toRaw)) (List.take_append_drop 18 ((witness.tables.drop 62).drop 1))
  simp only [List.drop_drop] at last
  simp only [List.flatMap_append, List.drop_drop] at split tail
  rw [first, List.nil_append, ← tail, last, List.append_nil] at split
  rw [← split, controlTables, HostHintReadBanks.receiver_tables, List.drop_take, List.take_take]
  simp only [List.drop_drop, Nat.reduceSub, min_eq_left (by decide : 18 ≤ 20)]

private theorem exit_fresh :
    HostExitBoundary.channel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro used
  change HostExitBoundary.channel.toRaw ∈ (LocalCore.baseEnsemble image source).channels ++
    [LocalCore.sourceChannel image source] at used
  rcases List.mem_append.mp used with used | used
  · have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, HostExitBoundary.channel,
      Channels.stateChannel, Channels.memoryChannel, Channels.byteChannel, Channels.programChannel,
      Channels.exitChannel, Channels.syscallChannel, Channels.publicValuesChannel,
      StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, Channel.toRaw] at present
  · have same := (List.mem_singleton.mp used).symm
    have heads := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList[4]?) same
    dsimp only [LocalCore.sourceChannel, PublicVerifier.channel, VerifierChannel.channel,
      Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName] at heads
    rw [String.toList_append] at heads
    simp [LocalSourceBoundary.checker, HostExitBoundary.channel] at heads

private theorem wrapper_exit_silent :
    HostExitBoundary.channel.toRaw ∉ (HostCallLedger.producer (p := p)).circuit.channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  change false = true at present
  exact Bool.noConfusion present

/-- Only checked HALT calls produce terminal receipts; the verifier supplies one possibly disabled pull. -/
theorem interactions
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (witness.interactionsWith HostExitBoundary.channel.toRaw).Perm
      ((((HostLocalHandoff.calls (HostHintQueueBoundary.projected witness)).filterMap receipt?).map
        HostExitBoundary.channel.pushedValue) ++
      [HostExitBoundary.channel.pulledIfValue (if source.host.exitCode = none ∧ bankFinal.exitCode.isSome then 1 else 0)
        (HostExitBoundary.encode (bankFinal.exitCode.getD 0))]) := by
  have wrapper : (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)).interactionsWith
      (HostHintQueueBoundary.projected witness).data HostExitBoundary.channel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    exact wrapper_exit_silent
  have split := HostLocalCore.interactions_split_new (HostHintQueueBoundary.projected witness)
    HostExitBoundary.channel.toRaw (by
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨HostCallReceivers.halt.component, ?_, ?_⟩
      · apply List.mem_append_left
        apply List.mem_map_of_mem
        simp [HostCallReceivers.available]
      · simp [HostCallReceivers.halt, HostHaltChip.circuit, circuit_norm]) exit_fresh
    (by simp [HostExitBoundary.channel, WritePermissionProvider.channel, Channel.toRaw])
  rw [wrapper, List.nil_append] at split
  have tail : HostLocalCore.auxiliaryTables (HostHintQueueBoundary.projected witness) =
      witness.tables.drop 62 := HostHintQueueBoundary.projected_drop witness 62 (by decide)
  rw [tail, HostHintQueueBoundary.projected_data, auxiliary_controls] at split
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  have controls := controls_interactions (HostHintQueueBoundary.projected witness) interface checks records.byte
  rw [HostHintQueueBoundary.projected_data] at controls
  rw [controls] at split
  have selected := calls_receipts (HostHintQueueBoundary.projected witness)
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks records)
  rw [HostHintQueueBoundary.projected_data] at selected
  have ledger := HostHintQueueBoundary.interactions_split witness HostExitBoundary.channel.toRaw
    (List.mem_append_right _ (by
      simp [HostHintQueueBoundary.boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm]))
  rw [split, ClosedVerifier.singleton_interactions, ClosedVerifier.operations, HostBoundary.closed_main,
    HostBoundary.terminal_values] at ledger
  exact ledger.trans ((selected.symm.map HostExitBoundary.channel.pushedValue).append_right _)

omit [Fact (2 ^ 25 < p)] in
private theorem balanced_receipts (produced : List (Word (ZMod p)))
    (source target : Option (BitVec 32))
    (balanced : BalancedInteractions (produced.map HostExitBoundary.channel.pushedValue ++
      [HostExitBoundary.channel.pulledIfValue (if source = none ∧ target.isSome then 1 else 0)
        (HostExitBoundary.encode (target.getD 0))])) :
    produced.Perm (if source = none then target.toList.map HostExitBoundary.encode else []) := by
  let : DecidableEq (ZMod p) := FiniteField.instDecidableEq
  have active : (produced.map HostExitBoundary.channel.pushedValue).filter
      (fun interaction => decide (interaction.mult ≠ 0)) = produced.map HostExitBoundary.channel.pushedValue := by
    apply List.filter_eq_self.mpr
    intro interaction member
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
    simp [Channel.pushedValue]
  have endpoint : [HostExitBoundary.channel.pulledIfValue (if source = none ∧ target.isSome then 1 else 0)
      (HostExitBoundary.encode (target.getD 0))].filter (fun interaction => decide (interaction.mult ≠ 0)) =
      (if source = none then target.toList.map HostExitBoundary.encode else []).map
        (HostExitBoundary.channel (p := p)).pulledValue := by
    cases source <;> cases target <;> simp [Channel.pulledIfValue, Channel.pulledValue]
  apply ((HostExitBoundary.channel.balanced_unit_iff _ _).mp ?_).2
  simpa only [List.filter_append, active, endpoint] using balanced.filter_nonzero

/-- The actual HALT-call inventory is empty or the exact advertised terminal word. -/
theorem receipts
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((HostLocalHandoff.calls (HostHintQueueBoundary.projected witness)).filterMap receipt?).Perm
      (if source.host.exitCode = none then bankFinal.exitCode.toList.map HostExitBoundary.encode else []) := by
  apply balanced_receipts
  apply balancedInteractions_of_perm (balanced HostExitBoundary.channel.toRaw ?_)
    (interactions witness constraints balanced)
  apply List.mem_append_left
  apply List.mem_append_right
  simp [HostHintQueueBoundary.boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm]

/-- A stopped source's supplied endpoint must retain its exact optional exit code. -/
theorem source_status
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (balanced : witness.BalancedChannels) :
    source.host.exitCode = none ∨ source.host.exitCode = bankFinal.exitCode := by
  have raw := HostHintQueueBoundary.boundary_checks witness balanced
  unfold ClosedVerifier.Checks ClosedVerifier.operations at raw
  rw [HostBoundary.closed_main] at raw
  exact (HostBoundary.constraints_spec _ _ _ _ _ _ _ _ raw).2

end SP1Clean.Soundness.HostTerminalLedger
