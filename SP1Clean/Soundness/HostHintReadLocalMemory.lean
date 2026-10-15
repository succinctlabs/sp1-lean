import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.HostLocalCoreMemoryBounds
import SP1Clean.Soundness.HostRamTouches

/-! # Full Memory balance of the installed hint handlers

The source-backed queue assembly derives the complete Memory record permutation directly from
its actual AIR constraints and balance. The word consumers and wrapper accesses stay in that
ledger. Source and pushed-record clock bounds transfer through that permutation to every prior
record, proving strict order for installed word writes. Predecessor value currency remains open.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Channels Model.Core Semantics HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance memoryLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance memoryLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem word_access (last : Bool) (input : Var HintReadWordChip.Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((HintReadWordChip.main last input).operations offset).ConstraintsHold env)
    (bytes : ((HintReadWordChip.main last input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    HostRamTouches.AccessFacts (eval env input).ram := by
  have retained : ⟨offset, HostRamAccessChip.circuit.toSubcircuit offset input.ram⟩ ∈
      ((HintReadWordChip.main last input).operations offset).subcircuits := by
    simp only [HintReadWordChip.main, circuit_norm, Operations.subcircuits]
  have checked := constraintsHold_generalSubcircuit_of_mem env _ HostRamAccessChip.circuit
    input.ram offset retained constraints
  have guarantees := (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
    HostRamAccessChip.circuit offset input.ram).mp
      (channelGuarantees_subcircuit_of_mem byteChannel.toRaw env _ _ retained bytes)
  have facts := HostRamTouches.of_constraints input.ram offset env checked guarantees
  have evaluated : eval env input.ram = (eval env input).ram := by
    rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
    rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
    simp only [circuit_norm]
  rwa [evaluated] at facts

/-- Every physical HINT_READ word contributes a bounded RAM touch at its call clock.
The actual AIR and Byte balance suffice; prior Memory guarantees and record authentication
are not premises of this structural step. -/
theorem word_touches {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    {names : ((HostLocalCore.tables image source
      ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image source others resources channels names))
    (interface : ExtensionInterface others resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel byteChannel.toRaw) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness) witness.data,
      HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram := by
  intro row member
  obtain ⟨⟨last, table⟩, paired, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have component := List.forall₂_zip (wordTables_aligned witness) paired
  have present := wordTables_mem witness table (List.of_mem_zip paired).2
  have checked := constraints table present physical physicalMem
  have bytes := byte_guarantees witness interface constraints balanced table present physical physicalMem
  rw [← component] at checked bytes
  rw [Component.constraintsHold_iff] at checked
  rw [Component.channelGuarantees_iff] at bytes
  simp only [HintReadCoverage.view, Component.rowOperations, HintReadWordChip.circuit] at checked bytes
  have facts := word_access last (varFromOffset HintReadWordChip.Inputs 0)
    (size HintReadWordChip.Inputs) (Environment.fromArray physical witness.data) checked bytes
  simpa only [eval_varFromOffset_valueFromOffset, HintReadCoverage.rowInput] using facts

omit [Fact (2 ^ 25 < p)] in
private theorem touch_at_clock (input : HintReadWordChip.Inputs (ZMod p))
    (facts : HostRamTouches.AccessFacts input.ram) (key : ZMod p × ZMod p)
    (same : HostHintReadPartition.clock input.previous = key) :
    TimedGrounding.TouchOK (clkNat key.1 key.2) (input.ram.prior, clkNat key.1 key.2) input.ram.pushed := by
  have time := congrArg (fun clock : ZMod p × ZMod p => clkNat clock.1 clock.2) same
  change clkNat input.ram.clk_high input.ram.clockLow = clkNat key.1 key.2 at time
  simpa only [time] using facts.touch

/-- Filtering the physical word tables by a handler clock puts every retained touch in that
same execution window, including the final padding word. -/
theorem call_word_touches {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    {names : ((HostLocalCore.tables image source
      ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image source others resources channels names))
    (interface : ExtensionInterface others resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel byteChannel.toRaw)
    (key : ZMod p × ZMod p) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (HostHintReadPartition.tablesFor key (wordTables witness) witness.data (wordTables_aligned witness)) witness.data,
      TimedGrounding.TouchOK (clkNat key.1 key.2)
        ((HintReadCoverage.rowInput row).ram.prior, clkNat key.1 key.2)
        (HintReadCoverage.rowInput row).ram.pushed := by
  intro row member
  rw [HostHintReadPartition.rows_for] at member
  obtain ⟨present, clock⟩ := List.mem_filter.mp member
  have facts := word_touches witness interface constraints balanced row present
  exact touch_at_clock _ facts key (of_decide_eq_true clock)

/-- Every physical consumer's prior/new pair occurs in the full interior, with order and
duplicate occurrences preserved. The statement also retains the mandatory padding words. -/
theorem word_memory_sublist {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    {names : ((HostLocalCore.tables image source
      ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup}
    (witness : EnsembleWitness (ensemble image source others resources channels names)) :
    ((TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness) witness.data).flatMap (fun row =>
      [memoryChannel.pulledValue (HintReadCoverage.rowInput row).ram.prior,
       memoryChannel.pushedValue (HintReadCoverage.rowInput row).ram.pushed])).Sublist
      ((HostLocalCore.memoryInterior witness).map TypedInteraction.raw) := by
  rw [HostLocalCore.memoryInterior_raw, ← HintReadWriteLedger.memory_ledger _ witness.data (wordTables_aligned witness)]
  have suffix : (witness.tables.drop 62).Sublist (witness.tables.drop 6) := by
    simpa only [List.drop_drop] using List.drop_sublist 56 (witness.tables.drop 6)
  have physical : (wordTables witness).Sublist (witness.tables.drop 6) :=
    ((List.take_sublist 2 _).trans (List.drop_sublist _ _)).trans suffix
  exact physical.flatMap _

private theorem word_memoryBinary (last : Bool) :
    NativeCore.MemoryBinary (HintReadCoverage.view (p := p) last).component := by
  intro data physical _ interaction member
  rw [HintReadWriteLedger.row_memory_values (last, Environment.fromArray physical data)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact signedVal_binary_of_selector_gated (1 : ZMod p) _ (Or.inr rfl) (Or.inl rfl)
  · exact signedVal_binary_of_selector_gated (1 : ZMod p) _ (Or.inr rfl) (Or.inr (Or.inr rfl))

private theorem word_typed_memory (row : HintReadCoverage.Row (p := p)) :
    typedInteractionValuesWith (HintReadCoverage.view row.1).component.operations memoryChannel row.2 =
      [TypedInteraction.pulledIfValue memoryChannel 1 (HintReadCoverage.rowInput row).ram.prior,
       TypedInteraction.pushedIfValue memoryChannel 1 (HintReadCoverage.rowInput row).ram.pushed] := by
  apply List.map_injective_iff.mpr TypedInteraction.raw_injective
  simp only [typedInteractionValuesWith_raw, List.map_cons, List.map_nil,
    TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw]
  exact HintReadWriteLedger.row_memory_values row

private theorem word_push_bound (last : Bool) (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (component : table.component = (HintReadCoverage.view last).component)
    (constraints : table.Constraints data) (bytes : table.ChannelGuarantees data byteChannel.toRaw) :
    ∀ message ∈ producedMessages (typedTableInteractionsWith table data memoryChannel),
      MemoryMsg.ClkBound message := by
  intro message member
  rw [typedTableInteractionsWith, producedMessages_flatMap] at member
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp member
  have checked := constraints physical physicalMem
  have byte := bytes physical physicalMem
  rw [component] at checked byte emitted
  rw [Component.constraintsHold_iff] at checked
  rw [Component.channelGuarantees_iff] at byte
  simp only [HintReadCoverage.view, Component.rowOperations, HintReadWordChip.circuit] at checked byte
  have bounds := word_access last (varFromOffset HintReadWordChip.Inputs 0) (size HintReadWordChip.Inputs)
    (Environment.fromArray physical data) checked byte
  rw [eval_varFromOffset_valueFromOffset] at bounds
  rw [word_typed_memory (last, Environment.fromArray physical data)] at emitted
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  have pos : signedVal (1 : ZMod p) = 1 := by
    rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  have neg : signedVal (-1 : ZMod p) = -1 := by
    rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  simp [producedMessages, pos, neg] at emitted
  exact emitted ▸ bounds.pushLow

/-- The installed source registry's non-word auxiliaries are statically Memory-silent. -/
theorem source_memory_silent (source : ExecutionSnapshot) :
    ∀ component ∈ (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      sourceResources source.host.io.hints,
      memoryChannel.toRaw ∉ component.circuit.channels := by
  have checked : ((receiver (p := p) :: HostCallReceivers.available).map
      (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
      sourceResources source.host.io.hints).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        (memoryChannel (p := p)).toRaw.name) = true := rfl
  intro component member used
  have silent := List.all_eq_true.mp checked component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

private theorem source_memoryBinary (source : ExecutionSnapshot) :
    ∀ component ∈ (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      (wordResources ++ sourceResources source.host.io.hints),
      NativeCore.MemoryBinary component := by
  intro component member
  have split : component ∈ wordResources ∨ component ∈
      (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
        sourceResources source.host.io.hints := by
    simpa only [List.mem_append, or_assoc, or_left_comm, or_comm] using member
  rcases split with word | other
  · simp only [wordResources, List.mem_cons, List.not_mem_nil, or_false] at word
    rcases word with rfl | rfl <;> exact word_memoryBinary _
  · exact NativeCore.memoryBinary_of_silent component (source_memory_silent source component other)

/-- None of the installed source-backed hint components contributes a Program fetch. -/
theorem source_program_silent (source : ExecutionSnapshot) :
    ∀ component ∈ (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      (wordResources ++ sourceResources source.host.io.hints),
      programChannel.toRaw ∉ component.circuit.channels := by
  have checked : ((receiver (p := p) :: HostCallReceivers.available).map
      (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
      (wordResources ++ sourceResources source.host.io.hints)).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        (programChannel (p := p)).toRaw.name) = true := rfl
  intro component member used
  have silent := List.all_eq_true.mp checked component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

/-- The installed host resources preserve private boundary ordering and both fixed membership channels. -/
theorem source_boundary_silent (source : ExecutionSnapshot)
    (channel : RawChannel (ZMod p))
    (boundary : channel ∈ [(OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
      source.sail.memorySnapshot.registerTable.channel.toRaw,
      (InitialMemoryLookup.membership source.sail.memorySnapshot.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw]) :
    ∀ component ∈ (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      (wordResources ++ sourceResources source.host.io.hints),
      channel ∉ component.circuit.channels := by
  have checked : ((receiver (p := p) :: HostCallReceivers.available).map
      (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
      (wordResources ++ sourceResources source.host.io.hints)).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        channel.name) = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at boundary
    rcases boundary with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · simp only [Channel.toRaw_name, StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows]
      rfl
    · simp only [Channel.toRaw_name, StaticTable.channel, InitialMemoryLookup.membership]
      rfl
  intro component member used
  have silent := List.all_eq_true.mp checked component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {channels : List (RawChannel (ZMod p))}

/-- The complete assembly's actual membership ledger survives both physical projections. -/
theorem source_membership_balance
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (balanced : witness.BalancedChannels) :
    ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).BalancedChannel channel := by
  intro channel known
  change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)).interactionsWith _)
  rw [HostLocalCore.localWitness_membership _ channel known (source_boundary_silent source _ (by
    simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
      List.not_mem_nil, or_false] at known ⊢
    tauto))]
  exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _ (by
    simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
      List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl <;> simp [LocalCore.baseEnsemble])

/-- The installed source/queue assembly closes the host word access facts without a caller
supplying a channel interface or any Memory guarantee. -/
theorem source_word_touches
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) (HostHintQueueBoundary.projected witness).data,
      HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram :=
  word_touches (HostHintQueueBoundary.projected witness)
    (source_interface source.host.io.hints)
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.record_channels witness balanced).byte

/-- The installed source/queue/word assembly closes the complete Memory record permutation.
There is no Memory guarantee, host-currentness, or multiplicity premise from the caller. -/
theorem source_memory_records_perm
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
      (LocalCore.sourceWitness (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ++
      producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))).Perm
    (FinalMemoryEnsemble.records
      (LocalCore.finalWitness (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ++
      consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))) :=
  HostLocalCore.memory_records_perm (HostHintQueueBoundary.projected witness)
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])) (source_memoryBinary source)

/-- All pushes in the installed full Memory interior have bounded low clocks, including
original instructions, refreshes, wrapper read-backs, and every physical hint word. -/
theorem source_memory_push_bound (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ message ∈ producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness)),
      MemoryMsg.ClkBound message := by
  let retained := HostHintQueueBoundary.projected witness
  have checked : retained.Constraints := by exact HostHintQueueBoundary.projected_constraints witness constraints
  have physicalChecks : ∀ table ∈ retained.tables, table.Constraints retained.data :=
    (EnsembleWitness.constraints_iff retained).mp checked
  have byteBalanced := (HostHintQueueBoundary.record_channels witness balanced).byte
  have bytes := byte_guarantees retained (source_interface source.host.io.hints) checked byteBalanced
  apply HostLocalCore.memoryInterior_push_bound valid retained checked bytes
  · change BalancedInteractions ((HostLocalCore.localWitness retained).interactionsWith programChannel.toRaw)
    rw [HostLocalCore.localWitness_program retained (source_program_silent source)]
    exact HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  · intro table member
    have componentMem := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [HostLocalCore.auxiliaryTables_components] at componentMem
    have split : table.component ∈ wordResources ∨ table.component ∈
        (receiver (p := p) :: HostCallReceivers.available).map (·.component) ++ sourceResources source.host.io.hints := by
      simpa only [List.mem_append, or_assoc, or_left_comm, or_comm] using componentMem
    have present : table ∈ retained.tables := List.mem_of_mem_drop member
    have tableChecked : table.Constraints retained.data := physicalChecks table present
    have tableBytes : table.ChannelGuarantees retained.data byteChannel.toRaw := bytes table present
    rcases split with word | other
    · simp only [wordResources, List.mem_cons, List.not_mem_nil, or_false] at word
      rcases word with component | component
      · exact word_push_bound false table retained.data component tableChecked tableBytes
      · exact word_push_bound true table retained.data component tableChecked tableBytes
    · have silent := table.interactionsWith_nil_of_channel_not_mem (data := retained.data)
        (source_memory_silent source table.component other)
      have typed : typedTableInteractionsWith table retained.data memoryChannel = [] := by
        apply (List.map_eq_nil_iff (f := TypedInteraction.raw)).mp
        rwa [typedTableInteractionsWith_raw]
      simp [typed, producedMessages]

/-- Full record conservation supplies the prior low-clock bound for every consumed Memory
record. This includes appended host accesses and uses no prior Memory guarantees. -/
theorem source_memory_prior_bound (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ message ∈ consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness)),
      MemoryMsg.ClkBound message := by
  intro message member
  have produced := (source_memory_records_perm witness constraints balanced).mem_iff.mpr
    (List.mem_append_right _ member)
  rcases List.mem_append.mp produced with sourceRecord | push
  · have checked := HostHintQueueBoundary.projected_constraints witness constraints
    have bytes := HostLocalCore.localWitness_byte (HostHintQueueBoundary.projected witness)
      (auxiliaryInterface (source_interface source.host.io.hints)) checked
      (HostHintQueueBoundary.record_channels witness balanced).byte
    have specs := LocalCore.sourceTables_spec_of_channels _
      (HostLocalCore.localWitness_constraints _ checked) bytes (source_membership_balance witness balanced)
    exact ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables _ specs
      message sourceRecord).2.1
  · exact source_memory_push_bound valid witness constraints balanced message push

/-- Every installed HINT_READ predecessor is strictly earlier than its physical write.
Both clock bounds now follow from the complete assembly's own constraints and balance. -/
theorem source_word_order (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) (HostHintQueueBoundary.projected witness).data,
      MemoryMsg.timeNat (HintReadCoverage.rowInput row).ram.prior <
        MemoryMsg.timeNat (HintReadCoverage.rowInput row).ram.pushed := by
  intro row member
  apply (source_word_touches witness constraints balanced row member).order
  apply source_memory_prior_bound valid witness constraints balanced
  have rawMem := (word_memory_sublist (HostHintQueueBoundary.projected witness)).subset
    (List.mem_flatMap.mpr ⟨row, member, List.mem_cons_self⟩)
  obtain ⟨interaction, present, same⟩ := List.mem_map.mp rawMem
  have typed : interaction = TypedInteraction.pulledIfValue memoryChannel 1 (HintReadCoverage.rowInput row).ram.prior :=
    TypedInteraction.raw_injective same
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  have negative : signedVal interaction.mult = -1 := by
    rw [typed, TypedInteraction.pulledIfValue_mult, signedVal_neg_is_real hp (Or.inr rfl),
      ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  have consumed := TypedInteraction.message_mem_consumedMessages interaction _ present negative
  simpa only [typed, TypedInteraction.pulledIfValue_message] using consumed

/-- Both physical boundary inventories are unique on the installed assembly's own private
ordering channels, giving the full host Memory ledger its per-location frontier equation. -/
theorem source_memory_frontier_balance
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    TimedGrounding.optMS (LocalCore.memoryInitialFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))) : Multiset _) =
      TimedGrounding.optMS (LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.projected witness))) : Multiset _) :=
  HostLocalCore.memory_frontier_balance (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface (source_interface source.host.io.hints))
    (source_boundary_silent source _ (List.mem_cons_self ..))
    (source_boundary_silent source _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (fun channel known => source_boundary_silent source channel (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known ⊢
      tauto))
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.record_channels witness balanced).byte
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced _
      (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels]))
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced _ (by simp [LocalCore.baseEnsemble]))
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced _ (by simp [LocalCore.baseEnsemble]))
    (fun channel known => HostHintQueueBoundary.projected_core_balancedChannel witness balanced channel (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons,
        List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl <;> simp [LocalCore.baseEnsemble]))
    (source_memoryBinary source) loc

end SP1Clean.Soundness.HostHintReadLocal
