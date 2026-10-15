import SP1Clean.Soundness.HostTableRegistry

/-! # Commitment histories in the installed local machine

The selected eight slot tables and their terminal are read from the actual mixed witness.
All other physical contributions on that bank's private channel are excluded by circuit
metadata. Verifier-owned endpoints therefore let the existing bank history theorem apply
without an auxiliary balance, provider, or semantic boundary premise.
-/

namespace SP1Clean.Soundness.HostHintReadBanks

open Circuit Air.Flat Model.Core HostHintReadLocal HostHintReadHandoff HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance bankLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
  {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

abbrev Witness := EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal
  HostCallReceivers.available (sourceResources source.host.io.hints) channels
    (source_unique_names image source source.host.io.hints))

private def start (deferred : Bool) : ℕ := if deferred then 11 else 3
private def gap (deferred : Bool) : ℕ := if deferred then 7 else 14

private def selected {α : Type*} (deferred : Bool) (tables : List α) : List α :=
  (tables.drop (start deferred)).take 8 ++
    (tables.drop (start deferred + 8 + gap deferred)).take 1

private def outside {α : Type*} (deferred : Bool) (tables : List α) : List α :=
  tables.take (start deferred) ++ (tables.drop (start deferred + 8)).take (gap deferred) ++
    tables.drop (start deferred + 8 + gap deferred + 1)

/-- The physical COMMIT or deferred tables, followed by that bank's physical terminal. -/
def bankTables (deferred : Bool) (witness : Witness (p := p) (image := image) (source := source)
    (final := final) (bankFinal := bankFinal) (channels := channels)) : List (Table (ZMod p)) :=
  indices.map fun index =>
    (HostTableRegistry.installedBankSlot image source final bankFinal channels deferred index).table witness

private theorem auxiliary_length
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.tables.drop 62).length = 27 := by
  have size := congrArg List.length (HostTableRegistry.auxiliary_components witness)
  simp only [List.length_map] at size
  exact size

private theorem slice_eq_ofFn {α : Type*} (rows : List α) (offset count : ℕ)
    (bound : offset + count ≤ rows.length) :
    (rows.drop offset).take count =
      List.ofFn (fun index : Fin count => rows[offset + index.val]'(by have := index.isLt; omega)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro index left right
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- The registered references select exactly the retained receiver/terminal inventory. -/
private theorem bankTables_eq (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    bankTables deferred witness = selected deferred (witness.tables.drop 62) := by
  have size := auxiliary_length witness
  simp only [bankTables, indices, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, TableSlot.table, HostTableRegistry.installedBankSlot_index]
  rw [← List.ofFn_eq_map]
  cases deferred <;>
    simp only [selected, start, gap, Bool.false_eq_true, if_false, if_true, Nat.reduceAdd] <;>
    rw [slice_eq_ofFn _ _ 8 (by omega), slice_eq_ofFn _ _ 1 (by omega)] <;>
    simp only [List.ofFn_succ, List.ofFn_zero, List.getElem_drop, HostTableRegistry.bankPosition,
      Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.reduceAdd,
      Nat.add_assoc]

/-- The original physical receiver prefix is retained under verifier projection. -/
theorem receiver_tables
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    HostLocalHandoff.receiverTables (HostHintQueueBoundary.projected witness) =
      (witness.tables.drop 62).take 21 := by
  change ((HostHintQueueBoundary.projected witness).tables.drop 62).take 21 = _
  rw [HostHintQueueBoundary.projected_drop witness 62 (by decide)]

private theorem read_calls (deferred : Bool) (slots : List (Fin 8))
    (tables terminal : List (Table (ZMod p))) (data : ProverData (ZMod p)) (size : slots.length = tables.length) :
    (TransitionView.readIndexedRows (slots.map some ++ [none]) (tables ++ terminal) data).filterMap call? =
      ReceiverView.messages (slots.map (HostCallReceivers.commit deferred)) tables data := by
  induction slots generalizing tables with
  | nil =>
      have empty : tables = [] := List.length_eq_zero_iff.mp size.symm
      subst tables
      cases terminal <;> simp [TransitionView.readIndexedRows, call?, ReceiverView.messages]
  | cons slot slots ih =>
      cases tables with
      | nil => simp at size
      | cons table tables =>
          simp only [List.map_cons, List.cons_append, TransitionView.readIndexedRows,
            List.zip_cons_cons, List.flatMap_cons, List.filterMap_append] at ih ⊢
          rw [ReceiverView.messages_cons, ih tables (by simpa using size)]
          simp only [List.filterMap_map, Function.comp_def, call?, Option.map_some, List.filterMap_eq_map',
            ReceiverView.tableMessages, HostCallReceivers.commit_message]

/-- Erasing the bank terminal leaves precisely its eight physical handler tables. -/
theorem calls_eq_slot_tables (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (TransitionView.readIndexedRows indices (bankTables deferred witness) witness.data).filterMap call? =
      ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        (((HostLocalHandoff.receiverTables (HostHintQueueBoundary.projected witness)).drop
          (if deferred then 11 else 3)).take 8) witness.data := by
  have size := auxiliary_length witness
  have slotsSize : (List.finRange 8).length =
      (((witness.tables.drop 62).drop (start deferred)).take 8).length := by
    simp only [List.length_drop] at size
    cases deferred <;> simp [start, List.length_take, List.length_drop] <;> omega
  have read := read_calls deferred (List.finRange 8)
    (((witness.tables.drop 62).drop (start deferred)).take 8)
    (((witness.tables.drop 62).drop (start deferred + 8 + gap deferred)).take 1) witness.data slotsSize
  rw [receiver_tables]
  simp only [List.drop_take, List.take_take]
  cases deferred <;> simpa only [bankTables_eq, selected, start, indices, Bool.false_eq_true,
    if_false, if_true, Nat.reduceSub, min_eq_left (by decide : 8 ≤ 18),
    min_eq_left (by decide : 8 ≤ 10), List.ofFn_eq_map] using read

theorem tables_aligned (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    List.Forall₂ (fun index table => (view deferred index).component = table.component)
      indices (bankTables deferred witness) := by
  have mapped : (bankTables deferred witness).map (·.component) =
      indices.map (fun index => (view deferred index).component) := by
    simp only [bankTables, List.map_map, Function.comp_def, TableSlot.table_component]
  have aligned : List.Forall₂ (· = ·)
      (indices.map fun index => (view (p := p) deferred index).component)
      ((bankTables deferred witness).map (·.component)) := by
    rw [List.forall₂_eq_eq_eq, mapped]
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using aligned

private theorem bank_mem (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (table : Table (ZMod p)) (member : table ∈ bankTables deferred witness) :
    table ∈ (HostHintQueueBoundary.projected witness).tables := by
  have within : table ∈ witness.tables.drop 62 := by
    rw [bankTables_eq] at member
    rcases List.mem_append.mp member with member | member <;>
      exact List.mem_of_mem_drop (List.mem_of_mem_take member)
  apply List.mem_of_mem_drop (i := 62)
  rw [HostHintQueueBoundary.projected_drop witness 62 (by decide)]
  exact within

private theorem flatMap_selected {α β : Type*} (deferred : Bool) (tables : List α) (f : α → List β)
    (silent : ∀ item ∈ outside deferred tables, f item = []) :
    tables.flatMap f = (selected deferred tables).flatMap f := by
  have first := congrArg (List.flatMap f) (List.take_append_drop (start deferred) tables).symm
  have slots := congrArg (List.flatMap f) (List.take_append_drop 8 (tables.drop (start deferred))).symm
  have middle := congrArg (List.flatMap f)
    (List.take_append_drop (gap deferred) (tables.drop (start deferred + 8))).symm
  have terminal := congrArg (List.flatMap f)
    (List.take_append_drop 1 (tables.drop (start deferred + 8 + gap deferred))).symm
  have empty : (outside deferred tables).flatMap f = [] := List.flatMap_eq_nil_iff.mpr silent
  simp only [outside, List.flatMap_append, List.append_eq_nil_iff] at empty
  simp only [List.flatMap_append, List.drop_drop] at first slots middle terminal
  rw [first, slots, middle, terminal, empty.1.1, empty.1.2, empty.2]
  simp only [selected, List.flatMap_append, List.nil_append, List.append_nil]

private theorem auxiliary_interactions (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.tables.drop 62).flatMap (·.interactionsWith witness.data (HostCommitChip.stateChannel deferred).toRaw) =
      (bankTables deferred witness).flatMap (·.interactionsWith witness.data (HostCommitChip.stateChannel deferred).toRaw) := by
  rw [bankTables_eq]
  apply flatMap_selected
  have checked : (outside deferred ((receiver (p := p) :: HostCallReceivers.available).map (·.component) ++
      (wordResources ++ sourceResources source.host.io.hints))).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        (HostCommitChip.stateChannel (p := p) deferred).toRaw.name) = true := by cases deferred <;> rfl
  intro table member
  apply Table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  have components := HostTableRegistry.auxiliary_components witness
  rw [List.map_drop] at components
  simp only [outside, List.map_append, List.map_take, List.map_drop, components] at mapped
  have absent := List.all_eq_true.mp checked table.component mapped
  intro used
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
  contradiction

private theorem bank_fresh (deferred : Bool) :
    (HostCommitChip.stateChannel deferred).toRaw ∉
      (LocalCore.ensemble (p := p) image source).channels := by
  intro used
  change (HostCommitChip.stateChannel deferred).toRaw ∈
    (LocalCore.baseEnsemble image source).channels ++ [LocalCore.sourceChannel image source] at used
  rcases List.mem_append.mp used with used | used
  · have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    cases deferred <;>
      simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
        SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, HostCommitChip.stateChannel,
        Channels.stateChannel, Channels.memoryChannel, Channels.byteChannel, Channels.programChannel,
        Channels.exitChannel, Channels.syscallChannel, Channels.publicValuesChannel,
        StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, Channel.toRaw] at present
  · have same := (List.mem_singleton.mp used).symm
    have heads := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList[4]?) same
    dsimp only [LocalCore.sourceChannel, PublicVerifier.channel, VerifierChannel.channel,
      Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName] at heads
    rw [String.toList_append] at heads
    cases deferred <;> simp [LocalSourceBoundary.checker, HostCommitChip.stateChannel] at heads

private theorem wrapper_bank_silent (deferred : Bool) :
    (HostCommitChip.stateChannel deferred).toRaw ∉ (HostCallLedger.producer (p := p)).circuit.channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  cases deferred <;> change false = true at present <;> exact Bool.noConfusion present

/-- The complete bank ledger retains physical rows and the verifier's two endpoint occurrences. -/
theorem interactions (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.interactionsWith (HostCommitChip.stateChannel deferred).toRaw).Perm
      ([(HostCommitChip.stateChannel deferred).pushedValue
          (HostCommitBoundary.start (HostCommitEnsemble.sourceValues deferred source.host)),
        (HostCommitChip.stateChannel deferred).pulledValue
          (HostCommitBoundary.final (HostCommitEnsemble.sourceValues deferred bankFinal))] ++
        (bankTables deferred witness).flatMap
          (·.interactionsWith witness.data (HostCommitChip.stateChannel deferred).toRaw)) := by
  have wrapper : (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)).interactionsWith
      (HostHintQueueBoundary.projected witness).data (HostCommitChip.stateChannel deferred).toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    exact wrapper_bank_silent deferred
  have split := HostLocalCore.interactions_split_new (HostHintQueueBoundary.projected witness)
    (HostCommitChip.stateChannel deferred).toRaw (by
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨{ circuit := HostCommitBoundary.terminal deferred }, ?_, ?_⟩
      · apply List.mem_append_right
        apply List.mem_append_right
        cases deferred <;> simp [sourceResources]
      · simp [HostCommitBoundary.terminal, circuit_norm]) (bank_fresh deferred)
    (by cases deferred <;> simp [HostCommitChip.stateChannel, WritePermissionProvider.channel, Channel.toRaw])
  rw [wrapper, List.nil_append] at split
  have tail : HostLocalCore.auxiliaryTables (HostHintQueueBoundary.projected witness) =
      witness.tables.drop 62 := HostHintQueueBoundary.projected_drop witness 62 (by decide)
  rw [tail, HostHintQueueBoundary.projected_data, auxiliary_interactions] at split
  have ledger := HostHintQueueBoundary.interactions_split witness (HostCommitChip.stateChannel deferred).toRaw
    (List.mem_append_right _ (by cases deferred <;>
      simp [HostHintQueueBoundary.boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm]))
  rw [split, ClosedVerifier.singleton_interactions, ClosedVerifier.operations, HostBoundary.closed_main,
    HostBoundary.bank_values] at ledger
  exact ledger.trans (List.perm_append_comm ..)

/-- Both bank endpoints and every local specification follow from the complete mixed AIR.
The fold here contains the selected bank's calls; `HostBankCPUReplay` supplies CPU-order agreement. -/
theorem ordered_history (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices (bankTables deferred witness) witness.data) ∧
      Walk.IsWalk (edge deferred)
        (HostCommitBoundary.start (HostCommitEnsemble.sourceValues deferred source.host))
        (HostCommitBoundary.final (HostCommitEnsemble.sourceValues deferred bankFinal)) path ∧
      path.foldlM (execute deferred policy context) source.host =
        some ((HostCommitBoundary.final (HostCommitEnsemble.sourceValues (p := p) deferred bankFinal)).apply deferred source.host) := by
  have checked := (EnsembleWitness.constraints_iff _).mp
    (HostHintQueueBoundary.projected_constraints witness constraints)
  have bytes := byte_guarantees (HostHintQueueBoundary.projected witness)
    (source_interface source.host.io.hints) (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.record_channels witness balanced).byte
  rw [HostHintQueueBoundary.projected_data] at checked bytes
  have physical (table : Table (ZMod p)) (member : table ∈ bankTables deferred witness) :
      table ∈ (HostHintQueueBoundary.projected witness).tables := bank_mem deferred witness table member
  have member : (HostCommitChip.stateChannel deferred).toRaw ∈
      (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
        (sourceResources source.host.io.hints) channels
        (source_unique_names image source source.host.io.hints)).channels := by
    apply List.mem_append_left
    apply List.mem_append_right
    cases deferred <;> simp [HostHintQueueBoundary.boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm]
  have bank := balancedInteractions_of_perm (balanced _ member) (interactions deferred witness)
  have history := HostCommitBank.ordered_history deferred (bankTables deferred witness) witness.data
    (HostCommitEnsemble.sourceValues deferred source.host) (HostCommitEnsemble.sourceValues deferred bankFinal)
    (tables_aligned deferred witness) (fun table member => checked table (physical table member))
    (fun table member => bytes table (physical table member)) bank policy characteristic context source.host
  simpa only [HostCommitEnsemble.source_apply] using history

/-- The actual bank calls, in strict clock order, execute from the source bank to its committed
final words. Only the administrative terminal is erased. `HostBankCPUReplay` connects this fold
to the CPU tape; neither a call-order premise nor a local specification is supplied here. -/
theorem ordered_calls (deferred : Bool)
    (witness : Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext) :
    ∃ calls : List (HostCallChip.Message (ZMod p)),
      calls.Perm ((TransitionView.readIndexedRows indices (bankTables deferred witness) witness.data).filterMap call?) ∧
      (calls.map fun call => Semantics.clkNat call.clk_high call.clk_low).Pairwise (· < ·) ∧
      calls.foldlM (executeCall deferred policy context) source.host =
        some ((HostCommitBoundary.final (HostCommitEnsemble.sourceValues (p := p) deferred bankFinal)).apply
          deferred source.host) := by
  obtain ⟨path, perm, walk, executed⟩ :=
    ordered_history deferred witness constraints balanced policy characteristic context
  have checked := (EnsembleWitness.constraints_iff _).mp
    (HostHintQueueBoundary.projected_constraints witness constraints)
  have bytes := byte_guarantees (HostHintQueueBoundary.projected witness)
    (source_interface source.host.io.hints) (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.record_channels witness balanced).byte
  rw [HostHintQueueBoundary.projected_data] at checked bytes
  have physical (table : Table (ZMod p)) (member : table ∈ bankTables deferred witness) :
      table ∈ (HostHintQueueBoundary.projected witness).tables := bank_mem deferred witness table member
  have specs := rows_spec_of_byte deferred (bankTables deferred witness) witness.data
    (tables_aligned deferred witness) (fun table member => checked table (physical table member))
    (fun table member => bytes table (physical table member))
  refine ⟨path.filterMap call?, perm.filterMap call?,
    calls_pairwise deferred walk (fun row member => specs row (perm.mem_iff.mp member)), ?_⟩
  rw [fold_calls, executed]

end SP1Clean.Soundness.HostHintReadBanks
