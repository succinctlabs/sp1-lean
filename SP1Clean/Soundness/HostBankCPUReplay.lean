import SP1Clean.Soundness.HostQueueCPUReplay
import SP1Clean.Soundness.HostHintReadBanks
import SP1Clean.Model.Core.BankReplay

/-! # Commitment histories agree with the ordered CPU tape

The complete HostCall permutation matches bank handler occurrences to CPU calls before any
projection. Selecting each bank's arguments preserves its clock and multiplicity. Strict CPU
and bank chronology then identifies the lists, including repeated overwrites. The semantic bank
fold is a projection of the existing full host interpreter.
-/

namespace SP1Clean.Soundness.HostBankCPUReplay

open Circuit Air.Flat Model.Core HostHintReadLocal HostQueueCallProjection NativeCore Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance replayLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance replayClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def label (message : HostCallChip.Message (ZMod p)) : ℕ × (BitVec 64 × BitVec 64) :=
  (clkNat message.clk_high message.clk_low, Word.toBitVec64 message.arg1, Word.toBitVec64 message.arg2)

def stamped (deferred : Bool) (message : HostCallChip.Message (ZMod p)) :
    Option (ℕ × (BitVec 64 × BitVec 64)) :=
  (bankCall? deferred (Word.toBitVec64 message.code) (Word.toBitVec64 message.arg1)
    (Word.toBitVec64 message.arg2)).map fun args => (clkNat message.clk_high message.clk_low, args)

noncomputable def stampedCPU (deferred : Bool) (data : ProverData (ZMod p)) (row : ExecutionRow p) :
    Option (ℕ × (BitVec 64 × BitVec 64)) :=
  (bankEvent? deferred row.event).map fun args => (StateMsg.timeNat (row.edge data).1, args)

private theorem code_value (deferred : Bool) :
    Word.toBitVec64 (HostCommitChip.codeWord (R := ZMod p) deferred) = (bankKind deferred).code := by
  have small (n : ℕ) (bound : n < 2 ^ 17) : (n : ZMod p).val = n :=
    ZMod.val_natCast_of_lt (lt_trans bound (Fact.out (p := 2 ^ 17 < p)))
  have sixteen : (16 : ZMod p).val = 16 := small 16 (by decide)
  have twentySix : (26 : ZMod p).val = 26 := small 26 (by decide)
  cases deferred <;> simp [HostCommitChip.codeWord, bankKind, SyscallKind.code,
    Word.toBitVec64, Word.toNat, sixteen, twentySix]

omit [Fact (2 ^ 25 < p)] in
private theorem messages_project {Label : Type*} (views : List (HostLocalHandoff.Receiver (p := p)))
    (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component) views tables)
    (constraints : ∀ table ∈ tables, table.Constraints data)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees data Channels.byteChannel.toRaw)
    (project expected : HostCallChip.Message (ZMod p) → Option Label)
    (same : ∀ receiver ∈ views, ∀ env, receiver.component.operations.ConstraintsHold env →
      receiver.component.operations.ChannelGuarantees Channels.byteChannel.toRaw env →
      project (receiver.message env) = expected (receiver.message env)) :
    (ReceiverView.messages views tables data).filterMap project =
      (ReceiverView.messages views tables data).filterMap expected := by
  induction aligned with
  | nil => rfl
  | @cons receiver table views tables component aligned ih =>
      rw [ReceiverView.messages_cons, List.filterMap_append, List.filterMap_append]
      congr 1
      · simp only [ReceiverView.tableMessages, List.filterMap_map]
        apply List.filterMap_congr
        intro physical member
        exact same receiver (List.mem_cons_self ..) _
          (component ▸ constraints table (List.mem_cons_self ..) physical member)
          (component ▸ bytes table (List.mem_cons_self ..) physical member)
      · exact ih (fun table member => constraints table (List.mem_cons_of_mem _ member))
          (fun table member => bytes table (List.mem_cons_of_mem _ member))
          (fun receiver member => same receiver (List.mem_cons_of_mem _ member))

private theorem commit_projection (deferred selected : Bool) (slot : Fin 8)
    (env : Environment (ZMod p))
    (constraints : (HostCallReceivers.commit (p := p) selected slot).component.operations.ConstraintsHold env)
    (bytes : (HostCallReceivers.commit (p := p) selected slot).component.operations.ChannelGuarantees
      Channels.byteChannel.toRaw env) :
    stamped deferred ((HostCallReceivers.commit selected slot).message env) =
      if deferred = selected then some (label ((HostCallReceivers.commit selected slot).message env)) else none := by
  have spec := HostCommitBank.view_spec_of_byte selected (some slot) env constraints bytes
  change HostCommitChip.Spec selected slot (valueFromOffset HostCommitChip.Inputs 0 env) at spec
  rw [HostCallReceivers.commit_message]
  simp only [stamped, bankCall?, spec.1.1, code_value]
  cases deferred <;> cases selected <;> simp [bankKind, SyscallKind.code, label]

private theorem quiet_projection (deferred : Bool) (receiver : HostLocalHandoff.Receiver (p := p))
    (member : receiver ∈ [HostCallReceivers.halt, HostCallReceivers.enter]) (env : Environment (ZMod p))
    (constraints : receiver.component.operations.ConstraintsHold env)
    (bytes : receiver.component.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    stamped deferred (receiver.message env) = none := by
  rcases List.mem_cons.mp member with rfl | member
  · have spec := HostHaltChip.component_spec_of_byte env constraints bytes
    change HostHaltChip.Spec (valueFromOffset HostHaltChip.Inputs 0 env) at spec
    rw [HostCallReceivers.halt_message]
    cases deferred <;> simp [stamped, bankCall?, spec.1, bankKind, SyscallKind.code, Word.toBitVec64, Word.toNat]
  · have same := List.mem_singleton.mp member
    subst receiver
    have spec := HostEnterChip.component_spec_of_constraints env constraints
    change HostEnterChip.Spec (valueFromOffset HostEnterChip.Inputs 0 env) at spec
    have three : (3 : ZMod p).val = 3 := ZMod.val_natCast_of_lt
      (lt_trans (by decide : 3 < 2 ^ 17) (Fact.out (p := 2 ^ 17 < p)))
    rw [HostCallReceivers.enter_message]
    cases deferred <;> simp [stamped, bankCall?, spec.1, HostEnterChip.codeWord,
      bankKind, SyscallKind.code, Word.toBitVec64, Word.toNat, three]

private theorem queue_silent (deferred : Bool) (row : HostQueueOrder.Row (p := p))
    (valid : (HostQueueOrder.view row.1).component.Spec row.2) :
    stamped deferred (HostQueueCPUOrder.call row) = none := by
  have projected := (queue_projection row valid).2
  simp only [project, queueCallEvent?] at projected
  split_ifs at projected with length read
  · cases deferred <;> simp [stamped, bankCall?, length, bankKind, SyscallKind.code]
  · cases deferred <;> simp [stamped, bankCall?, read, bankKind, SyscallKind.code]

private theorem control_projection (deferred : Bool) (tables : List (Table (ZMod p)))
    (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component)
      ((HostCallReceivers.available (p := p)).take 18) tables)
    (constraints : ∀ table ∈ tables, table.Constraints data)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees data Channels.byteChannel.toRaw) :
    (ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18) tables data).filterMap (stamped deferred) =
      (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        ((tables.drop (if deferred then 10 else 2)).take 8) data).map label := by
  have sliced (start count : ℕ) : List.Forall₂ (fun receiver table => receiver.component = table.component)
      (((HostCallReceivers.available (p := p)).take 18).drop start |>.take count)
      ((tables.drop start).take count) := List.forall₂_take count (List.forall₂_drop start aligned)
  have quiet := messages_project _ _ data (sliced 0 2)
    (fun table member => constraints table (List.mem_of_mem_drop (List.mem_of_mem_take member)))
    (fun table member => bytes table (List.mem_of_mem_drop (List.mem_of_mem_take member)))
    (stamped deferred) (fun _ => none) (quiet_projection deferred)
  simp only [List.drop_zero] at quiet
  have commits (selected : Bool) := messages_project _ _ data (sliced (if selected then 10 else 2) 8)
    (fun table member => constraints table (List.mem_of_mem_drop (List.mem_of_mem_take member)))
    (fun table member => bytes table (List.mem_of_mem_drop (List.mem_of_mem_take member)))
    (stamped deferred) (fun message => if deferred = selected then some (label message) else none)
    (fun receiver member env checked byte => by
      have slots : receiver ∈ List.ofFn (fun slot => HostCallReceivers.commit selected slot) := by
        cases selected <;> exact member
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp slots
      exact commit_projection deferred selected slot env checked byte)
  have length : tables.length = 18 := aligned.length_eq.symm
  have last : tables.drop 10 = (tables.drop 10).take 8 := by
    symm
    apply List.take_of_length_le
    simp [List.length_drop, length]
  rw [ReceiverView.messages_take_drop _ _ data 2]
  rw [ReceiverView.messages_take_drop (((HostCallReceivers.available (p := p)).take 18).drop 2) (tables.drop 2) data 8]
  simp only [List.filterMap_append, List.drop_drop]
  change _ ++ (_ ++ _) = _
  rw [show (ReceiverView.messages _ _ data).filterMap (stamped deferred) = [] from
    quiet.trans (by simp)]
  change [] ++ ((ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit false slot)
    ((tables.drop 2).take 8) data).filterMap (stamped deferred) ++
    (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit true slot)
      (tables.drop 10) data).filterMap (stamped deferred)) = _
  have committed := commits false
  have deferredCalls := commits true
  change (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit false slot)
    ((tables.drop 2).take 8) data).filterMap (stamped deferred) = _ at committed
  change (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit true slot)
    ((tables.drop 10).take 8) data).filterMap (stamped deferred) = _ at deferredCalls
  rw [last, committed, deferredCalls]
  cases deferred <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
    List.filterMap_eq_map', List.filterMap_none, List.nil_append, List.append_nil] <;> rfl

omit [Fact (2 ^ 25 < p)] in
private theorem control_slot_tables (deferred : Bool) (tables : List (Table (ZMod p))) :
    (((tables.drop 1).take 18).drop (if deferred then 10 else 2)).take 8 =
      (tables.drop (if deferred then 11 else 3)).take 8 := by
  cases deferred <;> simp only [Bool.false_eq_true, if_false, if_true, List.drop_take,
    List.take_take, List.drop_drop, Nat.reduceSub, Nat.reduceAdd, min_eq_left (by decide : 8 ≤ 16), min_self]

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}
  {resources : List (Component (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

private theorem project_split {Message Row Label : Type*}
    (project : Message → Option Label) (call : Row → Message)
    (messages control : List Message) (rows : List Row) (labels : List Label)
    (split : messages.Perm (rows.map call ++ control))
    (quiet : ∀ row ∈ rows, project (call row) = none)
    (selected : control.filterMap project = labels) :
    (messages.filterMap project).Perm labels := by
  have erased : (rows.map call).filterMap project = [] := by
    rw [List.filterMap_map]
    exact List.filterMap_eq_nil_iff.mpr quiet
  have projected := split.filterMap project
  rwa [List.filterMap_append, erased, List.nil_append, selected] at projected

private theorem control_calls (deferred : Bool)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (bytes : witness.BalancedChannel Channels.byteChannel.toRaw) :
    (ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18) (controlTables witness) witness.data).filterMap
      (stamped deferred) =
      (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        (((controlTables witness).drop (if deferred then 10 else 2)).take 8) witness.data).map label := by
  have aligned := ReceiverView.aligned_of_map_eq ((HostCallReceivers.available (p := p)).take 18)
    (controlTables witness) (by
      simp only [controlTables, List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
        List.map_cons, List.drop_succ_cons, List.drop_zero])
  exact control_projection deferred _ witness.data aligned
    (fun table member => constraints table (controlTables_mem witness table member))
    (fun table member => byte_guarantees _ interface constraints bytes table (controlTables_mem witness table member))

private theorem calls_projection_generic (deferred : Bool)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data) :
    ((HostLocalHandoff.calls witness).filterMap (stamped deferred)).Perm
      ((ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        (((HostLocalHandoff.receiverTables witness).drop (if deferred then 11 else 3)).take 8) witness.data).map label) := by
  apply project_split (stamped deferred) HostQueueCPUOrder.call _ _ _ _ (calls_split witness)
  · intro row member
    exact queue_silent deferred row (HostQueueOrder.rows_spec _ witness.data (queueTables_aligned witness) specs row member)
  · simpa only [controlTables, control_slot_tables] using
      control_calls deferred witness interface constraints bytes

/-- Selecting a bank from the complete physical handoff retains exactly its handler occurrences. -/
theorem calls_projection (deferred : Bool)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((HostLocalHandoff.calls (HostHintQueueBoundary.projected witness)).filterMap (stamped deferred)).Perm
      (((TransitionView.readIndexedRows HostCommitBank.indices (HostHintReadBanks.bankTables deferred witness) witness.data).filterMap
        HostCommitBank.call?).map label) := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  rw [HostHintReadBanks.calls_eq_slot_tables]
  have projected := calls_projection_generic deferred (HostHintQueueBoundary.projected witness) interface checks records.byte
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks records)
  simpa only [HostHintQueueBoundary.projected_data] using projected

private theorem wrapper_projection (deferred : Bool) (data : ProverData (ZMod p))
    (input : HostCallChip.Inputs (ZMod p)) (flag : ZMod p) :
    stampedCPU deferred data (.syscall input.instruction) = stamped deferred (input.message flag) := by
  simp only [stampedCPU, ExecutionRow.event, bankEvent?, rawCode_syscallEventOfRow,
    arg1_syscallEventOfRow, arg2_syscallEventOfRow, stamped, HostCallChip.Inputs.message]
  rfl

private theorem syscall_projection (deferred : Bool) (data : ProverData (ZMod p))
    (env : Environment (ZMod p)) :
    stampedCPU deferred data (.syscall (HostCallLedger.input env).instruction) =
      stamped deferred (HostCallLedger.call env) :=
  wrapper_projection deferred data (HostCallLedger.input env) _

private theorem inventory_projection (deferred : Bool) (data : ProverData (ZMod p))
    (instructions : List (DecodedInstructionRow p)) (haltRows : List (HaltChip.Inputs (ZMod p)))
    (wrappers : List (Environment (ZMod p)))
    (codeZero : ∀ row ∈ haltRows, Word.toBitVec64 row.x5_memory.prev_value = 0) :
    ((instructions.map ExecutionRow.instruction ++ haltRows.map ExecutionRow.halt ++
      (wrappers.map fun env => ExecutionRow.syscall (HostCallLedger.input env).instruction)).filterMap
        (stampedCPU deferred data)) = (wrappers.map HostCallLedger.call).filterMap (stamped deferred) := by
  apply HostQueueCPUReplay.filterMap_inventory
  · intro row _
    rfl
  · intro row member
    cases deferred <;> simp only [stampedCPU, ExecutionRow.event, bankEvent?, haltEventOfRow,
      codeZero row member, bankCall?, bankKind, Bool.false_eq_true,
      SyscallKind.code, BitVec.reduceEq, ↓reduceIte, Option.map_none]
  · exact syscall_projection deferred data

private theorem cpu_inventory (deferred : Bool)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (constraints : witness.Constraints) :
    ((LocalCore.executionRows (HostLocalCore.localWitness witness)).filterMap (stampedCPU deferred witness.data)) =
      (HostCallLedger.calls (HostLocalCore.hostCallTable witness) witness.data).filterMap (stamped deferred) := by
  rw [LocalCore.executionRows, ← HostLocalCore.hostCallTable_projection, List.map_map]
  exact inventory_projection deferred witness.data _ _ _ (fun row member => HostQueueCPUReplay.halt_code
    (HostLocalCore.localWitness witness) (HostLocalCore.localWitness_constraints witness constraints) row member)

private theorem stampedCPU_time (deferred : Bool) (data : ProverData (ZMod p)) (row : ExecutionRow p)
    (stamp : ℕ × (BitVec 64 × BitVec 64)) (present : stampedCPU deferred data row = some stamp) :
    stamp.1 = StateMsg.timeNat (row.edge data).1 := by
  obtain ⟨args, _, rfl⟩ := Option.map_eq_some_iff.mp present
  rfl

private theorem ordered_projection (deferred : Bool) (data : ProverData (ZMod p))
    (cpu : List (ExecutionRow p)) (calls : List (HostCallChip.Message (ZMod p)))
    (same : (cpu.filterMap (stampedCPU deferred data)).Perm (calls.map label))
    (cpuSorted : (cpu.map fun row => StateMsg.timeNat (row.edge data).1).Pairwise (· < ·))
    (bankSorted : (calls.map fun call => clkNat call.clk_high call.clk_low).Pairwise (· < ·)) :
    cpu.filterMap (stampedCPU deferred data) = calls.map label := by
  apply same.eq_of_pairwise (le := fun a b => a.1 < b.1)
  · intro a b _ _ forward backward
    exact (Nat.lt_asymm forward backward).elim
  · apply (List.pairwise_map.mp cpuSorted).filterMap
    intro a b ordered x hx y hy
    rw [stampedCPU_time deferred data a x hx, stampedCPU_time deferred data b y hy]
    exact ordered
  · exact List.pairwise_map.mpr (List.pairwise_map.mp bankSorted)

private theorem cpu_calls (deferred : Bool)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    {cpu : List (ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness))) :
    (cpu.filterMap (stampedCPU deferred witness.data)).Perm
      ((ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        (((HostLocalHandoff.receiverTables witness).drop (if deferred then 11 else 3)).take 8) witness.data).map label) := by
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface)
    constraints calls
  exact (exhaustive.filterMap (stampedCPU deferred witness.data)).trans
    ((List.Perm.of_eq (cpu_inventory deferred witness constraints)).trans
      ((handoff.filterMap (stamped deferred)).trans
        (calls_projection_generic deferred witness interface constraints bytes specs)))

private theorem cpu_ordered (deferred : Bool)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (handoff : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    {cpu : List (ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    {calls : List (HostCallChip.Message (ZMod p))}
    (bankExhaustive : calls.Perm
      (ReceiverView.messages (List.ofFn fun slot => HostCallReceivers.commit deferred slot)
        (((HostLocalHandoff.receiverTables witness).drop (if deferred then 11 else 3)).take 8) witness.data))
    (bankSorted : (calls.map fun call => clkNat call.clk_high call.clk_low).Pairwise (· < ·)) :
    cpu.filterMap (stampedCPU deferred witness.data) = calls.map label := by
  have projected := cpu_calls deferred witness interface constraints handoff bytes specs exhaustive
  have edgeData : ExecutionRow.canonEdge (HostLocalCore.localWitness witness).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  have publicInput : (HostLocalCore.localWitness witness).publicInput = witness.publicInput := rfl
  have cpuSorted := LocalCore.ordered_times_pairwise (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints) ordering exhaustive
    (by simpa only [edgeData, publicInput] using walk)
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness witness).data witness.data] at cpuSorted
  exact ordered_projection deferred witness.data cpu calls (projected.trans (bankExhaustive.map label).symm)
    cpuSorted bankSorted

/-- Every ordered bank history is the same subsequence of the exhaustive CPU tape, including
the argument values and incoming clocks of repeated updates. -/
theorem cpu_projection (deferred : Bool)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    {calls : List (HostCallChip.Message (ZMod p))}
    (bankExhaustive : calls.Perm ((TransitionView.readIndexedRows HostCommitBank.indices
      (HostHintReadBanks.bankTables deferred witness) witness.data).filterMap HostCommitBank.call?))
    (bankSorted : (calls.map fun call => clkNat call.clk_high call.clk_low).Pairwise (· < ·)) :
    cpu.filterMap (stampedCPU deferred witness.data) = calls.map label := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have interface := source_interface (p := p) source.host.io.hints
  have handoff := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  rw [HostHintReadBanks.calls_eq_slot_tables deferred witness] at bankExhaustive
  have ordered := cpu_ordered deferred (HostHintQueueBoundary.projected witness) interface checks handoff records.byte ordering
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks records)
    (cpu := cpu) (calls := calls)
  simp only [HostHintQueueBoundary.projected_data, HostHintQueueBoundary.projected_publicInput] at ordered
  exact ordered exhaustive walk bankExhaustive bankSorted

omit [Fact (2 ^ 25 < p)] in
private theorem executeCall_bank (deferred : Bool) (policy : HostPolicy) (context : HostReadContext)
    (host middle : HostState) (call : HostCallChip.Message (ZMod p))
    (first : HostCommitBank.executeCall deferred policy context host call = some middle) :
    bankUpdate (host.bank deferred) (label call).2 = middle.bank deferred := by
  change (host.executeKind policy context (bankKind deferred)
    (Word.toBitVec64 call.arg1) (Word.toBitVec64 call.arg2)).map HostEffect.state = some middle at first
  obtain ⟨effect, ran, rfl⟩ := Option.map_eq_some_iff.mp first
  exact HostState.executeBank_bank deferred ran

omit [Fact (2 ^ 25 < p)] in
private theorem fold_bank (deferred : Bool) (policy : HostPolicy) (context : HostReadContext)
    (calls : List (HostCallChip.Message (ZMod p))) (host target : HostState)
    (success : calls.foldlM (HostCommitBank.executeCall deferred policy context) host = some target) :
    (calls.map fun call => (label call).2).foldl bankUpdate (host.bank deferred) = target.bank deferred := by
  induction calls generalizing host with
  | nil => cases success; rfl
  | cons call rest ih =>
      change ((HostCommitBank.executeCall deferred policy context host call).bind
        fun next => rest.foldlM (HostCommitBank.executeCall deferred policy context) next) = some target at success
      obtain ⟨middle, first, tail⟩ := Option.bind_eq_some_iff.mp success
      have one := executeCall_bank deferred policy context host middle call first
      simp only [List.map_cons, List.foldl_cons, one, ih middle tail]

private theorem final_bank (deferred : Bool) (host target : HostState) :
    ((HostCommitBoundary.final (HostCommitEnsemble.sourceValues (p := p) deferred target)).apply deferred host).bank deferred =
      target.bank deferred := by
  cases deferred <;> simp [HostCommitBoundary.final, HostCommitEnsemble.sourceValues,
    HostCommitChip.State.apply, HostCommitChip.State.decode, HostState.bank,
    Vector.map_map, Function.comp_def, Target.toBitVec64_bitVecToWord]

/-- The bank endpoints authenticated by the installed AIR equal the banks of its actual replay.
The CPU walk and successful replay here are supplied internally by the execution capstone. -/
theorem replay_bank (deferred : Bool)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (program : Target.GuestProgram)
    (target : ExecutionState)
    (replay : replayEvents? policy program source.realize (cpu.map ExecutionRow.event) = some target) :
    target.host.bank deferred = bankFinal.bank deferred := by
  obtain ⟨calls, bankExhaustive, bankSorted, executed⟩ := HostHintReadBanks.ordered_calls deferred witness
    constraints balanced policy characteristic (.ofSail source.sail.realize)
  have projected := cpu_projection deferred witness constraints balanced exhaustive walk bankExhaustive bankSorted
  have erased := congrArg (List.map Prod.snd) projected
  simp only [stampedCPU, List.map_filterMap, Option.map_map, Function.comp_def,
    Option.map_id_fun', id_eq, List.map_map] at erased
  have actual := replayEvents?_bank replay deferred
  simp only [List.filterMap_map, Function.comp_def] at actual
  rw [erased] at actual
  exact actual.symm.trans ((fold_bank deferred policy (.ofSail source.sail.realize) calls source.host _ executed).trans
    (final_bank deferred source.host bankFinal))

end SP1Clean.Soundness.HostBankCPUReplay
