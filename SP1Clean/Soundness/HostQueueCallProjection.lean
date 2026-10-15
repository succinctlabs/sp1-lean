import SP1Clean.Soundness.HostQueueCPUOrder
import SP1Clean.Soundness.HostCommitBank
import SP1Clean.Model.Core.QueueReplay
import SP1Clean.Proofs.Chips.HostHaltChip.Bridge
import SP1Clean.Proofs.Chips.HostEnterChip.Bridge

/-! # Queue actions in the complete installed HostCall inventory

The installed control handlers preserve the hint queue and exclude WRITE. The remaining
receivers are exactly HINT_READ and the two HINT_LEN variants. Their physical rows determine
the semantic queue actions, including the natural read length rather than its modular image.
-/

namespace SP1Clean.Soundness.HostQueueCallProjection

open Circuit Air.Flat Model.Core HostHintReadLocal HostQueueOrder HostQueueCPUOrder Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance projectionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def project (message : HostCallChip.Message (ZMod p)) : Option HintQueue.Event :=
  queueCallEvent? (Word.toBitVec64 message.code) (Word.toBitVec64 message.arg2)
    (Word.toBitVec64 message.result)

def safe (message : HostCallChip.Message (ZMod p)) : Prop :=
  Word.toBitVec64 message.code ≠ SyscallKind.write.code

private def ControlCode (code : Word (ZMod p)) : Prop :=
  code = 0 ∨ code = HostEnterChip.codeWord ∨
    code = HostCommitChip.codeWord false ∨ code = HostCommitChip.codeWord true

private theorem control_code (receiver : HostLocalHandoff.Receiver (p := p))
    (member : receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (env : Environment (ZMod p)) (constraints : receiver.component.operations.ConstraintsHold env)
    (bytes : receiver.component.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    ControlCode (receiver.message env).code := by
  change receiver ∈ ([HostCallReceivers.halt, HostCallReceivers.enter] ++
    (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
    (List.ofFn fun slot => HostCallReceivers.commit true slot)) at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at member
  rcases member with ((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩
  · have valid := HostHaltChip.component_spec_of_byte env constraints bytes
    change HostHaltChip.Spec (valueFromOffset HostHaltChip.Inputs 0 env) at valid
    rw [HostCallReceivers.halt_message]
    exact Or.inl valid.1
  · have valid := HostEnterChip.component_spec_of_constraints env constraints
    change HostEnterChip.Spec (valueFromOffset HostEnterChip.Inputs 0 env) at valid
    rw [HostCallReceivers.enter_message]
    exact Or.inr (Or.inl valid.1)
  · have valid := HostCommitBank.view_spec_of_byte false (some slot) env constraints bytes
    change HostCommitChip.Spec false slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    rw [HostCallReceivers.commit_message]
    exact Or.inr (Or.inr (Or.inl valid.1.1))
  · have valid := HostCommitBank.view_spec_of_byte true (some slot) env constraints bytes
    change HostCommitChip.Spec true slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    rw [HostCallReceivers.commit_message]
    exact Or.inr (Or.inr (Or.inr valid.1.1))

private theorem control_projection (message : HostCallChip.Message (ZMod p))
    (code : ControlCode message.code) :
    safe message ∧ project message = none ∧ Word.toBitVec64 message.code ≠ SyscallKind.verifyProof.code := by
  have small (n : ℕ) (bound : n < 2 ^ 17) : ((n : ℕ) : ZMod p).val = n :=
    ZMod.val_natCast_of_lt (lt_trans bound (Fact.out (p := 2 ^ 17 < p)))
  have three : (3 : ZMod p).val = 3 := small 3 (by decide)
  have sixteen : (16 : ZMod p).val = 16 := small 16 (by decide)
  have twentySix : (26 : ZMod p).val = 26 := small 26 (by decide)
  rcases code with code | code | code | code
  all_goals
    simp [safe, project, code, HostEnterChip.codeWord, HostCommitChip.codeWord,
      Word.toBitVec64, Word.toNat, three, sixteen, twentySix, queueCallEvent?, SyscallKind.code]

/-- Both queue operations have the exact action decoded from their complete call. -/
theorem queue_projection (row : Row (p := p)) (valid : (view row.1).component.Spec row.2) :
    safe (call row) ∧ project (call row) = some (HostQueueHistory.event row) := by
  rcases row with ⟨index, env⟩
  cases index with
  | none =>
    change HostHintReadChip.Spec (HostHintReadCoverage.input env) at valid
    have length : Word.isU64 (HostHintReadCoverage.input env).call.arg2 := by
      rw [valid.2.2.2.2.1]
      exact valid.2.2.2.2.2.2.2.2.1.2.1
    simp only [safe, project, call, valid.1, HostHintReadChip.codeWord,
      Target.toBitVec64_bitVecToWord, queueCallEvent?, SyscallKind.code,
      BitVec.reduceEq, ↓reduceIte, Word.toBitVec64_toNat length, HostQueueHistory.event]
    decide
  | some empty =>
    change HostHintLengthChip.Spec empty (valueFromOffset HostHintLengthChip.Inputs 0 env) at valid
    simp only [safe, project, call, valid.1, HostHintLengthChip.codeWord,
      Target.toBitVec64_bitVecToWord, queueCallEvent?, SyscallKind.code,
      ↓reduceIte, HostQueueHistory.event]
    decide

private theorem control_run (receiver : HostLocalHandoff.Receiver (p := p))
    (member : receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (env : Environment (ZMod p)) (constraints : receiver.component.operations.ConstraintsHold env)
    (bytes : receiver.component.operations.ChannelGuarantees Channels.byteChannel.toRaw env)
    (host : HostState) (running : host.exitCode = none) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext)
    (observed : context.register 5 = some (Word.toBitVec64 (receiver.message env).code) ∧
      context.register 10 = some (Word.toBitVec64 (receiver.message env).arg1) ∧
      context.register 11 = some (Word.toBitVec64 (receiver.message env).arg2)) :
    ∃ execution, host.run policy context = some execution ∧
      execution.result = Word.toBitVec64 (receiver.message env).result ∧ execution.effect.write = none := by
  change receiver ∈ ([HostCallReceivers.halt, HostCallReceivers.enter] ++
    (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
    (List.ofFn fun slot => HostCallReceivers.commit true slot)) at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at member
  rcases member with ((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩
  · have valid := HostHaltChip.component_spec_of_byte env constraints bytes
    change HostHaltChip.Spec (valueFromOffset HostHaltChip.Inputs 0 env) at valid
    rw [HostCallReceivers.halt_message] at observed ⊢
    exact ⟨_, HostHaltChip.run_of_spec _ valid host running policy characteristic context
      observed.1 observed.2.1 observed.2.2, rfl, rfl⟩
  · have valid := HostEnterChip.component_spec_of_constraints env constraints
    change HostEnterChip.Spec (valueFromOffset HostEnterChip.Inputs 0 env) at valid
    rw [HostCallReceivers.enter_message] at observed ⊢
    exact ⟨_, HostEnterChip.run_of_spec _ valid host running policy context
      observed.1 observed.2.1 observed.2.2, rfl, rfl⟩
  · have valid := HostCommitBank.view_spec_of_byte false (some slot) env constraints bytes
    change HostCommitChip.Spec false slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    rw [HostCallReceivers.commit_message] at observed ⊢
    exact ⟨_, HostCommitChip.run_of_callSpec false slot _ valid.1 host running policy characteristic context
      observed.1 observed.2.1 observed.2.2, rfl, rfl⟩
  · have valid := HostCommitBank.view_spec_of_byte true (some slot) env constraints bytes
    change HostCommitChip.Spec true slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    rw [HostCallReceivers.commit_message] at observed ⊢
    exact ⟨_, HostCommitChip.run_of_callSpec true slot _ valid.1 host running policy characteristic context
      observed.1 observed.2.1 observed.2.2, rfl, rfl⟩

private theorem controls_run (receivers : List (HostLocalHandoff.Receiver (p := p)))
    (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component) receivers tables)
    (registered : ∀ receiver ∈ receivers, receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (constraints : ∀ table ∈ tables, table.Constraints data)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees data Channels.byteChannel.toRaw)
    (message : HostCallChip.Message (ZMod p)) (member : message ∈ ReceiverView.messages receivers tables data)
    (host : HostState) (running : host.exitCode = none) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext)
    (observed : context.register 5 = some (Word.toBitVec64 message.code) ∧
      context.register 10 = some (Word.toBitVec64 message.arg1) ∧
      context.register 11 = some (Word.toBitVec64 message.arg2)) :
    ∃ execution, host.run policy context = some execution ∧
      execution.result = Word.toBitVec64 message.result ∧ execution.effect.write = none := by
  induction aligned with
  | nil => simp [ReceiverView.messages, TransitionView.readIndexedRows] at member
  | @cons receiver table receivers tables same aligned ih =>
    rw [ReceiverView.messages_cons] at member
    rcases List.mem_append.mp member with first | rest
    · obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp first
      apply control_run receiver (registered receiver (List.mem_cons_self ..))
        (Environment.fromArray physical data) ?_ ?_ host running policy characteristic context observed
      · rw [same]
        exact constraints table (List.mem_cons_self ..) physical physicalMem
      · rw [same]
        exact bytes table (List.mem_cons_self ..) physical physicalMem
    · exact ih (fun receiver member => registered receiver (List.mem_cons_of_mem _ member))
        (fun table member => constraints table (List.mem_cons_of_mem _ member))
        (fun table member => bytes table (List.mem_cons_of_mem _ member)) rest

private theorem controls_projection (receivers : List (HostLocalHandoff.Receiver (p := p)))
    (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component) receivers tables)
    (registered : ∀ receiver ∈ receivers, receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (constraints : ∀ table ∈ tables, table.Constraints data)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees data Channels.byteChannel.toRaw) :
    ∀ message ∈ ReceiverView.messages receivers tables data,
      safe message ∧ project message = none ∧ Word.toBitVec64 message.code ≠ SyscallKind.verifyProof.code := by
  induction aligned with
  | nil => simp [ReceiverView.messages, TransitionView.readIndexedRows]
  | @cons receiver table receivers tables same aligned ih =>
    intro message member
    rw [ReceiverView.messages_cons] at member
    rcases List.mem_append.mp member with first | rest
    · obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp first
      apply control_projection
      apply control_code receiver (registered receiver (List.mem_cons_self ..))
      · rw [same]
        exact constraints table (List.mem_cons_self ..) physical physicalMem
      · rw [same]
        exact bytes table (List.mem_cons_self ..) physical physicalMem
    · exact ih (fun receiver member => registered receiver (List.mem_cons_of_mem _ member))
        (fun table member => constraints table (List.mem_cons_of_mem _ member))
        (fun table member => bytes table (List.mem_cons_of_mem _ member)) message rest

private def queueReceiver : Index → HostLocalHandoff.Receiver (p := p)
  | none => HostHintReadHandoff.receiver
  | some empty => HostCallReceivers.hintLength empty

private theorem queue_message (index : Index) (env : Environment (ZMod p)) :
    (queueReceiver index).message env = call (index, env) := by
  cases index with
  | none => simp only [queueReceiver, HostHintReadHandoff.receiver, call]
  | some empty =>
    have evaluated (input : Var HostHintLengthChip.Inputs (ZMod p)) : eval env input.call = (eval env input).call := by
      cases input
      simp only [circuit_norm]
    simp only [queueReceiver, HostCallReceivers.hintLength, evaluated, eval_varFromOffset_valueFromOffset]
    rfl

private theorem queue_messages (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) :
    ReceiverView.messages (indices.map queueReceiver) tables data =
      (TransitionView.readIndexedRows indices tables data).map call := by
  simp only [ReceiverView.messages, TransitionView.readIndexedRows, List.zip_map_left,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro pair _
  apply List.map_congr_left
  intro physical _
  exact queue_message pair.1 (Environment.fromArray physical data)

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

/-- Physical control and commitment handlers in the installed receiver prefix. -/
def controlTables
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names)) :=
  ((HostLocalHandoff.receiverTables witness).drop 1).take 18

/-- Every selected control table is an original physical table of the witness. -/
theorem controlTables_mem
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (table : Table (ZMod p)) (member : table ∈ controlTables witness) : table ∈ witness.tables :=
  List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take member)))

/-- Complete calls split into queue handlers and the retained control/commitment inventory. -/
theorem calls_split
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names)) :
    (HostLocalHandoff.calls witness).Perm
      ((TransitionView.readIndexedRows indices (queueTables witness) witness.data).map call ++
        ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18) (controlTables witness) witness.data) := by
  have head : HostLocalHandoff.receiverTables witness =
      handlerTable witness :: (HostLocalHandoff.receiverTables witness).drop 1 := by
    have bound := (HostLocalHandoff.receiverTables_aligned witness).length_eq
    change (HostHintReadHandoff.receiver :: HostCallReceivers.available).length =
      (HostLocalHandoff.receiverTables witness).length at bound
    exact (List.cons_getElem_drop_succ (l := HostLocalHandoff.receiverTables witness) (n := 0)
      (h := by simp only [List.length_cons] at bound; omega)).symm
  rw [← queue_messages, queueTables]
  change (ReceiverView.messages (HostHintReadHandoff.receiver :: HostCallReceivers.available)
    (HostLocalHandoff.receiverTables witness) witness.data).Perm _
  conv_lhs => rw [head, ReceiverView.messages_cons,
    ReceiverView.messages_take_drop HostCallReceivers.available _ witness.data 18]
  change List.Perm (α := HostCallChip.Message (ZMod p)) (_ ++ (_ ++ _))
    ((ReceiverView.messages (HostHintReadHandoff.receiver :: [HostCallReceivers.hintLength false,
      HostCallReceivers.hintLength true]) (handlerTable witness ::
        (HostLocalHandoff.receiverTables witness).drop 19) witness.data) ++ _)
  rw [ReceiverView.messages_cons]
  simp only [List.drop_drop]
  exact (List.Perm.refl _).append List.perm_append_comm |>.trans
    (List.Perm.of_eq (List.append_assoc _ _ _).symm)

private theorem control_calls
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel Channels.byteChannel.toRaw) :
    ∀ message ∈ ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18) (controlTables witness) witness.data,
      safe message ∧ project message = none ∧ Word.toBitVec64 message.code ≠ SyscallKind.verifyProof.code := by
  have aligned := ReceiverView.aligned_of_map_eq ((HostCallReceivers.available (p := p)).take 18)
    (controlTables witness) (by
      simp only [controlTables, List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
        List.map_cons, List.drop_succ_cons, List.drop_zero])
  exact controls_projection _ _ witness.data aligned (fun _ present => present)
    (fun table present => constraints table (controlTables_mem witness table present))
    (fun table present => byte_guarantees witness interface constraints balanced table
      (controlTables_mem witness table present))

/-- Every installed call is either an actual queue-handler row or a control call whose
dispatch succeeds on the observed registers of any running host. Control dispatch modifies
the actual host state, independently of later authentication of its complete outgoing snapshot. -/
theorem calls_run_or_queue
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel Channels.byteChannel.toRaw)
    (message : HostCallChip.Message (ZMod p)) (member : message ∈ HostLocalHandoff.calls witness) :
    (∃ row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data, message = call row) ∨
    (Word.toBitVec64 message.code ≠ SyscallKind.hintRead.code ∧
      ∀ (host : HostState), host.exitCode = none → ∀ (policy : HostPolicy), policy.characteristic = p →
      ∀ (context : HostReadContext),
        (context.register 5 = some (Word.toBitVec64 message.code) ∧
          context.register 10 = some (Word.toBitVec64 message.arg1) ∧
          context.register 11 = some (Word.toBitVec64 message.arg2)) →
        ∃ execution, host.run policy context = some execution ∧
          execution.result = Word.toBitVec64 message.result ∧ execution.effect.write = none) := by
  rcases List.mem_append.mp ((calls_split witness).mem_iff.mp member) with queue | control
  · obtain ⟨row, rowMem, same⟩ := List.mem_map.mp queue
    exact Or.inl ⟨row, rowMem, same.symm⟩
  · right
    constructor
    · have projected := (control_calls witness interface constraints balanced message control).2.1
      intro read
      simp only [project, read, queueCallEvent?, SyscallKind.code, BitVec.reduceEq, ↓reduceIte] at projected
      cases projected
    · have aligned := ReceiverView.aligned_of_map_eq ((HostCallReceivers.available (p := p)).take 18)
        (controlTables witness) (by
          simp only [controlTables, List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
            List.map_cons, List.drop_succ_cons, List.drop_zero])
      exact controls_run _ _ witness.data aligned (fun _ present => present)
        (fun table present => constraints table (controlTables_mem witness table present))
        (fun table present => byte_guarantees witness interface constraints balanced table
          (controlTables_mem witness table present)) message control

/-- Keep the call clock with its queue observation, so order comparison retains event contents. -/
def stamped (message : HostCallChip.Message (ZMod p)) : Option (ℕ × HintQueue.Event) :=
  (project message).map fun event => (clkNat message.clk_high message.clk_low, event)

private theorem projection_of_split {Message Row Label : Type*}
    (safe : Message → Prop) (stamped : Message → Option Label) (call : Row → Message) (label : Row → Label)
    (messages control : List Message) (rows : List Row) (split : messages.Perm (rows.map call ++ control))
    (queue : ∀ row ∈ rows, safe (call row) ∧ stamped (call row) = some (label row))
    (controls : ∀ message ∈ control, safe message ∧ stamped message = none) :
    (∀ message ∈ messages, safe message) ∧
      (messages.filterMap stamped).Perm (rows.map label) := by
  constructor
  · intro message member
    rcases List.mem_append.mp (split.mem_iff.mp member) with queueMem | controlMem
    · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp queueMem
      exact (queue row rowMem).1
    · exact (controls message controlMem).1
  · have projected := split.filterMap stamped
    have silent : control.filterMap stamped = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro message member
      exact (controls message member).2
    rw [List.filterMap_append, silent, List.append_nil, List.filterMap_map] at projected
    simp only [Function.comp_def] at projected
    have actual : rows.filterMap (fun row => stamped (call row)) = rows.map label := by
      apply List.filterMap_eq_map_iff_forall_eq_some.mpr
      intro row member
      exact (queue row member).2
    rwa [actual] at projected

/-- The complete installed receiver inventory excludes WRITE and projects to precisely the
physical queue-handler actions. No successful host execution is a premise. -/
theorem calls_projection
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data) :
    (∀ message ∈ HostLocalHandoff.calls witness, safe message) ∧
      ((HostLocalHandoff.calls witness).filterMap stamped).Perm
        ((TransitionView.readIndexedRows indices (queueTables witness) witness.data).map fun row =>
          (eventTime row, HostQueueHistory.event row)) := by
  apply projection_of_split safe stamped call (fun row => (eventTime row, HostQueueHistory.event row))
    _ _ _ (calls_split witness)
  · intro row member
    have facts := queue_projection row (rows_spec _ witness.data (queueTables_aligned witness) specs row member)
    refine ⟨facts.1, ?_⟩
    simp only [stamped, facts.2, Option.map_some, call_time]
  · intro message member
    have facts := control_calls witness interface constraints balanced message member
    exact ⟨facts.1, by simp only [stamped, facts.2.1, Option.map_none]⟩

/-- The installed registry contains no VERIFY handler. Its absence follows from complete call
accounting, independently of the semantic frame lemma that consumes it. -/
theorem calls_not_verify
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    (message : HostCallChip.Message (ZMod p)) (member : message ∈ HostLocalHandoff.calls witness) :
    Word.toBitVec64 message.code ≠ SyscallKind.verifyProof.code := by
  rcases List.mem_append.mp ((calls_split witness).mem_iff.mp member) with queue | control
  · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp queue
    have projected := (queue_projection row
      (rows_spec _ witness.data (queueTables_aligned witness) specs row rowMem)).2
    intro same
    simp only [project, queueCallEvent?, same, SyscallKind.code, BitVec.reduceEq, ↓reduceIte] at projected
    cases projected
  · exact (control_calls witness interface constraints balanced message control).2.2

end SP1Clean.Soundness.HostQueueCallProjection
