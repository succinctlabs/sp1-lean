import SP1Clean.Soundness.HostCallLedger
import ToClean.Circuit.SubcircuitProjection
import ToClean.Air.EnsembleProjection
import ToClean.Air.ExpressionScope

/-! # The host wrapper retains instruction constraints and State chronology

The instruction is the prefix of the physical wrapper row. Its circuit has no local witness
cells, so the wrapper's extra input fields do not shift any original observation. Constraints
project, the State ledger is unchanged, and original Byte interactions are retained.
Memory interactions deliberately do not project: WRITE adds an x12 read-back pair.
-/

namespace SP1Clean.Soundness.HostCallProjection

open Circuit Air.Flat Channels HostCallLedger

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def original : Component (ZMod p) := { circuit := SyscallInstrsChip.circuit }

/-- WRITE's additional register read, using the constraint-determined full-word selector. -/
def extraRead (env : Environment (ZMod p)) : Readers.RegisterRead.Inputs (ZMod p) :=
  (HostCallLedger.input env).read (HostCallChip.writeFlag (HostCallLedger.input env).instruction.op_a_memory.prev_value)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem instruction_var : (varFromOffset HostCallChip.Inputs (F := ZMod p) 0).instruction =
    varFromOffset SyscallInstrsChip.Inputs 0 := by
  rw [ProvableStruct.varFromOffset_eq_varFromOffset (α := HostCallChip.Inputs)]
  change (ProvableStruct.fromComponents (α := HostCallChip.Inputs)
    (.cons (varFromOffset SyscallInstrsChip.Inputs (F := ZMod p) 0)
      (.cons (varFromOffset Circuits.Types.RegisterAccessCols (size SyscallInstrsChip.Inputs)) .nil))).instruction = _
  rw [HostCallChip.Inputs.fromComponents_cons]

omit [Fact (2 ^ 25 < p)] in
private theorem cpu_offset (row : Var Readers.CPUState.Inputs (ZMod p)) (a b : ℕ) :
    ((Readers.CPUState.main row).operations a).toFlat = ((Readers.CPUState.main row).operations b).toFlat := by
  simp only [Readers.CPUState.main, circuit_norm]

private theorem register_offset (row : Var Readers.RegisterAccessCols.Inputs (ZMod p)) (a b : ℕ) :
    ((Readers.RegisterAccessCols.main row).operations a).toFlat =
      ((Readers.RegisterAccessCols.main row).operations b).toFlat := by
  simp only [Readers.RegisterAccessCols.main, circuit_norm, FormalAssertion.toSubcircuit_toFlat,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main]

omit [Fact (2 ^ 25 < p)] in
private theorem zero_offset (row : Var IsZeroOperation.Inputs (ZMod p)) (a b : ℕ) :
    ((IsZeroOperation.main row).operations a).toFlat = ((IsZeroOperation.main row).operations b).toFlat := by
  simp only [IsZeroOperation.main, circuit_norm, Gadgets.Equality.circuit,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_toFlat, Nat.add_zero,
    Circuit.forEach.operations_eq, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem bytes_offset (row : Var U16toU8OperationSafe.Inputs (ZMod p)) (a b : ℕ) :
    ((U16toU8OperationSafe.main row).operations a).toFlat = ((U16toU8OperationSafe.main row).operations b).toFlat := by
  simp only [U16toU8OperationSafe.main, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem pcArm_offset (row : Var SyscallInstrsChip.PcArm.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.PcArm.circuit.main row).operations a).toFlat =
      ((SyscallInstrsChip.PcArm.circuit.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.PcArm.circuit, SyscallInstrsChip.PcArm.main, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem writeArm_offset (row : Var SyscallInstrsChip.WriteArm.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.WriteArm.circuit.main row).operations a).toFlat =
      ((SyscallInstrsChip.WriteArm.circuit.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.WriteArm.circuit, SyscallInstrsChip.WriteArm.main, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem dispatchArm_offset (row : Var SyscallInstrsChip.DispatchArm.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.DispatchArm.circuit.main row).operations a).toFlat =
      ((SyscallInstrsChip.DispatchArm.circuit.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.DispatchArm.circuit, SyscallInstrsChip.DispatchArm.main, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem commitArm_offset (row : Var SyscallInstrsChip.CommitArm.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.CommitArm.circuit.main row).operations a).toFlat =
      ((SyscallInstrsChip.CommitArm.circuit.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.CommitArm.circuit, SyscallInstrsChip.CommitArm.main, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem compare_offset (row : Var U16CompareOperation.Inputs (ZMod p)) (a b : ℕ) :
    ((U16CompareOperation.main row).operations a).toFlat =
      ((U16CompareOperation.main row).operations b).toFlat := by
  simp only [U16CompareOperation.main, circuit_norm, Gadgets.Equality.circuit,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_toFlat, Circuit.forEach.operations_eq,
    circuit_norm]

private theorem fieldBoundArm_offset (row : Var SyscallInstrsChip.FieldBoundArm.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.FieldBoundArm.circuit.main row).operations a).toFlat =
      ((SyscallInstrsChip.FieldBoundArm.circuit.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.FieldBoundArm.circuit, SyscallInstrsChip.FieldBoundArm.main, circuit_norm,
    FormalAssertion.toSubcircuit_toFlat, U16CompareOperation.circuit, compare_offset (b := 0)]

private theorem original_offset (row : Var SyscallInstrsChip.Inputs (ZMod p)) (a b : ℕ) :
    ((SyscallInstrsChip.main row).operations a).toFlat = ((SyscallInstrsChip.main row).operations b).toFlat := by
  simp only [SyscallInstrsChip.main, circuit_norm, FormalAssertion.toSubcircuit_toFlat,
    GeneralFormalCircuit.toSubcircuit_toFlat, Nat.add_zero,
    Readers.CPUState.circuit, Readers.RegisterAccessCols.circuit, IsZeroOperation.circuit,
    U16toU8OperationSafe.circuit,
    cpu_offset (b := 0), register_offset (b := 0), zero_offset (b := 0), bytes_offset (b := 0),
    pcArm_offset (b := 0), writeArm_offset (b := 0), dispatchArm_offset (b := 0),
    commitArm_offset (b := 0), fieldBoundArm_offset (b := 0)]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_instruction (row : Var HostCallChip.Inputs (ZMod p)) (env : Environment (ZMod p)) :
    eval env row.instruction = (eval env row).instruction := by
  cases row
  simp only [circuit_norm]

/-- Physical wrapper decoding retains the complete original instruction input. -/
theorem input_original (env : Environment (ZMod p)) :
    (HostCallLedger.input env).instruction = original.rowInput env := by
  change (valueFromOffset HostCallChip.Inputs 0 env).instruction = valueFromOffset SyscallInstrsChip.Inputs 0 env
  rw [← eval_varFromOffset_valueFromOffset, ← eval_instruction, instruction_var, eval_varFromOffset_valueFromOffset]

/-- Every original assertion and lookup follows from the actual wrapper's raw constraints. -/
theorem constraints_original (env : Environment (ZMod p))
    (constraints : producer.operations.ConstraintsHold env) : original.operations.ConstraintsHold env := by
  have core := HostCallChip.instruction_of_constraints (varFromOffset HostCallChip.Inputs 0)
    (size HostCallChip.Inputs) env ((Component.constraintsHold_iff env).mp constraints)
  rw [instruction_var] at core
  have kept := CoreSyscallChip.main_constraints_original _ _ env core
  change ((SyscallInstrsChip.main (varFromOffset SyscallInstrsChip.Inputs 0)).operations
    (size HostCallChip.Inputs)).ConstraintsHold env at kept
  rw [← Circuit.constraintsHold_toFlat_iff, original_offset _ (size HostCallChip.Inputs)
    (size SyscallInstrsChip.Inputs), Circuit.constraintsHold_toFlat_iff] at kept
  exact (Component.constraintsHold_iff env).mpr kept

private theorem main_other_interactions (channel : RawChannel (ZMod p))
    (byte : channel ≠ byteChannel.toRaw) (memory : channel ≠ memoryChannel.toRaw)
    (host : channel ≠ HostCallChip.channel.toRaw)
    (row : Var HostCallChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main row.instruction).operations offset).interactionsWith channel =
      ((HostCallChip.main row).operations offset).interactionsWith channel := by
  rw [HostCallChip.main_other_interactions channel byte memory host]
  simp only [CoreSyscallChip.circuit, CoreSyscallChip.main, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    SyscallCodeGuard.circuit, SyscallCodeGuard.main, SyscallInstrsChip.circuit,
    Operations.interactionsWith]

private theorem main_byte_subset (row : Var HostCallChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main row.instruction).operations offset).interactionsWith byteChannel.toRaw ⊆
      ((HostCallChip.main row).operations offset).interactionsWith byteChannel.toRaw := by
  rw [HostCallChip.operations_eq]
  simp only [GeneralFormalCircuit.toSubcircuit_interactions,
    FormalCircuit.toSubcircuit_interactions, CoreSyscallChip.circuit,
    CoreSyscallChip.main, circuit_norm, FormalAssertion.toSubcircuit_interactions,
    SyscallCodeGuard.circuit, SyscallCodeGuard.main, SyscallInstrsChip.circuit,
    Operations.interactionsWith]
  simp only [List.filter_append]
  exact List.subset_append_left _ _

/-- The original Byte ledger is retained inside the larger physical wrapper. -/
theorem byte_subset : (original (p := p)).operations.interactionsWith byteChannel.toRaw ⊆
    producer.operations.interactionsWith byteChannel.toRaw := by
  simp only [original, producer, Component.interactionsWith_eq, Component.rowOperations,
    HostCallChip.circuit, SyscallInstrsChip.circuit]
  have kept := main_byte_subset (varFromOffset HostCallChip.Inputs (F := ZMod p) 0) (size HostCallChip.Inputs)
  rw [instruction_var] at kept
  simpa only [Operations.interactionsWith, ← Operations.interactions_toFlat, original_offset (b := 0)] using kept

/-- The larger assembly's Byte guarantees suffice for every original instruction check. -/
theorem byte_guarantees (env : Environment (ZMod p))
    (guarantees : producer.operations.ChannelGuarantees byteChannel.toRaw env) :
    original.operations.ChannelGuarantees byteChannel.toRaw env :=
  Operations.channelGuarantees_of_interactionsWith_subset _ _ _ byte_subset env guarantees

omit [Fact (2 ^ 25 < p)] in
private theorem eval_read (input : Var HostCallChip.Inputs (ZMod p)) (flag : Expression (ZMod p))
    (env : Environment (ZMod p)) :
    eval env (input.read flag) = (eval env input).read (env flag) := by
  rcases input with ⟨instruction, length⟩
  cases instruction
  cases length
  simp only [HostCallChip.Inputs.read, circuit_norm]

private theorem main_memory_values (input : Var HostCallChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((HostCallChip.main input).operations offset).ConstraintsHold env) :
    ((HostCallChip.main input).operations offset).interactionValuesWith memoryChannel.toRaw env =
      ((SyscallInstrsChip.main input.instruction).operations offset).interactionValuesWith memoryChannel.toRaw env ++
      [memoryChannel.pulledIfValue
        ((eval env input).read (HostCallChip.writeFlag (eval env input).instruction.op_a_memory.prev_value)).is_real
        ((eval env input).read (HostCallChip.writeFlag (eval env input).instruction.op_a_memory.prev_value)).prior,
       memoryChannel.pushedIfValue
        ((eval env input).read (HostCallChip.writeFlag (eval env input).instruction.op_a_memory.prev_value)).is_real
        ((eval env input).read (HostCallChip.writeFlag (eval env input).instruction.op_a_memory.prev_value)).pushed] := by
  rw [Operations.interactionValuesWith, HostCallChip.main_memory_interactions, List.map_append]
  have core : ((CoreSyscallChip.circuit.main input.instruction).operations offset).interactionsWith memoryChannel.toRaw =
      ((SyscallInstrsChip.main input.instruction).operations offset).interactionsWith memoryChannel.toRaw := by
    simp only [CoreSyscallChip.circuit, CoreSyscallChip.main, circuit_norm,
      GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
      SyscallCodeGuard.circuit, SyscallCodeGuard.main, SyscallInstrsChip.circuit, Operations.interactionsWith]
  rw [core]
  congr 1
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, Channel.eval_pushedIf]
  -- Both sides evaluate the same field expressions once `read`/`prior`/`pushed` are unfolded and
  -- the selector is rewritten by its constraint-derived value; `circuit_norm` pushes every
  -- projection of `eval env input` down to the cell level (the input stays opaque).
  have hsel := HostCallChip.selector_of_constraints input offset env constraints
  have hv : (ProvableStruct.eval env input.instruction).op_a_memory.prev_value =
      Vector.map (Expression.eval env) input.instruction.op_a_memory.prev_value := by
    rw [SyscallInstrsChip.Inputs.eval_op_a_memory, ProvableStruct.eval_eq_eval,
      Circuits.Types.RegisterAccessCols.eval_prev_value, ProvableType.eval_fields]
  have hv' : (ProvableStruct.eval env input.length).prev_value =
      Vector.map (Expression.eval env) input.length.prev_value := by
    rw [Circuits.Types.RegisterAccessCols.eval_prev_value, ProvableType.eval_fields]
  simp only [HostCallChip.Inputs.read, Readers.RegisterRead.Inputs.prior,
    Readers.RegisterRead.Inputs.pushed, circuit_norm, hsel, hv, hv']

/-- The wrapper retains all original Memory interactions and adds exactly its gated x12 pair. -/
theorem memory_values (env : Environment (ZMod p))
    (constraints : producer.operations.ConstraintsHold env) :
    producer.operations.interactionValuesWith memoryChannel.toRaw env =
      original.operations.interactionValuesWith memoryChannel.toRaw env ++
      [memoryChannel.pulledIfValue (extraRead env).is_real (extraRead env).prior,
       memoryChannel.pushedIfValue (extraRead env).is_real (extraRead env).pushed] := by
  have projected := main_memory_values (varFromOffset HostCallChip.Inputs 0)
    (size HostCallChip.Inputs) env ((Component.constraintsHold_iff env).mp constraints)
  rw [instruction_var, eval_varFromOffset_valueFromOffset] at projected
  simp only [Operations.interactionValuesWith, original, producer, Component.interactionsWith_eq,
    Component.rowOperations, HostCallChip.circuit, SyscallInstrsChip.circuit]
  simpa only [Operations.interactionValuesWith, Operations.interactionsWith,
    ← Operations.interactions_toFlat, original_offset (b := 0), extraRead, HostCallLedger.input] using projected

/-- The wrapper changes only Byte, Memory, and HostCall interactions. Every other channel
retains the complete original physical ledger, including disabled rows. -/
theorem other_interactions (channel : RawChannel (ZMod p))
    (byte : channel ≠ byteChannel.toRaw) (memory : channel ≠ memoryChannel.toRaw)
    (host : channel ≠ HostCallChip.channel.toRaw) :
    (original (p := p)).operations.interactionsWith channel =
      producer.operations.interactionsWith channel := by
  simp only [original, producer, Component.interactionsWith_eq, Component.rowOperations,
    HostCallChip.circuit, SyscallInstrsChip.circuit]
  rw [← main_other_interactions channel byte memory host, instruction_var]
  simp only [Operations.interactionsWith, ← Operations.interactions_toFlat, original_offset (b := 0)]

/-- The full State interaction list is unchanged by the wrapper. -/
theorem state_interactions : (original (p := p)).operations.interactionsWith stateChannel.toRaw =
    producer.operations.interactionsWith stateChannel.toRaw :=
  other_interactions stateChannel.toRaw (by simp [stateChannel, byteChannel, Channel.toRaw])
    (by simp [stateChannel, memoryChannel, Channel.toRaw])
    (by simp [stateChannel, HostCallChip.channel, Channel.toRaw])

section Scope

attribute [local circuit_norm]
  original Component.constraints_eq Component.interactions_eq Component.rowOperations
  SyscallInstrsChip.circuit SyscallInstrsChip.main Circuit.forEach.operations_eq
  FlatOperation.constraints_append FlatOperation.interactions_append
  GeneralFormalCircuit.toSubcircuit_toFlat FormalAssertion.toSubcircuit_toFlat
  Readers.CPUState.circuit Readers.CPUState.main Readers.RegisterAccessCols.circuit
  Readers.RegisterAccessCols.main Readers.RegisterAccessTimestamp.circuit
  Readers.RegisterAccessTimestamp.main IsZeroOperation.circuit IsZeroOperation.main
  Gadgets.Equality.circuit Gadgets.Equality.main
  U16toU8OperationSafe.circuit U16toU8OperationSafe.main
  SyscallInstrsChip.PcArm.circuit SyscallInstrsChip.PcArm.main
  SyscallInstrsChip.WriteArm.circuit SyscallInstrsChip.WriteArm.main
  SyscallInstrsChip.DispatchArm.circuit SyscallInstrsChip.DispatchArm.main
  SyscallInstrsChip.CommitArm.circuit SyscallInstrsChip.CommitArm.main
  SyscallInstrsChip.FieldBoundArm.circuit SyscallInstrsChip.FieldBoundArm.main
  U16CompareOperation.circuit U16CompareOperation.main

/-- Clean's scope checker bounds every original assertion, multiplicity and message by the
instruction's own width, independent of the wider host wrapper. -/
theorem original_scope :
    Extraction.expressionsBadVariable (original (p := p)).width
      (original (p := p)).operations.constraints = none ∧
    Extraction.expressionsBadVariable (original (p := p)).width
      ((original (p := p)).operations.interactions.flatMap fun interaction =>
        interaction.mult :: interaction.msg.toList) = none := by
  have width : (original (p := p)).width = 65 := rfl
  rw [width]
  constructor <;> simp only [circuit_norm] <;> cbv

end Scope

/-- Truncating an actual host row retains the original instruction constraints at canonical data. -/
theorem constraints_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (checked : producer.operations.ConstraintsHold (Environment.fromArray row data)) :
    original.operations.ConstraintsHold
      (Environment.fromArray (row.extract 0 (original (p := p)).width) data') := by
  apply Extraction.constraints_extract row data data' SyscallInstrsChip.lookups_empty ?_
    (constraints_original _ checked)
  exact (original_scope (p := p)).1

/-- The original Byte checks survive truncation even when canonical data changes. -/
theorem byte_guarantees_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (guarantees : producer.operations.ChannelGuarantees byteChannel.toRaw (Environment.fromArray row data)) :
    original.operations.ChannelGuarantees byteChannel.toRaw
      (Environment.fromArray (row.extract 0 (original (p := p)).width) data') := by
  intro interaction member channel
  have scope : Extraction.expressionsBadVariable (original (p := p)).width
      (interaction.mult :: interaction.msg.toList) = none :=
    List.findSome?_eq_none_iff.mpr fun expression used =>
      List.findSome?_eq_none_iff.mp (original_scope (p := p)).2 expression
        (List.mem_flatMap.mpr ⟨interaction, member, used⟩)
  rw [← AbstractInteraction.eval_guarantees, Extraction.interaction_eval_extract row data data' _ scope]
  have kept := byte_guarantees (Environment.fromArray row data) guarantees interaction member channel
  rcases interaction with ⟨declared, mult, msg, assume⟩
  cases channel
  simpa only [Interaction.Guarantees, AbstractInteraction.eval, AbstractInteraction.Guarantees,
    Interaction.msgVector, byteChannel, Channel.toRaw] using kept

/-- Physical prefix decoding recovers the same original instruction from a host row. -/
theorem input_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p)) :
    original.rowInput (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      (HostCallLedger.input (Environment.fromArray row data)).instruction := by
  rw [input_original]
  apply ProvableType.valueFromOffset_congr
  intro index bound
  have within : index < (original (p := p)).width := by
    change index < 65 at bound ⊢
    exact bound
  by_cases inside : index < row.size <;> simp [within, inside]

/-- The original instruction's complete ledger depends only on its physical prefix. -/
theorem original_values_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (channel : RawChannel (ZMod p)) :
    original.operations.interactionValuesWith channel
        (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      original.operations.interactionValuesWith channel (Environment.fromArray row data) := by
  simp only [Operations.interactionValuesWith]
  apply List.map_congr_left
  intro interaction member
  apply Extraction.interaction_eval_extract
  apply List.findSome?_eq_none_iff.mpr
  intro expression used
  exact List.findSome?_eq_none_iff.mp (original_scope (p := p)).2 expression
    (List.mem_flatMap.mpr ⟨interaction, (List.mem_filter.mp member).1, used⟩)

/-- Prefix projection retains every occurrence on channels unchanged by the host wrapper. -/
theorem other_values_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (channel : RawChannel (ZMod p)) (byte : channel ≠ byteChannel.toRaw)
    (memory : channel ≠ memoryChannel.toRaw) (host : channel ≠ HostCallChip.channel.toRaw) :
    original.operations.interactionValuesWith channel
        (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      producer.operations.interactionValuesWith channel (Environment.fromArray row data) := by
  rw [original_values_prefix, Operations.interactionValuesWith, Operations.interactionValuesWith,
    other_interactions channel byte memory host]

end SP1Clean.Soundness.HostCallProjection
