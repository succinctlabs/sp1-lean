import SP1Clean.Proofs.Chips.HostCallChip.Formal
import SP1Clean.Native.Readers.RegisterReadLedger

/-! # Authenticated host-call selection and the actual interaction ledger

Raw constraints determine WRITE selection without Memory grounding. The composed circuit keeps
all original instruction interactions, adds the selected x12 pair, and emits one gated host call.
The call channel authenticates requests; it does not yet prove the host's returned value or effects.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
set_option linter.unusedSectionVars false in
private theorem equality_empty (target : RawChannel (ZMod p))
    (input : Var (ProvablePair Word Word) (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions (Gadgets.IsEqual.circuit.toSubcircuit offset input).ops.toFlat).filter
      (fun (interaction : AbstractInteraction (ZMod p)) => decide (interaction.channel = target)) = [] := by
  have empty := InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil
    (Gadgets.IsEqual.circuit (α := Word)) target (n := offset) input []
    List.not_mem_nil List.not_mem_nil
  simpa only [Operations.interactionsWith_subcircuit, Operations.interactionsWith_nil,
    List.append_nil] using empty

/-- Raw constraints retain the original instruction and its full-code check. -/
theorem instruction_of_constraints (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (constraints : ((main input).operations offset).ConstraintsHold env) :
    ((CoreSyscallChip.circuit.main input.instruction).operations offset).ConstraintsHold env := by
  rw [← Circuit.constraintsHold_toFlat_iff, operations_eq] at constraints
  simp only [circuit_norm] at constraints
  have original := (FlatOperation.constraintsHold_append.mp constraints).1
  rw [← Circuit.constraintsHold_toFlat_iff]
  simpa only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat] using original

/-- Full-word WRITE selection is a consequence of raw constraints alone. -/
theorem selector_of_constraints (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (constraints : ((main input).operations offset).ConstraintsHold env) :
    env (selector input offset) = writeFlag (eval env input.instruction.op_a_memory.prev_value) := by
  rw [← Circuit.constraintsHold_toFlat_iff, operations_eq] at constraints
  simp only [circuit_norm] at constraints
  have equality := (FlatOperation.constraintsHold_append.mp
    (FlatOperation.constraintsHold_append.mp constraints).2).1
  have spec := (Gadgets.IsEqual.circuit.toSubcircuit offset
    (input.instruction.op_a_memory.prev_value, const writeWord)).soundness env (by trivial) equality (by
      rw [FlatOperation.guarantees_iff_forall_mem]
      intro interaction member
      have present := (List.mem_filter (p := fun i => decide (i.channel = interaction.channel))).mpr ⟨member, by simp⟩
      rw [equality_empty interaction.channel] at present
      exact False.elim (List.not_mem_nil present))
  simpa only [selector, Gadgets.IsEqual.circuit, Gadgets.IsEqual.Spec, writeFlag,
    writeWord, circuit_norm] using spec.1

theorem main_memory_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      ((CoreSyscallChip.circuit.main input.instruction).operations offset).interactionsWith memoryChannel.toRaw ++
      [(memoryChannel.pulledIf (input.read (selector input offset)).is_real
        (input.read (selector input offset)).prior).toRaw,
       (memoryChannel.pushedIf (input.read (selector input offset)).is_real
        (input.read (selector input offset)).pushed).toRaw] := by
  rw [operations_eq]
  have reader := Readers.RegisterRead.main_memory_interactions
    (input.read (selector input offset)) (offset + 8)
  simp only [Operations.interactionsWith, Circuit.operations] at reader ⊢
  simp only [circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append, equality_empty,
    Readers.RegisterRead.circuit, reader, List.nil_append]
  simp [channel, memoryChannel, circuit_norm]

theorem main_host_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith channel.toRaw =
      [(channel.pushedIf input.instruction.is_real (input.message (selector input offset))).toRaw] := by
  have coreEmpty := InteractionRecovery.interactionsWith_main_eq_nil
    CoreSyscallChip.circuit.base channel.toRaw input.instruction offset
    (by simp [core_guarantees, core_requirements, circuit_norm, channel,
      byteChannel, memoryChannel, stateChannel, programChannel, exitChannel, syscallChannel,
      publicValuesChannel])
  have readEmpty := InteractionRecovery.interactionsWith_main_eq_nil
    Readers.RegisterRead.circuit.base channel.toRaw (input.read (selector input offset)) (offset + 8)
    (by simp [Readers.RegisterRead.circuit, circuit_norm, channel, byteChannel, memoryChannel])
  rw [operations_eq]
  simp only [Operations.interactionsWith, Circuit.operations] at coreEmpty readEmpty ⊢
  simp only [circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append, coreEmpty, readEmpty,
    equality_empty, List.nil_append]
  simp [circuit_norm]

/-- Every channel other than Byte, Memory and the new handoff is preserved exactly. -/
theorem main_other_interactions (target : RawChannel (ZMod p))
    (notByte : target ≠ byteChannel.toRaw) (notMemory : target ≠ memoryChannel.toRaw)
    (notHost : target ≠ channel.toRaw) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target =
      ((CoreSyscallChip.circuit.main input.instruction).operations offset).interactionsWith target := by
  have readEmpty := InteractionRecovery.interactionsWith_main_eq_nil
    Readers.RegisterRead.circuit.base target (input.read (selector input offset)) (offset + 8)
    (by simp [Readers.RegisterRead.circuit, circuit_norm, notByte, notMemory])
  rw [operations_eq]
  simp only [Operations.interactionsWith, Circuit.operations] at readEmpty ⊢
  simp only [circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append, readEmpty,
    equality_empty, List.nil_append]
  simp [circuit_norm, Ne.symm notHost]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_message_fields (env : Environment (ZMod p))
    (high low0 low1 flag : Expression (ZMod p)) (code arg1 arg2 result length : Var Word (ZMod p)) :
    eval env (⟨high, low0 + low1 * 65536, code, arg1, arg2, result, length.map (flag * ·)⟩ :
      Message (Expression (ZMod p))) =
      (⟨env high, env low0 + env low1 * 65536, eval env code, eval env arg1, eval env arg2,
        eval env result, (eval env length).map (env flag * ·)⟩ : Message (ZMod p)) := by
  simp only [circuit_norm, Vector.map_map, Function.comp_def]

/-- The evaluated handoff exposes the instruction fields and the constraint-derived length gate. -/
theorem host_values_of_constraints (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (constraints : ((main input).operations offset).ConstraintsHold env) :
    ((main input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedIfValue (env input.instruction.is_real)
        ⟨env input.instruction.state.clk_high,
         env input.instruction.state.clk_0_16 + env input.instruction.state.clk_16_24 * 65536,
         eval env input.instruction.op_a_memory.prev_value,
         eval env input.instruction.op_b_memory.prev_value,
         eval env input.instruction.op_c_memory.prev_value, eval env input.instruction.op_a_value,
         (eval env input.length.prev_value).map
           (writeFlag (eval env input.instruction.op_a_memory.prev_value) * ·)⟩] := by
  simp only [Operations.interactionValuesWith, main_host_interactions, List.map_cons,
    List.map_nil, Channel.eval_pushedIf, Inputs.message]
  rw [eval_message_fields, selector_of_constraints input offset env constraints,
    ProvableType.eval_field]

end SP1Clean.HostCallChip
