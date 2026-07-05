import SP1Clean.Native.Chips.LoadX0Chip.Defs

/-! # `SP1Clean.LoadX0Chip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadX0Chip

open Circuit
open Extracted (LoadX0Columns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; the load targets a non-reserved, in-range address. The offset bits are
bits 0–2 of the address and boolean (alignment per width is enforced in-circuit by the alignment gates,
not assumed). The final conjunct is the **W11 memory-flip** obligation: the value read from RAM
(`memory_access.prev_value`, which for a load is the loaded word) is a valid 64-bit word — honest at the
single-row level (the memory bus range-checks every value it holds; the read pins `new_value = prev_value`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    Word.isU64 input.memory_access.prev_value

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_pv_isu64⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, h_b0, h_b1, h_b2, h_b3, h_b4, h_b5, h_b6, h_gate,
    h_al2, h_al1, h_al0, h_oa1, h_oa2⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- eval→value bridge for the offset bits (the only nested vector field the gates reference in value form).
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmap_ob⟩ := h_input
  have eob : ∀ i (hi : i < 3), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  -- the `AddressOperation` Assumptions (eval form).
  have hob0' : Expression.eval env input_var_offset_bit[0] = 0
      ∨ Expression.eval env input_var_offset_bit[0] = 1 := by rw [eob 0 (by omega)]; exact hob0
  have hob1' : Expression.eval env input_var_offset_bit[1] = 0
      ∨ Expression.eval env input_var_offset_bit[1] = 1 := by rw [eob 1 (by omega)]; exact hob1
  have hob2' : Expression.eval env input_var_offset_bit[2] = 0
      ∨ Expression.eval env input_var_offset_bit[2] = 1 := by rw [eob 2 (by omega)]; exact hob2
  have h_off' : (Expression.eval env input_var_offset_bit[0]).val
        + 2 * (Expression.eval env input_var_offset_bit[1]).val
        + 4 * (Expression.eval env input_var_offset_bit[2]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)]; exact h_off
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1], Expression.eval env input_var_offset_bit[2]⟩
        : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, hob0', hob1', hob2', h_ge, h_off'⟩
  have h_addr_spec := h_addr h_addr_as
  simp only [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)] at h_addr_spec
  have h_it := h_itype ⟨h_bin, h_bin⟩
  -- the alignment gates, in value form.
  simp only [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)] at h_al0 h_al1 h_al2
  simp only [← sub_eq_add_neg] at h_oa1 h_oa2
  simp only [isReal, opcodeVal]
  refine ⟨⟨h_addr_spec, h_mem ⟨h_bin, fun _ => h_pv_isu64⟩, h_it,
      bool_of_mul_pred h_b0, bool_of_mul_pred h_b1, bool_of_mul_pred h_b2, bool_of_mul_pred h_b3,
      bool_of_mul_pred h_b4, bool_of_mul_pred h_b5, bool_of_mul_pred h_b6,
      h_bin, h_al2, h_al1, h_al0, h_oa1, h_oa2⟩, ?_⟩
  -- the per-subcircuit channel-requirement tail (`channels = [] ∨ <sub>.Assumptions`); `MemoryAccess`'s
  -- read push owes `isU64 prev_value` (chip assumption; a read pins `new_value = prev_value`).
  exact ⟨h_bin, Or.inr h_addr_as, Or.inr ⟨h_bin, fun _ => h_pv_isu64⟩, Or.inr ⟨h_bin, h_bin⟩⟩

/-- Prover-side row well-formedness: operand `isU64`s + address facts + selector binaries + alignment
equations + the `op_a_0` forcing facts + the reader/CPUState/MemoryAccess `Spec`s. -/
def ProverAssumptions (input : Inputs (ZMod p)) (data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    Word.isU64 input.memory_access.prev_value ∧
    (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
    (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
    (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
    (input.is_ld = 0 ∨ input.is_ld = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.is_ld * input.offset_bit[2] = 0 ∧
    (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1] = 0 ∧
    (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[0] = 0 ∧
    isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
    (isReal input - 1) * input.adapter.op_a_0 = 0 ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, opcodeVal input⟩ ∧
    -- SC Phase 2c: the honest prover supplies the State pull's `StateTruth`.
    (isReal input = 1 → SP1Clean.Semantics.StateTruth (Readers.CPUState.stateMsgOf input.state) data)

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  simp only [isReal, opcodeVal] at h_assumptions
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_pv_isu64, h_b0, h_b1, h_b2, h_b3, h_b4, h_b5,
    h_b6, hbin, h_al2, h_al1, h_al0, h_oa1, h_oa2, h_cpu, h_mem, h_it, h_st⟩ := h_assumptions
  simp only [sub_eq_add_neg] at h_oa1 h_oa2
  obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, hmap_pc⟩, _, _, hmap_ob⟩ := h_input
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have hob0' : Expression.eval env.toEnvironment input_var_offset_bit[0] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[0] = 1 := by rw [eob 0 (by omega)]; exact hob0
  have hob1' : Expression.eval env.toEnvironment input_var_offset_bit[1] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[1] = 1 := by rw [eob 1 (by omega)]; exact hob1
  have hob2' : Expression.eval env.toEnvironment input_var_offset_bit[2] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[2] = 1 := by rw [eob 2 (by omega)]; exact hob2
  have h_off' : (Expression.eval env.toEnvironment input_var_offset_bit[0]).val
        + 2 * (Expression.eval env.toEnvironment input_var_offset_bit[1]).val
        + 4 * (Expression.eval env.toEnvironment input_var_offset_bit[2]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)]; exact h_off
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1],
          Expression.eval env.toEnvironment input_var_offset_bit[2]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, hob0', hob1', hob2', h_ge, h_off'⟩
  refine ⟨⟨?_, ?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · -- SC Phase 2c: the CPUState state pull's `StateTruth`, supplied by the honest prover (`h_st`).
    simp only [Readers.CPUState.stateMsgOf]; exact h_st
  · exact ⟨hbin, fun _ => h_pv_isu64⟩
  · exact h_mem
  · exact ⟨hbin, hbin⟩
  · exact h_it
  · rcases h_b0 with h | h <;> rw [h] <;> simp
  · rcases h_b1 with h | h <;> rw [h] <;> simp
  · rcases h_b2 with h | h <;> rw [h] <;> simp
  · rcases h_b3 with h | h <;> rw [h] <;> simp
  · rcases h_b4 with h | h <;> rw [h] <;> simp
  · rcases h_b5 with h | h <;> rw [h] <;> simp
  · rcases h_b6 with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp
  · simp only [eob 2 (by omega)]; exact h_al2
  · simp only [eob 1 (by omega)]; exact h_al1
  · simp only [eob 0 (by omega)]; exact h_al0
  · exact h_oa1
  · exact h_oa2

/-- The `LoadX0` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadX0Columns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadX0Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    soundness := soundness, completeness := completeness,
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8); the
    -- enabled flag is the **derived** umbrella selector sum (SP1's `is_real`, all seven load opcodes).
    exposedChannels := fun input _ =>
      stateChannel.expose
        [ stateChannel.pulledIf (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
              + input.is_lw + input.is_lwu + input.is_ld)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
              + input.is_lw + input.is_lwu + input.is_ld)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
        List.map_cons, List.map_nil]
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        AddressOperation.circuit, AddressOperation.main,
        AddrAddOperation.circuit, AddrAddOperation.main,
        Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
        Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.LoadX0Chip
