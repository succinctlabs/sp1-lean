import SP1Clean.Native.Chips.StoreHalfChip.Defs

/-! # `SP1Clean.StoreHalfChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreHalfChip

open Circuit
open Extracted (StoreHalfColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the store targets a **valid, aligned, non-reserved** address: the sum
fits in 48 bits, is non-reserved (`≥ 2^16`), is 2-byte aligned (`addr mod 2 = 0`), and `offset_bit[0..1]`
are bits 1–2 (`2·offset_bit[0] + 4·offset_bit[1] = addr mod 8`) and boolean. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 2 = 0 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    2 * input.offset_bit[0].val + 4 * input.offset_bit[1].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8

set_option maxHeartbeats 8000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, hob0, hob1, h_off⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, hr0, hr1, hr2, hr3, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- eval→value bridges for the nested vectors the RMW equations / subcircuit input reference.
  have hmap_ob : Vector.map (Expression.eval env) input_var_offset_bit = input_offset_bit :=
    h_input.2.2.2.2.1
  have hmap_sv : Vector.map (Expression.eval env) input_var_store_value = input_store_value :=
    h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
  have eob0 : Expression.eval env input_var_offset_bit[0] = input_offset_bit[0] := by
    rw [← hmap_ob]; simp only [Vector.getElem_map]
  have eob1 : Expression.eval env input_var_offset_bit[1] = input_offset_bit[1] := by
    rw [← hmap_ob]; simp only [Vector.getElem_map]
  have esv0 : Expression.eval env input_var_store_value[0] = input_store_value[0] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv1 : Expression.eval env input_var_store_value[1] = input_store_value[1] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv2 : Expression.eval env input_var_store_value[2] = input_store_value[2] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv3 : Expression.eval env input_var_store_value[3] = input_store_value[3] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv0 : Expression.eval env input_var_memory_access_prev_value[0]
      = input_memory_access_prev_value[0] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv1 : Expression.eval env input_var_memory_access_prev_value[1]
      = input_memory_access_prev_value[1] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv2 : Expression.eval env input_var_memory_access_prev_value[2]
      = input_memory_access_prev_value[2] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv3 : Expression.eval env input_var_memory_access_prev_value[3]
      = input_memory_access_prev_value[3] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap0 : Expression.eval env input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  simp only [esv0, esv1, esv2, esv3, epv0, epv1, epv2, epv3, eoap0, eob0, eob1, ← sub_eq_add_neg]
    at hr0 hr1 hr2 hr3
  have h_it := h_itype h_bin
  have hob0' : Expression.eval env input_var_offset_bit[0] = 0
      ∨ Expression.eval env input_var_offset_bit[0] = 1 := by rw [eob0]; exact hob0
  have hob1' : Expression.eval env input_var_offset_bit[1] = 0
      ∨ Expression.eval env input_var_offset_bit[1] = 1 := by rw [eob1]; exact hob1
  have h_off' : (0 : ZMod p).val + 2 * (Expression.eval env input_var_offset_bit[0]).val
        + 4 * (Expression.eval env input_var_offset_bit[1]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob0, eob1]; simp only [ZMod.val_zero]; omega
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, hob0', hob1', h_ge, h_off'⟩
  have h_addr_spec := h_addr h_addr_as
  simp only [eob0, eob1] at h_addr_spec
  refine ⟨⟨h_addr_spec, h_mem h_bin, h_it,
    ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩, ?_⟩
  exact ⟨Or.inr h_bin, Or.inr h_addr_as, Or.inr h_bin, Or.inr h_bin⟩

/-- Prover-side row well-formedness: operand `isU64`s + address-fits/alignment + the `offset_bit`
decomposition + offset binaries + `is_real` binary + the reader `Spec`s + the read-modify-write equations. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 2 = 0 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    2 * input.offset_bit[0].val + 4 * input.offset_bit[1].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    (input.store_value[0] = input.memory_access.prev_value[0]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0])
          * (1 - input.offset_bit[0]) * (1 - input.offset_bit[1]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[1])
          * input.offset_bit[0] * (1 - input.offset_bit[1]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2])
          * (1 - input.offset_bit[0]) * input.offset_bit[1] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[3])
          * input.offset_bit[0] * input.offset_bit[1]) ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.store_value, input.is_real⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 37⟩

set_option maxHeartbeats 8000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_align, hob0, hob1, h_off, hbin, ⟨hr0, hr1, hr2, hr3⟩,
    h_cpu, h_mem, h_it⟩ := h_assumptions
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
  have hmap_ob : Vector.map (Expression.eval env.toEnvironment) input_var_offset_bit
      = input_offset_bit := h_input.2.2.2.2.1
  have hmap_sv : Vector.map (Expression.eval env.toEnvironment) input_var_store_value
      = input_store_value := h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob0 : Expression.eval env.toEnvironment input_var_offset_bit[0]
      = input_offset_bit[0] := by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have eob1 : Expression.eval env.toEnvironment input_var_offset_bit[1]
      = input_offset_bit[1] := by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have esv0 : Expression.eval env.toEnvironment input_var_store_value[0] = input_store_value[0] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv1 : Expression.eval env.toEnvironment input_var_store_value[1] = input_store_value[1] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv2 : Expression.eval env.toEnvironment input_var_store_value[2] = input_store_value[2] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have esv3 : Expression.eval env.toEnvironment input_var_store_value[3] = input_store_value[3] := by
    rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv0 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[0]
      = input_memory_access_prev_value[0] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv1 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[1]
      = input_memory_access_prev_value[1] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv2 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[2]
      = input_memory_access_prev_value[2] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv3 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[3]
      = input_memory_access_prev_value[3] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap0 : Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  have hob0' : Expression.eval env.toEnvironment input_var_offset_bit[0] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[0] = 1 := by rw [eob0]; exact hob0
  have hob1' : Expression.eval env.toEnvironment input_var_offset_bit[1] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[1] = 1 := by rw [eob1]; exact hob1
  have h_off' : (0 : ZMod p).val + 2 * (Expression.eval env.toEnvironment input_var_offset_bit[0]).val
        + 4 * (Expression.eval env.toEnvironment input_var_offset_bit[1]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob0, eob1]; simp only [ZMod.val_zero]; omega
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, hob0', hob1', h_ge, h_off'⟩
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc0, epc1, epc2]; exact h_cpu
  · exact hbin
  · exact h_mem
  · exact hbin
  · exact h_it
  · simp only [esv0, epv0, eoap0, eob0, eob1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr0
  · simp only [esv1, epv1, eoap0, eob0, eob1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr1
  · simp only [esv2, epv2, eoap0, eob0, eob1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr2
  · simp only [esv3, epv3, eoap0, eob0, eob1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `StoreHalf` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreHalfColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreHalfColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.StoreHalfChip
