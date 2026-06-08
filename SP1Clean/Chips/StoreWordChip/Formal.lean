import SP1Clean.Chips.StoreWordChip.Defs

/-! # `SP1Clean.StoreWordChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreWordChip

open Circuit
open Extracted (StoreWordColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the store targets a **valid, aligned, non-reserved** address: the sum
fits in 48 bits, is non-reserved (`≥ 2^16`), is 4-byte aligned (`addr mod 4 = 0`), and `offset_bit` is
bit 2 (`4·offset_bit = addr mod 8`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, hr0, hr1, hr2, hr3, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- eval→value bridges for the nested vectors the RMW equations reference.
  have hmap_sv : Vector.map (Expression.eval env) input_var_store_value = input_store_value :=
    h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
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
  have eoap1 : Expression.eval env input_var_adapter_op_a_memory_prev_value[1]
      = input_adapter_op_a_memory_prev_value[1] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  simp only [esv0, esv1, esv2, esv3, epv0, epv1, epv2, epv3, eoap0, eoap1, ← sub_eq_add_neg]
    at hr0 hr1 hr2 hr3
  have h_it := h_itype h_bin
  have h_off' : (0 : ZMod p).val + 2 * (0 : ZMod p).val + 4 * input_offset_bit.val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    simp only [ZMod.val_zero]; omega
  have h_off_bin : input_offset_bit = 0 ∨ input_offset_bit = 1 := by
    have h8 : (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 < 8 :=
      Nat.mod_lt _ (by norm_num)
    have hv : input_offset_bit.val = 0 ∨ input_offset_bit.val = 1 := by omega
    rcases hv with h | h
    · left; exact (ZMod.val_eq_zero _).mp h
    · right; have := ZMod.natCast_zmod_val input_offset_bit; rw [h, Nat.cast_one] at this; exact this.symm
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, input_offset_bit⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, h_off_bin, h_ge, h_off'⟩
  refine ⟨⟨h_addr h_addr_as, h_mem h_bin, h_it,
    ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩, ?_⟩
  exact ⟨Or.inr h_bin, Or.inr h_addr_as, Or.inr h_bin, Or.inr h_bin⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits/alignment + the
`offset_bit` decomposition + `is_real` binary + the reader `Spec`s + the read-modify-write equations. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    (input.store_value[0] = input.memory_access.prev_value[0]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[0]) * (1 - input.offset_bit) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
        + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[1]) * (1 - input.offset_bit) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
        + (input.adapter.op_a_memory.prev_value[0] - input.memory_access.prev_value[2]) * input.offset_bit ∧
      input.store_value[3] = input.memory_access.prev_value[3]
        + (input.adapter.op_a_memory.prev_value[1] - input.memory_access.prev_value[3]) * input.offset_bit) ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.store_value, input.is_real⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 38⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, hbin, ⟨hr0, hr1, hr2, hr3⟩, h_cpu, h_mem, h_it⟩ :=
    h_assumptions
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
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
  have eoap1 : Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1]
      = input_adapter_op_a_memory_prev_value[1] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  have h_off' : (0 : ZMod p).val + 2 * (0 : ZMod p).val + 4 * input_offset_bit.val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    simp only [ZMod.val_zero]; omega
  have h_off_bin : input_offset_bit = 0 ∨ input_offset_bit = 1 := by
    have h8 : (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 < 8 :=
      Nat.mod_lt _ (by norm_num)
    have hv : input_offset_bit.val = 0 ∨ input_offset_bit.val = 1 := by omega
    rcases hv with h | h
    · left; exact (ZMod.val_eq_zero _).mp h
    · right; have := ZMod.natCast_zmod_val input_offset_bit; rw [h, Nat.cast_one] at this; exact this.symm
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, input_offset_bit⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, h_off_bin, h_ge, h_off'⟩
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc0, epc1, epc2]; exact h_cpu
  · exact hbin
  · exact h_mem
  · exact hbin
  · exact h_it
  · simp only [esv0, epv0, eoap0, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr0
  · simp only [esv1, epv1, eoap1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr1
  · simp only [esv2, epv2, eoap0, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr2
  · simp only [esv3, epv3, eoap1, ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `StoreWord` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreWordColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreWordColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.StoreWordChip
