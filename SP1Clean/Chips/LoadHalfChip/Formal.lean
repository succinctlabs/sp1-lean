import SP1Clean.Chips.LoadHalfChip.Defs

/-! # `SP1Clean.LoadHalfChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadHalfChip

open Circuit
open Extracted (LoadHalfColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the load targets a **valid, aligned, non-reserved** address: the sum
fits in 48 bits, is non-reserved (`≥ 2^16`), is 2-byte aligned (`addr mod 2 = 0`), `offset_bit[0..1]` are
bits 1–2 (`2·offset_bit[0] + 4·offset_bit[1] = addr mod 8`) and boolean, and all four memory limbs are
genuinely 16-bit (`prev_value[i] < 2^16` — honest at the single-row level). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 2 = 0 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    2 * input.offset_bit[0].val + 4 * input.offset_bit[1].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    input.memory_access.prev_value[0].val < 2 ^ 16 ∧ input.memory_access.prev_value[1].val < 2 ^ 16 ∧
    input.memory_access.prev_value[2].val < 2 ^ 16 ∧ input.memory_access.prev_value[3].val < 2 ^ 16

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hfit, h_ge, h_align, hob0, hob1, h_off, hpv0, hpv1, hpv2, hpv3⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_msb, h_itype, hsel0, hsel1, hsel2, hsel3, h_op_a_0,
    h_msbgate, h_lh_gate, h_lhu_gate, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_lh_bin := bool_of_mul_pred h_lh_gate
  -- eval→value bridges for the nested vector fields the sub-`Spec`s / selection gates reference.
  have hmap_ob : Vector.map (Expression.eval env) input_var_offset_bit = input_offset_bit :=
    h_input.2.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.2.2.1.1
  have eob0 : Expression.eval env input_var_offset_bit[0] = input_offset_bit[0] := by
    rw [← hmap_ob]; simp only [Vector.getElem_map]
  have eob1 : Expression.eval env input_var_offset_bit[1] = input_offset_bit[1] := by
    rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv0 : Expression.eval env input_var_memory_access_prev_value[0]
      = input_memory_access_prev_value[0] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv1 : Expression.eval env input_var_memory_access_prev_value[1]
      = input_memory_access_prev_value[1] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv2 : Expression.eval env input_var_memory_access_prev_value[2]
      = input_memory_access_prev_value[2] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv3 : Expression.eval env input_var_memory_access_prev_value[3]
      = input_memory_access_prev_value[3] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [eob0, eob1, epv0, epv1, epv2, epv3, ← sub_eq_add_neg] at hsel0 hsel1 hsel2 hsel3
  have h_it := h_itype h_bin
  -- the `AddressOperation` Assumptions (eval form, matching the subcircuit input).
  have hob0' : Expression.eval env input_var_offset_bit[0] = 0
      ∨ Expression.eval env input_var_offset_bit[0] = 1 := by rw [eob0]; exact hob0
  have hob1' : Expression.eval env input_var_offset_bit[1] = 0
      ∨ Expression.eval env input_var_offset_bit[1] = 1 := by rw [eob1]; exact hob1
  have h_off' : (0 : ZMod p).val + 2 * (Expression.eval env input_var_offset_bit[0]).val
        + 4 * (Expression.eval env input_var_offset_bit[1]).val
      = (Word.toNat input_op_b_val + Word.toNat input_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob0, eob1]; simp only [ZMod.val_zero]; omega
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_op_b_val, input_op_c_imm, 0, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, hob0', hob1', h_ge, h_off'⟩
  have h_addr_spec := h_addr h_addr_as
  simp only [eob0, eob1] at h_addr_spec
  -- `selected_half < 2^16` on a real row: it equals one of the four 16-bit limbs by the offset corner.
  have h_sel_lt : input_selected_half.val < 2 ^ 16 := by
    rcases hob0 with hb0 | hb0
    · rcases hob1 with hb1 | hb1
      · -- (0,0): gate 0 ⟹ selected_half = prev_value[0].
        have ho : input_offset_bit[1] - 1 ≠ 0 := by rw [hb1, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        have hi : input_offset_bit[0] - 1 ≠ 0 := by rw [hb0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel0).resolve_right ho)).resolve_right hi)]
        exact hpv0
      · -- (0,1): gate 2 ⟹ selected_half = prev_value[2].
        have ho : input_offset_bit[1] ≠ 0 := by rw [hb1]; exact one_ne_zero
        have hi : input_offset_bit[0] - 1 ≠ 0 := by rw [hb0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel2).resolve_right ho)).resolve_right hi)]
        exact hpv2
    · rcases hob1 with hb1 | hb1
      · -- (1,0): gate 1 ⟹ selected_half = prev_value[1].
        have ho : input_offset_bit[1] - 1 ≠ 0 := by rw [hb1, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        have hi : input_offset_bit[0] ≠ 0 := by rw [hb0]; exact one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right ho)).resolve_right hi)]
        exact hpv1
      · -- (1,1): gate 3 ⟹ selected_half = prev_value[3].
        have ho : input_offset_bit[1] ≠ 0 := by rw [hb1]; exact one_ne_zero
        have hi : input_offset_bit[0] ≠ 0 := by rw [hb0]; exact one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right ho)).resolve_right hi)]
        exact hpv3
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_selected_half, ⟨input_msb⟩, input_is_lh⟩ : U16MSBOperation.Inputs (ZMod p)) :=
    ⟨fun _ => h_sel_lt, h_lh_bin⟩
  have h_msb_spec := h_msb h_msb_as
  refine ⟨⟨h_addr_spec, h_mem h_bin, h_msb_spec, h_it, ⟨hsel0, hsel1, hsel2, hsel3⟩, h_op_a_0,
    h_msbgate, h_lh_bin, bool_of_mul_pred h_lhu_gate, h_bin⟩, ?_⟩
  refine ⟨Or.inr h_bin, Or.inr h_addr_as, Or.inr h_bin,
    Or.inr ⟨fun _ => h_sel_lt, h_lh_bin⟩, Or.inr h_bin⟩

/-- Prover-side row well-formedness: the address facts + the reader/gadget `Spec`s + the selector
binaries + `op_a_0 = 0` + the offset-selection equations + the `is_lhu·msb` zero-extension gate. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 2 = 0 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    2 * input.offset_bit[0].val + 4 * input.offset_bit[1].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    input.memory_access.prev_value[0].val < 2 ^ 16 ∧ input.memory_access.prev_value[1].val < 2 ^ 16 ∧
    input.memory_access.prev_value[2].val < 2 ^ 16 ∧ input.memory_access.prev_value[3].val < 2 ^ 16 ∧
    (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    ((input.selected_half - input.memory_access.prev_value[0])
        * (input.offset_bit[0] - 1) * (input.offset_bit[1] - 1) = 0 ∧
      (input.selected_half - input.memory_access.prev_value[1])
        * input.offset_bit[0] * (input.offset_bit[1] - 1) = 0 ∧
      (input.selected_half - input.memory_access.prev_value[2])
        * (input.offset_bit[0] - 1) * input.offset_bit[1] = 0 ∧
      (input.selected_half - input.memory_access.prev_value[3])
        * input.offset_bit[0] * input.offset_bit[1] = 0) ∧
    input.is_lhu * input.msb = 0 ∧
    U16MSBOperation.Spec ⟨input.selected_half, ⟨input.msb⟩, input.is_lh⟩ ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
        input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hfit, h_ge, h_align, hob0, hob1, h_off, hpv0, hpv1, hpv2, hpv3,
    h_lh_bin, h_lhu_bin, hbin, h_op_a_0, ⟨hsel0, hsel1, hsel2, hsel3⟩, h_msbgate, h_msb_spec,
    h_cpu, h_mem, h_it⟩ := h_assumptions
  simp only [isReal] at hbin
  -- eval→value bridges for the nested vectors the reader/gadget `Spec`s reference.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.2.2.2.1.2.2.2
  have hmap_ob : Vector.map (Expression.eval env.toEnvironment) input_var_offset_bit
      = input_offset_bit := h_input.2.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.2.2.1.1
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0]
      = input_state_pc[0] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1]
      = input_state_pc[1] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2]
      = input_state_pc[2] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob0 : Expression.eval env.toEnvironment input_var_offset_bit[0]
      = input_offset_bit[0] := by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have eob1 : Expression.eval env.toEnvironment input_var_offset_bit[1]
      = input_offset_bit[1] := by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv0 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[0]
      = input_memory_access_prev_value[0] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv1 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[1]
      = input_memory_access_prev_value[1] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv2 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[2]
      = input_memory_access_prev_value[2] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epv3 : Expression.eval env.toEnvironment input_var_memory_access_prev_value[3]
      = input_memory_access_prev_value[3] := by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have hob0' : Expression.eval env.toEnvironment input_var_offset_bit[0] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[0] = 1 := by rw [eob0]; exact hob0
  have hob1' : Expression.eval env.toEnvironment input_var_offset_bit[1] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[1] = 1 := by rw [eob1]; exact hob1
  have h_off' : (0 : ZMod p).val + 2 * (Expression.eval env.toEnvironment input_var_offset_bit[0]).val
        + 4 * (Expression.eval env.toEnvironment input_var_offset_bit[1]).val
      = (Word.toNat input_op_b_val + Word.toNat input_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob0, eob1]; simp only [ZMod.val_zero]; omega
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_op_b_val, input_op_c_imm, 0, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, hob0', hob1', h_ge, h_off'⟩
  have h_sel_lt : input_selected_half.val < 2 ^ 16 := by
    rcases hob0 with hb0 | hb0
    · rcases hob1 with hb1 | hb1
      · have ho : input_offset_bit[1] - 1 ≠ 0 := by rw [hb1, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        have hi : input_offset_bit[0] - 1 ≠ 0 := by rw [hb0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel0).resolve_right ho)).resolve_right hi)]
        exact hpv0
      · have ho : input_offset_bit[1] ≠ 0 := by rw [hb1]; exact one_ne_zero
        have hi : input_offset_bit[0] - 1 ≠ 0 := by rw [hb0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel2).resolve_right ho)).resolve_right hi)]
        exact hpv2
    · rcases hob1 with hb1 | hb1
      · have ho : input_offset_bit[1] - 1 ≠ 0 := by rw [hb1, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        have hi : input_offset_bit[0] ≠ 0 := by rw [hb0]; exact one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right ho)).resolve_right hi)]
        exact hpv1
      · have ho : input_offset_bit[1] ≠ 0 := by rw [hb1]; exact one_ne_zero
        have hi : input_offset_bit[0] ≠ 0 := by rw [hb0]; exact one_ne_zero
        rw [sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right ho)).resolve_right hi)]
        exact hpv3
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨⟨fun _ => h_sel_lt, h_lh_bin⟩, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, h_op_a_0, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc0, epc1, epc2]; exact h_cpu
  · exact hbin
  · exact h_mem
  · exact h_msb_spec
  · exact hbin
  · exact h_it
  · simp only [eob0, eob1, epv0, ← sub_eq_add_neg]; exact hsel0
  · simp only [eob0, eob1, epv1, ← sub_eq_add_neg]; exact hsel1
  · simp only [eob0, eob1, epv2, ← sub_eq_add_neg]; exact hsel2
  · simp only [eob0, eob1, epv3, ← sub_eq_add_neg]; exact hsel3
  · exact h_msbgate
  · rcases h_lh_bin with h | h <;> rw [h] <;> simp
  · rcases h_lhu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `LoadHalf` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadHalfColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadHalfColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.LoadHalfChip
