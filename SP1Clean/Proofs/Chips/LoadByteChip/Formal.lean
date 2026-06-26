import SP1Clean.Native.Chips.LoadByteChip.Defs

/-! # `SP1Clean.LoadByteChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadByteChip

open Circuit
open Extracted (LoadByteColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; the load targets a non-reserved, in-range address (no alignment for byte
loads). The offset bits are bits 0–2 of the address and boolean. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1)

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, hu8, hmsb_rcv, h_itype, hsel0, hsel1, hsel2, hsel3, hmux,
    h_op_a_0, h_msbgate, h_lb_gate, h_lbu_gate, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_lb_bin := bool_of_mul_pred h_lb_gate
  have h_lbu_bin := bool_of_mul_pred h_lbu_gate
  simp only [circuit_norm, byteChannel] at hu8 hmsb_rcv
  -- eval→value bridges (extracted directly from `h_input`; `tauto` over this context is too slow).
  obtain ⟨_, _, _, _, ⟨hmap_pv, _, _, _, _, _⟩, hmap_ob, _, _, _, _⟩ := h_input
  have eob : ∀ i (hi : i < 3), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega), epv 1 (by omega),
    epv 2 (by omega), epv 3 (by omega), ← sub_eq_add_neg] at hsel0 hsel1 hsel2 hsel3
  simp only [eob 0 (by omega), ← sub_eq_add_neg] at hmux
  -- the byte-mux equation in value form.
  have hmux_eq : input_selected_byte = input_offset_bit[0]
      * ((input_selected_limb - input_selected_limb_low_byte) * (256 : ZMod p)⁻¹)
      + ((1 : ZMod p) - input_offset_bit[0]) * input_selected_limb_low_byte := sub_eq_zero.mp hmux
  -- the real-row byte bounds, from the inline U8Range-pair receive.
  have h_u8 : input_is_lb + input_is_lbu = 1 →
      input_selected_limb_low_byte.val < 256
        ∧ ((input_selected_limb - input_selected_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 := by
    intro h1
    have hneg : -(input_is_lb + input_is_lbu) = -1 := by rw [h1]
    have G := hu8 hneg
    have hb := (byteRowSpec_u8range_pair _ _).mp G
    rw [show (2:ℕ)^8 = 256 from by norm_num, ← sub_eq_add_neg] at hb
    exact hb
  -- `selected_byte < 256`, by the byte-mux + the offset-bit-0 case split.
  have h_byte_lt : input_is_lb + input_is_lbu = 1 → input_selected_byte.val < 256 := by
    intro h1
    obtain ⟨hlo, hhi⟩ := h_u8 h1
    rw [hmux_eq]
    rcases hob0 with h0 | h0
    · rw [h0]; simp only [zero_mul, zero_add, sub_zero, one_mul]; exact hlo
    · rw [h0]; simp only [one_mul, sub_self, zero_mul, add_zero]; exact hhi
  -- the LB-row sign-bit fact, from the inline MSB receive.
  have h_msb_fact : input_is_lb = 1 →
      (input_msb = 0 ∨ input_msb = 1) ∧ (input_msb = 1 ↔ 128 ≤ input_selected_byte.val) := by
    intro h1
    have hneg : -input_is_lb = -1 := by rw [h1]
    have G := hmsb_rcv hneg
    have := (byteRowSpec_msb _ _).mp G
    exact ⟨this.2.1, this.2.2⟩
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
  have h_it := h_itype h_bin
  refine ⟨⟨h_addr_spec, h_mem h_bin, h_it,
      fun h1 => ⟨(h_u8 h1).1, (h_u8 h1).2, h_byte_lt h1⟩, h_msb_fact,
      ⟨hsel0, hsel1, hsel2, hsel3⟩, hmux_eq, h_op_a_0, h_msbgate, h_lb_bin, h_lbu_bin, h_bin⟩,
    h_bin, Or.inr h_addr_as, Or.inr h_bin,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    fun h1 h0 => off_gate_vacuous h_lb_bin h1 h0,
    Or.inr h_bin⟩

/-- Prover-side row well-formedness: the address facts + selector binaries + `op_a_0 = 0` + the byte
value bounds + the sign-bit fact + the limb-selection / byte-mux equations + the reader `Spec`s. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    input.selected_limb_low_byte.val < 256 ∧ (highByte input).val < 256 ∧ input.selected_byte.val < 256 ∧
    (input.msb = 0 ∨ input.msb = 1) ∧ (input.msb = 1 ↔ 128 ≤ input.selected_byte.val) ∧
    input.is_lbu * input.msb = 0 ∧
    ((input.selected_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
    input.selected_byte = input.offset_bit[0] * highByte input
        + (1 - input.offset_bit[0]) * input.selected_limb_low_byte ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
        input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb,
        65535 * input.msb⟩

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_lb_bin, h_lbu_bin, hbin, h_op_a_0,
    hlo_pa, hhi_pa, hbyte_pa, h_msb_bin, h_msb_iff, h_msbgate, ⟨hsel0, hsel1, hsel2, hsel3⟩,
    hmux_pa, h_cpu, h_mem, h_it⟩ := h_assumptions
  obtain ⟨_, _, ⟨_, _, _, hmap_pc⟩, _, ⟨hmap_pv, _, _, _, _, _⟩, hmap_ob, _, _, _, _⟩ := h_input
  simp only [isReal] at hbin
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_msb_lt : input_msb.val < 256 := by
    rcases h_msb_bin with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
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
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact hbin
  · exact h_mem
  · -- U8Range-pair receive obligation (real row); value is raw (`toRaw` (gated post-#398)).
    intro _
    simp only [byteChannel]; rw [← sub_eq_add_neg]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hlo_pa, hhi_pa⟩
  · -- MSB receive obligation (real LB row); value is raw (`toRaw` (gated post-#398)).
    intro _
    simp only [byteChannel]
    exact (byteRowSpec_msb _ _).mpr ⟨⟨h_msb_lt, hbyte_pa⟩, h_msb_bin, h_msb_iff⟩
  · exact hbin
  · exact h_it
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega), ← sub_eq_add_neg]; exact hsel0
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 1 (by omega), ← sub_eq_add_neg]; exact hsel1
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 2 (by omega), ← sub_eq_add_neg]; exact hsel2
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 3 (by omega), ← sub_eq_add_neg]; exact hsel3
  · simp only [eob 0 (by omega), ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hmux_pa
  · exact h_op_a_0
  · exact h_msbgate
  · rcases h_lb_bin with h | h <;> rw [h] <;> simp
  · rcases h_lbu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `LoadByte` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadByteColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadByteColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw],
    soundness := soundness, completeness := completeness }

end SP1Clean.LoadByteChip
