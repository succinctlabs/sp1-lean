import SP1Clean.Native.Chips.LoadWordChip.Defs

/-! # `SP1Clean.LoadWordChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadWordChip

open Circuit
open Extracted (LoadWordColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the load targets a **valid, aligned, non-reserved** address: the sum
fits in 48 bits, is non-reserved (`≥ 2^16`), is 4-byte aligned (`addr mod 4 = 0`), `offset_bit` is bit 2
(`4·offset_bit = addr mod 8`), and the selected high limb is genuinely 16-bit (`prev_value[1]`,
`prev_value[3] < 2^16` — memory values are 16-bit-limbed; honest at the single-row level). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    input.memory_access.prev_value[1].val < 2 ^ 16 ∧ input.memory_access.prev_value[3].val < 2 ^ 16

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `op_b_val`/`op_c_imm` are reducible adapter projections (`adapter.op_b_memory.prev_value` /
  -- `adapter.op_c_imm`), not committed columns — unfold them to the destructured adapter binders.
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, hpv1, hpv3⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_msb, h_itype, hsel0, hsel1, hsel2, hsel3, h_op_a_0,
    h_msbgate, h_lw_gate, h_lwu_gate, h_gate⟩ := h_holds
  -- the proven `is_real`-binary gate discharges the readers'/`MemoryAccess`'s `Assumptions`.
  have h_bin := bool_of_mul_pred h_gate
  have h_lw_bin := bool_of_mul_pred h_lw_gate
  -- eval→value bridges for the nested vector fields the sub-`Spec`s / selection gates reference.
  have hmap_sw : Vector.map (Expression.eval env) input_var_selected_word = input_selected_word :=
    h_input.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have esw : ∀ i (hi : i < 2), Expression.eval env input_var_selected_word[i]
      = input_selected_word[i] := fun i hi => by rw [← hmap_sw]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [esw 0 (by omega), esw 1 (by omega), epv 0 (by omega), epv 1 (by omega),
    epv 2 (by omega), epv 3 (by omega), ← sub_eq_add_neg] at hsel0 hsel1 hsel2 hsel3
  simp only [← sub_eq_add_neg] at h_msbgate
  rw [esw 1 (by omega)] at h_msb
  have h_it := h_itype h_bin
  simp only [esw 0 (by omega), esw 1 (by omega)] at h_it
  -- the `AddressOperation` Assumptions: operand `isU64`s + fits, offset bits boolean (0, 0, the witnessed
  -- `offset_bit`), non-reserved, and the offset decomposition `4·offset_bit = addr % 8`.
  have h_off' : (0 : ZMod p).val + 2 * (0 : ZMod p).val + 4 * input_offset_bit.val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    simp only [ZMod.val_zero]; omega
  -- `offset_bit` binary, derived from 4-alignment + the offset decomposition bound.
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
  have h_addr_spec := h_addr h_addr_as
  -- `selected_word[1] < 2^16` on a real `is_lw` row: it equals `prev_value[1]` (offset 0) or
  -- `prev_value[3]` (offset 1), both genuine 16-bit memory limbs.
  have h_sel1_lt : input_selected_word[1].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · -- offset 0: gate B forces `selected_word[1] = prev_value[1]`.
      have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      have heq := sub_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right hne)
      rw [heq]; exact hpv1
    · -- offset 1: gate D forces `selected_word[1] = prev_value[3]`.
      have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      have heq := sub_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right hne)
      rw [heq]; exact hpv3
  -- eval-form variant of the 16-bit bound, for the `U16MSBOperation` channel-requirement tail.
  have h_sel1_lt_eval : (Expression.eval env input_var_selected_word[1]).val < 2 ^ 16 := by
    rw [esw 1 (by omega)]; exact h_sel1_lt
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_selected_word[1], ⟨input_msb⟩, input_is_lw⟩ : U16MSBOperation.Inputs (ZMod p)) :=
    ⟨fun _ => h_sel1_lt, h_lw_bin⟩
  have h_msb_spec := h_msb h_msb_as
  refine ⟨⟨h_addr_spec, h_mem h_bin, h_msb_spec, h_it, ⟨hsel0, hsel1, hsel2, hsel3⟩, h_op_a_0,
    h_msbgate, h_lw_bin, bool_of_mul_pred h_lwu_gate, h_bin⟩, ?_⟩
  -- the per-subcircuit channel-requirement tail (`channels = [] ∨ <sub>.Assumptions`; the
  -- `U16MSBOperation` byte-bus subcircuit contributes its own `Assumptions` in eval form).
  refine ⟨h_bin, Or.inr h_addr_as, Or.inr h_bin,
    Or.inr ⟨fun _ => h_sel1_lt_eval, h_lw_bin⟩, Or.inr h_bin⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits/alignment + the
`offset_bit` decomposition + the selected-limb 16-bit bounds + the reader/gadget `Spec`s + the selector
binaries + `op_a_0 = 0` + the offset-selection equations + the `(is_lw-1)·msb` zero-extension gate. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    input.memory_access.prev_value[1].val < 2 ^ 16 ∧ input.memory_access.prev_value[3].val < 2 ^ 16 ∧
    (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    ((input.selected_word[0] - input.memory_access.prev_value[0]) * (input.offset_bit - 1) = 0 ∧
      (input.selected_word[1] - input.memory_access.prev_value[1]) * (input.offset_bit - 1) = 0 ∧
      (input.selected_word[0] - input.memory_access.prev_value[2]) * input.offset_bit = 0 ∧
      (input.selected_word[1] - input.memory_access.prev_value[3]) * input.offset_bit = 0) ∧
    input.msb * (input.is_lw - 1) = 0 ∧
    U16MSBOperation.Spec ⟨input.selected_word[1], ⟨input.msb⟩, input.is_lw⟩ ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
        input.selected_word[0], input.selected_word[1], 65535 * input.msb, 65535 * input.msb⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, hpv1, hpv3, h_lw_bin, h_lwu_bin, hbin, h_op_a_0,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, h_msbgate, h_msb_spec, h_cpu, h_mem, h_it⟩ := h_assumptions
  simp only [isReal] at hbin
  -- eval→value bridges for the nested vectors the reader/gadget `Spec`s reference.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.2.1.2.2.2
  have hmap_sw : Vector.map (Expression.eval env.toEnvironment) input_var_selected_word
      = input_selected_word := h_input.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have esw : ∀ i (hi : i < 2), Expression.eval env.toEnvironment input_var_selected_word[i]
      = input_selected_word[i] := fun i hi => by rw [← hmap_sw]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  -- the `AddressOperation` subcircuit `Assumptions`.
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
  -- `selected_word[1] < 2^16` (value + eval form), for the `U16MSBOperation` assertion `Assumptions`.
  have h_sel1_lt : input_selected_word[1].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right hne)]; exact hpv1
    · have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right hne)]; exact hpv3
  have h_sel1_lt_eval : (Expression.eval env.toEnvironment input_var_selected_word[1]).val < 2 ^ 16 := by
    rw [esw 1 (by omega)]; exact h_sel1_lt
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨⟨fun _ => h_sel1_lt_eval, h_lw_bin⟩, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, h_op_a_0, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact hbin
  · exact h_mem
  · simp only [esw 1 (by omega)]; exact h_msb_spec
  · exact hbin
  · simp only [esw 0 (by omega), esw 1 (by omega)]; exact h_it
  · simp only [esw 0 (by omega), epv 0 (by omega), ← sub_eq_add_neg]; exact hsel0
  · simp only [esw 1 (by omega), epv 1 (by omega), ← sub_eq_add_neg]; exact hsel1
  · simp only [esw 0 (by omega), epv 2 (by omega), ← sub_eq_add_neg]; exact hsel2
  · simp only [esw 1 (by omega), epv 3 (by omega), ← sub_eq_add_neg]; exact hsel3
  · simp only [← sub_eq_add_neg]; exact h_msbgate
  · rcases h_lw_bin with h | h <;> rw [h] <;> simp
  · rcases h_lwu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `LoadWord` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadWordColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadWordColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw],
    soundness := soundness, completeness := completeness }

end SP1Clean.LoadWordChip
