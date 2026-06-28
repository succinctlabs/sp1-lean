import SP1Clean.Native.Chips.StoreByteChip.Defs

/-! # `SP1Clean.StoreByteChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreByteChip

open Circuit
open Extracted (StoreByteColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; the store targets a non-reserved, in-range address (no alignment). -/
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
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, hreg_rcv, hmem_rcv, hsel0, hsel1, hsel2, hsel3,
    hincr, hr0, hr1, hr2, hr3, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  simp only [circuit_norm, byteChannel] at hreg_rcv hmem_rcv
  obtain ⟨_, _, ⟨_, ⟨hmap_oap, _, _⟩, _, _, _, _⟩, ⟨hmap_pv, _, _, _, _, _⟩,
    hmap_ob, _, _, _, _, hmap_sv⟩ := h_input
  have eoap0 : Expression.eval env input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have esv : ∀ i (hi : i < 4), Expression.eval env input_var_store_value[i] = input_store_value[i] :=
    fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
  simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega), epv 1 (by omega),
    epv 2 (by omega), epv 3 (by omega), ← sub_eq_add_neg] at hsel0 hsel1 hsel2 hsel3
  simp only [eob 0 (by omega), ← sub_eq_add_neg] at hincr
  simp only [esv 0 (by omega), esv 1 (by omega), esv 2 (by omega), esv 3 (by omega),
    epv 0 (by omega), epv 1 (by omega), epv 2 (by omega), epv 3 (by omega),
    eob 1 (by omega), eob 2 (by omega), ← sub_eq_add_neg] at hr0 hr1 hr2 hr3
  -- the real-row byte bounds, from the two inline U8Range-pair receives.
  have h_bytes : input_is_real = 1 →
      input_register_low_byte.val < 256 ∧
        ((input_adapter_op_a_memory_prev_value[0] - input_register_low_byte) * (256 : ZMod p)⁻¹).val < 256
        ∧ input_mem_limb_low_byte.val < 256
        ∧ ((input_mem_limb - input_mem_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 := by
    intro h1
    have hneg : -input_is_real = -1 := by rw [h1]
    have Gr := hreg_rcv hneg; have Gm := hmem_rcv hneg
    have hbr := (byteRowSpec_u8range_pair _ _).mp Gr
    have hbm := (byteRowSpec_u8range_pair _ _).mp Gm
    rw [show (2:ℕ)^8 = 256 from by norm_num, ← sub_eq_add_neg, eoap0] at hbr
    rw [show (2:ℕ)^8 = 256 from by norm_num, ← sub_eq_add_neg] at hbm
    exact ⟨hbr.1, hbr.2, hbm.1, hbm.2⟩
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
  refine ⟨⟨h_addr_spec, h_mem h_bin, h_it,
      fun h1 => ⟨(h_bytes h1).1, (h_bytes h1).2.1, (h_bytes h1).2.2.1, (h_bytes h1).2.2.2⟩,
      ⟨hsel0, hsel1, hsel2, hsel3⟩, sub_eq_zero.mp hincr,
      ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩,
    h_bin, Or.inr h_addr_as, Or.inr h_bin, Or.inr ⟨h_bin, h_bin⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩

/-- Prover-side row well-formedness. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    input.register_low_byte.val < 256 ∧ (regHigh input).val < 256 ∧
    input.mem_limb_low_byte.val < 256 ∧ (memHigh input).val < 256 ∧
    ((input.mem_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.mem_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
    input.increment = (input.register_low_byte - input.mem_limb_low_byte) * (1 - input.offset_bit[0])
      + 256 * (input.register_low_byte
          - (input.mem_limb - input.mem_limb_low_byte) * (256 : ZMod p)⁻¹) * input.offset_bit[0] ∧
    (input.store_value[0] = input.memory_access.prev_value[0]
        + input.increment * (1 - input.offset_bit[1]) * (1 - input.offset_bit[2]) ∧
      input.store_value[1] = input.memory_access.prev_value[1]
        + input.increment * input.offset_bit[1] * (1 - input.offset_bit[2]) ∧
      input.store_value[2] = input.memory_access.prev_value[2]
        + input.increment * (1 - input.offset_bit[1]) * input.offset_bit[2] ∧
      input.store_value[3] = input.memory_access.prev_value[3]
        + input.increment * input.offset_bit[1] * input.offset_bit[2]) ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.store_value, input.is_real⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 36⟩ ∧
    (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, hbin, hreg_pa, hreghi_pa, hmem_pa, hmemhi_pa,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, hincr_pa, ⟨hr0, hr1, hr2, hr3⟩, h_cpu, h_mem, h_it, hdec⟩ :=
    h_assumptions
  obtain ⟨_, ⟨_, _, _, hmap_pc⟩, ⟨_, ⟨hmap_oap, _, _⟩, _, _, _, _⟩,
    ⟨hmap_pv, _, _, _, _, _⟩, hmap_ob, _, _, _, _, hmap_sv⟩ := h_input
  have eoap0 : Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  simp only [regHigh, memHigh] at hreghi_pa hmemhi_pa
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have esv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_store_value[i]
      = input_store_value[i] := fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
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
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact hbin
  · exact h_mem
  · exact ⟨hbin, hbin⟩
  · exact h_it
  · intro _
    simp only [byteChannel]; rw [← sub_eq_add_neg, eoap0]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hreg_pa, hreghi_pa⟩
  · intro _
    simp only [byteChannel]; rw [← sub_eq_add_neg]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hmem_pa, hmemhi_pa⟩
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega), ← sub_eq_add_neg]; exact hsel0
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 1 (by omega), ← sub_eq_add_neg]; exact hsel1
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 2 (by omega), ← sub_eq_add_neg]; exact hsel2
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 3 (by omega), ← sub_eq_add_neg]; exact hsel3
  · simp only [eob 0 (by omega), ← sub_eq_add_neg]; exact sub_eq_zero_of_eq hincr_pa
  · simp only [esv 0 (by omega), eob 1 (by omega), eob 2 (by omega), epv 0 (by omega),
      ← sub_eq_add_neg]
    exact sub_eq_zero_of_eq hr0
  · simp only [esv 1 (by omega), eob 1 (by omega), eob 2 (by omega), epv 1 (by omega),
      ← sub_eq_add_neg]
    exact sub_eq_zero_of_eq hr1
  · simp only [esv 2 (by omega), eob 1 (by omega), eob 2 (by omega), epv 2 (by omega),
      ← sub_eq_add_neg]
    exact sub_eq_zero_of_eq hr2
  · simp only [esv 3 (by omega), eob 1 (by omega), eob 2 (by omega), epv 3 (by omega),
      ← sub_eq_add_neg]
    exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `StoreByte` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreByteColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreByteColumns :=
  -- `byteChannel` dropped (W11 Phase 0c): the two off-gate byte-pull `Requirements` (register/mem U8 pairs)
  -- are discharged by the inline `is_real` boolean gate in `main`; the residual buses are the readers'.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel, programChannel,
        AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReaderImmutable.circuit,
        Readers.MemoryAccess.circuit]; grind,
    exposedChannels := fun input _ =>
      expose stateChannel
        [ pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        AddressOperation.circuit, AddressOperation.main,
        AddrAddOperation.circuit, AddrAddOperation.main,
        Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
        Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, byteChannel] }

end SP1Clean.StoreByteChip
