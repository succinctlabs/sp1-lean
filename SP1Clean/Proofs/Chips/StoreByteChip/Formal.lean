import SP1Clean.Native.Chips.StoreByteChip.Defs

/-! # `SP1Clean.StoreByteChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreByteChip

open Circuit
open Extracted (StoreByteColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; the store targets a non-reserved, in-range address (no alignment). The
final conjunct is the **W11 memory-flip** obligation: the merged `store_value` written to the memory bus is
a valid 64-bit word — honest at the single-row level (the memory bus range-checks every value it receives;
the store is the pusher). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_sv⟩ := h_assumptions
  obtain ⟨h_cpu, h_addr, h_mem, h_itype, hreg_rcv, hmem_rcv, hsel0, hsel1, hsel2, hsel3,
    hincr, hr0, hr1, hr2, hr3, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `MemoryAccess`'s RAM effect slot (`clk_low + 1`) and
  -- `ITypeReaderImmutable`'s two read-back pushes (`clk_low + 4` / `+ 3`). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
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
    epv 2 (by omega), epv 3 (by omega)] at hsel0 hsel1 hsel2 hsel3
  simp only [eob 0 (by omega)] at hincr
  simp only [esv 0 (by omega), esv 1 (by omega), esv 2 (by omega), esv 3 (by omega),
    epv 0 (by omega), epv 1 (by omega), epv 2 (by omega), epv 3 (by omega),
    eob 1 (by omega), eob 2 (by omega)] at hr0 hr1 hr2 hr3
  -- the real-row byte bounds, from the two inline U8Range-pair receives.
  have h_bytes : input_is_real = 1 →
      input_register_low_byte.val < 256 ∧
        ((input_adapter_op_a_memory_prev_value[0] - input_register_low_byte) * (256 : ZMod p)⁻¹).val < 256
        ∧ input_mem_limb_low_byte.val < 256
        ∧ ((input_mem_limb - input_mem_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 := by
    intro h1
    have hneg : - input_is_real = -1 := by rw [h1]
    have Gr := hreg_rcv hneg; have Gm := hmem_rcv hneg
    have hbr := (byteRowSpec_u8range_pair _ _).mp Gr
    have hbm := (byteRowSpec_u8range_pair _ _).mp Gm
    rw [show (2:ℕ)^8 = 256 from by norm_num, eoap0] at hbr
    rw [show (2:ℕ)^8 = 256 from by norm_num] at hbm
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
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm, eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)] at h_addr_spec
  have h_it := h_itype ⟨h_bin, h_bin, h_clk⟩
  refine ⟨⟨h_addr_spec,
      h_mem ⟨h_bin, h_sv, h_clk⟩, h_it,
      fun h1 => ⟨(h_bytes h1).1, (h_bytes h1).2.1, (h_bytes h1).2.2.1, (h_bytes h1).2.2.2⟩,
      ⟨hsel0, hsel1, hsel2, hsel3⟩, sub_eq_zero.mp hincr,
      ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩,
    Or.inr h_addr_as, Or.inr ⟨h_bin, h_sv, h_clk⟩,
    ⟨h_bin, h_bin, h_clk⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩

/-- Prover-side row well-formedness. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
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
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, hbin, hreg_pa, hreghi_pa, hmem_pa, hmemhi_pa,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, hincr_pa, ⟨hr0, hr1, hr2, hr3⟩, h_cpu, h_mem, h_it, hdec, h_sv⟩ :=
    h_assumptions
  -- G1: the *push*-side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
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
  · exact ⟨hbin, h_sv, h_clk⟩
  · exact h_mem
  · exact ⟨hbin, hbin, h_clk⟩
  · exact h_it
  · intro _
    simp only [byteChannel]; rw [eoap0]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hreg_pa, hreghi_pa⟩
  · intro _
    simp only [byteChannel]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hmem_pa, hmemhi_pa⟩
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega)]; exact hsel0
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 1 (by omega)]; exact hsel1
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 2 (by omega)]; exact hsel2
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 3 (by omega)]; exact hsel3
  · simp only [eob 0 (by omega)]; exact sub_eq_zero_of_eq hincr_pa
  · simp only [esv 0 (by omega), eob 1 (by omega), eob 2 (by omega), epv 0 (by omega)]
    exact sub_eq_zero_of_eq hr0
  · simp only [esv 1 (by omega), eob 1 (by omega), eob 2 (by omega), epv 1 (by omega)]
    exact sub_eq_zero_of_eq hr1
  · simp only [esv 2 (by omega), eob 1 (by omega), eob 2 (by omega), epv 2 (by omega)]
    exact sub_eq_zero_of_eq hr2
  · simp only [esv 3 (by omega), eob 1 (by omega), eob 2 (by omega), epv 3 (by omega)]
    exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- StoreByte's exact Memory-channel interaction list — the store-family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the immutable I-type register
entries (op_a = rs2 pull + read-back at `clk + 4`, op_b = rs1 pull + read-back at `clk + 3` — both
genuine reads, no `RegisterWrite`).  The RAM push is a **genuine write**: SB pushes the
read-modify-write word `store_value` (the signed byte delta `increment` applied to the
`offset_bit[1..2]`-selected limb of `memory_access.prev_value`, the other limbs kept).  Keeping this
list beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.store_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact RAM-access pull occupies its declared slot in StoreByte's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-A (rs2) pull occupies its declared slot in StoreByte's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in StoreByte's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

set_option maxHeartbeats 2000000 in
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
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReaderImmutable`,
      -- gate `is_trusted = is_real`, opcode `SB = 36`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 36,
             input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
             input.adapter.op_a_0, 0, 1⟩ ],
    exposedChannels_eq := by
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      all_goals
        simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          AddressOperation.circuit, AddressOperation.main,
          AddrAddOperation.circuit, AddrAddOperation.main,
          Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
          Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
      · simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          Channels.byteChannel_eq_programChannel_false,
          Channels.stateChannel_eq_programChannel_false,
          Channels.memoryChannel_eq_programChannel_false,
          decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append] }

/-- The completed StoreByte circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.StoreByteChip
