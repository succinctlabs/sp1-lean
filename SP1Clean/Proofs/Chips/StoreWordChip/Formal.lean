import SP1Clean.Native.Chips.StoreWordChip.Defs

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
bit 2 (`4·offset_bit = addr mod 8`). The final conjunct is the **W11 memory-flip** obligation: the merged
`store_value` written to the memory bus is a valid 64-bit word — honest at the single-row level (the memory
bus range-checks every value it receives; the store is the pusher). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, h_sv⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, hr0, hr1, hr2, hr3, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- eval→value bridges for the nested vectors the RMW equations reference.
  have hmap_sv : Vector.map (Expression.eval env) input_var_store_value = input_store_value :=
    h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
  have esv : ∀ i (hi : i < 4), Expression.eval env input_var_store_value[i] = input_store_value[i] :=
    fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap : ∀ i (hi : i < 2), Expression.eval env input_var_adapter_op_a_memory_prev_value[i]
      = input_adapter_op_a_memory_prev_value[i] := fun i hi => by rw [← hmap_oap]; simp only [Vector.getElem_map]
  simp only [esv 0 (by omega), esv 1 (by omega), esv 2 (by omega), esv 3 (by omega),
    epv 0 (by omega), epv 1 (by omega), epv 2 (by omega), epv 3 (by omega),
    eoap 0 (by omega), eoap 1 (by omega)] at hr0 hr1 hr2 hr3
  have h_it := h_itype ⟨h_bin, h_bin⟩
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
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm] at h_addr_spec
  refine ⟨⟨h_addr_spec, h_mem ⟨h_bin, h_sv⟩, h_it,
    ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩, ?_⟩
  exact ⟨Or.inr h_addr_as, Or.inr ⟨h_bin, h_sv⟩, ⟨h_bin, h_bin⟩⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits/alignment + the
`offset_bit` decomposition + `is_real` binary + the reader `Spec`s + the read-modify-write equations. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
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
        input.state.pc, 38⟩ ∧
    (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, hbin, ⟨hr0, hr1, hr2, hr3⟩, h_cpu, h_mem, h_it, hdec,
      h_sv⟩ := h_assumptions
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
  have hmap_sv : Vector.map (Expression.eval env.toEnvironment) input_var_store_value
      = input_store_value := h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have esv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_store_value[i]
      = input_store_value[i] := fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap : ∀ i (hi : i < 2), Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[i]
      = input_adapter_op_a_memory_prev_value[i] := fun i hi => by rw [← hmap_oap]; simp only [Vector.getElem_map]
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
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact ⟨hbin, h_sv⟩
  · exact h_mem
  · exact ⟨hbin, hbin⟩
  · exact h_it
  · simp only [esv 0 (by omega), epv 0 (by omega), eoap 0 (by omega)]
    exact sub_eq_zero_of_eq hr0
  · simp only [esv 1 (by omega), epv 1 (by omega), eoap 1 (by omega)]
    exact sub_eq_zero_of_eq hr1
  · simp only [esv 2 (by omega), epv 2 (by omega), eoap 0 (by omega)]
    exact sub_eq_zero_of_eq hr2
  · simp only [esv 3 (by omega), epv 3 (by omega), eoap 1 (by omega)]
    exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- StoreWord's exact Memory-channel interaction list — the store-family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the immutable I-type register
entries (op_a = rs2 pull + read-back at `clk + 4`, op_b = rs1 pull + read-back at `clk + 3` — both
genuine reads, no `RegisterWrite`).  The RAM push is a **genuine write**: SW pushes the
read-modify-write word `store_value` (rs2's low two limbs merged into the `offset_bit`-selected half
of the aligned doubleword, the other half kept from `memory_access.prev_value`).  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
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
/-- The exact RAM-access pull occupies its declared slot in StoreWord's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-A (rs2) pull occupies its declared slot in StoreWord's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in StoreWord's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `StoreWord` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreWordColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreWordColumns :=
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
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
      -- gate `is_trusted = is_real`, opcode `SW = 38`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 38,
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

/-- The completed StoreWord circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.StoreWordChip
