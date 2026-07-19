import SP1Clean.Native.Chips.StoreDoubleChip.Defs

/-! # `SP1Clean.StoreDoubleChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreDoubleChip

open Circuit
open Extracted (StoreDoubleColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the store targets a **valid, aligned, non-reserved** address: the
sum fits in 48 bits, is non-reserved (`≥ 2^16`), and is 8-byte aligned (`addr mod 8 = 0`, since SD's
offset bits are `0`). The address conditions are the "prover commits a valid SD address"
preconditions that `AddressOperation` needs (its inverse gate + offset range check). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align⟩ := h_assumptions
  obtain ⟨h_cpu, h_addr, h_mem, h_itype, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `MemoryAccess`'s RAM effect slot (`clk_low + 1`) and
  -- `ITypeReaderImmutable`'s two read-back pushes (`clk_low + 4` / `+ 3`). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk : ∀ (delta : ZMod p) (k : ℕ), delta.val = k → k ≤ 4 → input_is_real = 1 →
      (input_state_clk_0_16 + input_state_clk_16_24 * 65536 + delta).val < 2 ^ 24 :=
    fun _ k hk hk4 hr => Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ k hk hk4
      (h_cpu h_bin hr).1 (h_cpu h_bin hr).2
  -- the RAM effect slot's offset is the literal `1`, whose `val` needs `Fact (1 < p)` (kept local so the
  -- instance does not leak into the surrounding heavy `simp` sets).
  have hv1 : (1 : ZMod p).val = 1 := by
    haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact ZMod.val_one p
  -- the `AddressOperation` Assumptions: operand `isU64`s + fits, the offset bits boolean (literal `0`),
  -- and the address-validity (non-reserved + 8-aligned, so the inverse gate / offset range check hold).
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm] at h_addr_spec
  have h_it := h_itype ⟨h_bin, h_bin, fun hr =>
    ⟨h_clk 4 4 (by simp) (by norm_num) hr, h_clk 3 3 (by simp) (by norm_num) hr⟩⟩
  -- (W11 memory flip) the pushed `new_value` for SD is the rs2 read (`op_a_memory.prev_value`), whose
  -- `isU64` is exposed by the immutable I-type adapter's `Spec` on a real row — no new assumption needed.
  have h_new : input_is_real = 1 → Word.isU64 input_adapter_op_a_memory_prev_value :=
    fun hr => (h_it.2.2.2.2.2 hr).1
  -- The remaining per-subcircuit channel requirements are structural obligations.
  exact ⟨⟨h_addr_spec,
      h_mem ⟨h_bin, h_new, fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩, h_it, h_bin⟩,
    Or.inr h_addr_as,
    Or.inr ⟨h_bin, h_new, fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩,
    ⟨h_bin, h_bin, fun hr =>
      ⟨h_clk 4 4 (by simp) (by norm_num) hr, h_clk 3 3 (by simp) (by norm_num) hr⟩⟩⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits bound + the reader
clock/timestamp `Spec`s + `is_real` binary. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0 ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.adapter.op_a_memory.prev_value, input.is_real⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 39⟩ ∧
    (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, hbin, h_cpu, h_mem, h_it, hdec⟩ := h_assumptions
  -- G1: the *push*-side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk : ∀ (delta : ZMod p) (k : ℕ), delta.val = k → k ≤ 4 → input_is_real = 1 →
      (input_state_clk_0_16 + input_state_clk_16_24 * 65536 + delta).val < 2 ^ 24 :=
    fun _ k hk hk4 hr => Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ k hk hk4
      (h_cpu hr).1 (h_cpu hr).2
  have hv1 : (1 : ZMod p).val = 1 := by
    haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact ZMod.val_one p
  -- eval→value bridge for the nested `pc` vector the CPUState `Spec` references.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  refine ⟨⟨hbin, ?_⟩, h_addr_as,
    ⟨⟨hbin, fun hr => (h_it.2.2.2.2.2 hr).1,
        fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩, h_mem⟩,
    ⟨⟨hbin, hbin, fun hr =>
        ⟨h_clk 4 4 (by simp) (by norm_num) hr, h_clk 3 3 (by simp) (by norm_num) hr⟩⟩, h_it⟩, ?_⟩
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- StoreDouble's exact Memory-channel interaction list — the store-family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the immutable I-type register
entries (op_a = rs2 pull + read-back at `clk + 4`, op_b = rs1 pull + read-back at `clk + 3` — both
genuine reads, no `RegisterWrite`).  The RAM push is a **genuine write**: SD writes the rs2 word
`adapter.op_a_memory.prev_value` verbatim (no `store_value` column, no read-modify-write).  Keeping
this list beside `circuit` makes Clean's exposure interface the single structural source consumed by
both faithfulness and semantic grounding. -/
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
       input.adapter.op_a_memory.prev_value⟩,
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
/-- The exact RAM-access pull occupies its declared slot in StoreDouble's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-A (rs2) pull occupies its declared slot in StoreDouble's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in StoreDouble's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `StoreDouble` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreDoubleColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreDoubleColumns :=
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
      -- gate `is_trusted = is_real`, opcode `SD = 39`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 39,
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

/-- The completed StoreDouble circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.StoreDoubleChip
