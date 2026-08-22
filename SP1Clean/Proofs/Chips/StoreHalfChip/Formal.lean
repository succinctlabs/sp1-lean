import SP1Clean.Native.Chips.StoreHalfChip.Defs
import Clean.Air.Circuit

/-! # `SP1Clean.StoreHalfChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreHalfChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The register/immediate operands are genuine 64-bit values, and the committed RAM write is a
valid 64-bit word on a real row. Address validity, non-reservation, two-byte alignment, and offset
decomposition follow from `AddressOperation` with a literal zero low-offset bit. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

-- Both proofs read `h_assumptions` / `h_holds` through `.1`/`.2` projections instead of a wide
-- `obtain`: an `And.casesOn` motive re-abstracts the (very large) goal once per component, which is
-- Clean's `doc/performance-problems.md` pattern 7. Both now clear Lean's plain default, so neither
-- carries a scoped elaboration budget any more (they were stamped at 1.5M each).
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  have ha := h_assumptions.1
  have hb := h_assumptions.2.1
  have h_sv := h_assumptions.2.2
  have h_cpu := h_holds.1
  have hh1 := h_holds.2
  have h_addr := hh1.1
  have hh2 := hh1.2
  have h_mem := hh2.1
  have hh3 := hh2.2
  have h_itype := hh3.1
  have hh4 := hh3.2
  have hr0 := hh4.1
  have hh5 := hh4.2
  have hr1 := hh5.1
  have hh6 := hh5.2
  have hr2 := hh6.1
  have hh7 := hh6.2
  have hr3 := hh7.1
  have h_gate := hh7.2
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `MemoryAccess`'s RAM effect slot (`clk_low + 1`) and
  -- `ITypeReaderImmutable`'s two read-back pushes (`clk_low + 4` / `+ 3`). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- eval→value bridges for the nested vectors the RMW equations / subcircuit input reference.
  have hmap_ob : Vector.map (Expression.eval env) input_var_offset_bit = input_offset_bit :=
    h_input.2.2.2.2.1
  have hmap_sv : Vector.map (Expression.eval env) input_var_store_value = input_store_value :=
    h_input.2.2.2.2.2
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1.1
  have hmap_oap : Vector.map (Expression.eval env) input_var_adapter_op_a_memory_prev_value
      = input_adapter_op_a_memory_prev_value := h_input.2.2.1.2.1.1
  have eob : ∀ i (hi : i < 2), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have esv : ∀ i (hi : i < 4), Expression.eval env input_var_store_value[i] = input_store_value[i] :=
    fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap0 : Expression.eval env input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  simp only [esv, epv, eoap0, eob] at hr0 hr1 hr2 hr3
  have h_it := h_itype ⟨h_bin, h_bin, h_clk⟩
  have h_addr_as : AddressOperation.SoundnessAssumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1],
          input_is_real⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, h_bin⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm, eob] at h_addr_spec
  refine ⟨⟨h_addr_spec,
    h_mem ⟨h_bin, h_sv, h_clk⟩, h_it,
    ⟨sub_eq_zero.mp hr0, sub_eq_zero.mp hr1, sub_eq_zero.mp hr2, sub_eq_zero.mp hr3⟩, h_bin⟩, ?_⟩
  exact ⟨Or.inr h_addr_as, Or.inr ⟨h_bin, h_sv, h_clk⟩,
    ⟨h_bin, h_bin, h_clk⟩⟩

/-- Prover-side row well-formedness: operand `isU64`s + address-fits/alignment + the `offset_bit`
decomposition + offset binaries + `is_real` binary + the reader `Spec`s + the read-modify-write equations. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    (input.is_real = 1 →
      2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48) ∧
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
        input.state.pc, 37⟩ ∧
    (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
    (input.is_real = 1 → Word.isU64 input.store_value)

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  have ha := h_assumptions.1
  have hp1 := h_assumptions.2
  have hb := hp1.1
  have hp2 := hp1.2
  have hfit := hp2.1
  have hp3 := hp2.2
  have h_ge := hp3.1
  have hp4 := hp3.2
  have h_align := hp4.1
  have hp5 := hp4.2
  have hob0 := hp5.1
  have hp6 := hp5.2
  have hob1 := hp6.1
  have hp7 := hp6.2
  have h_off := hp7.1
  have hp8 := hp7.2
  have hbin := hp8.1
  have hp9 := hp8.2
  have hr0 := hp9.1.1
  have hr1 := hp9.1.2.1
  have hr2 := hp9.1.2.2.1
  have hr3 := hp9.1.2.2.2
  have hp10 := hp9.2
  have h_cpu := hp10.1
  have hp11 := hp10.2
  have h_mem := hp11.1
  have hp12 := hp11.2
  have h_it := hp12.1
  have hp13 := hp12.2
  have hdec := hp13.1
  have h_sv := hp13.2
  -- G1: the *push*-side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
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
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 2), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have esv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_store_value[i]
      = input_store_value[i] := fun i hi => by rw [← hmap_sv]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have eoap0 : Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0]
      = input_adapter_op_a_memory_prev_value[0] := by rw [← hmap_oap]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1],
          input_is_real⟩ : AddressOperation.Inputs (ZMod p)) := by
    simp only [eob]
    exact ⟨ha, hb, hbin, hfit, Or.inl rfl, hob0, hob1, h_ge, by simpa using h_off⟩
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc]; exact h_cpu
  · exact ⟨hbin, h_sv, h_clk⟩
  · exact h_mem
  · exact ⟨hbin, hbin, h_clk⟩
  · exact h_it
  · simp only [esv, epv, eoap0, eob]; exact sub_eq_zero_of_eq hr0
  · simp only [esv, epv, eoap0, eob]; exact sub_eq_zero_of_eq hr1
  · simp only [esv, epv, eoap0, eob]; exact sub_eq_zero_of_eq hr2
  · simp only [esv, epv, eoap0, eob]; exact sub_eq_zero_of_eq hr3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- StoreHalf's exact Memory-channel interaction list — the store-family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the immutable I-type register
entries (op_a = rs2 pull + read-back at `clk + 4`, op_b = rs1 pull + read-back at `clk + 3` — both
genuine reads, no `RegisterWrite`).  The RAM push is a **genuine write**: SH pushes the
read-modify-write word `store_value` (rs2's low limb merged into the `offset_bit[0..1]`-selected u16
limb, the other limbs kept from `memory_access.prev_value`).  Keeping this list beside `circuit`
makes Clean's exposure interface the single structural source consumed by both faithfulness and
semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
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
/-- The exact RAM-access pull occupies its declared slot in StoreHalf's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-A (rs2) pull occupies its declared slot in StoreHalf's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in StoreHalf's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `StoreHalf` chip row as a `GeneralFormalCircuit`; output is the extracted `Columns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
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
      -- gate `is_trusted = is_real`, opcode `SH = 37`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 37,
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

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 4 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 4 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed StoreHalf circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.StoreHalfChip
