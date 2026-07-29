import SP1Clean.Native.Chips.AluX0Chip.Defs
import Clean.Air.Circuit

/-! # `SP1Clean.AluX0Chip` — contract: `Assumptions` / soundness / completeness / `circuit`

Verifier-side `Assumptions` are trivial (`True`) — soundness derives `is_real` binary and the
reader contract purely from the in-circuit gates. -/

namespace SP1Clean.AluX0Chip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The byte-table meaning of AluX0's dynamic-opcode lookup.  This is an equivalence, not merely
the completeness direction: soundness uses the same trusted Byte table row to recover
`opcode.val < 29`. -/
lemma byteRowSpec_ltu_29_iff {op : ZMod p} :
    ByteRowSpec (⟨(4 : ZMod p), 1, op, 29⟩ : ByteRow (ZMod p)) ↔ op.val < 29 := by
  have h29 : (29 : ZMod p).val = 29 :=
    ZMod.val_natCast_of_lt (show (29 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
  constructor
  · rintro ⟨byteOpcode, opcodeEq, constrained⟩
    have indexEq : byteOpcode.idx = 4 :=
      cast_le6_inj (by cases byteOpcode <;> decide) (by norm_num) (by
        rw [opcodeEq]
        norm_cast)
    cases byteOpcode <;> simp only [ByteOpcode.idx] at indexEq
    all_goals first | omega | skip
    simp only [ByteOpcode.constrain_LTU, ZMod.val_one, h29] at constrained
    exact constrained.2.2.mp trivial
  · intro h
    refine ⟨ByteOpcode.LTU, by norm_cast, ?_⟩
    simp only [ByteOpcode.constrain_LTU, ZMod.val_one, h29]
    exact ⟨⟨by norm_num, by omega, by norm_num⟩, Or.inr trivial, fun _ => h, fun _ => trivial⟩

/-- Completeness-facing projection of `byteRowSpec_ltu_29_iff`. -/
lemma byteRowSpec_ltu_29 {op : ZMod p} (h : op.val < 29) :
    ByteRowSpec (⟨(4 : ZMod p), 1, op, 29⟩ : ByteRow (ZMod p)) :=
  byteRowSpec_ltu_29_iff.mpr h

/-- Verifier-side `Assumptions` — trivial. `AluX0` discards its result, so there are no operand
well-formedness obligations; `is_real` binary and the reader contract are derived in soundness from the
in-circuit gates. -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

-- Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000.
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_ltu, h_reader, h_gate, h_oa1, h_oa2⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  have h_op_lt : input_is_real = 1 → input_opcode.val < 29 := by
    intro real
    apply byteRowSpec_ltu_29_iff.mp
    apply h_ltu
    rw [real]
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `ALUTypeReaderImmutable`'s three read-back pushes
  -- (op_a at `clk_low + 4`, op_b at `+ 3`, op_c at `+ 2`; there is no `RegisterWrite` here, the
  -- result is discarded). The offset is left to unification, so this line never names the
  -- destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  simp only [isReal, clkLow, opcodeVal]
  -- The per-emitter channel-requirement tail: the off-gate-vacuous byte pull (`is_real ∈ {0,1}`
  -- rules out the `¬is_real = 0` ∧ `¬-is_real = -1` antecedents), and the immutable reader.
  exact ⟨⟨h_reader ⟨h_bin, h_bin, h_clk⟩,
      h_bin, h_oa1, h_oa2, h_op_lt⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    Or.inr ⟨h_bin, h_bin, h_clk⟩⟩

/-- Honest prover-side row well-formedness: `is_real` binary, the two `op_a_0` forcing gates, the
CPUState clock bounds + the immutable-ALU-reader contract, and the dynamic opcode in ALU range
(`opcode < 29`, the LTU byte pull's witness — the honest prover only emits real ALU opcodes). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  (isReal input = 0 ∨ isReal input = 1) ∧
  isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
  (isReal input - 1) * input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
  Readers.ALUTypeReaderImmutable.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, opcodeVal input⟩ ∧
  (isReal input = 1 → input.opcode.val < 29)

-- Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000.
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [isReal, clkLow, opcodeVal] at h_assumptions
  obtain ⟨h_bin, h_oa1, h_oa2, h_cpu, h_reader, h_op_lt⟩ := h_assumptions
  -- G1: the *push* side clock bounds (op_a `+ 4` / op_b `+ 3` / op_c `+ 2`), from the prover-supplied
  -- CPUState clock byte bounds. The *pull* side bounds are already carried by `h_reader`, since
  -- `ProverAssumptions` names `Readers.ALUTypeReaderImmutable.Spec` wholesale.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  refine ⟨⟨h_bin, h_cpu⟩, ?_,
    ⟨⟨h_bin, h_bin, h_clk⟩, h_reader⟩,
    ?_, h_oa1, h_oa2⟩
  · -- the LTU `opcode < 29` byte pull (fires on real rows).
    intro hneg
    simp only [byteChannel]
    exact byteRowSpec_ltu_29 (h_op_lt (neg_inj.mp hneg))
  · -- `is_real` binary gate.
    rcases h_bin with h | h <;> rw [h] <;> simp

/-- Exact State-channel pair emitted by the composed CPU-state reader. -/
def exposedStateInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

/-- Exact Byte-channel list: two CPU clock checks, the chip-owned opcode check, and the six
register-timestamp checks emitted by the immutable ALU adapter. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let opCGate := input.is_real - input.adapter.imm_c
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf input.is_real ⟨4, 1, input.opcode, 29⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 4 - input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 3 - input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf opCGate
      ⟨6, input.adapter.op_c_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf opCGate
      ⟨3, 0,
       (clkLow + 2 - input.adapter.op_c_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩ ]

/-- AluX0's exact Memory-channel interaction list, descended verbatim from the composed
`ALUTypeReaderImmutable`: op_a read-prior pull + read-back push at `clk + 4` (rd = x0 is a **read**
here — the result is discarded), op_b read-prior pull + read-back push at `clk + 3`, and the
(`is_real - imm_c`)-gated op_c pull/push pair at `clk + 2`, addressed by the low limb `op_c[0]` (an
immediate does no register read).  No `RegisterWrite` push and no witness cells.  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (_offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
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
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ]

/-- Exact Program fetch emitted by the immutable ALU adapter. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], input.opcode,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
       input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact op_a (x0 rd read-prior) pull occupies its declared slot in AluX0's exposed Memory
list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in AluX0's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in AluX0's exposed
Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `AluX0` chip row as a `GeneralFormalCircuit`: validates the ALU-into-`x0` program/register accesses
and advances state (the result discarded); output is the native `Columns` row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate LTU byte-pull `Requirements` is discharged by the
  -- inline `is_real` boolean gate in `main`; the residual buses (state/memory/program) are the readers'.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel, programChannel,
        Readers.CPUState.circuit, Readers.ALUTypeReaderImmutable.circuit]; grind,
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    -- The chip's own LTU byte-pull and the reader's pulls are on byteChannel/programChannel/memoryChannel,
    -- filtered out by `interactionsWith stateChannel`.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ALUTypeReaderImmutable`,
      -- gate `is_trusted = is_real`, opcode = the committed input opcode), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel (exposedProgramInteractions input),
    exposedChannels_eq := by
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, exposedStateInteractions, exposedProgramInteractions,
        List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      all_goals
        simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
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

@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 0 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq, Nat.add_zero]

/-- The completed AluX0 circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw, (exposedStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed AluX0 circuit emits exactly the nine Byte interactions above.
Runs at the plain default: the former 2000000 ceiling was ~50x over; measured floor <= 40000. -/
theorem interactionsWith_byte_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input).map ChannelInteraction.toRaw := by
  simp [main, exposedByteInteractions,
    Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]

/-- The completed AluX0 circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed AluX0 circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw, (exposedProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.AluX0Chip
