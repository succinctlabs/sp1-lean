import SP1Clean.Native.Chips.SubChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.SubChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.SubChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.SubChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  -- `circuit_proof_start` unfolds the inlined R-type Spec, re-normalizes
  -- `wv*` result-word fields, and drops the leading CPUState `True` fragment.
  circuit_proof_start
  obtain ⟨h_cpu, h_sub, h_adapter, _h_regwrite, _h_op_a_0, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `RTypeReader`'s two read-back pushes (`clk_low + 3` /
  -- `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification,
  -- so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Apply the
  -- `RTypeReader` sub-soundness `h_adapter` (its `Assumptions` is `⟨is_real binary, is_trusted binary⟩`,
  -- both `h_bin` since `is_trusted = is_real`, plus the two push clock bounds) to get its `Spec`; its 7th
  -- conjunct is the **memory-pull-derived** operand `isU64` trio `(is_real = 1 → isU64 op_a/op_b/op_c prev)`.
  -- Operand `isU64` thus flows reader → here, not from a chip assumption — no cycle.
  have h_rspec := h_adapter ⟨h_bin, h_bin, h_clk⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  -- Feed operand `isU64` (gated on `is_real`) into `SubOperation`'s sub-soundness → `isU64 value` (.1) + the
  -- gated sub identity (.2). The witnessed result `value`'s `isU64` then discharges the new `RegisterWrite`
  -- op_a write push's `Assumptions`.
  have h_subspec := h_sub ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2.1⟩, h_bin⟩
  refine ⟨⟨h_rspec, h_bin, fun hr => (h_subspec hr).2⟩, ?_⟩
  and_intros <;>
    first
      | exact h_bin
      | exact Or.inl rfl
      | exact Or.inr ⟨h_bin, h_bin, h_clk⟩
      | exact ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2.1⟩, h_bin⟩
      | exact Or.inr ⟨h_bin, fun hr => (h_subspec hr).1,
          h_clk.at_four⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ :=
    h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have mapEq : ∀ (vv : Word (Expression (ZMod p))) (v : Word (ZMod p)),
      Vector.map (Expression.eval env.toEnvironment) vv = v →
      (#v[Expression.eval env.toEnvironment vv[0], Expression.eval env.toEnvironment vv[1],
        Expression.eval env.toEnvironment vv[2], Expression.eval env.toEnvironment vv[3]] : Word (ZMod p)) = v :=
    fun vv v h => by rw [← h]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hbeq := mapEq input_var_adapter_op_b_memory_prev_value _ hob
  have hceq := mapEq input_var_adapter_op_c_memory_prev_value _ hoc
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = SubOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    -- `h_env` now bundles the chip's `value` witness-gen equations with the GFC `RTypeReader`
    -- subcircuit's completeness obligation — the witness equations are `h_env.1`.
    rw [h_env.2.1 ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    simp only [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
        fun hr => ⟨ha_prev hr, ha, hb, (hprevclk hr).1, (hprevclk hr).2.1, (hprevclk hr).2.2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩, hop_a_0, ?_⟩
  · rw [hval]; exact SubOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed result `value = populate op_b op_c`,
    -- whose `isU64` is `spec_populate.1`.
    intro hr; rw [hval]; exact (SubOperation.spec_populate ha hb input_is_real hr).1
  rcases hbin with h | h <;> rw [h] <;> simp

/-- Sub's exact Memory-channel interaction list.  Keeping this list beside `circuit` makes Clean's
exposure interface the single structural source consumed by both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Sub's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-C pull occupies its declared slot in Sub's exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The Sub chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed
gadget + the two readers; output is the native `Columns` row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8) so the
    -- chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone State pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `RTypeReader`, gate
      -- `is_trusted = is_real`, opcode `SUB = 2`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 2,
             input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
             #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩ ],
    exposedChannels_eq := by
      intro input offset
      have h_byte : (byteChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
        intro h
        have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
        simp only [Channel.toRaw_name, byteChannel, stateChannel] at hn
        exact (by decide : ("SP1Byte" : String) ≠ "SP1State") hn
      have h_program : (programChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
        intro h
        have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
        simp only [Channel.toRaw_name, programChannel, stateChannel] at hn
        exact (by decide : ("SP1Program" : String) ≠ "SP1State") hn
      have h_memory : (memoryChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
        intro h
        have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
        simp only [Channel.toRaw_name, memoryChannel, stateChannel] at hn
        exact (by decide : ("SP1Memory" : String) ≠ "SP1State") hn
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.RTypeReader.circuit, Readers.RTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.RTypeReader.circuit, Readers.RTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.SubOperation.circuit, SP1Clean.SubOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          Soundness.rTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          SubOperation.circuit, SubOperation.elaborated,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil,
          or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          Soundness.rTypeProgramMessage]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append] }

/-- The completed Sub circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.SubChip
