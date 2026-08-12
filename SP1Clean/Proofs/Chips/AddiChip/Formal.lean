import SP1Clean.Native.Chips.AddiChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit

/-! # `SP1Clean.AddiChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.AddiChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddiChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨h_cpu, h_add, h_adapter, _h_regwrite, _h_op_a_0, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee — `ITypeReader`'s op_b read-back push (`clk_low + 3`)
  -- and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification, so this
  -- line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- **Option B cycle-break.** The immediate `op_c`'s `isU64` is assumed (`h_assumptions`); the register
  -- `op_b`'s `isU64` is *derived* from the `ITypeReader` reader sub-`Spec` (its 6th conjunct is the memory-
  -- pull-derived tuple `is_real=1 → isU64 op_a/op_b prev ∧ their two `prev_low` clock bounds`). Feeding
  -- both into `AddOperation` gives `isU64 value` (.1) + the gated add identity (.2); the result `isU64`
  -- discharges the `RegisterWrite` op_a write push.
  have h_rspec := h_adapter ⟨h_bin, h_bin, h_clk⟩
  have h_pair := h_rspec.2.2.2.2.2
  have h_addspec := h_add ⟨fun hr => ⟨(h_pair hr).2.1, h_assumptions⟩, h_bin⟩
  refine ⟨⟨h_rspec, h_bin, fun hr => (h_addspec hr).2⟩, ?_⟩
  and_intros <;>
    first
      | exact h_bin
      | exact Or.inl rfl
      | exact Or.inr ⟨h_bin, h_bin, h_clk⟩
      | exact ⟨fun hr => ⟨(h_pair hr).2.1, h_assumptions⟩, h_bin⟩
      | exact Or.inr ⟨fun hr => ⟨(h_pair hr).2.1, h_assumptions⟩, h_bin⟩
      | exact Or.inr ⟨h_bin, fun hr => (h_addspec hr).1,
          h_clk.at_four⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hdec, hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, hoc⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq := (vec4_eval env.toEnvironment input_var_adapter_op_b_memory_prev_value).trans hob
  have hceq := (vec4_eval env.toEnvironment input_var_adapter_op_c_imm).trans hoc
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_imm := by
    rw [← AddOperation.populateIR_eval env _ _ _ _ hbeq hceq ha hb]
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    -- `h_env` now bundles the chip's `value` witness-gen equations with the GFC `ITypeReader`
    -- subcircuit's completeness obligation (SC Phase 2pre) — the witness equations are `h_env.1`.
    -- `exact` crosses the struct-projection defeq gap between the destructured names and the
    -- `Inputs.op_b_val`/`op_c_val` spellings inside the folded `populateIR` obligation.
    exact h_env.2.1 ⟨i, hi⟩
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, (fun _ => Or.inl hop_a_0), hrac_a, hrac_b, hdec,
        fun hr => ⟨ha_prev hr, ha, (hprevclk hr).1, (hprevclk hr).2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩, hop_a_0, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed result `value = populate op_b op_c_imm`,
    -- whose `isU64` is `spec_populate.1`.
    intro hr; rw [hval]; exact (AddOperation.spec_populate ha hb input_is_real hr).1
  rcases hbin with h | h <;> rw [h] <;> simp

/-- Addi's exact Memory-channel interaction list (I-type: no op_c register read — the second operand
is the immediate).  Keeping this list beside `circuit` makes Clean's exposure interface the single
structural source consumed by both faithfulness and semantic grounding. -/
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
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Addi's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `Addi` chip row as a `GeneralFormalCircuit`: single-variant `is_real`-gated RV64 `add`
semantic contract over a register source + immediate, composing the witnessed `AddOperation` gadget;
output is the native `Columns` row. Soundness/completeness are fully proven. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- as chip-owned interactions (the Clean `VmTables` re-base that motivated the shape was investigated
    -- and deferred — roadmap W11); descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReader`, gate
      -- `is_trusted = is_real`, opcode `ADDI = 1`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 1,
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
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ITypeReader.circuit, Readers.ITypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ITypeReader.circuit, Readers.ITypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, witnessIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          Soundness.iTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          SP1Clean.AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil,
          or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          List.append_nil, Soundness.iTypeProgramMessage]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append] }

@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 4 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 4 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed Addi circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.AddiChip
