import SP1Clean.Native.Chips.AddwChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.AddwChip` — contract: `Assumptions` / soundness / completeness / `circuit`

`Spec` (ALUTypeReader.Spec ∧ binary ∧ gated `RV64.addw`) + `Assumptions`/`ProverAssumptions` in
`FormalModel/Contracts/`. -/

namespace SP1Clean.AddwChip

open Circuit
open Extracted (AddwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddwChip` namespace). -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- W-instruction soundness (Option B memory flip). Landmines: use `.2.1`/`.2.2.1`/… projections on
`h_holds` (never `obtain`/`rcases`), keep `Spec` opaque so `RV64.addw` stays out of `circuit_norm`; arith
goes via `rv64_addw_eq` by hand. `op_b`'s `isU64` is **derived** from the `ALUTypeReader` reader `Spec`'s
`is_real`-gated memory read-prior pull (usable inside the `is_real = 1` branch where the W result is needed);
`op_c`'s `isU64` is the chip `Assumptions` (`AddwOperation` has an *ungated* operand `isU64` precondition, and
`op_c`'s reader guarantee is gated by `is_real - imm_c`, with `imm_c = 0` a decode-only fact). The witnessed
result's `isU64` discharges the new `RegisterWrite` op_a write push. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h_addw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  have h_bin := bool_of_mul_pred h_holds.2.2.2.2
  have hb := h_assumptions
  -- The `ALUTypeReader` sub-`Spec` (its `Assumptions` = ⟨is_real binary, is_trusted binary⟩, both `h_bin`
  -- since `is_trusted = is_real`); its op_a/op_b `isU64` conjunct (`is_real = 1 → isU64 op_a ∧ isU64 op_b`).
  have h_rspec := h_adapter ⟨h_bin, h_bin⟩
  have h_ob := h_rspec.2.2.2.2.2.2.2.2.2.1
  -- Build the (ungated) `AddwOperation` Assumptions on the `is_real = 1` branch: op_b from the reader pull,
  -- op_c from the chip Assumption. `h_addspec hr` is the operation's `Spec` on a real row.
  have h_addspec := fun (hr : input_is_real = 1) => h_addw ⟨(h_ob hr).2, hb, h_bin⟩
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · simpa only [Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.SpecD, resultWord,
      Vector.getElem_map, Vector.getElem_mapRange, circuit_norm] using h_rspec
  · refine Eq.trans ?_ (rv64_addw_eq _ _).symm
    simpa only [resultWord, AddwOperation.resultWord, Vector.getElem_map] using
      ((h_addspec hr).2 hr).2
  · and_intros <;>
      first
        | exact h_bin
        | exact ⟨h_bin, h_bin⟩
        | exact Or.inl rfl
        | exact Or.inr ⟨h_bin, h_bin⟩
        | exact Or.inr ⟨h_bin, fun hr => by
            have hisu := ((h_addspec hr).2 hr).1
            simp only [AddwOperation.resultWord, Vector.getElem_map, Vector.getElem_mapRange,
              circuit_norm] at hisu ⊢
            exact hisu⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, himm, h_cpu, hrac_a, hrac_b, hrac_c, hdec⟩ :=
    h_assumptions
  -- `op_c_memory` is grouped since `imm_c` is the final field of the ALU adapter block.
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, ⟨hoc, -, -⟩, -⟩ := h_input
  -- `h_env` now bundles the chip's `value`/`msb` witness-gen equations with the GFC `ALUTypeReader`
  -- subcircuit's completeness obligation (SC Phase 2pre) — discard the trailing reader obligation.
  obtain ⟨-, h_env_val, h_env_msb, -⟩ := h_env
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have mapEq : ∀ (vv : Word (Expression (ZMod p))) (v : Word (ZMod p)),
      Vector.map (Expression.eval env.toEnvironment) vv = v →
      (#v[Expression.eval env.toEnvironment vv[0], Expression.eval env.toEnvironment vv[1],
        Expression.eval env.toEnvironment vv[2], Expression.eval env.toEnvironment vv[3]] : Word (ZMod p)) = v :=
    fun vv v h => by rw [← h]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hbeq := mapEq input_var_adapter_op_b_memory_prev_value _ hob
  have hceq := mapEq input_var_adapter_op_c_memory_prev_value _ hoc
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i => var { index := i₀ + i }) : Vector (ZMod p) 2)
      = AddwOperation.addwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    simp only [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2) = AddwOperation.addwMsbWitness input_adapter_op_b_memory_prev_value
      input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c, hdec, fun hr => ⟨ha_prev hr, ha⟩, fun _ => hb⟩⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · rw [hval, hmsbeq]; exact AddwOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (the op_a write push): the witnessed result word's `isU64` from
    -- `spec_populate.2 hr).1`, bridged from the operation's `populate resultWord` to the chip's explicit
    -- `#v[value[0], value[1], msb·65535, msb·65535]` (in `env.get` form) via `hval`/`hmsbeq`.
    intro hr
    have hisu := ((AddwOperation.spec_populate ha hb input_is_real).2 hr).1
    have e0 := congrArg (fun v => v[0]) hval
    have e1 := congrArg (fun v => v[1]) hval
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm] at e0 e1
    simp only [AddwOperation.resultWord, AddwOperation.populate] at hisu
    simp only [e0, e1, hmsbeq]
    exact hisu
  rcases hbin with h | h <;> rw [h] <;> simp

/-- Addw's exact Memory-channel interaction list — the first ALU-type (immediate-capable) instance.
Unlike the R-type six-pack, the op_c register pull/read-back pair is gated by **`is_real - imm_c`**
(an immediate does no register read) and addressed by the low limb `op_c[0]` (the ALU adapter's `op_c`
is a full `Word`).  The op_a write push carries the **sign-extended** W result
`[v0, v1, msb·65535, msb·65535]` (witness cells `offset..offset+2`).  Keeping this list beside
`circuit` makes Clean's exposure interface the single structural source consumed by both faithfulness
and semantic grounding. -/
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
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[var { index := offset }, var { index := offset + 1 },
          var { index := offset + 2 } * 65535, var { index := offset + 2 } * 65535]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Addw's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in Addw's exposed
Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The ADDW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the CPUState + the immediate-capable register reader; output is the extracted `AddwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ALUTypeReader`, gate
      -- `is_trusted = is_real`, opcode `ADDW = 19`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 19,
             input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
             input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ],
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
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.AddwOperation.circuit, SP1Clean.AddwOperation.main,
          SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.AddwOperation.circuit, SP1Clean.AddwOperation.main,
          SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
          Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          Soundness.aluTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          AddwOperation.circuit, AddwOperation.elaborated,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil,
          or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          List.append_nil, Soundness.aluTypeProgramMessage] }

/-- The completed Addw circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.AddwChip
