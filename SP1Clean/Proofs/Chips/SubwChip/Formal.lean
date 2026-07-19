import SP1Clean.Native.Chips.SubwChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.SubwChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.SubwChip

open Circuit
open Extracted (SubwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.SubwChip` namespace). -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- W-instruction soundness. Landmines: (1) use `.2.1`/`.2.2.1`/`.2.2.2` projections on `h_holds`
(never `obtain`/`rcases` — the nested `.msb.msb * 65535` sign-fill in the reader's bus emits forces
deep `ProvableStruct` whnf via the case-motive and blows past 16M heartbeats); (2) the inlined `Spec`
keeps `RV64.subw` intact through `circuit_proof_start`; arith via `rv64_subw_eq`. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h_subw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  -- `RegisterWrite` is now `h_holds.2.2.2.1`; the inline gate shifted to `.2.2.2.2`.
  have h_bin := bool_of_mul_pred h_holds.2.2.2.2
  -- G1: the CPUState sub-`Spec`'s (`h_holds.1`) two clock byte bounds discharge the *push* side of the
  -- memory channel's `MemoryMsg.ClkBound` guarantee — `RTypeReader`'s two read-back pushes
  -- (`clk_low + 3` / `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_holds.1 h_bin)
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Derive it from the
  -- `RTypeReader` sub-`Spec`'s memory-pull `isU64` trio (its 7th conjunct, gated on `is_real`).
  have h_rspec := h_adapter ⟨h_bin, h_bin, h_clk⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  have h_as : SubwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } :=
    ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2.1⟩, h_bin⟩
  -- The `RegisterWrite` op_a write push owes `isU64` of the sign-extended write word `[v0, v1, msb·65535,
  -- msb·65535]` (= `SubwOperation.resultWord cols`); align its `Vector.map`/`env.get` slots.
  have h_rw_isU64 : input_is_real = 1 →
      Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2) * 65535, env.get (i₀ + 2) * 65535]
        : Word (ZMod p)) := fun hr => by
    simpa only [SubwOperation.resultWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      using ((h_subw h_as).2 hr).1
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · simpa only [Readers.RTypeReader.circuit, Readers.RTypeReader.SpecD,
      Vector.getElem_map] using h_rspec
  · refine Eq.trans ?_ (rv64_subw_eq _ _).symm
    simpa only [SubwOperation.resultWord, Vector.getElem_map, Vector.getElem_mapRange,
      Inputs.op_b_val, Inputs.op_c_val, circuit_norm] using
      ((h_subw h_as).2 hr).2
  · and_intros <;>
      first
        | exact h_bin
        | exact Or.inl rfl
        | exact Or.inr ⟨h_bin, h_bin, h_clk⟩
        | exact ⟨fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2.1⟩, h_bin⟩
        | exact Or.inr ⟨h_bin, h_rw_isU64, h_clk.at_four⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ :=
    h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  -- `h_env` now bundles the `value`/`msb` witness-gen equations with the GFC `RTypeReader` subcircuit's
  -- completeness obligation (its third component); the witness equations are the first two.
  obtain ⟨-, h_env_val, h_env_msb, -⟩ := h_env
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_b_memory_prev_value := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_c_memory_prev_value := by
    rw [← hoc]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i => var { index := i₀ + i }) : Vector (ZMod p) 2)
      = SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    simp only [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2)
      = SubwOperation.subwMsbWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
        fun hr => ⟨ha_prev hr, ha, hb, (hprevclk hr).1, (hprevclk hr).2.1, (hprevclk hr).2.2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩, ?_⟩
  · rw [hval, hmsbeq]; exact SubwOperation.spec_populate ha hb input_is_real
  · -- RegisterWrite's `isU64 value` (op_a write push): the witnessed op_a write word is the sign-extended
    -- `resultWord (populate op_b op_c)`, whose `isU64` is `spec_populate.2 _ |>.1`. The write value appears
    -- as individual `env.get` slots, so bridge them to the operation's witnessed limbs via `hval`/`hmsbeq`.
    intro hr
    have h0 : env.get i₀ = (SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
        input_adapter_op_c_memory_prev_value)[0] := by
      simpa only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        using congrArg (fun v => v[0]) hval
    have h1 : env.get (i₀ + 1) = (SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
        input_adapter_op_c_memory_prev_value)[1] := by
      simpa only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        using congrArg (fun v => v[1]) hval
    have hword : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2) * 65535, env.get (i₀ + 2) * 65535]
          : Word (ZMod p))
        = SubwOperation.resultWord (SubwOperation.populate input_adapter_op_b_memory_prev_value
            input_adapter_op_c_memory_prev_value) := by
      rw [h0, h1, hmsbeq]; simp only [SubwOperation.resultWord, SubwOperation.populate]
    rw [hword]
    exact ((SubwOperation.spec_populate ha hb input_is_real).2 hr).1
  rcases hbin with h | h <;> rw [h] <;> simp

/-- Subw's exact Memory-channel interaction list.  The op_a write push carries the **sign-extended** W
result `[v0, v1, msb·65535, msb·65535]` (witness cells `offset..offset+2`).  Keeping this list beside
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
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[var { index := offset }, var { index := offset + 1 },
          var { index := offset + 2 } * 65535, var { index := offset + 2 } * 65535]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Subw's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-C pull occupies its declared slot in Subw's exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The SUBW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the two readers; output is the extracted `SubwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubwCols :=
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
      -- The Program-bus instruction fetch (descended from the composed `RTypeReader`, gate
      -- `is_trusted = is_real`, opcode `SUBW = 20`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 20,
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
          SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
          SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
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
          SP1Clean.SubwOperation.circuit, SP1Clean.SubwOperation.main,
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
          Soundness.rTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          SubwOperation.circuit, SubwOperation.elaborated,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil,
          or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          List.append_nil, Soundness.rTypeProgramMessage] }

/-- The completed Subw circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.SubwChip
