import SP1Clean.Native.Chips.JalChip.Defs
import SP1Clean.Model.InteractionRecovery

/-! # `SP1Clean.JalChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.JalChip

open Circuit
open Extracted (JalColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Operands `isU64`; the padding convention `is_real = 0 → op_a_0 = 0` ensures the additive
`is_real - op_a_0` link-gate is binary on every row. `is_real`-binary is proven from the in-circuit gate,
not assumed here. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 → input.adapter.op_a_0 = 0)

/-- The jump-target word the chip witnesses for `add_operation.value` (`pc + op_b_imm`, base-2^16). -/
def jumpTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] input.adapter.op_b_imm

/-- The link-address word the chip witnesses for `op_a_operation.value` (`pc + 4`, base-2^16). -/
def linkTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] #v[4, 0, 0, 0]

/-- Honest prover-side row well-formedness: operand `isU64`s, `is_real` binary, CPUState clock bounds,
op_a register-access timestamp bounds, `value[3] = 0` for both add results, and the `is_real`-gated
4-byte alignment check (`jump_target[0] / 4 < 2^14`). Covers `rd ≠ x0` rows (`op_a_0 = 0`); soundness
handles both the `op_a_0 = 0` and `op_a_0 = 1` (jal x0) cases. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  -- (Option B pure-read JTypeReader) the op_a read-prior `isU64`, for the reader's op_a memory pull
  -- completeness (its `Spec` now derives + owes the read-prior `isU64`).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  (jumpTargetWord input)[3] = 0 ∧
  (linkTargetWord input)[3] = 0 ∧
  (input.is_real = 1 → ((jumpTargetWord input)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14) ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16 ∧
    input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the pulled prior record's 24-bit access clock (`Channels.MemoryMsg.ClkBound`, the clock half of
  -- the memory channel's `Guarantees`) — the `JTypeReader` op_a read-prior pull's completeness must
  -- exhibit the guarantee it consumes. Soundness *derives* it there from the pull itself.
  (input.is_real = 1 → input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24)

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_pad⟩ := h_assumptions
  obtain ⟨h_cpu, h_add1, h_av3, h_add2, h_oav3, h_jt0, _h_regwrite, h_align, h_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — here only `RegisterWrite`'s op_a link write push at
  -- `clk_low + 4` (`JTypeReader` is a pure read and owes no push bound). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  have h_jt : Readers.JTypeReader.Spec _ := h_jt0 ⟨h_bin, h_bin⟩
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := h_jt.2.1
  -- eval-of-pc rewrites: circuit's `a` operand `#v[eval pc[i], 0]` equals the concrete `pcWord`.
  have hpc : Vector.map (Expression.eval env) input_var_state_pc = input_state_pc := h_input.2.1.2.2.2
  have epc : ∀ i (hi : i < 3), Expression.eval env input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]
  have ha1U : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := ha1eq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  -- the link gate `is_real - op_a_0` is binary on every row (real: `op_a_0` binary; padding: `op_a_0 = 0`).
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_jt, h_bin, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hr1
    have := (h_add1 ⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩ hr1).2
    rw [ha1eq] at this
    simpa only [pcWord] using this
  · intro hr1 hop_a_0
    have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
    have := (h_add2 ⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩ hg1).2
    rw [ha1eq] at this
    simpa only [pcWord] using this
  · -- 4-byte alignment of the jump target, from the in-circuit `÷4` byte-range pull `h_align`
    -- (`(value[0] · 4⁻¹).val < 2^14 ⇒ value[0].val % 4 = 0`). The Sail bridge lifts it to the whole word.
    intro hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    have hguar := h_align (by rw [hr1])
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    exact val_mod_four_of_mul_inv_four_lt ((byteRowSpec_range _ h14p).mp hguar)
  · exact Or.inr ⟨h_bin, h_bin⟩
  · refine Or.inr ⟨h_bin, ?_, h_clk.at_four⟩
    -- RegisterWrite op_a write push: `isU64` of the link value `op_a_value`. On `rd ≠ x0` (`op_a_0 = 0`)
    -- it is the link add result `pc + 4`; on `rd = x0` (`op_a_0 = 1`) the `op_a_0` zeroing gates pin it to `0`.
    intro hr1
    replace hr1 : input_is_real = 1 := hr1
    rcases h_op_a_0 with h0 | h0
    · have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, h0]; simp
      exact (h_add2 ⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩ hg1).1
    · obtain ⟨z0, z1, z2, z3⟩ := h_jt.1
      rw [h0, one_mul] at z0 z1 z2 z3
      refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
        simp only [Vector.getElem_mapRange, circuit_norm] <;> simp_all
  · exact fun h1 h0 => off_gate_vacuous h_bin h1 h0

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_oap, h_bin, h_op_a_0, h_cpu, h_rac, h_jt3, h_lt3, h_align_pa, hdec,
    hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bound, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  simp only [jumpTargetWord, linkTargetWord] at h_jt3 h_lt3 h_align_pa
  -- `h_env` now bundles the two witness-vector equations with the GFC `JTypeReader` subcircuit's
  -- completeness obligation (SC Phase 2pre); the witness equations are `he_av`/`he_oav`.
  obtain ⟨he_av, he_oav, -, _⟩ := h_env
  -- eval-of-input rewrites.
  have hpc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc :=
    h_input.2.1.2.2.2
  have hob : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_imm
      = input_adapter_op_b_imm := h_input.2.2.2.2.2.1
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]
  have ha1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p)) := ha1eq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have hb1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[3]] : Word (ZMod p))
      = input_adapter_op_b_imm := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval1 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] input_adapter_op_b_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    simp only [he_av ⟨i, hi⟩, hb1eq]
  have hval2 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_oav ⟨i, hi⟩]
  have hav0 : env.get i₀
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_b_imm)[0] := by
    have := congrArg (·[0]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hav3 : env.get (i₀ + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_b_imm)[3] := by
    have := congrArg (·[3]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hoav3 : env.get (i₀ + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hval2
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  -- link gate `is_real - op_a_0` reduces to `is_real` when `op_a_0 = 0`.
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩, ?_⟩, ?_,
    ⟨⟨h_bin, h_bin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl h_op_a_0, h_rac, hdec,
      fun hr => ⟨h_oap hr, hprevclk hr⟩⟩⟩,
    ⟨⟨h_bin, ?_, h_clk.at_four⟩, trivial⟩, ?_, ?_⟩
  · rw [hval1]; exact AddOperation.spec_populate ha1U h_imm input_is_real
  · rw [hav3]; exact h_jt3
  · rw [hval2]; exact AddOperation.spec_populate ha1U h4U (input_is_real - input_adapter_op_a_0)
  · rw [hoav3]; exact h_lt3
  · -- RegisterWrite op_a write push: `isU64` of the link value `pc + 4` (completeness covers `op_a_0 = 0`).
    intro hr
    rw [hval2]
    exact (AddOperation.spec_populate ha1U h4U (input_is_real - input_adapter_op_a_0)
      (by rw [h_op_a_0]; simpa using hr)).1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hav0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_align_pa hr1)
  · rcases h_bin with h | h <;> rw [h] <;> simp

/-- Jal's exact Memory-channel interaction list (J-type: both operand slots carry immediates — the
only register traffic is the rd slot).  The op_a read-prior pull descends from the composed
`JTypeReader`; the op_a write push from the composed `RegisterWrite`, carrying the witnessed link
address `op_a_value` (cells `offset+4..7`, the four cells after the jump target `add_value`).
Keeping this list beside `circuit` makes Clean's exposure interface the single structural source
consumed by both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + 4 + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact rd read-prior pull occupies its declared slot in Jal's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The JAL chip row as a `GeneralFormalCircuit`: the data-dependent jump/link semantics, composing the
two witnessed `AddOperation` gadgets and the J-type reader; output is the extracted `JalColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs JalColumns :=
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate alignment byte-pull `Requirements` is discharged by
  -- the inline `is_real` boolean gate in `main`; the residual buses are the readers'/add-ops'.
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      have h_byte : (byteChannel (p := p)).toRaw ∈
          (elaborated (p := p)).channelsWithGuarantees := by
        simp only [circuit_norm]
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.subcircuitChannelsWithRequirements_append,
          Operations.subcircuitChannelsWithRequirements_witness,
          Operations.subcircuitChannelsWithRequirements_subcircuit,
          Operations.subcircuitChannelsWithRequirements_assert,
          Operations.subcircuitChannelsWithRequirements_interact,
          Operations.subcircuitChannelsWithRequirements_nil,
          GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
          FormalAssertion.toSubcircuit_channelsWithRequirements,
          Readers.CPUState.channelsWithRequirements_eq,
          AddOperation.circuit, Readers.JTypeReader.circuit, Readers.RegisterWrite.circuit,
          Gadgets.Equality.channelsWithRequirements_eq, List.nil_append, List.append_nil]
        simp only [List.subset_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · intro channel h_channel
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowChannels_append, Operations.shallowChannels_witness,
          Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
          Operations.shallowChannels_interact, Operations.shallowChannels_nil,
          List.nil_append] at h_channel
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_channel
        subst channel
        exact Or.inl h_byte
      · intro env h_constraints
        have h_gate : Expression.eval env input_var.is_real *
            (Expression.eval env input_var.is_real - 1) = 0 := by
          simpa only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
            witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
            HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
            ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
            Operations.forAllNoOffset, true_and, and_true, eval_mul, eval_sub,
            Expression.eval] using h_constraints
        have h_bool : Expression.eval env input_var.is_real = 0 ∨
            Expression.eval env input_var.is_real = 1 := bool_of_mul_pred h_gate
        have h_bool' : (ProvableStruct.eval env input_var).is_real = 0 ∨
            (ProvableStruct.eval env input_var).is_real = 1 := by
          simpa only [circuit_norm] using h_bool
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
          Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
          Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
          List.nil_append] at h_interaction
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
        subst interaction
        right
        rw [ChannelInteraction.toRaw_requirements]
        intro h1 h0
        simp only [circuit_norm] at h1 h0
        exact off_gate_vacuous h_bool' h1 h0,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair so the chip is a
    -- `VmTables` table. Unlike straight-line ALU chips, `next_pc` is the **witnessed** jump target
    -- `add_value[0..2]` (cells `offset+0..2`) the chip feeds the composed `CPUState`.
    exposedChannels := fun input offset =>
      Readers.CPUState.exposedState
        ⟨input.state, #v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩],
          8, input.is_real⟩ ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `JTypeReader`, gate
      -- `is_trusted = is_real`, opcode `JAL = 46`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf input.is_real
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 46,
             input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
             input.adapter.op_a_0, 1, 1⟩ ],
    exposedChannels_eq := by
      intro input offset
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [Readers.CPUState.exposedState, expose, List.mem_append,
        List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          Readers.CPUState.interactionsWith_state_subcircuit,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.JTypeReader.circuit, Readers.JTypeReader.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
          Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
          Operations.interactionsWith_assert, Operations.interactionsWith_interact,
          Operations.interactionsWith_nil, List.nil_append]
        simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
          Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
        simp only [Channels.byteChannel_eq_stateChannel_false, if_false, List.append_nil]
      · -- Memory branch: compositional — the J-type reader keeps its op_a pull and `RegisterWrite`
        -- its write push via the reader-local `_subcircuit` lemmas; every other child is nil.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_witness,
          Soundness.jTypeReader_memoryInteractions_subcircuit,
          Soundness.registerWrite_memoryInteractions_subcircuit,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Gadgets.Equality.channelsWithGuarantees_eq,
          Gadgets.Equality.channelsWithRequirements_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.memoryChannel_eq_byteChannel_false,
          Channels.memoryChannel_eq_stateChannel_false, not_false_eq_true,
          Operations.interactionsWith_assert, Operations.interactionsWith_interact,
          Operations.interactionsWith_nil, Soundness.jTypeMemoryInteractions,
          Soundness.registerWriteMemoryInteractions, List.cons_append, List.nil_append]
        simp only [circuit_norm]
        simp only [Channels.byteChannel_eq_memoryChannel_false, if_false,
          exposedMemoryInteractions, List.map_cons, List.map_nil]
        rfl
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorNative, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          Soundness.jTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_interact, Operations.interactionsWith_nil,
          List.map_cons, List.map_nil, List.nil_append, Soundness.jTypeProgramMessage]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append]
        simp only [Channels.byteChannel_eq_programChannel_false, if_false] }

/-- The completed Jal circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, Readers.CPUState.exposedState, expose])

end SP1Clean.JalChip
