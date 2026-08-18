import SP1Clean.Native.Chips.UTypeChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit

/-! # `SP1Clean.UTypeChip` — soundness / completeness / `circuit`

The chip `Spec` (J-type reader sub-`Spec` + `is_real`/`is_auipc`-binary + `RV64.lui`/`RV64.auipc`
identities) lives in `FormalModel/Contracts/Chips.lean`; `Assumptions`/`ProverAssumptions` in
`FormalModel/Contracts/ChipAssumptions.lean`. -/

namespace SP1Clean.UTypeChip

open Circuit

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- `Word.toBitVec64 #v[0,0,0,0] = 0`. -/
lemma toBitVec64_zero_word : Word.toBitVec64 (#v[(0 : ZMod p), 0, 0, 0] : Word (ZMod p)) = 0 := by
  simp [Word.toBitVec64, Word.toNat_def]

/-- `RV64.auipc imm pc = pc + RV64.lui imm` (AUIPC's offset is `RV64.lui`'s value added to `pc`). -/
lemma auipc_eq_add_lui (imm : BitVec 20) (pcv : BitVec 64) :
    RV64.auipc imm pcv = pcv + RV64.lui imm := by
  rw [RV64.auipc, RV64.lui]; exact BitVec.add_comm _ _

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_dec⟩ := h_assumptions
  obtain ⟨h_cpu, h_add, h_jt0, _h_regwrite, h_ad0, h_ad1, h_ad2, h_iaui_gate,
    h_pad_gate, h_real_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_real_gate
  have h_iaui : input_is_auipc = 0 ∨ input_is_auipc = 1 := bool_of_mul_pred h_iaui_gate
  have h_pad (hr : input_is_real = 0) : input_adapter_op_a_0 = 0 := by
    rw [hr] at h_pad_gate
    simpa using h_pad_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — here only `RegisterWrite`'s op_a write push at
  -- `clk_low + 4` (`JTypeReader` is a pure read and owes no push bound). The offset is left to
  -- unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  have h_jt := h_jt0 ⟨h_bin, h_bin⟩
  have h_op_a_0 (hr : input_is_real = 1) :
      input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 :=
    h_jt.2.1 hr
  have hpc : Vector.map (Expression.eval env) input_var_state_pc = input_state_pc := h_input.2.1.2.2.2
  have epc : ∀ i (hi : i < 3), Expression.eval env input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have ha0 : env.get i₀ = input_is_auipc * input_state_pc[0] := by
    rw [epc 0 (by omega)] at h_ad0; exact sub_eq_zero.mp h_ad0
  have ha1 : env.get (i₀ + 1) = input_is_auipc * input_state_pc[1] := by
    rw [epc 1 (by omega)] at h_ad1; exact sub_eq_zero.mp h_ad1
  have ha2 : env.get (i₀ + 2) = input_is_auipc * input_state_pc[2] := by
    rw [epc 2 (by omega)] at h_ad2; exact sub_eq_zero.mp h_ad2
  have haddend0 : input_is_auipc = 0 →
      (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) = #v[0, 0, 0, 0] := by
    intro h; rw [ha0, ha1, ha2, h]; simp
  have haddendpc : input_is_auipc = 1 →
      (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p))
        = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    intro h; rw [ha0, ha1, ha2, h]; simp
  have h_addendU : Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) := by
    rcases h_iaui with h | h
    · rw [haddend0 h]; refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;> simp
    · rw [haddendpc h]; exact h_pcU
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 h with h0 | h0 <;> rw [h, h0] <;> simp
  have h_addspec := h_add ⟨fun _ => ⟨h_addendU, h_imm⟩, h_gate2⟩
  refine ⟨⟨h_jt, h_bin, h_iaui, ?_, ?_⟩,
    Or.inr ⟨h_bin, h_bin⟩,
    Or.inr ⟨h_bin, ?_, h_clk.at_four⟩⟩
  · intro hr1 hop0 hiaui0
    have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, hop0]; simp
    have hsem := (h_addspec hg1).2
    simp only [haddend0 hiaui0, toBitVec64_zero_word] at hsem
    rw [hsem]; simpa using h_dec
  · intro hr1 hop0 hiaui1
    have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, hop0]; simp
    have hsem := (h_addspec hg1).2
    simp only [haddendpc hiaui1] at hsem
    rw [hsem, auipc_eq_add_lui, ← h_dec]
    simp only [pcWord]
  · -- RegisterWrite op_a write push: `isU64` of the written result `add_value`. On `rd ≠ x0` (`op_a_0 = 0`)
    -- it is the LUI/AUIPC add result; on `rd = x0` (`op_a_0 = 1`) the `op_a_0` zeroing gates pin it to `0`.
    intro hr1
    replace hr1 : input_is_real = 1 := hr1
    rcases h_op_a_0 hr1 with h0 | h0
    · have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, h0]; simp
      exact (h_addspec hg1).1
    · obtain ⟨z0, z1, z2, z3⟩ := h_jt.1
      rw [h0, one_mul] at z0 z1 z2 z3
      refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
        simp only [Vector.getElem_mapRange, circuit_norm] <;> simp_all

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_oap, h_bin, h_iaui, h_op0, h_cpu, h_rac, _h_dec, hdec, hprevclk⟩ :=
    h_assumptions
  -- G1: the *push* side clock bound, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨_, ⟨_, _, _, hpc⟩, ⟨_, _, h_a0, hob, _⟩, hiau⟩ := h_input
  -- `h_env` now bundles the addend/add-result witness equations with the GFC `JTypeReader` subcircuit's
  -- completeness obligation (SC Phase 2pre); the witness equations are `he_addend`/`he_addval`.
  obtain ⟨he_addend, he_addval, -, _⟩ := h_env
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have hg0 : env.get i₀ = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[0] := by
    simpa [circuit_norm, hiau] using he_addend 0
  have hg1 : env.get (i₀ + 1) = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[1] := by
    simpa [circuit_norm, hiau] using he_addend 1
  have hg2 : env.get (i₀ + 2) = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[2] := by
    simpa [circuit_norm, hiau] using he_addend 2
  have hAeq : (#v[input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[0],
        input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[1],
        input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] := by rw [hg0, hg1, hg2]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_imm[0],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[1],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[2],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[3]] : Word (ZMod p))
      = input_adapter_op_b_imm := (vec4_eval _ _).trans hob
  have hA_U : Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) := by
    rcases h_iaui with h | h
    · have e : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) = #v[0, 0, 0, 0] := by
        rw [hg0, hg1, hg2, h]; simp
      rw [e]; refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;> simp
    · have e : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p))
          = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
        rw [hg0, hg1, hg2, h, epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; simp
      rw [e]; exact h_pcU
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 3 + i }) : Word (ZMod p))
      = AddOperation.populate #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0]
          input_adapter_op_b_imm := by
    -- The addend operand of the witness IR is the *input* product `is_auipc * pc`; `hAeq` is what
    -- identifies it with the addend cells this statement is phrased in.
    rw [← AddOperation.populateIRGated_eval_off env input_var_adapter_op_a_0
      #v[input_var_is_auipc * input_var_state_pc[0], input_var_is_auipc * input_var_state_pc[1],
         input_var_is_auipc * input_var_state_pc[2], 0]
      input_var_adapter_op_b_imm _ _ (by simpa [circuit_norm, hiau] using hAeq) hbeq hA_U h_imm
      (h_a0.trans h_op0)]
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact he_addval ⟨i, hi⟩
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rw [h_op0]; simpa using h_bin
  refine ⟨⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨hA_U, h_imm⟩, h_gate2⟩, ?_⟩,
    ⟨⟨h_bin, h_bin⟩, ⟨⟨?_, ?_, ?_, ?_⟩, (fun _ => Or.inl h_op0), h_rac, hdec,
      fun hr => ⟨h_oap hr, hprevclk hr⟩⟩⟩,
    ⟨⟨h_bin, ?_, h_clk.at_four⟩, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate hA_U h_imm (input_is_real - input_adapter_op_a_0)
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · -- RegisterWrite op_a write push: `isU64` of the result `add_value` (completeness covers `op_a_0 = 0`).
    intro hr
    rw [hval]
    exact (AddOperation.spec_populate hA_U h_imm (input_is_real - input_adapter_op_a_0)
      (by rw [h_op0]; simpa using hr)).1
  · rw [hg0]; ring_nf
  · rw [hg1]; ring_nf
  · rw [hg2]; ring_nf
  · rcases h_iaui with h | h <;> rw [h] <;> simp
  · rw [h_op0]; simp
  · rcases h_bin with h | h <;> rw [h] <;> simp

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

/-- Exact Byte-channel list emitted by UType: two CPU clock checks, four add-result limb checks, and
the J-type reader's two destination-register timestamp checks. The add rows are gated by
`is_real - op_a_0`, exactly as in the pinned Rust AIR. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let addGate := input.is_real - input.adapter.op_a_0
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf addGate
      ⟨6, var ⟨offset + 3⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf addGate
      ⟨6, var ⟨offset + 4⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf addGate
      ⟨6, var ⟨offset + 5⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf addGate
      ⟨6, var ⟨offset + 6⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 4 - input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩ ]

/-- UType's exact Memory-channel interaction list (J-type: both operand slots carry immediates — the
only register traffic is the rd slot).  The op_a read-prior pull descends from the composed
`JTypeReader`; the op_a write push from the composed `RegisterWrite`, carrying the witnessed
LUI/AUIPC result `add_value` (cells `offset+3..6`, after the three addend limbs).  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + 3 + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact rd read-prior pull occupies its declared slot in UType's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- Exact Program fetch emitted by the J-type adapter. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       input.is_auipc * 48 + (1 - input.is_auipc) * 49,
       input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
       input.adapter.op_a_0, 1, 1⟩ ]

/-- The U-type chip row as a `GeneralFormalCircuit`: the flag-gated `RV64.lui`/`RV64.auipc` semantics,
composing the witnessed `AddOperation` gadget and the J-type reader; output is the native `Columns` row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.subcircuitChannelsWithRequirements_append,
          Operations.subcircuitChannelsWithRequirements_witness,
          Operations.subcircuitChannelsWithRequirements_subcircuit,
          Operations.subcircuitChannelsWithRequirements_assert,
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
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowChannels_append, Operations.shallowChannels_witness,
          Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
          Operations.shallowChannels_nil, List.nil_append] at h_channel
        simp only [List.not_mem_nil] at h_channel
      · intro env _h_constraints
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
          Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
          Operations.shallowInteractions_nil, List.nil_append] at h_interaction
        simp only [List.not_mem_nil] at h_interaction,
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      expose programChannel (exposedProgramInteractions input),
    exposedChannels_eq := by
      intro input offset
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, exposedStateInteractions, exposedProgramInteractions,
        List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
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
          Operations.interactionsWith_assert, Operations.interactionsWith_nil, List.nil_append]
        simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
          Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
        simp [Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg,
          Readers.CPUState.nextMsg]
        exact ⟨rfl, rfl⟩
      · -- Memory branch: compositional — the J-type reader keeps its op_a pull and `RegisterWrite`
        -- its write push via the reader-local `_subcircuit` lemmas; every other child is nil.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
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
          Operations.interactionsWith_assert, Operations.interactionsWith_nil,
          Soundness.jTypeMemoryInteractions,
          Soundness.registerWriteMemoryInteractions, List.cons_append, List.nil_append]
        simp only [circuit_norm]
        simp only [exposedMemoryInteractions, List.map_cons, List.map_nil]
        rfl
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
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
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          Soundness.jTypeProgramMessage]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append] }

/-- Folded circuit projections used by whole-chip row codecs without unfolding the proof bundle. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 7 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 7 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed UType circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw, (exposedStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

private def cpuByteInteractionsRaw
    (input : Var Readers.CPUState.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, (input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0, input.cols.clk_16_24, 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem cpuByteInteractions_exact
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main input).operations offset).interactionsWith byteChannel.toRaw =
      cpuByteInteractionsRaw input := by
  simp [Readers.CPUState.main, cpuByteInteractionsRaw, circuit_norm]

private theorem cpuByteInteractions_subcircuit
    (input : Var Readers.CPUState.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit ((Readers.CPUState.circuit (p := p)).toSubcircuit offset input) :: ops) =
      cpuByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.CPUState.circuit byteChannel.toRaw input offset ops _
    (cpuByteInteractions_exact input offset)

private def addByteInteractionsRaw
    (input : Var AddOperation.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[0], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[3], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem addByteInteractions_exact
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ) :
    ((AddOperation.main input).operations offset).interactionsWith byteChannel.toRaw =
      addByteInteractionsRaw input := by
  simp [AddOperation.main, addByteInteractionsRaw, circuit_norm]

private theorem addByteInteractions_subcircuit
    (input : Var AddOperation.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit ((AddOperation.circuit (p := p)).toSubcircuit offset input) :: ops) =
      addByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
    AddOperation.circuit byteChannel.toRaw input offset ops _
    (addByteInteractions_exact input offset)

private def jTypeByteInteractionsRaw
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (input.clk_low + 4 - input.cols.op_a_memory.access_timestamp.prev_low - 1 -
          input.cols.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩).toRaw ]

private theorem jTypeByteInteractions_exact
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.JTypeReader.main input).operations offset).interactionsWith byteChannel.toRaw =
      jTypeByteInteractionsRaw input := by
  simp [Readers.JTypeReader.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, jTypeByteInteractionsRaw, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions, circuit_norm]

private theorem jTypeByteInteractions_subcircuit
    (input : Var Readers.JTypeReader.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.JTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      jTypeByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.JTypeReader.circuit byteChannel.toRaw input offset ops _
    (jTypeByteInteractions_exact input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem registerWriteByteInteractions_exact
    (input : Var Readers.RegisterWrite.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.RegisterWrite.main input).operations offset).interactionsWith byteChannel.toRaw =
      [] := by
  simp [Readers.RegisterWrite.main, circuit_norm]

private theorem registerWriteByteInteractions_subcircuit
    (input : Var Readers.RegisterWrite.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.RegisterWrite.circuit (p := p)).toSubcircuit offset input) :: ops) =
      Operations.interactionsWith byteChannel.toRaw ops := by
  simpa only [List.nil_append] using
    InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
      Readers.RegisterWrite.circuit byteChannel.toRaw input offset ops []
      (registerWriteByteInteractions_exact input offset)

private def uTypeByteInteractionsRaw
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (AbstractInteraction (ZMod p)) :=
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let value : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 3 + i }
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨#v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩, 0],
      input.adapter.op_b_imm, { value := value },
      input.is_real - input.adapter.op_a_0⟩
  let readerInput : Var Readers.JTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
      input.is_auipc * 48 + (1 - input.is_auipc) * 49,
      value[0], value[1], value[2], value[3]⟩
  cpuByteInteractionsRaw cpuInput ++ addByteInteractionsRaw addInput ++
    jTypeByteInteractionsRaw readerInput

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeByteInteractionsRaw_eq_exposed
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    uTypeByteInteractionsRaw input offset =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw := by
  simp only [uTypeByteInteractionsRaw, exposedByteInteractions,
    cpuByteInteractionsRaw, addByteInteractionsRaw, jTypeByteInteractionsRaw,
    circuit_norm, List.cons_append, List.nil_append, List.map_cons, List.map_nil]

private theorem uTypeByteInteractions_exact
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      uTypeByteInteractionsRaw input offset := by
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p))
      (ops : Operations (ZMod p)) =>
    @InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp ops
      List.not_mem_nil List.not_mem_nil
  simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
  simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
    cpuByteInteractions_subcircuit, addByteInteractions_subcircuit,
    jTypeByteInteractions_subcircuit, registerWriteByteInteractions_subcircuit, heq,
    Operations.interactionsWith_assert, Operations.interactionsWith_nil, List.nil_append]
  simp only [uTypeByteInteractionsRaw, cpuByteInteractionsRaw,
    addByteInteractionsRaw, jTypeByteInteractionsRaw, circuit_norm,
    List.cons_append, List.nil_append]

/-- The completed UType circuit emits exactly its eight Byte interactions. -/
theorem interactionsWith_byte_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw :=
  (uTypeByteInteractions_exact input offset).trans
    (uTypeByteInteractionsRaw_eq_exposed input offset)

/-- The completed UType circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed UType circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw,
      (exposedProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.UTypeChip
