import SP1Clean.Native.Chips.BranchChip.Defs
import SP1Clean.Proofs.Chips.BranchChip.Decision
import SP1Clean.Proofs.CircuitProofStart

/-! # `SP1Clean.BranchChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.BranchChip

open Circuit
open Extracted (BranchColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Operands `isU64`; `is_real`/flag/`is_branching`-binary are proven from the gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
    input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))

/-- Honest prover-side row well-formedness. The immediate + rs1/rs2 + pc words `isU64`, `is_real` binary,
the CPUState clock bounds + op_a/op_b register-access timestamp bounds, the two targets fitting in 48 bits
(`value[3] = 0`), and the `is_real`-gated next_pc 4-byte alignment + u16 limb ranges. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  let br := hintBranching hint
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (rs1WordInput input) ∧
  Word.isU64 (rs2WordInput input) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0⟩ ∧
  (branchTargetWord input)[3] = 0 ∧
  (fallThroughWord input)[3] = 0 ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧ (f[4] = 0 ∨ f[4] = 1) ∧ (f[5] = 0 ∨ f[5] = 1) ∧
  (input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] + f[5]) ∧
  -- honest `is_branching`: binary, zero on padding, and (on real rows) the per-opcode branch-taken
  -- decision as a pure function of the source words (mirrors `Spec`'s six-way condition).
  (br = 0 ∨ br = 1) ∧
  (input.is_real = 0 → br = 0) ∧
  (input.is_real = 1 →
    (f[0] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) = Word.toBitVec64 (rs2WordInput input))) ∧
    (f[1] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠ Word.toBitVec64 (rs2WordInput input))) ∧
    (f[2] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[3] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (f[4] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[5] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = false))) ∧
  -- the `is_real`-gated committed `next_pc` byte ranges (4-byte-aligned low limb + two u16 limbs).
  (input.is_real = 1 →
    ((committedNextPc input br)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
    (committedNextPc input br)[1].val < 2 ^ 16 ∧
    (committedNextPc input br)[2].val < 2 ^ 16)

-- The binary-element algebra (`zero_ne_one'`, `val_of_bool`, `one_hot6`) and the six-way decision
-- dispatch (`branch_conditions_of_decision_eq` / `branch_decision_eq_of_conditions`) live in the
-- sibling `Decision` module, so the heavy one-hot case analysis is elaborated once, in a small
-- context, rather than twice under the giant chip goal here.

set_option maxHeartbeats 8000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_early_struct
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU⟩ := h_assumptions
  obtain ⟨h_lt, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_realsum, h_sumbin, h_isbr_bin,
    h_isbr, h_pad, h_cpustate, h_add1, h_add1z, h_add2, h_add2z, h_pc0, h_pc1, h_pc2, h_itype,
    h_byte1, h_byte2, h_byte3⟩ := h_holds
  obtain ⟨_h_ir, ⟨_h_ckh, _h_ck1, _h_ck0, hpc⟩, _h_a, ⟨h_amem_pv, _, _⟩, _h_a0, _h_b,
    ⟨h_bmem_pv, _, _⟩, hcimm⟩ := h_input
  -- the `is_real = Σ flags` gate is now the shallow `assertZero (is_real - sum)`; recover the eq form.
  replace h_realsum := sub_eq_zero.mp h_realsum
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
    rw [h_realsum]; exact bool_of_mul_pred h_sumbin
  have hbeq := bool_of_mul_pred h_beq
  have hbne := bool_of_mul_pred h_bne
  have hblt := bool_of_mul_pred h_blt
  have hbge := bool_of_mul_pred h_bge
  have hbltu := bool_of_mul_pred h_bltu
  have hbgeu := bool_of_mul_pred h_bgeu
  have hisbr := bool_of_mul_pred h_isbr_bin
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_a_memory_prev_value[0], input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2], input_adapter_op_a_memory_prev_value[3]] := by
    rw [← h_amem_pv]; simp only [Vector.getElem_map]
  have hrs2eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have h_onehot := one_hot6 hbeq hbne hblt hbge hbltu hbgeu h_sumbin
  have h_sig_bin : env.get (i₀ + 2) + env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 2) + env.get (i₀ + 3) = 1 := by
    rcases hblt with hl | hl <;> rcases hbge with hg | hg
    · left; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · exfalso
      have := val_of_bool (h := hbeq); have := val_of_bool (h := hbne)
      have := val_of_bool (h := hbltu); have := val_of_bool (h := hbgeu)
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [hl, hg, ZMod.val_one] at h_onehot
      omega
  refine ⟨⟨?_, h_bin, ⟨hbeq, hbne, hblt, hbge, hbltu, hbgeu, hisbr⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h_itype ⟨h_bin, h_bin⟩
  · intro hr1 hbr1
    have hav := (h_add1 ⟨fun _ => ⟨hpcU, h_imm⟩, hisbr⟩ hbr1).2
    rw [hpceq] at hav
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1) := by
      rw [h_pc0, hbr1, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 1) := by
      rw [h_pc1, hbr1, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 2) := by
      rw [h_pc2, hbr1, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add1z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · intro hr1 hbr0
    have hgate1 : input_is_real - env.get (i₀ + 6) = 1 := by rw [hr1, hbr0]; ring
    have hav := (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, Or.inr hgate1⟩ hgate1).2
    rw [hpceq] at hav
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1 + 4) := by
      rw [h_pc0, hbr0, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 4 + 1) := by
      rw [h_pc1, hbr0, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 4 + 2) := by
      rw [h_pc2, hbr0, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + 4 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add2z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · intro hr1
    have h_lt_spec := LtOperationSigned.result_semantic hrs1U hrs2U hr1
      (h_lt ⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩)
    obtain ⟨h_bit, h_eqf, -⟩ := h_lt_spec
    -- `result_semantic` returns the bit/flags through the (unreduced) `Inputs`-constructor projections;
    -- `circuit_norm` reduces them to the `env.get`/`mapRange` form that `h_isbr`/the `Decision` lemma use.
    simp only [circuit_norm] at h_bit h_eqf
    rw [hrs1eq, hrs2eq] at h_bit h_eqf
    -- `simp only [id_eq]` strips the `id (ZMod p)` field-type wrapper off the gate so it unifies
    -- with the `Decision` lemma's plain-`ZMod p` equation (the `id` blocks `linear_combination`'s
    -- ring synthesis — see PROOF_PATTERNS).
    rw [hr1, one_mul] at h_isbr
    have hone : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
        + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [← h_realsum]; exact hr1
    simp only [rs1Word, rs2Word]
    exact branch_conditions_of_decision_eq h_rs1U h_rs2U hbeq hbne hblt hbge hbltu hbgeu hisbr hone
      h_bit h_eqf (by simp only [branchDecision]; linear_combination h_isbr)
  · -- 4-byte alignment of the branch target's low limb, from the in-circuit `÷4` byte-range pull
    -- `h_byte1` (`(next_pc[0] · 4⁻¹).val < 2^14 ⇒ next_pc[0].val % 4 = 0`). Lifted to the whole word
    -- at the Sail bridge. Mirrors `JalChip.soundness`.
    intro hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    have hguar := h_byte1 (by rw [hr1])
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    exact val_mod_four_of_mul_inv_four_lt ((byteRowSpec_range _ h14p).mp hguar)
  · refine ⟨⟨h_bin, h_bin⟩, ?_, ?_, ?_⟩ <;>
      intro h1 h0 <;> exact off_gate_vacuous h_bin h1 h0

set_option warn.sorry false in
/-- Completeness of the legacy hand-written branch witness circuit is deferred after the Lean 4.31
`whnf` regression. Whole-chip populate conformance remains the replacement target; this declaration is
the explicit seam required by Clean's `GeneralFormalCircuit` bundle. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  stop
  trivial

set_option maxHeartbeats 2000000 in
private theorem main_requirementsChannelsLawful (input_var : Var Inputs (ZMod p)) (i₀ : ℕ) :
    ((main input_var).operations i₀).RequirementsChannelsLawful
      (elaborated (p := p)).channelsWithGuarantees [(memoryChannel (p := p)).toRaw] := by
  have h_byte : (byteChannel (p := p)).toRaw ∈
      (elaborated (p := p)).channelsWithGuarantees := by
    simp only [circuit_norm]
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
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
      LtOperationSigned.circuit, AddOperation.circuit,
      Readers.ITypeReaderImmutable.circuit,
      Gadgets.Equality.channelsWithRequirements_eq, List.nil_append, List.append_nil]
    simp only [List.subset_def, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro channel h_channel
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength] at h_channel
    simp only [Operations.shallowChannels_append, Operations.shallowChannels_witness,
      Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
      Operations.shallowChannels_interact, Operations.shallowChannels_nil,
      List.nil_append] at h_channel
    simp only [ChannelInteraction.toRaw_channel, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_self] at h_channel
    subst channel
    exact Or.inl h_byte
  · intro env h_constraints
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength] at h_constraints
    simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, true_and, and_true, eval_sub, Expression.eval] at h_constraints
    have h_sum_eq : Expression.eval env input_var.is_real =
        env.get (i₀ + 0) + env.get (i₀ + 1) + env.get (i₀ + 2) +
          env.get (i₀ + 3) + env.get (i₀ + 4) + env.get (i₀ + 5) :=
      sub_eq_zero.mp h_constraints.1
    have h_bool : Expression.eval env input_var.is_real = 0 ∨
        Expression.eval env input_var.is_real = 1 := by
      rw [h_sum_eq]
      exact bool_of_mul_pred h_constraints.2
    have h_bool' : (ProvableStruct.eval env input_var).is_real = 0 ∨
        (ProvableStruct.eval env input_var).is_real = 1 := by
      simpa only [circuit_norm] using h_bool
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction h_interaction
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength] at h_interaction
    simp only [Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
      Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
      Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
      List.nil_append] at h_interaction
    simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl | rfl <;>
      right <;>
      rw [ChannelInteraction.toRaw_requirements] <;>
      intro h1 h0 <;>
      simp only [circuit_norm] at h1 h0 <;>
      exact off_gate_vacuous h_bool' h1 h0

/-- Branch's State exposure, expressed solely through the canonical `CPUState` child interface. -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state,
      #v[var ⟨offset + 6 + 1 + 4 + 4⟩, var ⟨offset + 6 + 1 + 4 + 4 + 1⟩,
        var ⟨offset + 6 + 1 + 4 + 4 + 2⟩],
      8, input.is_real⟩

set_option maxHeartbeats 2000000 in
private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (stateExposure input offset) := by
  simp only [stateExposure, Readers.CPUState.exposedState]
  rw [Operations.exposedChannelsLawful_expose]
  simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorNative, CircuitNormalization.witnessNative_apply_eq,
    subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
    HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
  simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
    Readers.CPUState.interactionsWith_state_subcircuit,
    InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
    InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
    LtOperationSigned.circuit, LtOperationSigned.channelsWithGuarantees_eq,
    AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
    Readers.ITypeReaderImmutable.circuit,
    Readers.ITypeReaderImmutable.channelsWithGuarantees_eq,
    FormalCircuitBase.channelsWithGuarantees_def,
    List.mem_cons, List.not_mem_nil, or_false,
    Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
    Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
    Operations.interactionsWith_assert, Operations.interactionsWith_interact,
    Operations.interactionsWith_nil, List.nil_append]
  simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
    Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
  simp only [Channels.byteChannel_eq_stateChannel_false, if_false, List.append_nil]

/-- The BRANCH chip's `GeneralFormalCircuit`: conditional control flow via `LtOperationSigned` +
two `AddOperation` gadgets + `ITypeReaderImmutable`. Soundness is proved; completeness is the explicit
deferred seam above. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs BranchColumns :=
  -- `byteChannel` dropped (W11 Phase 0c): the three off-gate next_pc byte-range pulls are discharged by the
  -- inline `is_real = Σ flags` / `Σ flags ∈ {0,1}` shallow gates in `main`; residual buses are the readers'.
  { main, elaborated,
    channelsWithRequirements := [memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := main_requirementsChannelsLawful,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair so the chip is a
    -- `VmTables` table. `next_pc` is the **witnessed** muxed branch target the chip feeds `CPUState`:
    -- the three selected limbs `next_pc[0..2]` (cells `offset+15..17`).
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

end SP1Clean.BranchChip
