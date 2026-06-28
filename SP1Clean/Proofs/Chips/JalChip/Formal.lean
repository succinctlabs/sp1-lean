import SP1Clean.Native.Chips.JalChip.Defs

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
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
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
    input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_pad⟩ := h_assumptions
  obtain ⟨h_cpu, h_add1, h_av3, h_add2, h_oav3, h_jt0, h_align, h_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
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
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_jt, h_bin, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro hr1
    have := (h_add1 ⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩ hr1).2
    rw [ha1eq] at this
    simpa only [pcWord] using this
  · intro hr1 hop_a_0
    have hg1 : input_is_real + -input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
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
  · exact h_bin
  · exact Or.inr ⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩
  · exact Or.inr ⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩
  · exact ⟨Or.inr ⟨h_bin, h_bin⟩, fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_bin, h_op_a_0, h_cpu, h_rac, h_jt3, h_lt3, h_align_pa, hdec⟩ := h_assumptions
  simp only [jumpTargetWord, linkTargetWord] at h_jt3 h_lt3 h_align_pa
  obtain ⟨he_av, he_oav⟩ := h_env
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
    rw [he_av ⟨i, hi⟩, hb1eq]
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
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩, ?_⟩, ?_,
    ⟨⟨h_bin, h_bin⟩, ⟨hz _, hz _, hz _, hz _⟩, Or.inl h_op_a_0, h_rac, hdec⟩, ?_, ?_⟩
  · rw [hval1]; exact AddOperation.spec_populate ha1U h_imm input_is_real
  · rw [hav3]; exact h_jt3
  · rw [hval2]; exact AddOperation.spec_populate ha1U h4U (input_is_real + -input_adapter_op_a_0)
  · rw [hoav3]; exact h_lt3
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hav0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_align_pa hr1)
  · rcases h_bin with h | h <;> rw [h] <;> simp

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
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel,
        AddOperation.circuit, Readers.CPUState.circuit, Readers.JTypeReader.circuit]; grind,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair so the chip is a
    -- `VmTables` table. Unlike straight-line ALU chips, `next_pc` is the **witnessed** jump target
    -- `add_value[0..2]` (cells `offset+0..2`) the chip feeds the composed `CPUState`.
    exposedChannels := fun input offset =>
      expose stateChannel
        [ pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.JTypeReader.circuit, Readers.JTypeReader.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main] }

end SP1Clean.JalChip
