import SP1Clean.Native.Chips.JalrChip.Defs

/-! # `SP1Clean.JalrChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.JalrChip

open Circuit
open Extracted (JalrColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Operands `isU64`; the padding convention `is_real = 0 → op_a_0 = 0` ensures `is_real - op_a_0` is
binary on every row. `is_real`/`lsb`-binary are proven from the in-circuit gates, not assumed here. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 → input.adapter.op_a_0 = 0)

/-- Honest prover-side row well-formedness: operand `isU64`s, `is_real`/`lsb` binary, CPUState + op_a/op_b
timestamp bounds, `value[3] = 0` for both add results, and the `is_real`-gated cleared-target 4-byte
alignment (`(jump_target[0] - lsb) / 4 < 2^14`). Covers `rd ≠ x0` rows (`op_a_0 = 0`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  (jumpTargetWord input)[3] = 0 ∧
  (linkTargetWord input)[3] = 0 ∧
  (input.is_real = 1 →
    (((jumpTargetWord input)[0] - lsbBit input) * (4 : ZMod p)⁻¹).val < 2 ^ 14)

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU, h_pad⟩ := h_assumptions
  obtain ⟨h_lsbgate, h_cpu, h_add1, h_av3, h_add2, h_oav3, h_it0, h_align, h_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  have h_lsb := bool_of_mul_pred h_lsbgate
  have h_it : Readers.ITypeReader.Spec _ := h_it0 h_bin
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := h_it.2.1
  -- `h_input` flattened: `op_a/op_b_memory` are 3-leaf sub-groups `prev_value ∧ ts_prev_low ∧ ts_diff`.
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, _hcimm⟩ := h_input
  have rb : ∀ i (hi : i < 4),
      Expression.eval env input_var_adapter_op_b_memory_prev_value[i]
        = input_adapter_op_b_memory_prev_value[i] :=
    fun i hi => by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [rb 0 (by omega), rb 1 (by omega), rb 2 (by omega), rb 3 (by omega)]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have epc : ∀ i (hi : i < 3), Expression.eval env input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_it, h_bin, h_lsb, ?_, ?_, ?_⟩, Or.inr h_bin, Or.inr ⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩,
    Or.inr ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩, Or.inr h_bin⟩
  · intro hr1
    have := (h_add1 ⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩ hr1).2
    rw [hrs1eq] at this
    simpa only [rs1Word] using this
  · intro hr1 hop_a_0
    have hg1 : input_is_real + -input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
    have := (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩ hg1).2
    rw [hpceq] at this
    simpa only [pcWord] using this
  · -- 4-byte alignment of the cleared low limb, from the (otherwise-unused) byte-range pull `h_align`:
    -- `((add_value[0] - lsb) · 4⁻¹).val < 2^14 ⇒ (add_value[0] - lsb).val % 4 = 0`.
    intro hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    have hguar := h_align (by rw [hr1])
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    rw [sub_eq_add_neg]
    exact val_mod_four_of_mul_inv_four_lt ((byteRowSpec_range _ h14p).mp hguar)

set_option maxHeartbeats 2000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU, h_bin, h_op_a_0, h_cpu, h_rac_a, h_rac_b, h_jt3, h_lt3,
    h_align_pa⟩ := h_assumptions
  simp only [jumpTargetWord, linkTargetWord, lsbBit, rs1WordI] at h_jt3 h_lt3 h_align_pa
  obtain ⟨he_av, he_oav, he_lsb⟩ := h_env
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, hcimm⟩ := h_input
  have rb : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[i]
        = input_adapter_op_b_memory_prev_value[i] :=
    fun i hi => by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [rb 0 (by omega), rb 1 (by omega), rb 2 (by omega), rb 3 (by omega)]
  have hrs1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hcimm_eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := by
    rw [← hcimm]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have hval1 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]]
          input_adapter_op_c_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_av ⟨i, hi⟩, hcimm_eq]
  have hval2 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_oav ⟨i, hi⟩]
  have hav0 : env.get i₀
      = (AddOperation.populate #v[input_adapter_op_b_memory_prev_value[0],
          input_adapter_op_b_memory_prev_value[1], input_adapter_op_b_memory_prev_value[2],
          input_adapter_op_b_memory_prev_value[3]] input_adapter_op_c_imm)[0] := by
    have := congrArg (·[0]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hrs1eq, circuit_norm] using this
  have hav3 : env.get (i₀ + 3)
      = (AddOperation.populate #v[input_adapter_op_b_memory_prev_value[0],
          input_adapter_op_b_memory_prev_value[1], input_adapter_op_b_memory_prev_value[2],
          input_adapter_op_b_memory_prev_value[3]] input_adapter_op_c_imm)[3] := by
    have := congrArg (·[3]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hrs1eq, circuit_norm] using this
  have hoav3 : env.get (i₀ + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hval2
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hpceq, circuit_norm] using this
  have hlsb_bin : env.get (i₀ + 4 + 4) = 0 ∨ env.get (i₀ + 4 + 4) = 1 := by
    rw [he_lsb]
    rcases Nat.mod_two_eq_zero_or_one (env.get i₀).val with h | h <;> rw [h] <;> simp
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨?_, ⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨hpceq ▸ h_pcU, h4U⟩, h_gate2⟩, ?_⟩,
    ?_, ⟨h_bin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl h_op_a_0, h_rac_a, h_rac_b⟩, ?_, ?_⟩
  · rcases hlsb_bin with h | h <;> rw [h] <;> simp
  · rw [hval1]; exact AddOperation.spec_populate hrs1U h_imm input_is_real
  · rw [hav3]; exact h_jt3
  · rw [hval2]; exact AddOperation.spec_populate (hpceq ▸ h_pcU) h4U (input_is_real + -input_adapter_op_a_0)
  · rw [hoav3]; exact h_lt3
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hav0, he_lsb]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (by rw [← sub_eq_add_neg]; exact h_align_pa hr1)
  · rcases h_bin with h | h <;> rw [h] <;> simp

/-- The JALR chip row as a `GeneralFormalCircuit`: register-indirect jump with LSB clearing, composing the
two witnessed `AddOperation` gadgets and the I-type reader; output is the extracted `JalrColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs JalrColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.JalrChip
