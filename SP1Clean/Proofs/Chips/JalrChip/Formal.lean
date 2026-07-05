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
def ProverAssumptions (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  -- (Option B pure-read ITypeReader) the op_a read-prior `isU64`, for the reader's op_a memory pull
  -- completeness (its `Spec` now derives + owes the read-prior `isU64` pair).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
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
    (((jumpTargetWord input)[0] - lsbBit input) * (4 : ZMod p)⁻¹).val < 2 ^ 14) ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16 ∧
    input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- SC Phase 2c: the honest prover supplies the State pull's `StateTruth`.
  (input.is_real = 1 → SP1Clean.Semantics.StateTruth (Readers.CPUState.stateMsgOf input.state) data)

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU, h_pad⟩ := h_assumptions
  obtain ⟨h_lsbgate, h_cpu, h_add1, h_av3, h_add2, h_oav3, h_it0, _h_regwrite, h_align, h_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  have h_lsb := bool_of_mul_pred h_lsbgate
  have h_it : Readers.ITypeReader.Spec _ := h_it0 ⟨h_bin, h_bin⟩
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := h_it.2.1
  -- `h_input` flattened: `op_a/op_b_memory` are 3-leaf sub-groups `prev_value ∧ ts_prev_low ∧ ts_diff`.
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, _hcimm⟩ := h_input
  have rb0 : Expression.eval env input_var_adapter_op_b_memory_prev_value[0]
      = input_adapter_op_b_memory_prev_value[0] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
      = input_adapter_op_b_memory_prev_value[1] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb2 : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
      = input_adapter_op_b_memory_prev_value[2] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
      = input_adapter_op_b_memory_prev_value[3] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [rb0, rb1, rb2, rb3]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
  have ep0 : Expression.eval env input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real + - input_adapter_op_a_0 = 0 ∨ input_is_real + - input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_it, h_bin, h_lsb, ?_, ?_, ?_, ?_⟩, h_bin, Or.inr ⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩,
    Or.inr ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩, Or.inr ⟨h_bin, h_bin⟩, Or.inr ⟨h_bin, ?_⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩
  · intro hr1
    have := (h_add1 ⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩ hr1).2
    rw [hrs1eq] at this
    simpa only [rs1Word] using this
  · intro hr1 hop_a_0
    have hg1 : input_is_real + - input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
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
  · -- LSB-clearing: the committed `nextPcWord` is `add_value` with bit 0 cleared (`~~~1#64 &&&`).
    -- The binary `lsb` gate + the `÷4` byte-range pin `lsb = bit0(add_value[0])`; with `add_value[3] = 0`
    -- this makes `toNat add_value = toNat nextPcWord + lsb`, so `ofNat64_clear_lsb_and` applies.
    intro hr1
    have hguar := h_align (by rw [hr1])
    simp only [byteChannel] at hguar
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    rw [← c14] at hguar
    have hlt := (byteRowSpec_range _ h14p).mp hguar
    have hdlt : (env.get i₀ + -env.get (i₀ + 4 + 4)).val < 2 ^ 16 :=
      val_lt_65536_of_mul_inv_four_lt hlt
    have hdmod : (env.get i₀ + -env.get (i₀ + 4 + 4)).val % 4 = 0 :=
      val_mod_four_of_mul_inv_four_lt hlt
    have hlsble : (env.get (i₀ + 4 + 4)).val ≤ 1 := by
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rcases h_lsb with h | h <;> rw [h] <;> simp [ZMod.val_one]
    have hp : 2 ^ 17 < p := Fact.out
    have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    have e17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
    have hav0 : (env.get i₀).val
        = (env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 4 + 4)).val := by
      conv_lhs => rw [show env.get i₀
        = (env.get i₀ + -env.get (i₀ + 4 + 4)) + env.get (i₀ + 4 + 4) from by ring]
      rw [ZMod.val_add_of_lt (by omega)]
    have hav3 : (env.get (i₀ + 3)).val = 0 := by rw [h_av3]; simp
    have e32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    have e48 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
    simp only [JalrChip.nextPcWord, Word.toBitVec64, Word.toNat_def, Vector.getElem_map,
      Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero, circuit_norm]
    -- goal: `ofNat 64 (toNat nextPcWord) = ~~~1#64 &&& ofNat 64 (toNat add_value)`; the two sums differ
    -- only by `lsb` in the low limb (`add_value[3] = 0`), so `ofNat64_clear_lsb_and` closes it.
    have hMeven : ((env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 1)).val * 2 ^ 16
        + (env.get (i₀ + 2)).val * 2 ^ 32 + 0 * 2 ^ 48) % 2 = 0 := by omega
    have hrel : (env.get i₀).val + (env.get (i₀ + 1)).val * 2 ^ 16 + (env.get (i₀ + 2)).val * 2 ^ 32
          + (env.get (i₀ + 3)).val * 2 ^ 48
        = ((env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 1)).val * 2 ^ 16
            + (env.get (i₀ + 2)).val * 2 ^ 32 + 0 * 2 ^ 48) + (env.get (i₀ + 4 + 4)).val := by
      rw [hav0, hav3]; ring
    rw [sub_eq_add_neg, hrel]
    exact ofNat64_clear_lsb_and hlsble hMeven
  · -- RegisterWrite op_a write push: `isU64` of the written link value `op_a_value`. On `rd ≠ x0`
    -- (`op_a_0 = 0`) it is the link add result `pc + 4` (`spec_populate.1`); on `rd = x0` (`op_a_0 = 1`)
    -- the `op_a_0` zeroing gates pin every limb to `0`.
    intro hr1
    replace hr1 : input_is_real = 1 := hr1
    rcases h_op_a_0 with h0 | h0
    · have hg1 : input_is_real + - input_adapter_op_a_0 = 1 := by rw [hr1, h0]; simp
      exact (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩ hg1).1
    · obtain ⟨z0, z1, z2, z3⟩ := h_it.1
      rw [h0, one_mul] at z0 z1 z2 z3
      refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
        simp only [Vector.getElem_mapRange, circuit_norm] <;> simp_all

set_option maxHeartbeats 2000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU, h_oap, h_bin, h_op_a_0, h_cpu, h_rac_a, h_rac_b, h_jt3, h_lt3,
    h_align_pa, hdec, h_st⟩ := h_assumptions
  -- op_b (rs1) read-prior `isU64` in the reader's **raw** `prev_value` form (from the reconstructed
  -- `h_rs1U`), for the pure-read `ITypeReader.Spec`'s memory-pull `isU64` pair.
  have hpb_raw : Word.isU64 input_adapter_op_b_memory_prev_value := by
    have he : (#v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]]
          : Word (ZMod p)) = input_adapter_op_b_memory_prev_value := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    rwa [he] at h_rs1U
  simp only [jumpTargetWord, linkTargetWord, lsbBit, rs1WordI] at h_jt3 h_lt3 h_align_pa
  -- `h_env` now bundles the two add-result + `lsb` witness-gen equations with the GFC `ITypeReader`
  -- subcircuit's completeness obligation (4th conjunct, discarded — the reader slot is discharged below).
  obtain ⟨he_av, he_oav, he_lsb, -, _⟩ := h_env
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, hcimm⟩ := h_input
  have rb0 : Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0]
      = input_adapter_op_b_memory_prev_value[0] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb1 : Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1]
      = input_adapter_op_b_memory_prev_value[1] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb2 : Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2]
      = input_adapter_op_b_memory_prev_value[2] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have rb3 : Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]
      = input_adapter_op_b_memory_prev_value[3] := by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [rb0, rb1, rb2, rb3]
  have hrs1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have ci0 : Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0]
      = input_adapter_op_c_imm[0] := by rw [← hcimm]; simp only [Vector.getElem_map]
  have ci1 : Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1]
      = input_adapter_op_c_imm[1] := by rw [← hcimm]; simp only [Vector.getElem_map]
  have ci2 : Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2]
      = input_adapter_op_c_imm[2] := by rw [← hcimm]; simp only [Vector.getElem_map]
  have ci3 : Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]
      = input_adapter_op_c_imm[3] := by rw [← hcimm]; simp only [Vector.getElem_map]
  have hcimm_eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := by
    rw [← hcimm]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have ep0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
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
  have h_gate2 : input_is_real + - input_adapter_op_a_0 = 0 ∨ input_is_real + - input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨?_, ⟨h_bin, h_cpu, h_st⟩, ⟨⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨hpceq ▸ h_pcU, h4U⟩, h_gate2⟩, ?_⟩,
    ?_, ⟨⟨h_bin, h_bin⟩, ⟨hz _, hz _, hz _, hz _⟩, Or.inl h_op_a_0, h_rac_a, h_rac_b, hdec,
      fun hr => ⟨h_oap hr, hpb_raw⟩⟩,
    ⟨⟨h_bin, ?_⟩, trivial⟩, ?_, ?_⟩
  · rcases hlsb_bin with h | h <;> rw [h] <;> simp
  · rw [hval1]; exact AddOperation.spec_populate hrs1U h_imm input_is_real
  · rw [hav3]; exact h_jt3
  · rw [hval2]; exact AddOperation.spec_populate (hpceq ▸ h_pcU) h4U (input_is_real + - input_adapter_op_a_0)
  · rw [hoav3]; exact h_lt3
  · -- RegisterWrite op_a write push: `isU64` of the link value `pc + 4` (completeness covers `op_a_0 = 0`).
    intro hr
    rw [hval2]
    exact (AddOperation.spec_populate (hpceq ▸ h_pcU) h4U (input_is_real + - input_adapter_op_a_0)
      (by rw [h_op_a_0]; simpa using hr)).1
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
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate alignment byte-pull `Requirements` is discharged by
  -- the inline `is_real` boolean gate in `main`; the residual buses are the readers'/add-ops'.
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel, programChannel,
        AddOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit,
        Readers.RegisterWrite.circuit]; grind,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair so the chip is a
    -- `VmTables` table. `next_pc` is the **witnessed** LSB-cleared jump target the chip feeds `CPUState`:
    -- low limb `add_value[0] - lsb` (cells `offset+0` minus `offset+8`), high limbs `add_value[1..2]`.
    exposedChannels := fun input offset =>
      stateChannel.expose
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             var ⟨offset⟩ - var ⟨offset + 8⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
        List.map_cons, List.map_nil]
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.ITypeReader.circuit, Readers.ITypeReader.main,
        Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.JalrChip
