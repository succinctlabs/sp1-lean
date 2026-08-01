import SP1Clean.Proofs.Chips.ShiftRightChip.Defs
import SP1Clean.Proofs.Chips.ShiftRightChip.Math
import SP1Clean.Proofs.Chips.ShiftRightChip.Flags
import SP1Clean.Proofs.CircuitProofStart

/-! # `ShiftRightChip` — srlw conjunct soundness (split for parallel compilation)

Logical word right-shift (SRLW) conjunct, proved as a standalone `GeneralFormalCircuit.Soundness`
over a single-conjunct local `Spec`. -/

namespace SP1Clean.ShiftRightChip.SoundSrlw

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The `srlw` conjunct of `ShiftRightChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_srlw = 1 →
      Word.toBitVec64 cols.a = RV64.srlw (Word.toBitVec64 input.adapter.op_c_memory.prev_value)
        (Word.toBitVec64 input.adapter.op_b_memory.prev_value))

set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 800000 in
/-- Soundness of the `srlw` conjunct (verbatim slice of the monolithic proof + the shared tail). -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_early_struct
  obtain ⟨h_cpu, h_msb1, h_msb2, h_msb3, h_alu, h_regwrite, h_realgate, h_realeq,
    h_srl_b, h_sra_b, h_srlw_b, h_sraw_b, h_sum_b, h_core,
    h_byte0, h_byte1, h_byte2, h_byte3, h_byte4, h_byte5, h_byte6, h_byte7, h_byte8⟩ := h_holds
  have h_core' := h_core trivial
  simp only [ShiftRightCore.circuit, ShiftRightChip.CoreSpec, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm] at h_core'
  obtain ⟨h_wimm, h_b0, h_b1, h_b2, h_b3, h_b4, h_b5,
    h_s0w, h_s0b, h_s1w, h_s1b, h_s2w, h_s2b, h_s3w, h_s3b, h_onehot,
    h_v01, h_v012, h_v0123,
    h_split0, h_split1, h_split2, h_split3,
    h_lr0, h_lr1, h_lr2, h_lr3,
    h_msbz, h_smv, h_srwz,
    h_o0, h_o1, h_o2, h_o3, h_o4, h_o5, h_o6, h_o7,
    h_o8, h_o9, h_o10, h_o11, h_o12, h_o13, h_o14, h_o15,
    h_w0, h_w1, h_w2, h_w3, h_w4, h_w5,
    h_opa0⟩ := h_core'
  -- W11 Option B: the op_a write `RegisterWrite` push's `isU64 a` requirement, via the shared result
  -- range-check `resultA_isU64` applied to this row's destructured constraints.
  have h_obmap : Vector.map (Expression.eval env) input_var_adapter_op_b_memory_prev_value =
      input_adapter_op_b_memory_prev_value := by
    obtain ⟨-, -, -, -, -, -, ⟨h, -, -⟩, -, -, -⟩ := h_input; exact h
  -- `resultA_isU64` deliberately keeps its `x * (x + -1) = 0` parameter forms (shared by all four
  -- Soundness files); `h_holds`'s destructured hyps are now `x - y` form (4.30 circuit_norm), and the
  -- rest of this proof relies on that `-` form downstream, so convert local COPIES (never mutate the
  -- originals) just for this one call.
  have h_srl_b2 := h_srl_b; have h_sra_b2 := h_sra_b; have h_srlw_b2 := h_srlw_b
  have h_sraw_b2 := h_sraw_b; have h_sum_b2 := h_sum_b; have h_b0_2 := h_b0
  have h_b1_2 := h_b1; have h_b2_2 := h_b2; have h_b3_2 := h_b3; have h_b4_2 := h_b4
  have h_s0b2 := h_s0b; have h_s1w2 := h_s1w; have h_s1b2 := h_s1b; have h_s2w2 := h_s2w
  have h_s2b2 := h_s2b; have h_s3w2 := h_s3w; have h_s3b2 := h_s3b
  have h_onehot2 := h_onehot; have h_v01_2 := h_v01; have h_v012_2 := h_v012
  have h_v0123_2 := h_v0123; have h_split2_2 := h_split2
  have h_lr0_2 := h_lr0; have h_lr1_2 := h_lr1; have h_lr2_2 := h_lr2; have h_lr3_2 := h_lr3
  have h_smv2 := h_smv
  have h_o0_2 := h_o0; have h_o1_2 := h_o1; have h_o2_2 := h_o2; have h_o3_2 := h_o3
  have h_o4_2 := h_o4; have h_o5_2 := h_o5; have h_o6_2 := h_o6; have h_o7_2 := h_o7
  have h_o8_2 := h_o8; have h_o9_2 := h_o9; have h_o10_2 := h_o10; have h_o11_2 := h_o11
  have h_o12_2 := h_o12; have h_o13_2 := h_o13; have h_o14_2 := h_o14; have h_o15_2 := h_o15
  have h_w0_2 := h_w0; have h_w1_2 := h_w1; have h_w2_2 := h_w2
  have h_w3_2 := h_w3; have h_w4_2 := h_w4; have h_w5_2 := h_w5
  have h_byte2_2 := h_byte2; have h_byte4_2 := h_byte4
  have h_byte6_2 := h_byte6; have h_byte8_2 := h_byte8
  simp only [sub_eq_add_neg] at h_srl_b2 h_sra_b2 h_srlw_b2 h_sraw_b2 h_sum_b2 h_b0_2 h_b1_2 h_b2_2
  simp only [sub_eq_add_neg] at h_b3_2 h_b4_2 h_s0b2 h_s1w2 h_s1b2 h_s2w2 h_s2b2 h_s3w2 h_s3b2
  simp only [sub_eq_add_neg] at h_onehot2 h_v01_2 h_v012_2 h_v0123_2 h_split2_2 h_lr0_2 h_lr1_2
  simp only [sub_eq_add_neg] at h_lr2_2 h_lr3_2 h_smv2 h_o0_2 h_o1_2 h_o2_2 h_o3_2 h_o4_2 h_o5_2
  simp only [sub_eq_add_neg] at h_o6_2 h_o7_2 h_o8_2 h_o9_2 h_o10_2 h_o11_2 h_o12_2 h_o13_2 h_o14_2
  simp only [sub_eq_add_neg] at h_o15_2 h_w0_2 h_w1_2 h_w2_2 h_w3_2 h_w4_2 h_w5_2
  simp only [sub_eq_add_neg] at h_byte2_2 h_byte4_2 h_byte6_2 h_byte8_2
  have hregW := resultA_isU64 i₀ env h_obmap h_assumptions.1 h_msb1 h_msb3 h_srl_b2 h_sra_b2
    h_srlw_b2 h_sraw_b2 h_sum_b2 h_b0_2 h_b1_2 h_b2_2 h_b3_2 h_b4_2 (by simpa using h_s0w)
    h_s0b2 h_s1w2 h_s1b2 h_s2w2
    h_s2b2 h_s3w2 h_onehot2 h_v01_2 h_v012_2 h_v0123_2 h_split2_2 h_lr0_2 h_lr1_2 h_lr2_2 h_lr3_2
    h_smv2 h_o0_2 h_o1_2 h_o2_2 h_o3_2 h_o4_2 h_o5_2 h_o6_2 h_o7_2 h_o8_2 h_o9_2 h_o10_2 h_o11_2
    h_o12_2 h_o13_2 h_o14_2 h_o15_2 h_w0_2 h_w1_2 h_w2_2 h_w3_2 h_w4_2 h_w5_2 h_byte1 h_byte2_2
    h_byte3 h_byte4_2 h_byte5 h_byte6_2 h_byte7 h_byte8_2
  -- post-#398 the nine byte receives owe no padding requirement.
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee for `ALUTypeReader`'s two read-back pushes
  -- (`clk_low + 3` / `+ 2`), which `main` composes at the chip's own `is_real` selector. The offset is
  -- left to unification, so this line never names the destructured state columns. `RegisterWrite`'s
  -- op_a write push is composed at the *committed flag sum* instead; `main`'s bind `h_realeq`
  -- (`is_real - (is_srl + is_sra + is_srlw + is_sraw) = 0`, mirroring `ShiftLeftChip.main`)
  -- identifies the two, so that push's clock bound is derived here as well.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu (bool_of_mul_pred h_realgate))
  refine ⟨?spec, ?aluA,
    Or.inr ⟨bool_of_mul_pred h_sum_b, hregW,
      fun hgate => h_clk.at_four (by linear_combination h_realeq + hgate)⟩,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0,
    fun h1 h0 => off_gate_vacuous (bool_of_mul_pred h_sum_b) h1 h0⟩
  case spec =>
      intro hreal hsrlw
      -- `is_srlw = 1` forces the other three variant flags to 0 (single-op selection).
      obtain ⟨h_srl0, h_sra0, h_sraw0⟩ :=
        single_flag hsrlw (bool_of_mul_pred h_srl_b) (bool_of_mul_pred h_sra_b)
          (bool_of_mul_pred h_sraw_b)
          (by rcases bool_of_mul_pred h_sum_b with h | h
              · exact Or.inl (by linear_combination h)
              · exact Or.inr (by linear_combination h))
      -- `b_msb = 0` on SRLW (no SRA/SRAW sign): from `(is_srl + is_srlw) * b_msb = 0` with `is_srl = 0`.
      have h_bmsb0 : env.get (i₀ + 4) = 0 := by
        have hh := h_msbz; rw [h_srl0, hsrlw] at hh; simpa using hh
      have hcolsa : (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + i }) : Word (ZMod p))
          = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)] := by
        apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i <;> rfl
      obtain ⟨h_rs1U, h_rs2U⟩ := h_assumptions
      set cb0 := env.get (i₀ + 4 + 1 + 1) with hcb0_def
      set cb1 := env.get (i₀ + 4 + 1 + 1 + 1) with hcb1_def
      set cb2 := env.get (i₀ + 4 + 1 + 1 + 2) with hcb2_def
      set cb3 := env.get (i₀ + 4 + 1 + 1 + 3) with hcb3_def
      set cb4 := env.get (i₀ + 4 + 1 + 1 + 4) with hcb4_def
      set cb5 := env.get (i₀ + 4 + 1 + 1 + 5) with hcb5_def
      set ll0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3) with hll0_def
      set ll1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) with hll1_def
      set ll2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) with hll2_def
      set ll3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) with hll3_def
      set hl0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) with hhl0_def
      set hl1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) with hhl1_def
      set hl2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) with hhl2_def
      set hl3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) with hhl3_def
      have hsum1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = 1 := by
        rw [h_srl0, h_sra0, hsrlw, h_sraw0]; ring
      have hsumneg : -(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
          + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 := by rw [hsum1]
      have hbyte_fact : ∀ {v w : ZMod p},
          (-(env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2)
              + env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3)) = -1 →
            byteChannel.Guarantees (⟨6, v, w, 0⟩
              : ByteRow (ZMod p)) env.data) → v.val < 2 ^ w.val := by
        intro v w hb
        exact byteRowSpec_range_val (hb hsumneg)
      have lt_ll0 := hbyte_fact h_byte1
      have lt_lh0 := hbyte_fact h_byte2
      have lt_ll1 := hbyte_fact h_byte3
      have lt_lh1 := hbyte_fact h_byte4
      have lt_ll2 := hbyte_fact h_byte5
      have lt_lh2 := hbyte_fact h_byte6
      have lt_ll3 := hbyte_fact h_byte7
      have lt_lh3 := hbyte_fact h_byte8
      have b_cb0 := bool_of_mul_pred h_b0
      have b_cb1 := bool_of_mul_pred h_b1
      have b_cb2 := bool_of_mul_pred h_b2
      have b_cb3 := bool_of_mul_pred h_b3
      have b_cb4 := bool_of_mul_pred h_b4
      have b_cb5 := bool_of_mul_pred h_b5
      set v0123 := env.get (i₀ + 4 + 1 + 1 + 6 + 1) with hv0123_def
      set v012 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) with hv012_def
      set v01 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) with hv01_def
      clear_value cb0 cb1 cb2 cb3 cb4 cb5 ll0 ll1 ll2 ll3 hl0 hl1 hl2 hl3 v0123 v012 v01
      obtain ⟨-, -, -, -, -, -, ⟨h_obmap, -, -⟩, -, ⟨h_ocmap, -, -⟩, -⟩ := h_input
      have hb0e : Expression.eval env input_var_adapter_op_b_memory_prev_value[0]
          = input_adapter_op_b_memory_prev_value[0] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hb1e : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
          = input_adapter_op_b_memory_prev_value[1] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hb2e : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
          = input_adapter_op_b_memory_prev_value[2] := by rw [← h_obmap]; simp only [Vector.getElem_map]
      have hc0e : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
          = input_adapter_op_c_memory_prev_value[0] := by rw [← h_ocmap]; simp only [Vector.getElem_map]
      have eq_v01 : v01 = (1 + -cb0 + 1) * 2 * ((1 + -cb1) * 3 + 1) := by
        linear_combination h_v01
      have eq_v012 : v012 = v01 * ((1 + -cb2) * 15 + 1) := by
        linear_combination h_v012
      have eq_v0123 : v0123 = v012 * ((1 + -cb3) * 255 + 1) := by
        linear_combination h_v0123
      have h_b0_dec : input_adapter_op_b_memory_prev_value[0] * v0123
          = hl0 * ((65536 : ℕ) : ZMod p) + ll0 * v0123 := by
        have h := h_split0; push_cast; linear_combination h
      have h_b1_dec : input_adapter_op_b_memory_prev_value[1] * v0123
          = hl1 * ((65536 : ℕ) : ZMod p) + ll1 * v0123 := by
        have h := h_split1; push_cast; linear_combination h
      -- limb-2 split is de-gated (e14 = 0) on SRLW, forcing `ll2 = 0` — drops `ll2·v0123` from limb_result[1].
      have h_split2_dec : hl2 * 65536 + ll2 * v0123 = 0 := by
        have h := h_split2; rw [h_srl0, h_sra0] at h; linear_combination -h
      -- Bridge the byte-pull range facts to the `srlw_close_su16_*_case`/`limb_result_lt` exponent form.
      rw [cb4sum_natCast] at lt_ll0 lt_ll1 lt_ll2 lt_ll3
      simp only [sub_eq_add_neg] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
      rw [cb4sum_sub_natCast] at lt_lh0 lt_lh1 lt_lh2 lt_lh3
      have hp17 : 2 ^ 17 < p := Fact.out
      have hne2 : (2 : ZMod p) ≠ 0 := by
        intro h; have := val_2_zmod_p (p := p); rw [h, ZMod.val_zero] at this; exact absurd this (by norm_num)
      have hne3 : (3 : ZMod p) ≠ 0 := by
        intro h; have h3 : (3 : ZMod p).val = 3 := val_3_zmod_p
        rw [h, ZMod.val_zero] at h3; exact absurd h3 (by norm_num)
      -- `ll2 = 0`.
      obtain ⟨-, h_ll2_0⟩ := ShiftRightMath.higher_lower_zero b_cb0 b_cb1 b_cb2 b_cb3
        eq_v01 eq_v012 eq_v0123 lt_lh2 lt_ll2 h_split2_dec
      -- The shift count `op_c[0].val % 32` as the 5-bit `c_bits` sum.
      have h_c0mod32 : input_adapter_op_c_memory_prev_value[0].val % 32
          = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 : ZMod p).val := by
        refine ShiftRightMath.is_mod_32 b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5 (by simpa using h_rs2U 0) ?_
        have he := hbyte_fact h_byte0
        rw [hc0e] at he
        have h10v : ((10 : ZMod p)).val = 10 := by
          rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) by push_cast; rfl]
          exact ZMod.val_natCast_of_lt (by omega)
        rw [h10v, show (2 : ℕ) ^ 10 = 1024 by norm_num] at he
        simpa using he
      -- Alias the byte-shift selectors + limb_result; one-hot + reassembly.
      set su0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) with hsu0_def
      set su1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) with hsu1_def
      set su2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) with hsu2_def
      set su3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) with hsu3_def
      set lr0 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4) with hlr0_def
      set lr1 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) with hlr1_def
      set lr2 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2) with hlr2_def
      set lr3 := env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) with hlr3_def
      set smv := env.get (i₀ + 4 + 1 + 1 + 6) with hsmv_def
      set srwmsb := env.get (i₀ + 5) with hsrwmsb_def
      clear_value su0 su1 su2 su3 lr0 lr1 lr2 lr3 smv srwmsb
      have honehot1 : su0 + su1 + su2 + su3 = 1 := by
        have hh := h_onehot; rw [hsum1] at hh; linear_combination hh
      have eq_lr0 : lr0 = hl0 + ll1 * v0123 := by
        linear_combination h_lr0
      have eq_lr1 : lr1 = hl1 + ll2 * v0123 := by
        linear_combination h_lr1
      have hsmv0 : smv = 0 := by
        have hh := h_smv; rw [h_bmsb0] at hh; linear_combination hh
      -- `a[2] = a[3] = srwmsb·65535` from the e13-gated high-fill asserts (e13 = is_srlw + is_sraw = 1).
      have a2eq : env.get (i₀ + 2) = srwmsb * 65535 := by
        have hh := h_w4; rw [hsrlw, h_sraw0] at hh; linear_combination hh
      have a3eq : env.get (i₀ + 3) = srwmsb * 65535 := by
        have hh := h_w5; rw [hsrlw, h_sraw0] at hh; linear_combination hh
      rw [hcolsa]
      rcases b_cb4 with hcb4 | hcb4
      · -- byteShift = 0 (su0 = 1): a[0] = limb_result[0], a[1] = limb_result[1] = hl1.
        have su1z : su1 = 0 := by
          have hh := h_s1w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su2z : su2 = 0 := by
          have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su3z : su3 = 0 := by
          have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su0o : su0 = 1 := by
          have hh := honehot1; rw [su1z, su2z, su3z] at hh; simpa using hh
        have ha0 : env.get i₀ = lr0 := by
          have hh := h_w0; rw [hsrlw, h_sraw0, su0o] at hh; linear_combination hh
        have ha1 : env.get (i₀ + 1) = lr1 := by
          have hh := h_w1; rw [hsrlw, h_sraw0, su0o, h_bmsb0, hsmv0] at hh
          linear_combination hh
        have hr0 : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[0].val < 2 ^ 16 := by
          show (env.get i₀).val < 2 ^ 16
          rw [ha0, eq_lr0]
          exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh0 lt_ll1
        have hr1 : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[1].val < 2 ^ 16 := by
          show (env.get (i₀ + 1)).val < 2 ^ 16
          rw [ha1, eq_lr1]
          exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
        have hm : srwmsb = if (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[1].val ≥ 32768 then 1 else 0 := by
          show srwmsb = if (env.get (i₀ + 1)).val ≥ 32768 then 1 else 0
          have hsp := (h_msb3 ⟨fun _ => by
              show (env.get (i₀ + 1)).val < 2 ^ 16
              rw [ha1, eq_lr1]
              exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123
                lt_lh1 lt_ll2,
            Or.inr (by rw [hsrlw, h_sraw0]; ring)⟩).2 (by rw [hsrlw, h_sraw0]; ring)
          simpa using hsp
        refine srlw_div_to_bitvec _ _ _ h_rs1U h_rs2U srwmsb hr0 hr1 hm ?_ ?_ ?_
        · show env.get (i₀ + 2) = srwmsb * 65535
          exact a2eq
        · show env.get (i₀ + 3) = srwmsb * 65535
          exact a3eq
        · show (ShiftRightMath.HWord.toBitVec32 #v[env.get i₀, env.get (i₀ + 1)]).toNat
              = (ShiftRightMath.HWord.toBitVec32 #v[input_adapter_op_b_memory_prev_value[0],
                  input_adapter_op_b_memory_prev_value[1]]).toNat
                / 2 ^ (input_adapter_op_c_memory_prev_value[0].val % 32)
          rw [ha0, ha1, eq_lr0, eq_lr1, h_ll2_0, zero_mul, add_zero, h_c0mod32]
          exact ShiftRightMath.srlw_dispatch_0 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
      · -- byteShift = 1 (su1 = 1): a[0] = limb_result[1] = hl1, a[1] = bmsbFill = 0.
        have su0z : su0 = 0 := by
          have hh := h_s0w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su2z : su2 = 0 := by
          have hh := h_s2w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su3z : su3 = 0 := by
          have hh := h_s3w; rw [hcb4, h_srl0, h_sra0] at hh; simp at hh
          first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])
        have su1o : su1 = 1 := by
          have hh := honehot1; rw [su0z, su2z, su3z] at hh; simpa using hh
        have ha0 : env.get i₀ = lr1 := by
          have hh := h_w2; rw [hsrlw, h_sraw0, su1o, h_bmsb0, hsmv0] at hh
          linear_combination hh
        have ha1 : env.get (i₀ + 1) = 0 := by
          have hh := h_w3; rw [hsrlw, h_sraw0, su1o, h_bmsb0] at hh
          linear_combination hh
        have hr0 : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[0].val < 2 ^ 16 := by
          show (env.get i₀).val < 2 ^ 16
          rw [ha0, eq_lr1]
          exact ShiftRightMath.limb_result_lt b_cb0 b_cb1 b_cb2 b_cb3 eq_v01 eq_v012 eq_v0123 lt_lh1 lt_ll2
        have hr1 : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[1].val < 2 ^ 16 := by
          show (env.get (i₀ + 1)).val < 2 ^ 16
          rw [ha1, ZMod.val_zero]; omega
        have hm : srwmsb = if (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2),
              env.get (i₀ + 3)] : Word (ZMod p))[1].val ≥ 32768 then 1 else 0 := by
          show srwmsb = if (env.get (i₀ + 1)).val ≥ 32768 then 1 else 0
          have hsp := (h_msb3 ⟨fun _ => by
              show (env.get (i₀ + 1)).val < 2 ^ 16
              rw [ha1, ZMod.val_zero]; omega,
            Or.inr (by rw [hsrlw, h_sraw0]; ring)⟩).2 (by rw [hsrlw, h_sraw0]; ring)
          simpa using hsp
        refine srlw_div_to_bitvec _ _ _ h_rs1U h_rs2U srwmsb hr0 hr1 hm ?_ ?_ ?_
        · show env.get (i₀ + 2) = srwmsb * 65535
          exact a2eq
        · show env.get (i₀ + 3) = srwmsb * 65535
          exact a3eq
        · show (ShiftRightMath.HWord.toBitVec32 #v[env.get i₀, env.get (i₀ + 1)]).toNat
              = (ShiftRightMath.HWord.toBitVec32 #v[input_adapter_op_b_memory_prev_value[0],
                  input_adapter_op_b_memory_prev_value[1]]).toNat
                / 2 ^ (input_adapter_op_c_memory_prev_value[0].val % 32)
          rw [ha0, ha1, eq_lr1, h_ll2_0, zero_mul, add_zero, h_c0mod32]
          exact ShiftRightMath.srlw_dispatch_1 b_cb0 b_cb1 b_cb2 b_cb3 hcb4 eq_v01 eq_v012 eq_v0123
            lt_ll0 lt_lh0 lt_ll1 lt_lh1 h_b0_dec h_b1_dec
  -- CPUState has no required channel; ALUTypeReader assumes `is_real` binary from the in-circuit gate.
  case aluA => exact Or.inr ⟨bool_of_mul_pred h_realgate, bool_of_mul_pred h_realgate,
    h_clk⟩
  -- The MSB gadgets expose empty requirement lists canonically; their local semantic
  -- assumptions no longer leak into the parent chip's channel-requirement tail.
end SP1Clean.ShiftRightChip.SoundSrlw
