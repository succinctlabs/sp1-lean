import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Tail

/-! # `DivRemChip` — `remu` conjunct soundness (split for parallel compilation)

Unsigned-64-bit REMU conjunct, proved as a standalone `GeneralFormalCircuit.Soundness` over a
single-conjunct local `Spec`. -/

namespace SP1Clean.DivRemChip.SoundRemu

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The `remu` conjunct of `DivRemChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_remu = 1 →
      Word.toBitVec64 cols.a = RV64.remu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

set_option maxHeartbeats 128000000 in
set_option linter.unusedSimpArgs false in
/-- Soundness of the `remu` conjunct. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  apply soundness_of_specObligation
  spec_proof_start
  -- `Assumptions` lives in `Defs` (an enclosing namespace here, not a current-namespace member as in
  -- `Formal`), so `circuit_proof_start`'s `dsimp only [Assumptions]` doesn't fire; project via
  -- `.1`/`.2` (whnf-unfolds the `def`) rather than `rcases`/`obtain`.
  have hbU := h_assumptions.1
  have hcU := h_assumptions.2
  obtain ⟨h_mul_lo, h_mul_hi,
    h_ctq0, h_ctq1, h_ctq2, h_ctq3, h_ctq4, h_ctq5, h_ctq6, h_ctq7,
    h_eqb, h_eqc, h_eqb2, h_eqc2, h_isc0, h_addc, h_addr, h_lt,
    h_msb0, h_msb1, h_msb2, h_msb3, h_msb4, h_msb5, h_msb6, h_cpu, h_rtype, h_own,
    hb_e123, hb_e127, hb_e131, hb_e135, hb_e139, hb_e143, hb_e147, hb_e151,
    hb_absc0, hb_absc1, hb_absc2, hb_absc3, hb_absr0, hb_absr1, hb_absr2, hb_absr3,
    hb_q0, hb_q1, hb_q2, hb_q3, hb_r0, hb_r1, hb_r2, hb_r3,
    hb_ctq0, hb_ctq1, hb_ctq2, hb_ctq3, hb_ctq4, hb_ctq5, hb_ctq6, hb_ctq7,
    hb_e2r1, hb_e2q1, _h_regwrite⟩ := h_holds
  simp only [ownAsserts] at h_own
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23, e29, e35, e41, e47, e48, e49, e51, e54, e57, e59,
    e61, e64, e67, e69, e70, e71, e73, e76, e79, e81, e83, e86, e89, e91, e96, e99, e103, e105, e107,
    e109, e111, e113, e115, e117, e119, e154, e157, e160, e163, e167, e171, e175, e179, e184, e189,
    e194, e199, e204, e209, e214, e219, e225, e228, e230, e232, e234, e236, e238, e240, e242, e244,
    e247, e250, e253, e256, e259, e262, e265, e268, e270, e272, e274, e276, e278, e280, e282, e284,
    e286, e288, e299, e300, e301, e302, e305, e307, e309, e311, e313, e315, e317, e319, e321, e323,
    e325, e327, e329, e331, e333, e335, e337, e339, e341, e343, e345, e347, e349, e351, e353, e355,
    e357, e359, e367, eopa0⟩ := h_own
  · intro hr
    set input_op_b_val : Word (ZMod p) :=
      Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + i }) with hbdef
    set input_op_c_val : Word (ZMod p) :=
      Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i }) with hcdef
    set input_var_op_b_val : Vector (Expression (ZMod p)) 4 :=
      Vector.mapRange 4 (fun i => var { index := i₀ + 8 + 4 + 4 + i }) with hvbdef
    set input_var_op_c_val : Vector (Expression (ZMod p)) 4 :=
      Vector.mapRange 4 (fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i }) with hvcdef
    simp only [circuit_norm] at e325 e327 e329 e331 e333 e335 e337 e339 e367
    have bd := bool_of_mul_pred e325; have bdu := bool_of_mul_pred e327
    have br := bool_of_mul_pred e329; have bru := bool_of_mul_pred e331
    have bdw := bool_of_mul_pred e333; have brw := bool_of_mul_pred e335
    have bduw := bool_of_mul_pred e337; have bruw := bool_of_mul_pred e339
    have hvalsum := flags_val_sum bd bdu br bru bdw brw bduw bruw (by linear_combination -e367)
    intro hflag
    have hdu : (env.get (i₀ + 3)).val = 1 := by rw [hflag]; exact ZMod.val_one p
    have hz_div : env.get i₀ = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divu : env.get (i₀ + 1) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_rem : env.get (i₀ + 2) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divw : env.get (i₀ + 4) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remw : env.get (i₀ + 5) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divuw : env.get (i₀ + 6) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remuw : env.get (i₀ + 7) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    -- For REMU (`e2 = 0`) the operands equal the raw reads (E20–E47), giving operand `isU64` + read-lift.
    have hbeq : input_op_b_val = input_adapter_op_b_memory_prev_value := by
      obtain ⟨-, -, -, -, -, -, ⟨h_obx, -, -⟩, -, -⟩ := h_input
      have e20' := e20; have e22' := e22; have e29' := e29; have e41' := e41
      simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        at e20' e22' e29' e41'
      rw [hz_divw, hz_remw, hz_divuw, hz_remuw] at e29' e41'
      rw [← h_obx]; apply Vector.ext; intro i hi
      interval_cases i <;>
        simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm] <;>
        first
          | linear_combination e20' | linear_combination -e20'
          | linear_combination e22' | linear_combination -e22'
          | linear_combination e29' | linear_combination -e29'
          | linear_combination e41'
    have hceq : input_op_c_val = input_adapter_op_c_memory_prev_value := by
      obtain ⟨-, -, -, -, -, -, -, -, ⟨h_ocx, -, -⟩⟩ := h_input
      have e21' := e21; have e23' := e23; have e35' := e35; have e47' := e47
      simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        at e21' e23' e35' e47'
      rw [hz_divw, hz_remw, hz_divuw, hz_remuw] at e35' e47'
      rw [← h_ocx]; apply Vector.ext; intro i hi
      interval_cases i <;>
        simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm] <;>
        first
          | linear_combination e21' | linear_combination -e21'
          | linear_combination e23' | linear_combination -e23'
          | linear_combination e35' | linear_combination -e35'
          | linear_combination e47'
    have hbU : Word.isU64 input_op_b_val := by rw [hbeq]; exact h_assumptions.1
    have hcU : Word.isU64 input_op_c_val := by rw [hceq]; exact h_assumptions.2
    simp only [circuit_norm] at e15 e17 e19 e48 e49 e59 e69 e70 e71 e81 e91 e96 e154 e157 e160 e163 e167 e171 e175 e179 e189 e199 e209 e219 e230 e232 e234 e236 e238 e240 e242 e244 e247 e250 e253 e256 e259 e262 e265 e268 e299 e300 e301 e302 e305 e307 e309 e311 e313 e315 e317 e319 e321 e323 e355
    set B := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 with hBdef
    have hov : env.get B = 0 := by
      rw [hz_div, hz_rem, hz_divw, hz_remw] at e96; linear_combination e96
    have hbneg0 : env.get (B + 1) = 0 := by
      rw [hz_div, hz_rem, hz_divw, hz_remw] at e15; linear_combination -e15
    have hrneg0 : env.get (B + 5) = 0 := by
      rw [hz_div, hz_rem, hz_divw, hz_remw] at e17; linear_combination -e17
    have hcneg0 : env.get (B + 6) = 0 := by
      rw [hz_div, hz_rem, hz_divw, hz_remw] at e19; linear_combination -e19
    rw [hov] at e154 e157 e160 e163 e167 e171 e175 e179
    rw [hbneg0, hrneg0] at e167 e171 e175 e179
    have hL0 : env.get (B + 7) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)
        = Expression.eval env input_var_op_b_val[0] + env.get (B + 7 + 8) * 65536 := by
      linear_combination e154
    have hL1 : env.get (B + 7 + 1) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) + env.get (B + 7 + 8)
        = Expression.eval env input_var_op_b_val[1] + env.get (B + 7 + 8 + 1) * 65536 := by
      linear_combination e157
    have hL2 : env.get (B + 7 + 2) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) + env.get (B + 7 + 8 + 1)
        = Expression.eval env input_var_op_b_val[2] + env.get (B + 7 + 8 + 2) * 65536 := by
      linear_combination e160
    have hL3 : env.get (B + 7 + 3) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) + env.get (B + 7 + 8 + 2)
        = Expression.eval env input_var_op_b_val[3] + env.get (B + 7 + 8 + 3) * 65536 := by
      linear_combination e163
    have hH4 : env.get (B + 7 + 4) + env.get (B + 7 + 8 + 3) = env.get (B + 7 + 8 + 4) * 65536 := by
      linear_combination e167
    have hH5 : env.get (B + 7 + 5) + env.get (B + 7 + 8 + 4) = env.get (B + 7 + 8 + 5) * 65536 := by
      linear_combination e171
    have hH6 : env.get (B + 7 + 6) + env.get (B + 7 + 8 + 5) = env.get (B + 7 + 8 + 6) * 65536 := by
      linear_combination e175
    have hH7 : env.get (B + 7 + 7) + env.get (B + 7 + 8 + 6) = env.get (B + 7 + 8 + 7) * 65536 := by
      linear_combination e179
    have hc0 := bool_of_mul_pred e309
    have hc1 := bool_of_mul_pred e311
    have hc2 := bool_of_mul_pred e313
    have hc3 := bool_of_mul_pred e315
    have hc4 := bool_of_mul_pred e317
    have hc5 := bool_of_mul_pred e319
    have hc6 := bool_of_mul_pred e321
    have hc7 := bool_of_mul_pred e323
    obtain ⟨h_oir, -, -, -, -, -, ⟨h_ob, -, -⟩, -, ⟨h_oc, -, -⟩⟩ := h_input
    have hrneg' : -input_is_real = -1 := by rw [hr]
    have hbb0 : Expression.eval env input_var_op_b_val[0] = input_op_b_val[0] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb1 : Expression.eval env input_var_op_b_val[1] = input_op_b_val[1] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb2 : Expression.eval env input_var_op_b_val[2] = input_op_b_val[2] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb3 : Expression.eval env input_var_op_b_val[3] = input_op_b_val[3] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hihm0 : env.get i₀ + env.get (i₀ + 2) = 0 := by rw [hz_div, hz_rem]; ring
    have hihmu1 : env.get (i₀ + 1) + env.get (i₀ + 3) = 1 := by rw [hz_divu, hflag]; ring
    have hgateD : env.get (i₀ + 1) + env.get (i₀ + 3) + env.get i₀ + env.get (i₀ + 2) = 1 := by
      rw [hz_divu, hflag, hz_div, hz_rem]; ring
    have hq0 : (env.get (i₀ + 8)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4)
          from by linear_combination e48]
      exact isU16_of_byteRowSpec (hb_q0 hrneg')
    have hq1 : (env.get (i₀ + 8 + 1)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8 + 1)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1)
          from by linear_combination e49]
      exact isU16_of_byteRowSpec (hb_q1 hrneg')
    have hq2 : (env.get (i₀ + 8 + 2)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8 + 2)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 2)
          from by have h := e59; rw [hgateD, one_mul] at h; linear_combination h]
      exact isU16_of_byteRowSpec (hb_q2 hrneg')
    have hq3 : (env.get (i₀ + 8 + 3)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8 + 3)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 3)
          from by have h := e69; rw [hgateD, one_mul] at h; linear_combination h]
      exact isU16_of_byteRowSpec (hb_q3 hrneg')
    have hqU : Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      exacts [hq0, hq1, hq2, hq3]
    have hr0 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)).val < 2 ^ 16 := by
      rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1)
          from by linear_combination e70]
      exact isU16_of_byteRowSpec (hb_r0 hrneg')
    have hr1 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)).val < 2 ^ 16 := by
      rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1)
          from by linear_combination e71]
      exact isU16_of_byteRowSpec (hb_r1 hrneg')
    have hr2 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)).val < 2 ^ 16 := by
      rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 2)
          from by have h := e81; rw [hgateD, one_mul] at h; linear_combination h]
      exact isU16_of_byteRowSpec (hb_r2 hrneg')
    have hr3 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)).val < 2 ^ 16 := by
      rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3)
          from by have h := e91; rw [hgateD, one_mul] at h; linear_combination h]
      exact isU16_of_byteRowSpec (hb_r3 hrneg')
    have hrU : Word.isU64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) :=
      Word.isU64_of_cases hr0 hr1 hr2 hr3
    have hrwloU : Word.isU64 (#v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2),
        env.get (B + 7 + 3)] : Word (ZMod p)) :=
      Word.isU64_of_cases (isU16_of_byteRowSpec (hb_ctq0 hrneg'))
        (isU16_of_byteRowSpec (hb_ctq1 hrneg')) (isU16_of_byteRowSpec (hb_ctq2 hrneg'))
        (isU16_of_byteRowSpec (hb_ctq3 hrneg'))
    have hrwhiU : Word.isU64 (#v[env.get (B + 7 + 4), env.get (B + 7 + 5), env.get (B + 7 + 6),
        env.get (B + 7 + 7)] : Word (ZMod p)) :=
      Word.isU64_of_cases (isU16_of_byteRowSpec (hb_ctq4 hrneg'))
        (isU16_of_byteRowSpec (hb_ctq5 hrneg')) (isU16_of_byteRowSpec (hb_ctq6 hrneg'))
        (isU16_of_byteRowSpec (hb_ctq7 hrneg'))
    have hlo := rwlo_product h_mul_lo hqU hcU hr
      (by simpa only [Vector.getElem_map] using h_ctq0)
      (by simpa only [Vector.getElem_map] using h_ctq1)
      (by simpa only [Vector.getElem_map] using h_ctq2)
      (by simpa only [Vector.getElem_map] using h_ctq3)
    -- `is_real_not_word = 1` (E13, word flags zero), the upper-Mul gate; then de-gate the four
    -- upper glue equalities (the 64-bit flag sum is `1` on a REMU row).
    have hirnw : env.get (B + 4) = 1 := by
      have h := e13; simp only [circuit_norm] at h
      rw [hz_divw, hz_remw, hz_divuw, hz_remuw, h_oir, hr] at h
      linear_combination h
    have h_ctq4' := h_ctq4; have h_ctq5' := h_ctq5
    have h_ctq6' := h_ctq6; have h_ctq7' := h_ctq7
    rw [hz_div, hz_divu, hz_rem, hflag] at h_ctq4' h_ctq5' h_ctq6' h_ctq7'
    simp only [add_zero, zero_add, one_mul, ← sub_eq_add_neg, sub_eq_zero]
      at h_ctq4' h_ctq5' h_ctq6' h_ctq7'
    have hhi := rwhi_product_unsigned h_mul_hi hqU hcU hirnw hihm0 hihmu1
      (by simpa only [circuit_norm, Vector.getElem_mapRange] using h_ctq4')
      (by simpa only [circuit_norm, Vector.getElem_mapRange] using h_ctq5')
      (by simpa only [circuit_norm, Vector.getElem_mapRange] using h_ctq6')
      (by simpa only [circuit_norm, Vector.getElem_mapRange] using h_ctq7')
    have hcl0 : env.get (B + 7) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)
        = input_op_b_val[0] + env.get (B + 7 + 8) * 65536 := by rw [← hbb0]; exact hL0
    have hcl1 : env.get (B + 7 + 1) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)
        + env.get (B + 7 + 8) = input_op_b_val[1] + env.get (B + 7 + 8 + 1) * 65536 := by
      rw [← hbb1]; exact hL1
    have hcl2 : env.get (B + 7 + 2) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)
        + env.get (B + 7 + 8 + 1) = input_op_b_val[2] + env.get (B + 7 + 8 + 2) * 65536 := by
      rw [← hbb2]; exact hL2
    have hcl3 : env.get (B + 7 + 3) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
        + env.get (B + 7 + 8 + 2) = input_op_b_val[3] + env.get (B + 7 + 8 + 3) * 65536 := by
      rw [← hbb3]; exact hL3
    have hid := hid_of_carry_chain (b := input_op_b_val) (c := input_op_c_val)
      (quotient := Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }))
      (remainder := #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
        env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)])
      (rwlo := #v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)])
      (rwhi := #v[env.get (B + 7 + 4), env.get (B + 7 + 5), env.get (B + 7 + 6), env.get (B + 7 + 7)])
      (carry := #v[env.get (B + 7 + 8), env.get (B + 7 + 8 + 1), env.get (B + 7 + 8 + 2),
        env.get (B + 7 + 8 + 3), env.get (B + 7 + 8 + 4), env.get (B + 7 + 8 + 5),
        env.get (B + 7 + 8 + 6), env.get (B + 7 + 8 + 7)])
      hcU hbU hqU hrU hrwloU hrwhiU hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      hcl0 hcl1 hcl2 hcl3 hH4 hH5 hH6 hH7 hlo hhi
    have hzero : Word.toNat input_op_c_val = 0 →
        Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) = 2 ^ 64 - 1 ∧
        Word.toNat (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))
            = Word.toNat input_op_b_val := by
      intro hc0
      have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
      obtain ⟨hcb0, hcb1, hcb2, hcb3⟩ := Word.lt_cases_of_isU64 hcU
      rw [Word.toNat_def] at hc0
      have hca0 : input_op_c_val[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hca1 : input_op_c_val[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hca2 : input_op_c_val[2] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hca3 : input_op_c_val[3] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      rw [if_pos ⟨hca0, hca1, hca2, hca3⟩] at hsem
      dsimp only at hsem
      rw [field_fromElements_one] at hsem
      simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
        Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
      rw [iszeroword_result_proj] at e230 e232 e234 e236 e238 e240 e242 e244
      simp only [Vector.getElem_mapRange, circuit_norm] at e230 e232 e234 e236 e238 e240 e242 e244
      rw [hsem, one_mul] at e230 e232 e234 e236 e238 e240 e242 e244
      have h59' := e59; rw [hgateD, one_mul] at h59'
      have h69' := e69; rw [hgateD, one_mul] at h69'
      refine ⟨?_, ?_⟩
      · rw [Word.toNat_def]; simp only [circuit_norm, Nat.add_zero]
        rw [show env.get (i₀ + 8) = (65535 : ZMod p) from by linear_combination e48 + e230,
            show env.get (i₀ + 8 + 1) = (65535 : ZMod p) from by linear_combination e49 + e232,
            show env.get (i₀ + 8 + 2) = (65535 : ZMod p) from by linear_combination h59' + e234,
            show env.get (i₀ + 8 + 3) = (65535 : ZMod p) from by linear_combination h69' + e236]
        simp only [val_65535_zmod_p]; norm_num
      · have q0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = input_op_b_val[0] := by
          rw [← hbb0]; linear_combination e238
        have q1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) = input_op_b_val[1] := by
          rw [← hbb1]; linear_combination e240
        have q2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) = input_op_b_val[2] := by
          rw [← hbb2]; linear_combination e242
        have q3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) = input_op_b_val[3] := by
          rw [← hbb3]; linear_combination e244
        rw [Word.toNat_def, Word.toNat_def]
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
        rw [q0, q1, q2, q3]
    have hlt : Word.toNat input_op_c_val ≠ 0 →
        Word.toNat (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))
            < Word.toNat input_op_c_val := by
      intro hcne
      have hcc0 : Expression.eval env input_var_op_c_val[0] = input_op_c_val[0] := by
        simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
        simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
        simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
        simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
      have hcnz : ¬ (input_op_c_val[0] = 0 ∧ input_op_c_val[1] = 0 ∧ input_op_c_val[2] = 0
          ∧ input_op_c_val[3] = 0) := by
        rintro ⟨z0, z1, z2, z3⟩; exact hcne (by rw [Word.toNat_def, z0, z1, z2, z3]; simp)
      rw [if_neg hcnz] at hsem
      dsimp only at hsem
      rw [field_fromElements_one] at hsem
      simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
        Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
      rw [iszeroword_result_proj] at e299 e300 e301 e302 e305
      simp only [Vector.getElem_mapRange, circuit_norm] at e299 e300 e301 e302 e305
      rw [hsem] at e299 e300 e301 e302 e305
      have hrcm : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 2) = 1 := by
        rw [show Expression.eval env input_var_is_real = (1 : ZMod p) from by rw [h_oir]; exact hr]
          at e305
        linear_combination -e305
      have habsrU : Word.isU64 (Vector.map (Expression.eval env)
          (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i })
          : Word (ZMod p)) := by
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        exacts [isU16_of_byteRowSpec (hb_absr0 hrneg'), isU16_of_byteRowSpec (hb_absr1 hrneg'),
          isU16_of_byteRowSpec (hb_absr2 hrneg'), isU16_of_byteRowSpec (hb_absr3 hrneg')]
      have hm0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11) := by linear_combination e299
      have hm1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 1)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 1) := by linear_combination e300
      have hm2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 2)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 2) := by linear_combination e301
      have hm3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 3)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 3) := by linear_combination e302
      have hmaxU : Word.isU64 (Vector.map (Expression.eval env)
          (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i })
          : Word (ZMod p)) := by
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · rw [hm0]; exact isU16_of_byteRowSpec (hb_absc0 hrneg')
        · rw [hm1]; exact isU16_of_byteRowSpec (hb_absc1 hrneg')
        · rw [hm2]; exact isU16_of_byteRowSpec (hb_absc2 hrneg')
        · rw [hm3]; exact isU16_of_byteRowSpec (hb_absc3 hrneg')
      have hbit := (LtOperationUnsigned.result_semantic habsrU hmaxU hrcm
        (h_lt ⟨fun _ => ⟨habsrU, hmaxU⟩, Or.inr hrcm⟩)).1
      have hbiteq : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1)
          = 1 := by have h := e307; rw [hrcm, one_mul] at h; linear_combination -h
      rw [hbiteq] at hbit
      have hcmp : Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i })
            : Word (ZMod p))
          < Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i })
            : Word (ZMod p)) := by
        by_contra hcon; rw [if_neg hcon] at hbit; exact one_ne_zero hbit
      have habsr_eq : Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i })
            : Word (ZMod p))
          = Word.toNat (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
        rw [Word.toNat_def, Word.toNat_def]
        simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) from by
              have h := e250; rw [hrneg0] at h; linear_combination h,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 1)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) from by
              have h := e256; rw [hrneg0] at h; linear_combination h,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 2)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) from by
              have h := e262; rw [hrneg0] at h; linear_combination h,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 3)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) from by
              have h := e268; rw [hrneg0] at h; linear_combination h]
      have hmax_eq : Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i })
            : Word (ZMod p))
          = Word.toNat input_op_c_val := by
        rw [Word.toNat_def, Word.toNat_def]
        simp only [circuit_norm, Nat.add_zero]
        rw [hm0, hm1, hm2, hm3,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11) = input_op_c_val[0] from by
              have h := e247; rw [hcneg0] at h; linear_combination h + hcc0,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 1) = input_op_c_val[1] from by
              have h := e253; rw [hcneg0] at h; linear_combination h + hcc1,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 2) = input_op_c_val[2] from by
              have h := e259; rw [hcneg0] at h; linear_combination h + hcc2,
            show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 3) = input_op_c_val[3] from by
              have h := e265; rw [hcneg0] at h; linear_combination h + hcc3]
      rw [habsr_eq, hmax_eq] at hcmp
      exact hcmp
    -- === STAGE 4: route the pair's remainder (`.2`) to `cols.a` (= remainder = remainder_comp) ===
    have hpair := divu_remu_of_identity hbU hcU hqU hrU hid hlt hzero
    have hgateRem : env.get (i₀ + 3) + env.get (i₀ + 2) + env.get (i₀ + 5) + env.get (i₀ + 7) = 1 := by
      rw [hflag, hz_rem, hz_remw, hz_remuw]; ring
    have hb0 : env.get (i₀ + 8 + 4) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) := by
      have h := e189; rw [hgateRem, one_mul] at h; linear_combination -h - e70
    have hb1 : env.get (i₀ + 8 + 4 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) := by
      have h := e199; rw [hgateRem, one_mul] at h; linear_combination -h - e71
    have hb2 : env.get (i₀ + 8 + 4 + 2) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) := by
      have h := e209; rw [hgateRem, one_mul] at h
      have h81' := e81; rw [hgateD, one_mul] at h81'
      linear_combination -h - h81'
    have hb3 : env.get (i₀ + 8 + 4 + 3) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) := by
      have h := e219; rw [hgateRem, one_mul] at h
      have h91' := e91; rw [hgateD, one_mul] at h91'
      linear_combination -h - h91'
    have haqc : (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))
        = #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
          env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
          env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
          env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] := by
      apply Vector.ext; intro i hi
      interval_cases i <;> simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exacts [hb0, hb1, hb2, hb3]
    rw [hbeq, hceq] at hpair; rw [haqc]; exact hpair.2

end SP1Clean.DivRemChip.SoundRemu
