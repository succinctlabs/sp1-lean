import SP1Clean.Chips.DivRemChip.Defs
import SP1Clean.Chips.DivRemChip.Soundness
import SP1Clean.Chips.DivRemChip.Assembly

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
  circuit_proof_start
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
    hb_e2r1, hb_e2q1⟩ := h_holds
  simp only [ownAsserts] at h_own
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23, e29, e35, e41, e47, e48, e49, e51, e54, e57, e59,
    e61, e64, e67, e69, e70, e71, e73, e76, e79, e81, e83, e86, e89, e91, e96, e99, e103, e105, e107,
    e109, e111, e113, e115, e117, e119, e154, e157, e160, e163, e167, e171, e175, e179, e184, e189,
    e194, e199, e204, e209, e214, e219, e225, e228, e230, e232, e234, e236, e238, e240, e242, e244,
    e247, e250, e253, e256, e259, e262, e265, e268, e270, e272, e274, e276, e278, e280, e282, e284,
    e286, e288, e299, e300, e301, e302, e305, e307, e309, e311, e313, e315, e317, e319, e321, e323,
    e325, e327, e329, e331, e333, e335, e337, e339, e341, e343, e345, e347, e349, e351, e353, e355,
    e357, e359, e367, eopa0⟩ := h_own
  refine ⟨?_spec, ?_tail⟩
  · intro hr
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
    simp only [circuit_norm] at e15 e17 e19 e48 e49 e59 e69 e70 e71 e81 e91 e96 e154 e157 e160 e163 e167 e171 e175 e179 e189 e199 e209 e219 e230 e232 e234 e236 e238 e240 e242 e244 e247 e250 e253 e256 e259 e262 e265 e268 e299 e300 e301 e302 e305 e307 e309 e311 e313 e315 e317 e319 e321 e323 e355
    set B := i₀ + 8 + 4 + 4 + 45 + 45 with hBdef
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
    obtain ⟨h_ob, h_oc, h_oir, -⟩ := h_input
    have hrneg' : -input_is_real = -1 := by rw [hr]
    have hbb0 : Expression.eval env input_var_op_b_val[0] = input_op_b_val[0] := by
      rw [← h_ob]; simp [Vector.getElem_map]
    have hbb1 : Expression.eval env input_var_op_b_val[1] = input_op_b_val[1] := by
      rw [← h_ob]; simp [Vector.getElem_map]
    have hbb2 : Expression.eval env input_var_op_b_val[2] = input_op_b_val[2] := by
      rw [← h_ob]; simp [Vector.getElem_map]
    have hbb3 : Expression.eval env input_var_op_b_val[3] = input_op_b_val[3] := by
      rw [← h_ob]; simp [Vector.getElem_map]
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
    have hhi := rwhi_product_unsigned h_mul_hi hqU hcU hr hihm0 hihmu1
      (by simpa only [Vector.getElem_map] using h_ctq4)
      (by simpa only [Vector.getElem_map] using h_ctq5)
      (by simpa only [Vector.getElem_map] using h_ctq6)
      (by simpa only [Vector.getElem_map] using h_ctq7)
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
        rw [← h_oc]; simp [Vector.getElem_map]
      have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
        rw [← h_oc]; simp [Vector.getElem_map]
      have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
        rw [← h_oc]; simp [Vector.getElem_map]
      have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
        rw [← h_oc]; simp [Vector.getElem_map]
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
    rw [haqc]; exact hpair.2
  · obtain ⟨h_ob, h_oc, h_oir, -⟩ := h_input
    set B := i₀ + 8 + 4 + 4 + 45 + 45 with hBdef
    have hbin : input_is_real = 0 ∨ input_is_real = 1 := by
      have h := e355; simp only [circuit_norm] at h; rw [h_oir] at h; exact bool_of_mul_pred h
    simp only [circuit_norm] at e325 e327 e329 e331 e333 e335 e337 e339 e367
    have bd := bool_of_mul_pred e325; have bdu := bool_of_mul_pred e327
    have br := bool_of_mul_pred e329; have bru := bool_of_mul_pred e331
    have bdw := bool_of_mul_pred e333; have brw := bool_of_mul_pred e335
    have bduw := bool_of_mul_pred e337; have bruw := bool_of_mul_pred e339
    have hvs := flags_val_sum bd bdu br bru bdw brw bduw bruw (by linear_combination -e367)
    have he2 : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 0 ∨
        env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 :=
      group_binary4 bdw brw bduw bruw (by omega)
    have hsel5 := group_binary4 bdu bru bd br (by omega)
    have hsel6 := group_binary2 bdw brw (by omega)
    have hsel7 := group_binary2 bduw bruw (by omega)
    have hsum567 : env.get (i₀ + 1) + env.get (i₀ + 3) + env.get i₀ + env.get (i₀ + 2)
        + (env.get (i₀ + 4) + env.get (i₀ + 5)) + (env.get (i₀ + 6) + env.get (i₀ + 7)) = 1 := by
      linear_combination -e367
    have hms6 := h_msb6 ⟨fun he2g => isU16_of_byteRowSpec (hb_e2q1 (by linear_combination -he2g)), he2⟩
    have hms5 := h_msb5 ⟨fun he2g => isU16_of_byteRowSpec (hb_e2r1 (by linear_combination -he2g)), he2⟩
    have hquotmsb := hms6.1
    have hremmsb := hms5.1
    have hqcU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      simp only [circuit_norm] at e48 e49 e51 e54 e59 e61 e64 e69
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [show env.get (i₀ + 8) = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+4)
            from by linear_combination e48]
        exact isU16_of_byteRowSpec (hb_q0 hrneg')
      · rw [show env.get (i₀ + 8 + 1) = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+4+1)
            from by linear_combination e49]
        exact isU16_of_byteRowSpec (hb_q1 hrneg')
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e59 e54 e51
          hquotmsb (isU16_of_byteRowSpec (hb_q2 hrneg'))
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e69 e64 e61
          hquotmsb (isU16_of_byteRowSpec (hb_q3 hrneg'))
    have hrcU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      simp only [circuit_norm] at e70 e71 e73 e76 e81 e83 e86 e91
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [show env.get (B + 7+8+8+11+11+11+4+4)
            = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1) from by linear_combination e70]
        exact isU16_of_byteRowSpec (hb_r0 hrneg')
      · rw [show env.get (B + 7+8+8+11+11+11+4+4+1)
            = env.get (B + 7+8+8+11+11+11+4+4+4+4+4+4+3+2+4+1+1+1) from by linear_combination e71]
        exact isU16_of_byteRowSpec (hb_r1 hrneg')
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e81 e76 e73
          hremmsb (isU16_of_byteRowSpec (hb_r2 hrneg'))
      · exact comp_limb_isU16 hsel5 hsel6 hsel7 hsum567 e91 e86 e83
          hremmsb (isU16_of_byteRowSpec (hb_r3 hrneg'))
    have habscU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      exacts [isU16_of_byteRowSpec (hb_absc0 hrneg'), isU16_of_byteRowSpec (hb_absc1 hrneg'),
        isU16_of_byteRowSpec (hb_absc2 hrneg'), isU16_of_byteRowSpec (hb_absc3 hrneg')]
    have habsrU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      exacts [isU16_of_byteRowSpec (hb_absr0 hrneg'), isU16_of_byteRowSpec (hb_absr1 hrneg'),
        isU16_of_byteRowSpec (hb_absr2 hrneg'), isU16_of_byteRowSpec (hb_absr3 hrneg')]
    have hbb1 : Expression.eval env input_var_op_b_val[1] = input_op_b_val[1] := by
      rw [← h_ob]; simp [Vector.getElem_map]
    have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
      rw [← h_oc]; simp [Vector.getElem_map]
    have hbb3 : Expression.eval env input_var_op_b_val[3] = input_op_b_val[3] := by
      rw [← h_ob]; simp [Vector.getElem_map]
    have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
      rw [← h_oc]; simp [Vector.getElem_map]
    -- `is_real_not_word` (E13 = `is_real * (1 - e2)`): binary, and `= 1 → is_real = 1 ∧ e2 = 0`.
    have h13t := e13; simp only [circuit_norm] at h13t; rw [h_oir] at h13t
    have hirnw : env.get (B + 4) = 0 ∨ env.get (B + 4) = 1 := by
      rcases hbin with h | h
      · left; rw [h] at h13t; linear_combination h13t
      · rcases he2 with h2 | h2
        · right; rw [h, h2] at h13t; linear_combination h13t
        · left; rw [h, h2] at h13t; linear_combination h13t
    have hirnw_imp : env.get (B + 4) = 1 →
        input_is_real = 1 ∧
          env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 0 := by
      intro hir
      rcases hbin with h | h
      · exfalso; rw [h, hir] at h13t; exact one_ne_zero (by linear_combination h13t)
      · rcases he2 with h2 | h2
        · exact ⟨h, h2⟩
        · exfalso; rw [h, h2, hir] at h13t; exact one_ne_zero (by linear_combination h13t)
    -- `max_abs_c_or_1` is `isU64`: `is_c_0 = 1 → #v[1,0,0,0]` (c = 0 branch), else `= abs_c` (E299-302).
    have hmaxU : input_is_real = 1 → Word.isU64 (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := B + 7+8+8+11+11+11+4+4+4 + i }) : Word (ZMod p)) := by
      intro hr
      have hrneg' : -input_is_real = -1 := by rw [hr]
      have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
      have h299 := e299; have h300 := e300; have h301 := e301; have h302 := e302
      simp only [circuit_norm] at h299 h300 h301 h302
      rw [iszeroword_result_proj] at h299 h300 h301 h302
      simp only [Vector.getElem_mapRange, circuit_norm] at h299 h300 h301 h302
      by_cases hcz : input_op_c_val[0] = 0 ∧ input_op_c_val[1] = 0 ∧ input_op_c_val[2] = 0
          ∧ input_op_c_val[3] = 0
      · rw [if_pos hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [hsem] at h299 h300 h301 h302
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
          rw [show env.get (B + 7+8+8+11+11+11+4+4+4) = 1 from by linear_combination h299,
            ZMod.val_one]; norm_num
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 1) = 0 from by linear_combination h300]; simp
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 2) = 0 from by linear_combination h301]; simp
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 3) = 0 from by linear_combination h302]; simp
      · rw [if_neg hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [hsem] at h299 h300 h301 h302
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4) = env.get (B + 7+8+8+11+11+11)
              from by linear_combination h299]
          exact isU16_of_byteRowSpec (hb_absc0 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 1) = env.get (B + 7+8+8+11+11+11 + 1)
              from by linear_combination h300]
          exact isU16_of_byteRowSpec (hb_absc1 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 2) = env.get (B + 7+8+8+11+11+11 + 2)
              from by linear_combination h301]
          exact isU16_of_byteRowSpec (hb_absc2 hrneg')
        · rw [show env.get (B + 7+8+8+11+11+11+4+4+4 + 3) = env.get (B + 7+8+8+11+11+11 + 3)
              from by linear_combination h302]
          exact isU16_of_byteRowSpec (hb_absc3 hrneg')
    refine ⟨?mulLo, ?mulHi, ?eqb, ?eqc, ?eqb2, ?eqc2, ?isc0, ?addc, ?addr, ?lt,
      ?msb0, ?msb1, ?msb2, ?msb3, ?msb4, ?msb5, ?msb6, ?cpu, ?rtype, ?own⟩
    case own => simp only [circuit_norm, assertZeros, forAllNoOffset_map_assert]
    case eqb => exact Or.inl rfl
    case eqc => exact Or.inl rfl
    case eqb2 => exact Or.inl rfl
    case eqc2 => exact Or.inl rfl
    case isc0 => exact Or.inl rfl
    case cpu => exact Or.inr hbin
    case rtype => exact Or.inr hbin
    case mulLo =>
      exact Or.inr ⟨fun hr => ⟨hqcU hr, hcU⟩, hbin, fun h => (zero_ne_one h).elim, hbin,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, by rcases hbin with h | h <;> simp [h]⟩
    case mulHi =>
      refine Or.inr ⟨fun hr => ⟨hqcU hr, hcU⟩, hbin, fun h => (zero_ne_one h).elim, Or.inl rfl,
        group_binary2 bd br (by omega), group_binary2 bdu bru (by omega), Or.inl rfl, Or.inl rfl, ?_⟩
      rcases group_binary4 bd br bdu bru (by omega) with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    case addc =>
      refine Or.inr ⟨fun hace => ?_, ?_⟩
      · have h286 := e286; simp only [circuit_norm] at h286
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h_oir, h, mul_zero, neg_zero, add_zero] at h286
            exact zero_ne_one (h286.symm.trans hace)
          · exact h
        exact ⟨hcU, habscU hr⟩
      · have h := e357; simp only [circuit_norm] at h; exact bool_of_mul_pred h
    case addr =>
      refine Or.inr ⟨fun hrae => ?_, ?_⟩
      · have h288 := e288; simp only [circuit_norm] at h288
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h_oir, h, mul_zero, neg_zero, add_zero] at h288
            exact zero_ne_one (h288.symm.trans hrae)
          · exact h
        exact ⟨hrcU hr, habsrU hr⟩
      · have h := e359; simp only [circuit_norm] at h; exact bool_of_mul_pred h
    case lt =>
      -- E305: `remainder_check_multiplicity = (1 - is_c_0.result) * is_real`.
      have h305 := e305; simp only [circuit_norm] at h305
      rw [iszeroword_result_proj] at h305
      simp only [Vector.getElem_mapRange, circuit_norm] at h305
      rw [h_oir] at h305
      refine Or.inr ⟨fun hrcm => ?_, ?_⟩
      · -- rcm = 1 → is_real = 1, then `abs_remainder`/`max_abs_c_or_1` are `isU64`.
        have hr : input_is_real = 1 := by
          rcases hbin with h | h
          · exfalso; rw [h] at h305; exact one_ne_zero (by linear_combination -h305 - hrcm)
          · exact h
        exact ⟨habsrU hr, hmaxU hr⟩
      · -- rcm binary: `(1 - is_c_0) * is_real` with `is_real`/`is_c_0` binary.
        rcases hbin with h | h
        · left; rw [h] at h305; linear_combination -h305
        · have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr h)) h
          by_cases hcz : input_op_c_val[0] = 0 ∧ input_op_c_val[1] = 0 ∧ input_op_c_val[2] = 0
              ∧ input_op_c_val[3] = 0
          · left
            rw [if_pos hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
            simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
              Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
            rw [h, hsem] at h305; linear_combination -h305
          · right
            rw [if_neg hcz] at hsem; dsimp only at hsem; rw [field_fromElements_one] at hsem
            simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
              Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
            rw [h, hsem] at h305; linear_combination -h305
    case msb0 =>
      refine Or.inr ⟨fun hirnwg => ?_, hirnw⟩
      obtain ⟨hr, he2z⟩ := hirnw_imp hirnwg
      have h41 := e41; simp only [circuit_norm] at h41; rw [he2z] at h41
      rw [show Expression.eval env input_var_adapter_op_b_memory_prev_value[3] = input_op_b_val[3]
          from by rw [← hbb3]; linear_combination -h41]
      exact (Word.lt_cases_of_isU64 hbU).2.2.2
    case msb1 =>
      refine Or.inr ⟨fun hirnwg => ?_, hirnw⟩
      obtain ⟨hr, he2z⟩ := hirnw_imp hirnwg
      have h47 := e47; simp only [circuit_norm] at h47; rw [he2z] at h47
      rw [show Expression.eval env input_var_adapter_op_c_memory_prev_value[3] = input_op_c_val[3]
          from by rw [← hcc3]; linear_combination -h47]
      exact (Word.lt_cases_of_isU64 hcU).2.2.2
    case msb2 =>
      refine Or.inr ⟨fun hirnwg => ?_, hirnw⟩
      obtain ⟨hr, -⟩ := hirnw_imp hirnwg
      have hrneg' : -input_is_real = -1 := by rw [hr]
      exact isU16_of_byteRowSpec (hb_r3 hrneg')
    case msb3 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      have h22 := e22; simp only [circuit_norm] at h22
      rw [show Expression.eval env input_var_adapter_op_b_memory_prev_value[1] = input_op_b_val[1]
          from by rw [← hbb1]; linear_combination h22]
      exact (Word.lt_cases_of_isU64 hbU).2.1
    case msb4 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      have h23 := e23; simp only [circuit_norm] at h23
      rw [show Expression.eval env input_var_adapter_op_c_memory_prev_value[1] = input_op_c_val[1]
          from by rw [← hcc1]; linear_combination h23]
      exact (Word.lt_cases_of_isU64 hcU).2.1
    case msb5 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2r1 (by linear_combination -he2g)), he2⟩
    case msb6 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2q1 (by linear_combination -he2g)), he2⟩

end SP1Clean.DivRemChip.SoundRemu
