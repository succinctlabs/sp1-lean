import SP1Clean.Chips.DivRemChip.Defs
import SP1Clean.Chips.DivRemChip.Soundness
import SP1Clean.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — `rem` conjunct soundness (split for parallel compilation)

Signed-64-bit REM conjunct, proved as a standalone `GeneralFormalCircuit.Soundness` over a
single-conjunct local `Spec`. -/

namespace SP1Clean.DivRemChip.SoundRem

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The `rem` conjunct of `DivRemChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_rem = 1 →
      Word.toBitVec64 cols.a = RV64.rem (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

set_option maxHeartbeats 128000000 in
set_option linter.unusedSimpArgs false in
/-- Soundness of the `rem` conjunct. -/
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
    have hdd : (env.get (i₀ + 2)).val = 1 := by rw [hflag]; exact ZMod.val_one p
    have hz_divu : env.get (i₀ + 1) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_div : env.get i₀ = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remu : env.get (i₀ + 3) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divw : env.get (i₀ + 4) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remw : env.get (i₀ + 5) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divuw : env.get (i₀ + 6) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remuw : env.get (i₀ + 7) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    simp only [circuit_norm] at e48 e49 e59 e69 e70 e71 e81 e91 e189 e199 e209 e219
    have hgateD : env.get (i₀ + 1) + env.get (i₀ + 3) + env.get i₀ + env.get (i₀ + 2) = 1 := by
      rw [hz_divu, hz_remu, hz_div, hflag]; ring
    -- the signed-64 identity on the `quotient_comp` column (= `quotient` for 64-bit, via E48/E59).
    have hrem_id : Word.toBitVec64 (#v[env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))
        = RV64.rem (Word.toBitVec64 input_op_c_val) (Word.toBitVec64 input_op_b_val) := by
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
      set B := i₀ + 8 + 4 + 4 + 45 + 45 with hBdef
      simp only [circuit_norm] at e70 e71 e81 e91 e230 e232 e234 e236 e238 e240 e242 e244
      -- `quotient_comp` is the byte-checked `quotient` column (E48/E49/E59/E69), hence `isU64`.
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
      by_cases hcz : input_op_c_val[0] = 0 ∧ input_op_c_val[1] = 0 ∧ input_op_c_val[2] = 0
          ∧ input_op_c_val[3] = 0
      · -- DIVZERO (`c = 0`): `quotient = -1`, `remainder = b` ⟹ `div_rem_divzero`.
        have hc0bv : Word.toBitVec64 input_op_c_val = 0#64 := by
          have hcn : Word.toNat input_op_c_val = 0 := by
            rw [Word.toNat_def, hcz.1, hcz.2.1, hcz.2.2.1, hcz.2.2.2]; simp
          rw [Word.toBitVec64, hcn]
        have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
        rw [if_pos hcz] at hsem
        dsimp only at hsem
        rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [iszeroword_result_proj] at e230 e232 e234 e236 e238 e240 e242 e244
        simp only [Vector.getElem_mapRange, circuit_norm] at e230 e232 e234 e236 e238 e240 e242 e244
        rw [hsem, one_mul] at e230 e232 e234 e236 e238 e240 e242 e244
        have h59' := e59; rw [hgateD, one_mul] at h59'
        have h69' := e69; rw [hgateD, one_mul] at h69'
        have hqm1 : Word.toBitVec64 (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) = -1#64 := by
          apply neg_one_of_toNat hqU
          rw [Word.toNat_def]; simp only [circuit_norm, Nat.add_zero]
          rw [show env.get (i₀ + 8) = (65535 : ZMod p) from by linear_combination e48 + e230,
              show env.get (i₀ + 8 + 1) = (65535 : ZMod p) from by linear_combination e49 + e232,
              show env.get (i₀ + 8 + 2) = (65535 : ZMod p) from by linear_combination h59' + e234,
              show env.get (i₀ + 8 + 3) = (65535 : ZMod p) from by linear_combination h69' + e236]
          simp only [val_65535_zmod_p]; norm_num
        have hrb : Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))
            = Word.toBitVec64 input_op_b_val := by
          rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hrU, Word.toBitVec64_toNat hbU]
          have q0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = input_op_b_val[0] := by
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
        exact (div_rem_divzero hc0bv hqm1 hrb).2
      · by_cases hovf : env.get B = 1
        · -- OVERFLOW (`is_overflow = 1`): `b = i64::MIN`, `c = -1`, `quotient = b`, `remainder = 0`.
          simp only [circuit_norm] at e105 e107 e109 e111 e113 e115 e117 e119
          have h59' := e59; rw [hgateD, one_mul] at h59'
          have h69' := e69; rw [hgateD, one_mul] at h69'
          -- `is_real_not_word = 1` (E13: real row, `E2 = 0`), the overflow `IsEqualWord` gate.
          have hirnw : env.get (B + 4) = 1 := by
            have h := e13; simp only [circuit_norm] at h
            rw [hz_divw, hz_remw, hz_divuw, hz_remuw, h_oir, hr] at h
            linear_combination h
          have hbsp := h_eqb (Or.inr hirnw)
          have hcsp := h_eqc (Or.inr hirnw)
          simp only [circuit_norm] at e96 e20 e21 e22 e23 e29 e35 e41 e47
          rw [hz_divw, hz_remw, hz_divuw, hz_remuw] at e29 e35 e41 e47
          have hcc0 : Expression.eval env input_var_op_c_val[0] = input_op_c_val[0] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          -- the eight `bpv ↔ op_b` / `cpv ↔ op_c` limb bridges (E20/E22/E29/E41 + c-analogues; `E2 = 0`).
          have qb0 : Expression.eval env input_var_adapter_op_b_memory_prev_value[0]
              = input_op_b_val[0] := by rw [← hbb0]; linear_combination e20
          have qb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
              = input_op_b_val[1] := by rw [← hbb1]; linear_combination e22
          have qb2 : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
              = input_op_b_val[2] := by rw [← hbb2]; linear_combination -e29
          have qb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
              = input_op_b_val[3] := by rw [← hbb3]; linear_combination -e41
          have qc0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
              = input_op_c_val[0] := by rw [← hcc0]; linear_combination e21
          have qc1 : Expression.eval env input_var_adapter_op_c_memory_prev_value[1]
              = input_op_c_val[1] := by rw [← hcc1]; linear_combination e23
          have qc2 : Expression.eval env input_var_adapter_op_c_memory_prev_value[2]
              = input_op_c_val[2] := by rw [← hcc2]; linear_combination -e35
          have qc3 : Expression.eval env input_var_adapter_op_c_memory_prev_value[3]
              = input_op_c_val[3] := by rw [← hcc3]; linear_combination -e47
          have hbpvW : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
              Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
              Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
              Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
              = input_op_b_val := by
            apply Vector.ext; intro i hi
            interval_cases i <;>
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                List.getElem_cons_succ]
            exacts [qb0, qb1, qb2, qb3]
          have hcpvW : (#v[Expression.eval env input_var_adapter_op_c_memory_prev_value[0],
              Expression.eval env input_var_adapter_op_c_memory_prev_value[1],
              Expression.eval env input_var_adapter_op_c_memory_prev_value[2],
              Expression.eval env input_var_adapter_op_c_memory_prev_value[3]] : Word (ZMod p))
              = input_op_c_val := by
            apply Vector.ext; intro i hi
            interval_cases i <;>
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                List.getElem_cons_succ]
            exacts [qc0, qc1, qc2, qc3]
          -- the overflow products force `b = i64::MIN`, `c = -1` (`overflow_of_iseqword`).
          have hpair := overflow_of_iseqword
            (by rw [hbpvW]; exact hbU) (by rw [hcpvW]; exact hcU) hirnw hbsp hcsp
            (by
              rw [iseqword_result_proj, iseqword_result_proj] at e96
              simp only [Vector.getElem_mapRange, circuit_norm] at e96
              have hE10 : env.get i₀ + env.get (i₀ + 2) + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by
                rw [hz_div, hflag, hz_divw, hz_remw]; ring
              rw [hovf, hE10, mul_one] at e96
              dsimp only
              rw [field_fromElements_one, field_fromElements_one]
              simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
                Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm]
              linear_combination -e96)
          have hb_im : Word.toBitVec64 input_op_b_val = BitVec.intMin 64 := by
            rw [← hbpvW]; exact hpair.1
          have hc_m1 : Word.toBitVec64 input_op_c_val = -1#64 := by
            rw [← hcpvW]; exact hpair.2
          -- `quotient_comp = b` (`E105/E109/E113/E117` pin `quotient = b` on the overflow branch;
          -- `E48/E49/E59/E69` bridge `quotient` to `quotient_comp`).
          have hqa0 : env.get (i₀ + 8) = input_op_b_val[0] := by
            have h := e105; rw [hovf, one_mul] at h; rw [← hbb0]; linear_combination e48 + h
          have hqa1 : env.get (i₀ + 8 + 1) = input_op_b_val[1] := by
            have h := e109; rw [hovf, one_mul] at h; rw [← hbb1]; linear_combination e49 + h
          have hqa2 : env.get (i₀ + 8 + 2) = input_op_b_val[2] := by
            have h := e113; rw [hovf, one_mul] at h; rw [← hbb2]; linear_combination h59' + h
          have hqa3 : env.get (i₀ + 8 + 3) = input_op_b_val[3] := by
            have h := e117; rw [hovf, one_mul] at h; rw [← hbb3]; linear_combination h69' + h
          have hq_eq : Word.toBitVec64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))
              = Word.toBitVec64 input_op_b_val := by
            rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hqU, Word.toBitVec64_toNat hbU,
              Word.toNat_def, Word.toNat_def]
            simp only [circuit_norm, Nat.add_zero]
            rw [hqa0, hqa1, hqa2, hqa3]
          -- `remainder_comp = 0` (`E107/E111/E115/E119` pin `remainder = 0`; `E70/E71/E81/E91` bridge).
          have hra0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = 0 := by
            have h := e107; rw [hovf, one_mul] at h; linear_combination e70 + h
          have hra1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) = 0 := by
            have h := e111; rw [hovf, one_mul] at h; linear_combination e71 + h
          have h81' := e81; rw [hgateD, one_mul] at h81'
          have h91' := e91; rw [hgateD, one_mul] at h91'
          have hra2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) = 0 := by
            have h := e115; rw [hovf, one_mul] at h; linear_combination h81' + h
          have hra3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) = 0 := by
            have h := e119; rw [hovf, one_mul] at h; linear_combination h91' + h
          have hr_eq : Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) = 0#64 := by
            rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hrU, Word.toNat_def]
            simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
              List.getElem_cons_succ]
            rw [hra0, hra1, hra2, hra3]; simp
          exact (div_rem_overflow hb_im hc_m1 hq_eq hr_eq).2
        · -- normal: signed Euclidean assembly (c≠0, no overflow). `b/c/quotient_comp/remainder_comp`
          -- in scope from the div setup; here de-gate the signed carry chain (`is_overflow = 0`),
          -- read the sign columns, and feed `euclid_identity_signed` + `assemble_signed_normal`.
          have hirnw : env.get (B + 4) = 1 := by
            have h := e13; simp only [circuit_norm] at h
            rw [hz_divw, hz_remw, hz_divuw, hz_remuw, h_oir, hr] at h
            linear_combination h
          simp only [circuit_norm] at e15 e17 e19 e41 e47 e154 e157 e160 e163 e167 e171 e175 e179 e309 e311 e313 e315 e317 e319 e321 e323 e341
          rw [hz_divw, hz_remw, hz_divuw, hz_remuw] at e41 e47
          -- `is_overflow = 0` (binary gate `E341`, and we are not the overflow branch).
          have hov0 : env.get B = 0 := by
            rcases bool_of_mul_pred e341 with h | h
            · exact h
            · exact absurd h hovf
          have hE10 : env.get i₀ + env.get (i₀ + 2) + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by
            rw [hz_div, hflag, hz_divw, hz_remw]; ring
          have hihm1 : env.get i₀ + env.get (i₀ + 2) = 1 := by rw [hz_div, hflag]; ring
          have hihmu0 : env.get (i₀ + 1) + env.get (i₀ + 3) = 0 := by rw [hz_divu, hz_remu]; ring
          have hgateD : env.get (i₀ + 1) + env.get (i₀ + 3) + env.get i₀ + env.get (i₀ + 2) = 1 := by
            rw [hz_divu, hz_remu, hz_div, hflag]; ring
          -- `c ≠ 0` (the normal branch's defining condition).
          have hc0bv : Word.toBitVec64 input_op_c_val ≠ 0#64 := by
            intro h
            apply hcz
            have hcn : Word.toNat input_op_c_val = 0 := by
              have := congrArg BitVec.toNat h
              rwa [Word.toBitVec64_toNat hcU, BitVec.toNat_zero] at this
            obtain ⟨c0, c1, c2, c3⟩ := Word.lt_cases_of_isU64 hcU
            rw [Word.toNat_def] at hcn
            exact ⟨(ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega),
              (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega)⟩
          -- limb bridges `bpv[3]=b[3]`, `cpv[3]=c[3]` (E2 = 0), for the sign-bit gadgets.
          have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have qb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
              = input_op_b_val[3] := by rw [← hbb3]; linear_combination -e41
          have qc3 : Expression.eval env input_var_adapter_op_c_memory_prev_value[3]
              = input_op_c_val[3] := by rw [← hcc3]; linear_combination -e47
          obtain ⟨_, _, _, hb3b⟩ := Word.lt_cases_of_isU64 hbU
          obtain ⟨_, _, _, hc3b⟩ := Word.lt_cases_of_isU64 hcU
          obtain ⟨_, _, _, hr3b⟩ := Word.lt_cases_of_isU64 hrU
          -- the routed `remainder[3]` (the U16MSB input) equals `remainder_comp[3]` (E90/E91).
          have hrem3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3) := by
            have h := e91; rw [hgateD, one_mul] at h; linear_combination h
          -- sign columns `b_neg = env(B+1)`, `c_neg = env(B+6)`, `rem_neg = env(B+5)`.
          have hbneg : env.get (B + 1) = if (Word.toBitVec64 input_op_b_val).msb then 1 else 0 := by
            have hbm := (h_msb0 ⟨fun _ => by rw [qb3]; exact hb3b, Or.inr hirnw⟩).2 hirnw
            dsimp only at hbm
            have hb1 : env.get (B + 1)
                = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4) := by
              have h := e15; rw [hE10, mul_one] at h; linear_combination -h
            rw [hb1, hbm]
            refine if_congr ?_ rfl rfl
            rw [qb3]; exact (toBitVec64_msb_iff hbU).symm
          have hcneg : env.get (B + 6) = if (Word.toBitVec64 input_op_c_val).msb then 1 else 0 := by
            have hcm := (h_msb1 ⟨fun _ => by rw [qc3]; exact hc3b, Or.inr hirnw⟩).2 hirnw
            dsimp only at hcm
            have hc1 : env.get (B + 6)
                = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1) := by
              have h := e19; rw [hE10, mul_one] at h; linear_combination -h
            rw [hc1, hcm]
            refine if_congr ?_ rfl rfl
            rw [qc3]; exact (toBitVec64_msb_iff hcU).symm
          have hrneg : env.get (B + 5)
              = if (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb
                then 1 else 0 := by
            have hrm := (h_msb2 ⟨fun _ => by rw [← hrem3]; exact hr3b, Or.inr hirnw⟩).2 hirnw
            dsimp only at hrm
            have hr1 : env.get (B + 5)
                = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1) := by
              have h := e17; rw [hE10, mul_one] at h; linear_combination -h
            rw [hr1, hrm]
            refine if_congr ?_ rfl rfl
            rw [← hrem3]; exact (toBitVec64_msb_iff hrU).symm
          -- de-gate the eight signed carry-chain limb equations (`is_overflow = 0`, keeping sign fills).
          have hl0 : env.get (B + 7) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)
              = input_op_b_val[0] + env.get (B + 7 + 8) * 65536 := by
            have h := e154; rw [hov0] at h; rw [← hbb0]; linear_combination h
          have hl1 : env.get (B + 7 + 1) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)
              + env.get (B + 7 + 8) = input_op_b_val[1] + env.get (B + 7 + 8 + 1) * 65536 := by
            have h := e157; rw [hov0] at h; rw [← hbb1]; linear_combination h
          have hl2 : env.get (B + 7 + 2) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)
              + env.get (B + 7 + 8 + 1) = input_op_b_val[2] + env.get (B + 7 + 8 + 2) * 65536 := by
            have h := e160; rw [hov0] at h; rw [← hbb2]; linear_combination h
          have hl3 : env.get (B + 7 + 3) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
              + env.get (B + 7 + 8 + 2) = input_op_b_val[3] + env.get (B + 7 + 8 + 3) * 65536 := by
            have h := e163; rw [hov0] at h; rw [← hbb3]; linear_combination h
          have hh4 : env.get (B + 7 + 4) + env.get (B + 5) * 65535 + env.get (B + 7 + 8 + 3)
              = env.get (B + 1) * 65535 + env.get (B + 7 + 8 + 4) * 65536 := by
            have h := e167; rw [hov0] at h; linear_combination h
          have hh5 : env.get (B + 7 + 5) + env.get (B + 5) * 65535 + env.get (B + 7 + 8 + 4)
              = env.get (B + 1) * 65535 + env.get (B + 7 + 8 + 5) * 65536 := by
            have h := e171; rw [hov0] at h; linear_combination h
          have hh6 : env.get (B + 7 + 6) + env.get (B + 5) * 65535 + env.get (B + 7 + 8 + 5)
              = env.get (B + 1) * 65535 + env.get (B + 7 + 8 + 6) * 65536 := by
            have h := e175; rw [hov0] at h; linear_combination h
          have hh7 : env.get (B + 7 + 7) + env.get (B + 5) * 65535 + env.get (B + 7 + 8 + 6)
              = env.get (B + 1) * 65535 + env.get (B + 7 + 8 + 7) * 65536 := by
            have h := e179; rw [hov0] at h; linear_combination h
          have hc0 := bool_of_mul_pred e309
          have hc1 := bool_of_mul_pred e311
          have hc2 := bool_of_mul_pred e313
          have hc3 := bool_of_mul_pred e315
          have hc4 := bool_of_mul_pred e317
          have hc5 := bool_of_mul_pred e319
          have hc6 := bool_of_mul_pred e321
          have hc7 := bool_of_mul_pred e323
          -- the two `c_times_quotient` halves, byte-checked.
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
          -- the two Mul product forms (low: `is_mul = 1`; high: signed `is_mulh = 1`, `is_mulhu = 0`).
          have hlo := rwlo_product h_mul_lo hqU hcU hr
            (by simpa only [Vector.getElem_map] using h_ctq0)
            (by simpa only [Vector.getElem_map] using h_ctq1)
            (by simpa only [Vector.getElem_map] using h_ctq2)
            (by simpa only [Vector.getElem_map] using h_ctq3)
          have hhi := rwhi_product_signed h_mul_hi hqU hcU hr hihm1 hihmu0
            (by simpa only [Vector.getElem_map] using h_ctq4)
            (by simpa only [Vector.getElem_map] using h_ctq5)
            (by simpa only [Vector.getElem_map] using h_ctq6)
            (by simpa only [Vector.getElem_map] using h_ctq7)
          -- the signed Euclidean identity (`b.toInt = quotient·c + remc`).
          have hid := euclid_identity_signed (b := input_op_b_val) (c := input_op_c_val)
            (quotient := Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }))
            (remc := #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)])
            (rwlo := #v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)])
            (rwhi := #v[env.get (B + 7 + 4), env.get (B + 7 + 5), env.get (B + 7 + 6), env.get (B + 7 + 7)])
            (carry := #v[env.get (B + 7 + 8), env.get (B + 7 + 8 + 1), env.get (B + 7 + 8 + 2),
              env.get (B + 7 + 8 + 3), env.get (B + 7 + 8 + 4), env.get (B + 7 + 8 + 5),
              env.get (B + 7 + 8 + 6), env.get (B + 7 + 8 + 7)])
            hbU hrU hrwloU hrwhiU hbneg hrneg hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
            hl0 hl1 hl2 hl3 hh4 hh5 hh6 hh7 hlo hhi
          -- === Stage B: abs columns, signed remainder range, sign conditions ===
          simp only [circuit_norm] at e225 e228 e247 e250 e253 e256 e259 e262 e265 e268 e270 e272 e274 e276 e278 e280 e282 e284 e286 e288 e299 e300 e301 e302 e305 e307
          have hir1 : Expression.eval env input_var_is_real = 1 := by rw [h_oir]; exact hr
          have hcc0 : Expression.eval env input_var_op_c_val[0] = input_op_c_val[0] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
            rw [← h_oc]; simp [Vector.getElem_map]
          have habscU : Word.isU64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + i }) : Word (ZMod p)) := by
            apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
            exacts [isU16_of_byteRowSpec (hb_absc0 hrneg'), isU16_of_byteRowSpec (hb_absc1 hrneg'),
              isU16_of_byteRowSpec (hb_absc2 hrneg'), isU16_of_byteRowSpec (hb_absc3 hrneg')]
          have habsrU : Word.isU64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p)) := by
            apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
            exacts [isU16_of_byteRowSpec (hb_absr0 hrneg'), isU16_of_byteRowSpec (hb_absr1 hrneg'),
              isU16_of_byteRowSpec (hb_absr2 hrneg'), isU16_of_byteRowSpec (hb_absr3 hrneg')]
          -- `abs_c = |op_c|` and `abs_remainder = |remainder_comp|` (signed-abs via `c_neg`/`rem_neg`).
          have hposc : (Word.toBitVec64 input_op_c_val).msb = false → Word.toBitVec64 (Vector.map
              (Expression.eval env) (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + i })
              : Word (ZMod p)) = Word.toBitVec64 input_op_c_val := by
            intro hm
            have hcn0 : env.get (B + 6) = 0 := by rw [hcneg, hm]; simp
            have heq : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + i }) : Word (ZMod p)) = input_op_c_val := by
              apply Vector.ext; intro i hi; interval_cases i
              · simp only [circuit_norm, Nat.add_zero]; have h := e247; rw [hcn0] at h; rw [← hcc0]; linear_combination h
              · simp only [circuit_norm, Nat.add_zero]; have h := e253; rw [hcn0] at h; rw [← hcc1]; linear_combination h
              · simp only [circuit_norm, Nat.add_zero]; have h := e259; rw [hcn0] at h; rw [← hcc2]; linear_combination h
              · simp only [circuit_norm, Nat.add_zero]; have h := e265; rw [hcn0] at h; rw [← hcc3]; linear_combination h
            rw [heq]
          have hnegc : (Word.toBitVec64 input_op_c_val).msb = true → Word.toBitVec64 (Vector.map
              (Expression.eval env) (Vector.mapRange 4 fun i => var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + i })
              : Word (ZMod p)) = -Word.toBitVec64 input_op_c_val := by
            intro hm
            have hcn1 : env.get (B + 6) = 1 := by rw [hcneg, hm]; simp
            have hace : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4) = 1 := by
              have h := e286; rw [hcn1, hir1] at h; linear_combination h
            have hk0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4) = 0 := by
              have h := e270; rw [hace] at h; linear_combination -h
            have hk1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 1) = 0 := by
              have h := e272; rw [hace] at h; linear_combination -h
            have hk2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 2) = 0 := by
              have h := e274; rw [hace] at h; linear_combination -h
            have hk3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 3) = 0 := by
              have h := e276; rw [hace] at h; linear_combination -h
            have hknoU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) := by
              apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
              · rw [hk0]; simp
              · rw [hk1]; simp
              · rw [hk2]; simp
              · rw [hk3]; simp
            have hkno_tb : Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = 0#64 := by
              rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hknoU, BitVec.toNat_zero, Word.toNat_def]
              simp only [circuit_norm, Nat.add_zero]; rw [hk0, hk1, hk2, hk3]; simp
            have hadd := ((h_addc ⟨fun _ => ⟨hcU, habscU⟩, Or.inr hace⟩) hace).2
            dsimp only at hadd
            rw [hkno_tb] at hadd
            bv_omega
          have hrcompU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + i }) : Word (ZMod p)) := by
            apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
            exacts [hr0, hr1, hr2, hr3]
          have hposr : (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb = false →
              Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
              = Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
            intro hm
            have hrn0 : env.get (B + 5) = 0 := by rw [hrneg, hm]; simp
            have heq : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
                = #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] := by
              apply Vector.ext; intro i hi; interval_cases i
              · simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
                  List.getElem_cons_zero, List.getElem_cons_succ]; have h := e250; rw [hrn0] at h; linear_combination h
              · simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
                  List.getElem_cons_zero, List.getElem_cons_succ]; have h := e256; rw [hrn0] at h; linear_combination h
              · simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
                  List.getElem_cons_zero, List.getElem_cons_succ]; have h := e262; rw [hrn0] at h; linear_combination h
              · simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
                  List.getElem_cons_zero, List.getElem_cons_succ]; have h := e268; rw [hrn0] at h; linear_combination h
            rw [heq]
          have hnegr : (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb = true →
              Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
              = -Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
            intro hm
            have hrn1 : env.get (B + 5) = 1 := by rw [hrneg, hm]; simp
            have hrae : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 1) = 1 := by
              have h := e288; rw [hrn1, hir1] at h; linear_combination h
            have hk0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4) = 0 := by
              have h := e278; rw [hrae] at h; linear_combination -h
            have hk1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 1) = 0 := by
              have h := e280; rw [hrae] at h; linear_combination -h
            have hk2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 2) = 0 := by
              have h := e282; rw [hrae] at h; linear_combination -h
            have hk3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 3) = 0 := by
              have h := e284; rw [hrae] at h; linear_combination -h
            have hknoU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) := by
              apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
              · rw [hk0]; simp
              · rw [hk1]; simp
              · rw [hk2]; simp
              · rw [hk3]; simp
            have hkno_tb : Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = 0#64 := by
              rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hknoU, BitVec.toNat_zero, Word.toNat_def]
              simp only [circuit_norm, Nat.add_zero]; rw [hk0, hk1, hk2, hk3]; simp
            have hadd := ((h_addr ⟨fun _ => ⟨hrcompU, habsrU⟩, Or.inr hrae⟩) hrae).2
            dsimp only at hadd
            rw [hkno_tb] at hadd
            have hrc_eq : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + i }) : Word (ZMod p))
                = #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] := by
              apply Vector.ext; intro i hi; interval_cases i <;>
                simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk, List.getElem_toArray,
                  List.getElem_cons_zero, List.getElem_cons_succ]
            rw [hrc_eq] at hadd
            bv_omega
          -- the unsigned `|remainder| < |c|` from `LtOperationUnsigned`, bridged `max_abs_c_or_1 = abs_c`.
          have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
          rw [if_neg hcz] at hsem
          dsimp only at hsem
          rw [field_fromElements_one] at hsem
          simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
            Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
          rw [iszeroword_result_proj] at e299 e300 e301 e302 e305
          simp only [Vector.getElem_mapRange, circuit_norm] at e299 e300 e301 e302 e305
          rw [hsem] at e299 e300 e301 e302 e305
          have hrcm : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 2) = 1 := by
            rw [hir1] at e305; linear_combination -e305
          have hm0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11) := by linear_combination e299
          have hm1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 1)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 1) := by linear_combination e300
          have hm2 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 2)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 2) := by linear_combination e301
          have hm3 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 3)
              = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 3) := by linear_combination e302
          have hmaxU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i }) : Word (ZMod p)) := by
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
          have hcmp0 : Word.toNat (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
              < Word.toNat (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i }) : Word (ZMod p)) := by
            by_contra hcon; rw [if_neg hcon] at hbit; exact one_ne_zero hbit
          have hmax_eq : Word.toNat (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i }) : Word (ZMod p))
              = Word.toNat (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
              var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + i }) : Word (ZMod p)) := by
            rw [Word.toNat_def, Word.toNat_def]; simp only [circuit_norm, Nat.add_zero]
            rw [hm0, hm1, hm2, hm3]
          rw [hmax_eq] at hcmp0
          have hlt := hlt_signed_of_abs habsrU habscU hposr hnegr hposc hnegc hcmp0
          -- sign conditions (`E225`/`E228`).
          have hE225 : env.get (B + 5) = 0 ∨ env.get (B + 1) = 1 := by
            rcases mul_eq_zero.mp e225 with h | h
            · exact Or.inl h
            · exact Or.inr (by linear_combination h)
          have hE228 : Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) = 0#64
              ∨ env.get (B + 5) = 1 ∨ env.get (B + 1) = 0 := by
            rcases mul_eq_zero.mp e228 with h | h
            · refine Or.inl ?_
              obtain ⟨d0, d1, d2, d3⟩ := Word.lt_cases_of_isU64 hrU
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                List.getElem_cons_succ] at d0 d1 d2 d3
              have hp : (2 ^ 24 : ℕ) < p := Fact.out
              -- bridge the routed `remainder` sum (`E220..E223`) to `remainder_comp`.
              rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) from by linear_combination -e70,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) from by linear_combination -e71,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 2)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) from by
                      have h2 := e81; rw [hgateD, one_mul] at h2; linear_combination -h2,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) from by
                      have h2 := e91; rw [hgateD, one_mul] at h2; linear_combination -h2] at h
              -- `Σ remainder_comp = 0` with each limb `< 2^16` ⟹ each limb `= 0` ⟹ `remc = 0#64`.
              set a := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) with ha
              set b := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) with hb
              set c := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) with hc
              set d := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) with hd
              have hsv : a.val + b.val + c.val + d.val = 0 := by
                have hab : (a + b : ZMod p).val = a.val + b.val := ZMod.val_add_of_lt (by omega)
                have habc : (a + b + c : ZMod p).val = a.val + b.val + c.val := by
                  rw [ZMod.val_add_of_lt (by rw [hab]; omega), hab]
                have habcd : (a + b + c + d : ZMod p).val = a.val + b.val + c.val + d.val := by
                  rw [ZMod.val_add_of_lt (by rw [habc]; omega), habc]
                have e := congrArg ZMod.val h
                rw [habcd, ZMod.val_zero] at e; exact e
              rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hrU, BitVec.toNat_zero, Word.toNat_def]
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                List.getElem_cons_succ]
              omega
            · rcases mul_eq_zero.mp h with h2 | h2
              · exact Or.inr (Or.inl (by linear_combination -h2))
              · exact Or.inr (Or.inr h2)
          have hsgn := sign_conditions (quotient := Word.toBitVec64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }))) hbneg hrneg hE225 hE228 hc0bv
            (by rw [hid]; ring) hlt
          exact (assemble_signed_normal hc0bv hid hlt hsgn.1 hsgn.2).2
    -- route `cols.a = remainder = remainder_comp` (E189 + E70), as in REMU stage 4.
    have hgateRem : env.get (i₀ + 3) + env.get (i₀ + 2) + env.get (i₀ + 5) + env.get (i₀ + 7) = 1 := by
      rw [hz_remu, hflag, hz_remw, hz_remuw]; ring
    have hb0 : env.get (i₀ + 8 + 4) = env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) := by
      have h := e189; rw [hgateRem, one_mul] at h; linear_combination -h - e70
    have hb1 : env.get (i₀ + 8 + 4 + 1) = env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) := by
      have h := e199; rw [hgateRem, one_mul] at h; linear_combination -h - e71
    have hb2 : env.get (i₀ + 8 + 4 + 2) = env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) := by
      have h := e209; rw [hgateRem, one_mul] at h
      have h81' := e81; rw [hgateD, one_mul] at h81'
      linear_combination -h - h81'
    have hb3 : env.get (i₀ + 8 + 4 + 3) = env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) := by
      have h := e219; rw [hgateRem, one_mul] at h
      have h91' := e91; rw [hgateD, one_mul] at h91'
      linear_combination -h - h91'
    have haqc : (Vector.map (Expression.eval env)
        (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))
        = #v[env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
          env.get (i₀ + 8 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] := by
      apply Vector.ext; intro i hi
      interval_cases i <;> simp only [circuit_norm, Nat.add_zero, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exacts [hb0, hb1, hb2, hb3]
    rw [haqc]; exact hrem_id
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

end SP1Clean.DivRemChip.SoundRem
