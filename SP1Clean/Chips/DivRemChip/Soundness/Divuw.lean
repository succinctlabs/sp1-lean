import SP1Clean.Chips.DivRemChip.Defs
import SP1Clean.Chips.DivRemChip.Soundness
import SP1Clean.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — `divuw` conjunct soundness (split for parallel compilation)

Unsigned-32-bit word DIVUW conjunct, proved as a standalone `GeneralFormalCircuit.Soundness` over
a single-conjunct local `Spec`. -/

namespace SP1Clean.DivRemChip.SoundDivuw

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The `divuw` conjunct of `DivRemChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_divuw = 1 →
      Word.toBitVec64 cols.a = RV64.divuw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

set_option maxHeartbeats 128000000 in
set_option linter.unusedSimpArgs false in
/-- Soundness of the `divuw` conjunct. -/
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
    -- operands/comp), routed to `cols.a = quotient` (sign-extended low-32).
    intro hflag
    have hduw : (env.get (i₀ + 6)).val = 1 := by rw [hflag]; exact ZMod.val_one p
    have hz_div : env.get i₀ = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divu : env.get (i₀ + 1) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_rem : env.get (i₀ + 2) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remu : env.get (i₀ + 3) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divw : env.get (i₀ + 4) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remw : env.get (i₀ + 5) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remuw : env.get (i₀ + 7) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    set B := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 with hBdef
    obtain ⟨h_oir, -, -, -, -, -, ⟨h_ob, -, -⟩, -, ⟨h_oc, -, -⟩⟩ := h_input
    have hrneg' : -input_is_real = -1 := by rw [hr]
    have he2g : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by
      rw [hflag, hz_divw, hz_remw, hz_remuw]; ring
    -- operand bridges (`eval(operand_var[i]) = operand[i]`) — the witnessed columns.
    have hbb0 : Expression.eval env input_var_op_b_val[0] = input_op_b_val[0] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb1 : Expression.eval env input_var_op_b_val[1] = input_op_b_val[1] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb2 : Expression.eval env input_var_op_b_val[2] = input_op_b_val[2] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hbb3 : Expression.eval env input_var_op_b_val[3] = input_op_b_val[3] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hcc0 : Expression.eval env input_var_op_c_val[0] = input_op_c_val[0] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
      simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
    have hir1 : Expression.eval env input_var_is_real = 1 := by rw [h_oir]; exact hr
    -- adapter-read bridges (`eval(read_var[i]) = read[i]`), for the operand↔read limb equalities.
    have hb0r : Expression.eval env input_var_adapter_op_b_memory_prev_value[0]
        = input_adapter_op_b_memory_prev_value[0] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hb1r : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
        = input_adapter_op_b_memory_prev_value[1] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hb2r : Expression.eval env input_var_adapter_op_b_memory_prev_value[2]
        = input_adapter_op_b_memory_prev_value[2] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hb3r : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
        = input_adapter_op_b_memory_prev_value[3] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hc0r : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
        = input_adapter_op_c_memory_prev_value[0] := by rw [← h_oc]; simp [Vector.getElem_map]
    have hc1r : Expression.eval env input_var_adapter_op_c_memory_prev_value[1]
        = input_adapter_op_c_memory_prev_value[1] := by rw [← h_oc]; simp [Vector.getElem_map]
    have hc2r : Expression.eval env input_var_adapter_op_c_memory_prev_value[2]
        = input_adapter_op_c_memory_prev_value[2] := by rw [← h_oc]; simp [Vector.getElem_map]
    have hc3r : Expression.eval env input_var_adapter_op_c_memory_prev_value[3]
        = input_adapter_op_c_memory_prev_value[3] := by rw [← h_oc]; simp [Vector.getElem_map]
    -- normalized copies of the operand↔read constraints E20-E47.
    have e20s := e20; have e21s := e21; have e22s := e22; have e23s := e23
    have e29s := e29; have e35s := e35; have e41s := e41; have e47s := e47
    simp only [hbdef, hcdef, hvbdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange,
      circuit_norm] at e20s e21s e22s e23s e29s e35s e41s e47s
    -- operand low limbs equal the reads (E20/E22, E21/E23) — for the read-lift truncation at the close.
    have hb0op : input_op_b_val[0] = input_adapter_op_b_memory_prev_value[0] := by
      simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      rw [← hb0r]; linear_combination -e20s
    have hb1op : input_op_b_val[1] = input_adapter_op_b_memory_prev_value[1] := by
      simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      rw [← hb1r]; linear_combination -e22s
    have hc0op : input_op_c_val[0] = input_adapter_op_c_memory_prev_value[0] := by
      simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      rw [← hc0r]; linear_combination -e21s
    have hc1op : input_op_c_val[1] = input_adapter_op_c_memory_prev_value[1] := by
      simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      rw [← hc1r]; linear_combination -e23s
    -- `is_real_not_word` (E13) binarity ⇒ `irnw` gate binary, feeding the `b_neg`/`c_neg` binaries.
    have h13t := e13; simp only [circuit_norm] at h13t; rw [h_oir] at h13t
    have hirnw : env.get (B + 4) = 0 ∨ env.get (B + 4) = 1 := by
      left; rw [hr, he2g] at h13t; linear_combination h13t
    have hE10 := group_binary4 bd br bdw brw (by omega)
    -- operand `isU64` (shadows the top read-`isU64`): low limbs = read; high limbs the `e2=1` sign-fill
    -- (E29/E41, E35/E47) with `b_neg`/`c_neg` binary (E15/E19 = msb·E10, the `U16MSB` gadget + E10).
    have hbU : Word.isU64 input_op_b_val := by
      obtain ⟨hbr0, hbr1, hbr2, hbr3⟩ := Word.lt_cases_of_isU64 h_assumptions.1
      refine operand_isU64
        (e2 := env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7))
        (s := env.get (B + 1)) hb0op hb1op ?_ ?_ hbr0 hbr1 hbr2 hbr3 (Or.inr he2g) ?_
      · simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hb2r]; linear_combination e29s
      · simp only [hbdef, hvbdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hb3r]; linear_combination e41s
      · have hbmsb := (h_msb0 ⟨fun _ => by rw [hb3r]; exact (Word.lt_cases_of_isU64 h_assumptions.1).2.2.2,
          hirnw⟩).1
        simp only [circuit_norm] at hbmsb
        have h15 := e15; simp only [circuit_norm] at h15
        rcases hbmsb with hm | hm <;> rcases hE10 with hE | hE <;>
          simp only [hm, hE, mul_zero, zero_mul, mul_one, one_mul, sub_zero] at h15 <;>
          first
            | exact Or.inl (by linear_combination -h15)
            | exact Or.inr (by linear_combination -h15)
    have hcU : Word.isU64 input_op_c_val := by
      obtain ⟨hcr0, hcr1, hcr2, hcr3⟩ := Word.lt_cases_of_isU64 h_assumptions.2
      refine operand_isU64
        (e2 := env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7))
        (s := env.get (B + 6)) hc0op hc1op ?_ ?_ hcr0 hcr1 hcr2 hcr3 (Or.inr he2g) ?_
      · simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hc2r]; linear_combination e35s
      · simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hc3r]; linear_combination e47s
      · have hcmsb := (h_msb1 ⟨fun _ => by rw [hc3r]; exact (Word.lt_cases_of_isU64 h_assumptions.2).2.2.2,
          hirnw⟩).1
        simp only [circuit_norm] at hcmsb
        have h19 := e19; simp only [circuit_norm] at h19
        rcases hcmsb with hm | hm <;> rcases hE10 with hE | hE <;>
          simp only [hm, hE, mul_zero, zero_mul, mul_one, one_mul, sub_zero] at h19 <;>
          first
            | exact Or.inl (by linear_combination -h19)
            | exact Or.inr (by linear_combination -h19)
    simp only [circuit_norm] at e15 e17 e19 e29 e35 e41 e47 e48 e49 e51 e57 e61 e67 e70 e71 e73 e83 e96 e154 e157 e160 e163 e184 e194 e204 e214 e230 e232 e234 e236 e238 e240 e242 e244 e247 e250 e253 e256 e259 e262 e265 e268 e299 e300 e301 e302 e305 e307 e309 e311 e313 e315 e355
    -- `is_overflow = 0`, sign bits `= 0` (`E10 = is_div+is_rem+is_divw+is_remw = 0`).
    have hov : env.get B = 0 := by rw [hz_div, hz_rem, hz_divw, hz_remw] at e96; linear_combination e96
    have hbneg0 : env.get (B + 1) = 0 := by rw [hz_div, hz_rem, hz_divw, hz_remw] at e15; linear_combination -e15
    have hrneg0 : env.get (B + 5) = 0 := by rw [hz_div, hz_rem, hz_divw, hz_remw] at e17; linear_combination -e17
    have hcneg0 : env.get (B + 6) = 0 := by rw [hz_div, hz_rem, hz_divw, hz_remw] at e19; linear_combination -e19
    -- operand zero-extension (`E2 = 1`, `b_neg = c_neg = 0`): the operand high halves are `0`.
    have hb2z : input_op_b_val[2] = 0 := by rw [hz_divw, hz_remw, hz_remuw, hflag, hbneg0] at e29; rw [← hbb2]; linear_combination e29
    have hb3z : input_op_b_val[3] = 0 := by rw [hz_divw, hz_remw, hz_remuw, hflag, hbneg0] at e41; rw [← hbb3]; linear_combination e41
    have hc2z : input_op_c_val[2] = 0 := by rw [hz_divw, hz_remw, hz_remuw, hflag, hcneg0] at e35; rw [← hcc2]; linear_combination e35
    have hc3z : input_op_c_val[3] = 0 := by rw [hz_divw, hz_remw, hz_remuw, hflag, hcneg0] at e47; rw [← hcc3]; linear_combination e47
    -- quotient_comp / remainder_comp zero-extension (`E7 = is_divuw + is_remuw = 1`).
    have hE7 : env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by rw [hflag, hz_remuw]; ring
    have hqc2z : env.get (i₀ + 8 + 2) = 0 := by have h := e51; rw [hE7, one_mul] at h; linear_combination h
    have hqc3z : env.get (i₀ + 8 + 3) = 0 := by have h := e61; rw [hE7, one_mul] at h; linear_combination h
    have hrc2z : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) = 0 := by have h := e73; rw [hE7, one_mul] at h; linear_combination h
    have hrc3z : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) = 0 := by have h := e83; rw [hE7, one_mul] at h; linear_combination h
    -- de-gate the four low carry-chain limb equations (`is_overflow = 0`).
    rw [hov] at e154 e157 e160 e163
    have hcl0 : env.get (B + 7) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = input_op_b_val[0] + env.get (B + 7 + 8) * 65536 := by rw [← hbb0]; linear_combination e154
    have hcl1 : env.get (B + 7 + 1) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) + env.get (B + 7 + 8) = input_op_b_val[1] + env.get (B + 7 + 8 + 1) * 65536 := by rw [← hbb1]; linear_combination e157
    have hcl2 : env.get (B + 7 + 2) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) + env.get (B + 7 + 8 + 1) = input_op_b_val[2] + env.get (B + 7 + 8 + 2) * 65536 := by rw [← hbb2]; linear_combination e160
    have hcl3 : env.get (B + 7 + 3) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) + env.get (B + 7 + 8 + 2) = input_op_b_val[3] + env.get (B + 7 + 8 + 3) * 65536 := by rw [← hbb3]; linear_combination e163
    have hc0 := bool_of_mul_pred e309
    have hc1 := bool_of_mul_pred e311
    have hc2 := bool_of_mul_pred e313
    have hc3 := bool_of_mul_pred e315
    -- quotient_comp limbs: low two byte-checked (E48/E49), high two `= 0`.
    have hq0 : (env.get (i₀ + 8)).val < 2 ^ 16 := by rw [show env.get (i₀ + 8) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4) from by linear_combination e48]; exact isU16_of_byteRowSpec (hb_q0 hrneg')
    have hq1 : (env.get (i₀ + 8 + 1)).val < 2 ^ 16 := by rw [show env.get (i₀ + 8 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1) from by linear_combination e49]; exact isU16_of_byteRowSpec (hb_q1 hrneg')
    have hqU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · exact hq0
      · exact hq1
      · rw [hqc2z]; simp [ZMod.val_zero]
      · rw [hqc3z]; simp [ZMod.val_zero]
    -- remainder_comp limbs: low two byte-checked (E70/E71), high two `= 0`.
    have hr0 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)).val < 2 ^ 16 := by rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1) from by linear_combination e70]; exact isU16_of_byteRowSpec (hb_r0 hrneg')
    have hr1 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)).val < 2 ^ 16 := by rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1) from by linear_combination e71]; exact isU16_of_byteRowSpec (hb_r1 hrneg')
    have hrU : Word.isU64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
      apply Word.isU64_of_cases
      · exact hr0
      · exact hr1
      · rw [hrc2z]; simp [ZMod.val_zero]
      · rw [hrc3z]; simp [ZMod.val_zero]
    have hrwloU : Word.isU64 (#v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)] : Word (ZMod p)) := Word.isU64_of_cases (isU16_of_byteRowSpec (hb_ctq0 hrneg')) (isU16_of_byteRowSpec (hb_ctq1 hrneg')) (isU16_of_byteRowSpec (hb_ctq2 hrneg')) (isU16_of_byteRowSpec (hb_ctq3 hrneg'))
    -- the low Mul product form (`mul_lower`, `is_mul = is_real = 1`).
    have hlo := rwlo_product h_mul_lo hqU hcU hr (by simpa only [Vector.getElem_map] using h_ctq0) (by simpa only [Vector.getElem_map] using h_ctq1) (by simpa only [Vector.getElem_map] using h_ctq2) (by simpa only [Vector.getElem_map] using h_ctq3)
    -- abbreviations for the operand/comp Words and their zero-high facts.
    have hqcW2 : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[2] = 0 := by simp only [circuit_norm, Nat.add_zero]; exact hqc2z
    have hqcW3 : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[3] = 0 := by simp only [circuit_norm, Nat.add_zero]; exact hqc3z
    -- the low-only unsigned word Euclidean identity.
    have hid := euclid_identity_word_unsigned (ctqlo := #v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)]) (rem := #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)]) (b := input_op_b_val) (qc := Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i })) (c := input_op_c_val) (carry := #v[env.get (B + 7 + 8), env.get (B + 7 + 8 + 1), env.get (B + 7 + 8 + 2), env.get (B + 7 + 8 + 3)]) hrwloU hrU hbU hqU hcU hqcW2 hqcW3 hc2z hc3z hb2z hb3z hrc2z hrc3z hc0 hc1 hc2 hc3 hcl0 hcl1 hcl2 hcl3 hlo
    -- === STAGE 3: divide-by-zero (`qc.toNat = 2^32-1`, low-32 all-ones) and remainder range. ===
    have hzero : Word.toNat input_op_c_val = 0 →
        Word.toNat (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) = 2 ^ 32 - 1 ∧
        Word.toNat (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))
            = Word.toNat input_op_b_val := by
      intro hcz0
      have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
      obtain ⟨hcb0, hcb1, hcb2, hcb3⟩ := Word.lt_cases_of_isU64 hcU
      rw [Word.toNat_def] at hcz0
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
      refine ⟨?_, ?_⟩
      · rw [Word.toNat_def]; simp only [circuit_norm, Nat.add_zero]
        rw [show env.get (i₀ + 8) = (65535 : ZMod p) from by linear_combination e48 + e230,
            show env.get (i₀ + 8 + 1) = (65535 : ZMod p) from by linear_combination e49 + e232,
            hqc2z, hqc3z]
        simp only [val_65535_zmod_p, ZMod.val_zero]; norm_num
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
        simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc1 : Expression.eval env input_var_op_c_val[1] = input_op_c_val[1] := by
        simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc2 : Expression.eval env input_var_op_c_val[2] = input_op_c_val[2] := by
        simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      have hcc3 : Expression.eval env input_var_op_c_val[3] = input_op_c_val[3] := by
        simp only [hcdef, hvcdef, Vector.getElem_map, Vector.getElem_mapRange]
      -- `is_c_0 = 0` (c ≠ 0), via the same projection bridge as `hzero`.
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
      -- `remainder_check_multiplicity = 1` (c ≠ 0, real).
      have hrcm : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 2) = 1 := by
        rw [show Expression.eval env input_var_is_real = (1 : ZMod p) from by rw [h_oir]; exact hr]
          at e305
        linear_combination -e305
      -- `abs_remainder`/`max_abs_c_or_1` are `isU64` (byte bus; `max = abs_c` on the `c ≠ 0` branch).
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
      -- the comparison bit is the unsigned `<` of `abs_remainder` and `max_abs_c_or_1`, and it is `1`.
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
      -- bridge: `abs_remainder = remainder_comp` (rem_neg = 0), `max_abs_c_or_1 = abs_c = op_c_val`.
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
    -- === STAGE 4: `cols.a = quotient` (output, sign-extended low-32); bridge to
    -- `signExtend 64 (extractLsb 31 0 quotient_comp)` (= RV64.divuw via `assemble_unsigned_word`). ===
    have hpair := assemble_unsigned_word hbU hcU hqU hrU hb2z hb3z hc2z hc3z hqcW2 hqcW3 hrc2z hrc3z hid hlt hzero
    have hgateDR : env.get (i₀ + 1) + env.get i₀ + env.get (i₀ + 4) + env.get (i₀ + 6) = 1 := by rw [hz_divu, hz_div, hz_divw, hflag]; ring
    have he2g : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by rw [hz_divw, hz_remw, hflag, hz_remuw]; ring
    have hqo1v : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1)).val < 2 ^ 16 := isU16_of_byteRowSpec (hb_q1 hrneg')
    have hqm := (h_msb6 ⟨fun _ => hqo1v, Or.inr he2g⟩).2 he2g
    dsimp only at hqm
    have ha0 : env.get (i₀ + 8 + 4) = env.get (i₀ + 8) := by have h := e184; rw [hgateDR, one_mul] at h; linear_combination -h - e48
    have ha1 : env.get (i₀ + 8 + 4 + 1) = env.get (i₀ + 8 + 1) := by have h := e194; rw [hgateDR, one_mul] at h; linear_combination -h - e49
    have ha1' : env.get (i₀ + 8 + 4 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1) := by have h := e194; rw [hgateDR, one_mul] at h; linear_combination -h
    have ha2 : env.get (i₀ + 8 + 4 + 2) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 2) := by have h := e204; rw [hgateDR, one_mul] at h; linear_combination -h
    have ha3 : env.get (i₀ + 8 + 4 + 3) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 3) := by have h := e214; rw [hgateDR, one_mul] at h; linear_combination -h
    have h57 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 2) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by have h := e57; rw [he2g, one_mul] at h; linear_combination h
    have h67 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 3) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by have h := e67; rw [he2g, one_mul] at h; linear_combination h
    have haU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [ha0]; exact hq0
      · rw [ha1]; exact hq1
      · rw [ha2, h57, hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      · rw [ha3, h67, hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
    have ha2sf : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))[2].val = (if 32768 ≤ (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))[1].val then 65535 else 0) := by
      simp only [circuit_norm, Nat.add_zero]; rw [ha2, h57, hqm, ha1']
      split <;> simp [val_65535_zmod_p, ZMod.val_zero]
    have ha3sf : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))[3].val = (if 32768 ≤ (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p))[1].val then 65535 else 0) := by
      simp only [circuit_norm, Nat.add_zero]; rw [ha3, h67, hqm, ha1']
      split <;> simp [val_65535_zmod_p, ZMod.val_zero]
    have hbridge : Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p)) = BitVec.signExtend 64 (BitVec.extractLsb 31 0 (Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)))) := by
      rw [word_eq_signExtend_lo haU ha2sf ha3sf,
          extractLsb_lo_congr haU hqU (by simp only [circuit_norm, Nat.add_zero]; exact ha0)
            (by simp only [circuit_norm, Nat.add_zero]; exact ha1)]
    rw [hbridge]
    rw [show RV64.divuw (Word.toBitVec64 input_op_c_val) (Word.toBitVec64 input_op_b_val)
          = RV64.divuw (Word.toBitVec64 input_adapter_op_c_memory_prev_value)
            (Word.toBitVec64 input_adapter_op_b_memory_prev_value) from by
        unfold RV64.divuw
        rw [toBitVec64_extractLsb hcU h_assumptions.2 hc0op hc1op,
            toBitVec64_extractLsb hbU h_assumptions.1 hb0op hb1op]] at hpair
    exact hpair.1
  · obtain ⟨h_oir, -, -, -, -, -, ⟨h_ob, -, -⟩, -, ⟨h_oc, -, -⟩⟩ := h_input
    set B := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 with hBdef
    -- the arithmetic operand `c` (witnessed column at `i₀+20..23`), distinct from the read; the IsZeroWord
    -- gadget tests *this* for the divide-by-zero split.
    set cop : Word (ZMod p) :=
        Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + 4 + 4 + i })
      with hcop
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
      simp only [neg_zero, add_zero] at e51 e61
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
      simp only [neg_zero, add_zero] at e73 e83
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
    have hbb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1]
        = input_adapter_op_b_memory_prev_value[1] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hcc1 : Expression.eval env input_var_adapter_op_c_memory_prev_value[1]
        = input_adapter_op_c_memory_prev_value[1] := by rw [← h_oc]; simp [Vector.getElem_map]
    have hbb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3]
        = input_adapter_op_b_memory_prev_value[3] := by rw [← h_ob]; simp [Vector.getElem_map]
    have hcc3 : Expression.eval env input_var_adapter_op_c_memory_prev_value[3]
        = input_adapter_op_c_memory_prev_value[3] := by rw [← h_oc]; simp [Vector.getElem_map]
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
      by_cases hcz : cop[0] = 0 ∧ cop[1] = 0 ∧ cop[2] = 0
          ∧ cop[3] = 0
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
    -- `isU64` of the operand `c` (= `cop`), distinct from `isU64` of the read (`hcU`), feeding the
    -- `MulOperation`/`AddOperation` Assumptions (`mulLo`/`mulHi`/`addc`). Low limbs equal the read (E21/E23,
    -- bounded by `hcU`); high limbs are `read·(1-E2) + c_neg·E2·65535` (E35/E47) — closed by the verified
    -- `operand_isU64` helper (`Extract.lean`) given `he2` + `c_neg` binary (E19: `c_neg = c_msb·E10`, the
    -- `U16MSB` gadget binary, `E10` from the mutually-exclusive flags). TODO: discharge via `operand_isU64`.
    have hcU_op : Word.isU64 cop := by
      obtain ⟨hcr0, hcr1, hcr2, hcr3⟩ := Word.lt_cases_of_isU64 hcU
      have hcc0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0]
          = input_adapter_op_c_memory_prev_value[0] := by rw [← h_oc]; simp [Vector.getElem_map]
      have hcc2 : Expression.eval env input_var_adapter_op_c_memory_prev_value[2]
          = input_adapter_op_c_memory_prev_value[2] := by rw [← h_oc]; simp [Vector.getElem_map]
      simp only [circuit_norm] at e21 e23 e35 e47
      refine operand_isU64
        (e2 := env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7))
        (s := env.get (B + 6)) ?_ ?_ ?_ ?_ hcr0 hcr1 hcr2 hcr3 he2 ?_
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc0]; linear_combination -e21
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc1]; linear_combination -e23
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc2]; linear_combination e35
      · simp only [hcop, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        rw [← hcc3]; linear_combination e47
      · -- `c_neg = c_msb.msb * E10` (E19) binary: `c_msb` binary from the `U16MSB` gadget (@ `irnw`,
        -- via `hirnw` — unconditional), `E10 = is_div+is_rem+is_divw+is_remw ∈ {0,1}` (disjoint flags).
        have hcmsb := (h_msb1 ⟨fun _ => by rw [hcc3]; exact (Word.lt_cases_of_isU64 hcU).2.2.2,
          hirnw⟩).1
        simp only [circuit_norm] at hcmsb
        have hE10 := group_binary4 bd br bdw brw (by omega)
        have h19 := e19; simp only [circuit_norm] at h19
        rcases hcmsb with hm | hm <;> rcases hE10 with hE | hE <;>
          simp only [hm, hE, mul_zero, zero_mul, mul_one, one_mul, sub_zero] at h19 <;>
          first
            | exact Or.inl (by linear_combination -h19)
            | exact Or.inr (by linear_combination -h19)
    refine ⟨?mulLo, ?mulHi, ?eqb, ?eqc, ?eqb2, ?eqc2, ?isc0, ?addc, ?addr, ?lt,
      ?msb0, ?msb1, ?msb2, ?msb3, ?msb4, ?msb5, ?msb6, ?cpu, ?rtype, ?own,
      ?b0, ?b1, ?b2, ?b3, ?b4, ?b5, ?b6, ?b7, ?b8, ?b9, ?b10, ?b11, ?b12, ?b13, ?b14, ?b15,
      ?b16, ?b17, ?b18, ?b19, ?b20, ?b21, ?b22, ?b23, ?b24, ?b25, ?b26, ?b27, ?b28, ?b29, ?b30, ?b31,
      ?b32, ?b33⟩
    case b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 | b8 | b9 | b10 | b11 | b12 | b13 | b14 | b15
      | b16 | b17 | b18 | b19 | b20 | b21 | b22 | b23 | b24 | b25 | b26 | b27 | b28 | b29 | b30 | b31 =>
        exact Channels.binary_gate_req_vacuous hbin _
    case b32 | b33 => exact Channels.binary_gate_req_vacuous he2 _
    case own => simp only [circuit_norm, assertZeros, forAllNoOffset_map_assert]
    case eqb => exact Or.inl rfl
    case eqc => exact Or.inl rfl
    case eqb2 => exact Or.inl rfl
    case eqc2 => exact Or.inl rfl
    case isc0 => exact Or.inl rfl
    case cpu => exact Or.inr hbin
    case rtype => exact Or.inr hbin
    case mulLo =>
      exact Or.inr ⟨fun hr => ⟨hqcU hr, hcU_op⟩, hbin, fun h => (zero_ne_one h).elim, hbin,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, by rcases hbin with h | h <;> simp [h]⟩
    case mulHi =>
      refine Or.inr ⟨fun hr => ⟨hqcU hr, hcU_op⟩, hbin, fun h => (zero_ne_one h).elim, Or.inl rfl,
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
        exact ⟨hcU_op, habscU hr⟩
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
          by_cases hcz : cop[0] = 0 ∧ cop[1] = 0 ∧ cop[2] = 0
              ∧ cop[3] = 0
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
      -- the U16MSB gadget tests the raw read `bpv[3]`, bounded directly by `isU64 (read)`.
      refine Or.inr ⟨fun _ => ?_, hirnw⟩
      rw [hbb3]; exact (Word.lt_cases_of_isU64 hbU).2.2.2
    case msb1 =>
      refine Or.inr ⟨fun _ => ?_, hirnw⟩
      rw [hcc3]; exact (Word.lt_cases_of_isU64 hcU).2.2.2
    case msb2 =>
      refine Or.inr ⟨fun hirnwg => ?_, hirnw⟩
      obtain ⟨hr, -⟩ := hirnw_imp hirnwg
      have hrneg' : -input_is_real = -1 := by rw [hr]
      exact isU16_of_byteRowSpec (hb_r3 hrneg')
    case msb3 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      rw [hbb1]; exact (Word.lt_cases_of_isU64 hbU).2.1
    case msb4 =>
      refine Or.inr ⟨fun _ => ?_, he2⟩
      rw [hcc1]; exact (Word.lt_cases_of_isU64 hcU).2.1
    case msb5 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2r1 (by linear_combination -he2g)), he2⟩
    case msb6 =>
      exact Or.inr ⟨fun he2g => isU16_of_byteRowSpec (hb_e2q1 (by linear_combination -he2g)), he2⟩

end SP1Clean.DivRemChip.SoundDivuw
