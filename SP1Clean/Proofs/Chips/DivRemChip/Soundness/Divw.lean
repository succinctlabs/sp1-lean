import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Tail

/-! # `DivRemChip` — `divw` conjunct soundness (split for parallel compilation)

Signed-32-bit word DIVW conjunct, proved as a standalone `GeneralFormalCircuit.Soundness` over a
single-conjunct local `Spec`. -/

namespace SP1Clean.DivRemChip.SoundDivw

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- The `divw` conjunct of `DivRemChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_divw = 1 →
      Word.toBitVec64 cols.a = RV64.divw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

set_option maxHeartbeats 128000000 in
set_option linter.unusedSimpArgs false in
/-- Soundness of the `divw` conjunct. -/
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
    -- alias the witnessed operand columns `b`/`c` (i₀+16..19, i₀+20..23) under the old names (local to
    -- `?_spec`). `input_op_b_val`/`input_op_c_val` now mean the *operands*; the read is the adapter value.
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
    -- word operands/comp), routed to `cols.a = quotient` (sign-extended low-32).
    intro hflag
    have hdw : (env.get (i₀ + 4)).val = 1 := by rw [hflag]; exact ZMod.val_one p
    have hz_div : env.get i₀ = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divu : env.get (i₀ + 1) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_rem : env.get (i₀ + 2) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remu : env.get (i₀ + 3) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remw : env.get (i₀ + 5) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_divuw : env.get (i₀ + 6) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hz_remuw : env.get (i₀ + 7) = 0 := (ZMod.val_eq_zero _).mp (by omega)
    set B := i₀ + 8 + 4 + 4 + 4 + 4 + 45 + 45 with hBdef
    obtain ⟨h_oir, -, -, -, -, -, ⟨h_ob, -, -⟩, -, ⟨h_oc, -, -⟩⟩ := h_input
    have hrneg' : - input_is_real = -1 := by rw [hr]
    have he2g : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by
      rw [hflag, hz_remw, hz_divuw, hz_remuw]; ring
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
    -- the signed-32 identity on the `quotient_comp` column (= `quotient` for 32-bit, via E48/E49).
    have hdivw_id : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (Word.toBitVec64 (Vector.map
          (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))))
        = RV64.divw (Word.toBitVec64 input_op_c_val) (Word.toBitVec64 input_op_b_val) := by
      simp only [circuit_norm] at e15 e17 e19 e29 e35 e41 e47 e48 e49 e54 e64 e70 e71 e76 e86 e96 e184 e194 e204 e214 e230 e232 e234 e236 e238 e240 e242 e244 e154 e157 e160 e163 e309 e311 e313 e315
      -- flag sums: `E2 = 1` (word), `E6 = is_divw+is_remw = 1`, `E10 = is_div+is_rem+is_divw+is_remw = 1`.
      have he2g : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by
        rw [hflag, hz_remw, hz_divuw, hz_remuw]; ring
      have hE6 : env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [hflag, hz_remw]; ring
      have hE10 : env.get i₀ + env.get (i₀ + 2) + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by
        rw [hz_div, hz_rem, hflag, hz_remw]; ring
      have hihm1 : env.get i₀ + env.get (i₀ + 2) = 0 := by rw [hz_div, hz_rem]; ring
      have hihmu0 : env.get (i₀ + 1) + env.get (i₀ + 3) = 0 := by rw [hz_divu, hz_remu]; ring
      -- `quotient_comp` is the byte-checked `quotient` column (E48/E49 low; high two via the sign-fills).
      have hq0 : (env.get (i₀ + 8)).val < 2 ^ 16 := by
        rw [show env.get (i₀ + 8) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4) from by linear_combination e48]
        exact isU16_of_byteRowSpec (hb_q0 hrneg')
      have hq1 : (env.get (i₀ + 8 + 1)).val < 2 ^ 16 := by
        rw [show env.get (i₀ + 8 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1) from by linear_combination e49]
        exact isU16_of_byteRowSpec (hb_q1 hrneg')
      have hr0 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4)).val < 2 ^ 16 := by
        rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1) from by linear_combination e70]
        exact isU16_of_byteRowSpec (hb_r0 hrneg')
      have hr1 : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)).val < 2 ^ 16 := by
        rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1) from by linear_combination e71]
        exact isU16_of_byteRowSpec (hb_r1 hrneg')
      -- the operand limb bridges `bpv[1] = b[1]`, `cpv[1] = c[1]` (E22/E23) for the e2-gated sign gadgets.
      obtain ⟨_, hb1b, _, _⟩ := Word.lt_cases_of_isU64 hbU
      obtain ⟨_, hc1b, _, _⟩ := Word.lt_cases_of_isU64 hcU
      -- sign columns from the e2-gated U16MSB gadgets (msb on limb [1] = bit 31).
      simp only [circuit_norm] at e20 e21 e22 e23
      have qb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1] = input_op_b_val[1] := by
        rw [← hbb1]; linear_combination e22
      have qc1 : Expression.eval env input_var_adapter_op_c_memory_prev_value[1] = input_op_c_val[1] := by
        rw [← hcc1]; linear_combination e23
      have hbsign : env.get (B + 1) = if 32768 ≤ input_op_b_val[1].val then 1 else 0 := by
        have hbm := (h_msb3 ⟨fun _ => by rw [qb1]; exact hb1b, Or.inr he2g⟩).2 he2g
        dsimp only at hbm
        have hb1 : env.get (B + 1)
            = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4) := by
          have h := e15; rw [hE10, mul_one] at h; linear_combination -h
        rw [hb1, hbm, qb1]
      have hcsign : env.get (B + 6) = if 32768 ≤ input_op_c_val[1].val then 1 else 0 := by
        have hcm := (h_msb4 ⟨fun _ => by rw [qc1]; exact hc1b, Or.inr he2g⟩).2 he2g
        dsimp only at hcm
        have hc1 : env.get (B + 6)
            = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1) := by
          have h := e19; rw [hE10, mul_one] at h; linear_combination -h
        rw [hc1, hcm, qc1]
      -- operand sign-fills (E2 = 1): `b[2] = b[3] = b_neg·65535`, `c[2] = c[3] = c_neg·65535`.
      rw [hz_remw, hz_divuw, hz_remuw, hflag] at e29 e35 e41 e47
      have hbf2v : input_op_b_val[2] = env.get (B + 1) * 65535 := by rw [← hbb2]; linear_combination e29
      have hbf3v : input_op_b_val[3] = env.get (B + 1) * 65535 := by rw [← hbb3]; linear_combination e41
      have hcf2v : input_op_c_val[2] = env.get (B + 6) * 65535 := by rw [← hcc2]; linear_combination e35
      have hcf3v : input_op_c_val[3] = env.get (B + 6) * 65535 := by rw [← hcc3]; linear_combination e47
      have hbf2 : input_op_b_val[2].val = (if 32768 ≤ input_op_b_val[1].val then 65535 else 0) := by
        rw [hbf2v, hbsign]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hbf3 : input_op_b_val[3].val = (if 32768 ≤ input_op_b_val[1].val then 65535 else 0) := by
        rw [hbf3v, hbsign]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hcf2 : input_op_c_val[2].val = (if 32768 ≤ input_op_c_val[1].val then 65535 else 0) := by
        rw [hcf2v, hcsign]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hcf3 : input_op_c_val[3].val = (if 32768 ≤ input_op_c_val[1].val then 65535 else 0) := by
        rw [hcf3v, hcsign]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      -- quot_msb / rem_msb from the e2-gated U16MSB gadgets (input = output quotient[1]/remainder[1]).
      have hqo1v : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1)).val < 2 ^ 16 := isU16_of_byteRowSpec (hb_q1 hrneg')
      have hro1v : (env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1)).val < 2 ^ 16 := isU16_of_byteRowSpec (hb_r1 hrneg')
      have hqm := (h_msb6 ⟨fun _ => hqo1v, Or.inr he2g⟩).2 he2g
      dsimp only at hqm
      have hrm := (h_msb5 ⟨fun _ => hro1v, Or.inr he2g⟩).2 he2g
      dsimp only at hrm
      -- comp sign-fills: quotient_comp[2,3] = quot_msb·65535 (E54/E64), remainder_comp[2,3] = rem_msb·65535 (E76/E86).
      -- and quotient_comp[1] = output quotient[1] (E49), remainder_comp[1] = output remainder[1] (E71).
      have hqc1eq : env.get (i₀ + 8 + 1)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1) := by
        linear_combination e49
      have hrc1eq : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1) := by
        linear_combination e71
      have hqc2v : env.get (i₀ + 8 + 2)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by
        have h := e54; rw [hE6, one_mul] at h; linear_combination h
      have hqc3v : env.get (i₀ + 8 + 3)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by
        have h := e64; rw [hE6, one_mul] at h; linear_combination h
      have hrc2v : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 6) * 65535 := by
        have h := e76; rw [hE6, one_mul] at h; linear_combination h
      have hrc3v : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)
          = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 6) * 65535 := by
        have h := e86; rw [hE6, one_mul] at h; linear_combination h
      have hqf2 : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[2].val
          = (if 32768 ≤ (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[1].val then 65535 else 0) := by
        simp only [circuit_norm, Nat.add_zero]; rw [hqc2v, hqm, hqc1eq]
        split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hqf3 : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[3].val
          = (if 32768 ≤ (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))[1].val then 65535 else 0) := by
        simp only [circuit_norm, Nat.add_zero]; rw [hqc3v, hqm, hqc1eq]
        split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hrf2 : (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))[2].val
          = (if 32768 ≤ (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))[1].val then 65535 else 0) := by
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [hrc2v, hrm, hrc1eq]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hrf3 : (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))[3].val
          = (if 32768 ≤ (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))[1].val then 65535 else 0) := by
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [hrc3v, hrm, hrc1eq]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      -- isU64 for the quotient/remainder comp Words (low byte-checked, high from the sign-fills).
      have hqU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
        apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
        · exact hq0
        · exact hq1
        · rw [hqc2v, hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
        · rw [hqc3v, hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      have hrU : Word.isU64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
        apply Word.isU64_of_cases
        · exact hr0
        · exact hr1
        · rw [hrc2v, hrm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
        · rw [hrc3v, hrm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      -- === STAGE 3: 3-way split. ===
      by_cases hcz : input_op_c_val[0] = 0 ∧ input_op_c_val[1] = 0 ∧ input_op_c_val[2] = 0 ∧ input_op_c_val[3] = 0
      · -- DIVZERO (low-32 of c is zero): quotient = -1, remainder = b (low halves).
        have hc0_lo : BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_c_val) = 0#32 := by
          apply BitVec.eq_of_toNat_eq
          rw [extractLsb_lo_toNat hcU, hcz.1, hcz.2.1, BitVec.toNat_zero]; simp [ZMod.val_zero]
        have hsem := IsZeroWordOperation.result_semantic (h_isc0 (Or.inr hr)) hr
        rw [if_pos hcz] at hsem
        dsimp only at hsem
        rw [field_fromElements_one] at hsem
        simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
          Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm] at hsem
        rw [iszeroword_result_proj] at e230 e232 e234 e236 e238 e240 e242 e244
        simp only [Vector.getElem_mapRange, circuit_norm] at e230 e232 e234 e236 e238 e240 e242 e244
        rw [hsem, one_mul] at e230 e232 e234 e236 e238 e240 e242 e244
        have hq_lo : BitVec.extractLsb 31 0 (Word.toBitVec64 (Vector.map (Expression.eval env)
            (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p))) = -1#32 := by
          apply BitVec.eq_of_toNat_eq
          rw [extractLsb_lo_toNat hqU]
          simp only [circuit_norm, Nat.add_zero]
          rw [show env.get (i₀ + 8) = (65535 : ZMod p) from by linear_combination e48 + e230,
              show env.get (i₀ + 8 + 1) = (65535 : ZMod p) from by linear_combination e49 + e232]
          rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]; simp [val_65535_zmod_p]
        have hr_lo : BitVec.extractLsb 31 0 (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
            env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)))
            = BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_b_val) := by
          apply extractLsb_lo_congr hrU hbU
          · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
              List.getElem_cons_succ]; rw [← hbb0]; linear_combination e238
          · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
              List.getElem_cons_succ]; rw [← hbb1]; linear_combination e240
        exact (divw_remw_divzero hc0_lo hq_lo hr_lo).1
      · by_cases hovf : env.get B = 1
        · -- OVERFLOW (`is_overflow = 1`): low-32 of b = i32::MIN, c = -1; quotient = b, remainder = 0.
          simp only [circuit_norm] at e105 e107 e109 e111
          -- the low-half `IsEqualWordOperation` overflow gate (`e2`-gated), bridging `bpv`→`b`/`cpv`→`c`.
          have hbsp := h_eqb2 (Or.inr he2g)
          have hcsp := h_eqc2 (Or.inr he2g)
          have qb0 : Expression.eval env input_var_adapter_op_b_memory_prev_value[0] = input_op_b_val[0] := by rw [← hbb0]; linear_combination e20
          have qc0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0] = input_op_c_val[0] := by rw [← hcc0]; linear_combination e21
          -- the overflow products pin low-32 `b = i32::MIN`, `c = -1` (`overflow_of_iseqword_word`).
          have hpair := overflow_of_iseqword_word (b := input_op_b_val) (c := input_op_c_val) hbU hcU he2g
            (by rw [show (#v[input_op_b_val[0], input_op_b_val[1], (0 : ZMod p), (0 : ZMod p)] : Word (ZMod p))
                  = #v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
                    Expression.eval env input_var_adapter_op_b_memory_prev_value[1], 0, 0] from by
                apply Vector.ext; intro i hi; interval_cases i <;>
                  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                    List.getElem_cons_succ]
                exacts [qb0.symm, qb1.symm]]; exact hbsp)
            (by rw [show (#v[input_op_c_val[0], input_op_c_val[1], (0 : ZMod p), (0 : ZMod p)] : Word (ZMod p))
                  = #v[Expression.eval env input_var_adapter_op_c_memory_prev_value[0],
                    Expression.eval env input_var_adapter_op_c_memory_prev_value[1], 0, 0] from by
                apply Vector.ext; intro i hi; interval_cases i <;>
                  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                    List.getElem_cons_succ]
                exacts [qc0.symm, qc1.symm]]; exact hcsp)
            (by
              rw [iseqword_result_proj, iseqword_result_proj] at e96
              simp only [Vector.getElem_mapRange, circuit_norm] at e96
              rw [hovf, hE10, mul_one] at e96
              dsimp only
              rw [field_fromElements_one, field_fromElements_one]
              simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop,
                Vector.getElem_mapRange, Nat.reduceAdd, circuit_norm]
              linear_combination -e96)
          have hb_im : BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_b_val) = BitVec.intMin 32 := hpair.1
          have hc_m1 : BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_c_val) = -1#32 := hpair.2
          -- quotient = b, remainder = 0 (low halves) via E105/E109 (E107/E111) + E48/E49 (E70/E71).
          have hqa0 : env.get (i₀ + 8) = input_op_b_val[0] := by
            have h := e105; rw [hovf, one_mul] at h; rw [← hbb0]; linear_combination e48 + h
          have hqa1 : env.get (i₀ + 8 + 1) = input_op_b_val[1] := by
            have h := e109; rw [hovf, one_mul] at h; rw [← hbb1]; linear_combination e49 + h
          have hra0 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = 0 := by
            have h := e107; rw [hovf, one_mul] at h; linear_combination e70 + h
          have hra1 : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) = 0 := by
            have h := e111; rw [hovf, one_mul] at h; linear_combination e71 + h
          have hq_lo : BitVec.extractLsb 31 0 (Word.toBitVec64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)))
              = BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_b_val) := by
            apply extractLsb_lo_congr hqU hbU <;> simp only [circuit_norm, Nat.add_zero]
            exacts [hqa0, hqa1]
          have hr_lo : BitVec.extractLsb 31 0 (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))) = 0#32 := by
            apply BitVec.eq_of_toNat_eq
            rw [extractLsb_lo_toNat hrU, BitVec.toNat_zero]
            simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
              List.getElem_cons_succ]
            rw [hra0, hra1]; simp [ZMod.val_zero]
          exact (divw_remw_overflow hb_im hc_m1 hq_lo hr_lo).1
        · -- NORMAL: signed Euclidean low-only assembly (`c ≠ 0` low-32, no overflow).
          have hc0bv : BitVec.extractLsb 31 0 (Word.toBitVec64 input_op_c_val) ≠ 0#32 := by
            intro h
            apply hcz
            have hcl : input_op_c_val[0].val + input_op_c_val[1].val * 2 ^ 16 = 0 := by
              have := congrArg BitVec.toNat h
              rwa [extractLsb_lo_toNat hcU, BitVec.toNat_zero] at this
            obtain ⟨d0, d1, _, _⟩ := Word.lt_cases_of_isU64 hcU
            have hc0z : input_op_c_val[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
            have hc1z : input_op_c_val[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
            refine ⟨hc0z, hc1z, ?_, ?_⟩
            · rw [hcf2v, hcsign, hc1z]; simp [ZMod.val_zero]
            · rw [hcf3v, hcsign, hc1z]; simp [ZMod.val_zero]
          simp only [circuit_norm] at e225 e228 e247 e250 e253 e256 e259 e262 e265 e268 e270 e272 e274 e276 e278 e280 e282 e284 e286 e288 e299 e300 e301 e302 e305 e307 e341 e79 e89
          -- `is_overflow = 0` (binary gate `E341`, and we are not the overflow branch).
          have hov0 : env.get B = 0 := by
            rcases bool_of_mul_pred e341 with h | h
            · exact h
            · exact absurd h hovf
          -- the four LOW carry-chain limb equations (`is_overflow = 0`), carry binaries, `c_times_quotient`.
          rw [hov0] at e154 e157 e160 e163
          have hcl0 : env.get (B + 7) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) = input_op_b_val[0] + env.get (B + 7 + 8) * 65536 := by rw [← hbb0]; linear_combination e154
          have hcl1 : env.get (B + 7 + 1) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) + env.get (B + 7 + 8) = input_op_b_val[1] + env.get (B + 7 + 8 + 1) * 65536 := by rw [← hbb1]; linear_combination e157
          have hcl2 : env.get (B + 7 + 2) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) + env.get (B + 7 + 8 + 1) = input_op_b_val[2] + env.get (B + 7 + 8 + 2) * 65536 := by rw [← hbb2]; linear_combination e160
          have hcl3 : env.get (B + 7 + 3) + env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) + env.get (B + 7 + 8 + 2) = input_op_b_val[3] + env.get (B + 7 + 8 + 3) * 65536 := by rw [← hbb3]; linear_combination e163
          have hc0 := bool_of_mul_pred e309
          have hc1 := bool_of_mul_pred e311
          have hc2 := bool_of_mul_pred e313
          have hc3 := bool_of_mul_pred e315
          have hrwloU : Word.isU64 (#v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)] : Word (ZMod p)) := Word.isU64_of_cases (isU16_of_byteRowSpec (hb_ctq0 hrneg')) (isU16_of_byteRowSpec (hb_ctq1 hrneg')) (isU16_of_byteRowSpec (hb_ctq2 hrneg')) (isU16_of_byteRowSpec (hb_ctq3 hrneg'))
          -- the low Mul product form (`mul_lower`, `is_mul = is_real = 1`).
          have hlo := rwlo_product h_mul_lo hqU hcU hr (by simpa only [Vector.getElem_map] using h_ctq0) (by simpa only [Vector.getElem_map] using h_ctq1) (by simpa only [Vector.getElem_map] using h_ctq2) (by simpa only [Vector.getElem_map] using h_ctq3)
          -- the 64-bit signed Euclidean identity (`b.toInt = quotient·c + remc`), low-only carry chain.
          have hid := euclid_identity_word_signed
            (ctqlo := #v[env.get (B + 7), env.get (B + 7 + 1), env.get (B + 7 + 2), env.get (B + 7 + 3)])
            (b := input_op_b_val)
            (c := input_op_c_val)
            (quotient := Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }))
            (remc := #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)])
            (carry := #v[env.get (B + 7 + 8), env.get (B + 7 + 8 + 1), env.get (B + 7 + 8 + 2), env.get (B + 7 + 8 + 3)])
            hrwloU hbU hcU hqU hrU hbf2 hbf3 hcf2 hcf3 hqf2 hqf3 hrf2 hrf3 hc0 hc1 hc2 hc3
            hcl0 hcl1 hcl2 hcl3 hlo
          -- === abs columns, signed remainder range, sign conditions (mirror DIV normal). ===
          -- sign columns in the **64-bit msb** form (convert from the limb-1 form via `toBitVec64_msb_iff`).
          have hbneg : env.get (B + 1) = if (Word.toBitVec64 input_op_b_val).msb then 1 else 0 := by
            rw [hbsign]; refine if_congr ?_ rfl rfl
            rw [toBitVec64_msb_iff hbU, hbf3]; split <;> omega
          have hcneg : env.get (B + 6) = if (Word.toBitVec64 input_op_c_val).msb then 1 else 0 := by
            rw [hcsign]; refine if_congr ?_ rfl rfl
            rw [toBitVec64_msb_iff hcU, hcf3]; split <;> omega
          have hrneg : env.get (B + 5)
              = if (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb then 1 else 0 := by
            have hrsign : env.get (B + 5)
                = if 32768 ≤ (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                    env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                    env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))[1].val then 1 else 0 := by
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
              rw [hrc1eq, ← hrm]
              have h := e17; rw [hE10, mul_one] at h; linear_combination -h
            rw [hrsign]; refine if_congr ?_ rfl rfl
            rw [toBitVec64_msb_iff hrU, hrf3]; split <;> omega
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
            exacts [hr0, hr1,
              by rw [hrc2v, hrm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero],
              by rw [hrc3v, hrm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]]
          have hposr : (Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb = false →
              Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
              = Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) := by
            intro hm
            have hrn0 : env.get (B + 5) = 0 := by rw [hrneg, hm]; simp
            have heq : (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
                = #v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
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
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p))).msb = true →
              Word.toBitVec64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i =>
                var { index := B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) : Word (ZMod p))
              = -Word.toBitVec64 (#v[env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4),
                env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
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
                  env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
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
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1), env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2),
              env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3)] : Word (ZMod p)) = 0#64
              ∨ env.get (B + 5) = 1 ∨ env.get (B + 1) = 0 := by
            rcases mul_eq_zero.mp e228 with h | h
            · refine Or.inl ?_
              obtain ⟨d0, d1, d2, d3⟩ := Word.lt_cases_of_isU64 hrU
              simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
                List.getElem_cons_succ] at d0 d1 d2 d3
              have hp : (2 ^ 24 : ℕ) < p := Fact.out
              have he79' : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 2)
                  = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 6) * 65535 := by
                have h2 := e79; rw [he2g, one_mul] at h2; linear_combination h2
              have he89' : env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3)
                  = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 6) * 65535 := by
                have h2 := e89; rw [he2g, one_mul] at h2; linear_combination h2
              rw [show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) from by linear_combination -e70,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 1)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) from by linear_combination -e71,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 2)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) from by linear_combination he79' - hrc2v,
                  show env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 3)
                    = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) from by linear_combination he89' - hrc3v] at h
              set a := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4) with ha
              set bb := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 1) with hb
              set cc := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 2) with hc
              set dd := env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 3) with hd
              have hsv : a.val + bb.val + cc.val + dd.val = 0 := by
                have hab : (a + bb : ZMod p).val = a.val + bb.val := ZMod.val_add_of_lt (by omega)
                have habc : (a + bb + cc : ZMod p).val = a.val + bb.val + cc.val := by
                  rw [ZMod.val_add_of_lt (by rw [hab]; omega), hab]
                have habcd : (a + bb + cc + dd : ZMod p).val = a.val + bb.val + cc.val + dd.val := by
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
          have hc0_64 : Word.toBitVec64 input_op_c_val ≠ 0#64 := by
            intro h; apply hc0bv; rw [h]; apply BitVec.eq_of_toNat_eq; simp
          have hsgn := sign_conditions (quotient := Word.toBitVec64 (Vector.map (Expression.eval env)
              (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }))) hbneg hrneg hE225 hE228 hc0_64
            (by rw [hid]; ring) hlt
          exact (assemble_signed_word_normal hbU hcU hqU hrU hbf2 hbf3 hcf2 hcf3 hqf2 hqf3 hrf2 hrf3
            hc0bv hid hlt hsgn.1 hsgn.2).1
    -- === STAGE 4: `cols.a = quotient` (output, sign-extended low-32); bridge to
    -- `signExtend 64 (extractLsb 31 0 quotient_comp)` (= RV64.divw via `assemble_signed_word_normal`). ===
    simp only [circuit_norm] at e48 e49 e57 e67 e184 e194 e204 e214
    have hgateDR : env.get (i₀ + 1) + env.get i₀ + env.get (i₀ + 4) + env.get (i₀ + 6) = 1 := by rw [hz_divu, hz_div, hflag, hz_divuw]; ring
    have he2g : env.get (i₀ + 4) + env.get (i₀ + 5) + env.get (i₀ + 6) + env.get (i₀ + 7) = 1 := by rw [hflag, hz_remw, hz_divuw, hz_remuw]; ring
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
    have hq0' : (env.get (i₀ + 8)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4) from by linear_combination e48]
      exact isU16_of_byteRowSpec (hb_q0 hrneg')
    have hq1' : (env.get (i₀ + 8 + 1)).val < 2 ^ 16 := by
      rw [show env.get (i₀ + 8 + 1) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 1) from by linear_combination e49]
      exact isU16_of_byteRowSpec (hb_q1 hrneg')
    have hE6 : env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [hflag, hz_remw]; ring
    have hqc2v' : env.get (i₀ + 8 + 2) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by
      have h := e54; simp only [circuit_norm] at h; rw [hE6, one_mul] at h; linear_combination h
    have hqc3v' : env.get (i₀ + 8 + 3) = env.get (B + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 7) * 65535 := by
      have h := e64; simp only [circuit_norm] at h; rw [hE6, one_mul] at h; linear_combination h
    have hqU' : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + i }) : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · exact hq0'
      · exact hq1'
      · rw [hqc2v', hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
      · rw [hqc3v', hqm]; split <;> simp [val_65535_zmod_p, ZMod.val_zero]
    have haU : Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 8 + 4 + i }) : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;> simp only [circuit_norm, Nat.add_zero]
      · rw [ha0]; exact hq0'
      · rw [ha1]; exact hq1'
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
          extractLsb_lo_congr haU hqU' (by simp only [circuit_norm, Nat.add_zero]; exact ha0)
            (by simp only [circuit_norm, Nat.add_zero]; exact ha1)]
    rw [hbridge]
    -- read-lift: `RV64.divw` truncates to the low 32 bits (`extractLsb 31 0`), and the operand and the
    -- raw read agree there (limbs 0,1 via E20/E22, E21/E23), so the operand identity gives the read identity.
    rw [show RV64.divw (Word.toBitVec64 input_op_c_val) (Word.toBitVec64 input_op_b_val)
          = RV64.divw (Word.toBitVec64 input_adapter_op_c_memory_prev_value)
            (Word.toBitVec64 input_adapter_op_b_memory_prev_value) from by
        unfold RV64.divw
        rw [toBitVec64_extractLsb hcU h_assumptions.2 hc0op hc1op,
            toBitVec64_extractLsb hbU h_assumptions.1 hb0op hb1op]] at hdivw_id
    exact hdivw_id

end SP1Clean.DivRemChip.SoundDivw
