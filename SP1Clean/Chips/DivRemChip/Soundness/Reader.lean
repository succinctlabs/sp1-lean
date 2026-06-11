import SP1Clean.Chips.DivRemChip.Defs
import SP1Clean.Chips.DivRemChip.Soundness
import SP1Clean.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — reader sub-`Spec` + `is_real`-binary (split for parallel compilation)

The `RTypeReader` register-reader sub-`Spec` (register reads/write, gated by the flag-weighted R-type opcode
and the result `cols.a` as the `op_a` write value) and the proven `is_real`-binary fact — the two
non-arithmetic conjuncts of `DivRemChip.Spec`, proved as a standalone `GeneralFormalCircuit.Soundness` over a
local two-conjunct `Spec`, the same split-for-parallel-compilation shape as the eight per-variant files.
`Formal.lean`'s top-level soundness reuses `.1` from here for the reader + binary conjuncts. The
`h_holds`/`h_own` destructure and the `?_tail` (`Operations.Requirements`) are the verbatim shared pieces from
the per-variant files; only the `?_spec` bullet differs (the reader guarantee `h_rtype` fed the binary gate
`E355`, plus the binary itself). -/

namespace SP1Clean.DivRemChip.SoundReader

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The `RTypeReader` reader sub-`Spec` ∧ the `is_real`-binary fact, as a standalone spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
        + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 128000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
/-- Soundness of the reader sub-`Spec` + `is_real`-binary conjuncts. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
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
  · -- reader sub-`Spec` (`h_rtype` guarantee, its `circuit.Spec` projection unfolded) ∧ `is_real`-binary
    -- (the gate `E355`, per `Defs.lean`).
    obtain ⟨h_ob, h_oc, h_oir, -⟩ := h_input
    have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
      have h := e355; simp only [circuit_norm] at h; rw [h_oir] at h; exact bool_of_mul_pred h
    have hr := h_rtype h_bin
    simp only [Readers.RTypeReader.circuit] at hr
    exact ⟨hr, h_bin⟩
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


end SP1Clean.DivRemChip.SoundReader
