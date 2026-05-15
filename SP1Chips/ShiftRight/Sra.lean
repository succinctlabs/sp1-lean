import SP1Chips.ShiftRight.Common

namespace ShiftRight

set_option linter.style.setOption false
-- Imbalanced goal tree: proof applies tactics per-focused-case.
set_option linter.style.multiGoal false
-- Unused variables expected because many proofs are currently stopped.
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

variable (Main : Vector (Fin KB) 69)

section sra

/-- Shared proof body for `spec.sra` and `spec.srai`. -/
private lemma spec.sra_common
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (eq_sra : Main[65] = 1) :
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
  := by
    have ⟨is_U64_a, is_U64_b, is_U64_c⟩ := ops_U64 Main cstrs (sra_real Main eq_sra)
    obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64 is_U64_b
    obtain ⟨c0_16, c1_16, c2_16, c3_16⟩ := Word.lt_cases_of_isU64 is_U64_c
    obtain ⟨sop_1, sop_2, sop_3, sop_4⟩ := single_op Main cstrs
    replace cstrs := (allHold_constraints_iff Main).mp cstrs
    set b0 := Main[15]
    set b1 := Main[16]
    set b2 := Main[17]
    set b3 := Main[18]
    set c0 := Main[25]
    set c1 := Main[26]
    set c2 := Main[27]
    set c3 := Main[28]
    set imm := Main[31]
    set a0 := Main[32]
    set a1 := Main[33]
    set a2 := Main[34]
    set a3 := Main[35]
    set msb_b := Main[36]
    set msb_srw := Main[37]
    set cb0 := Main[38]
    set cb1 := Main[39]
    set cb2 := Main[40]
    set cb3 := Main[41]
    set cb4 := Main[42]
    set cb5 := Main[43]
    set smv := Main[44]
    set v0123 := Main[45]
    set v012 := Main[46]
    set v01 := Main[47]
    set ll0 := Main[48]
    set ll1 := Main[49]
    set ll2 := Main[50]
    set ll3 := Main[51]
    set hl0 := Main[52]
    set hl1 := Main[53]
    set hl2 := Main[54]
    set hl3 := Main[55]
    set lr0 := Main[56]
    set lr1 := Main[57]
    set lr2 := Main[58]
    set lr3 := Main[59]
    set su160 := Main[60]
    set su161 := Main[61]
    set su162 := Main[62]
    set su163 := Main[63]
    set srl := Main[64]
    set sra := Main[65]
    set srlw := Main[66]
    set sraw := Main[67]
    set bop := Main[68]
    obtain ⟨h_msb_b3, h_msb_b1, h_msb_a1, cpu, alu,
             b_srl, b_sra, b_srlw, b_sraw, one_of_ops, eq_bop,
             b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
             h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163, one_of_su16s,
             eq_v01, eq_v012, eq_v0123,
             lt_ll0, lt_hl0, h_b0_dec, lt_ll1, lt_hl1, h_b1_dec,
             lt_ll2, lt_hl2, h_b2_dec, lt_ll3, lt_hl3, h_b3_dec,
             eq_lr0, eq_lr1, eq_lr2, eq_lr3,
             w_msb_b, eq_smv, w_msb_srv, sr_rest⟩ := cstrs
    obtain ⟨nw_00, nw_01, nw_02, nw_03, nw_04, nw_05, nw_06, nw_07, nw_08, nw_09, nw_10, nw_11, nw_12, nw_13, nw_14, nw_15,
             w_00, w_01, w_02, w_03, w_04, w_05, eq_op_a_0⟩ := sr_rest
    clear h_msb_b1 h_msb_a1 cpu alu eq_op_a_0
    simp_all
    rw [← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    have : ((Word.toBitVec64 #v[c0, c1, c2, c3]).toNat % 64) = c0.val % 64 := by
      rw [Word.toBitVec64_toNat is_U64_c]; simp [Word.toNat]
      omega
    rw [this]; clear this
    have : c0.val % 64 = cb0.val + cb1.val * 2 + cb2.val * 4 + cb3.val * 8 + cb4.val * 16 + cb5.val * 32 := by
      rw [is_mod_64 (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)]
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · clear *- b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
        omega
      · omega
      · exact diff
    clear diff
    rw [this]; clear this
    rw [Word.toBitVec64_toInt (w := #v[a0, a1, a2, a3]) is_U64_a]
    rw [Word.toBitVec64_toInt (w := #v[b0, b1, b2, b3]) is_U64_b]
    have msb_b3_spec := U16MSBOperation.spec b3_16 h_msb_b3
    simp at msb_b3_spec
    have b_msb : msb_b = 0 ∨ msb_b = 1 := by
      clear *- msb_b3_spec
      split_ifs at msb_b3_spec <;> simp_all
    have b_msb_iff_neg_b : Word.isNegative #v[b0, b1, b2, b3] ↔ msb_b = 1 := by rw [msb_b3_spec, Word.isNegative]; aesop
    have b_msb_iff_neg_a : Word.isNegative #v[a0, a1, a2, a3] ↔ msb_b = 1 := by
      simp [msb_b3_spec, Word.isNegative]
      rcases b_su163 with h_su163 | h_su163 <;> simp_all
      · rcases b_su162 with h_su162 | h_su162 <;> simp_all
        · rcases b_su161 with h_su161 | h_su161 <;> simp_all
          · have ⟨h_cb4, h_cb5⟩ : cb4 = 0 ∧ cb5 = 0 := by clear *- b_cb4 b_cb5 h_su160; aesop
            simp_all
            clear *- b3_16 b_cb0 b_cb1 b_cb2 b_cb3 h_b3_dec lt_hl3 lt_ll3
            rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;> rcases b_cb3 <;>
            split_ifs <;> simp_all <;>
            (try apply cancel_mul_65536_v1 (by simp) at h_b3_dec) <;>
            omega
          · clear *-; split_ifs <;> omega
        · clear *-; split_ifs <;> omega
      · clear *-; split_ifs <;> omega
    by_cases h_neg : 32768 ≤ b3 <;> simp_all
    all_goals
      rcases b_cb0 <;> rcases b_cb1 <;> rcases b_cb2 <;>
      rcases b_cb3 <;> rcases b_cb4 <;> rcases b_cb5 <;>
      simp_all
    all_goals {
      try apply cancel_mul_65536_v1 (by simp) at h_b0_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b1_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b2_dec
      try apply cancel_mul_65536_v1 (by simp) at h_b3_dec
      simp_all
      iterate 2 rw [Word.toInt]
      try rw [if_pos b_msb_iff_neg_a, if_pos b_msb_iff_neg_b]
      try rw [if_neg b_msb_iff_neg_a, if_neg b_msb_iff_neg_b]
      iterate 2 rw [Word.toNat_def]
      iterate 8 rw [Vector.getElem_mk]
      simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
      clear *- lt_ll0 lt_hl0 lt_ll1 lt_hl1 lt_ll2 lt_hl2 lt_ll3 lt_hl3
      try simp only [Fin.add_def, Fin.mul_def]
      repeat rw [Nat.mod_eq_of_lt (a := _ * _) (b := 2130706433) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
      simp_all
      omega
    }

lemma spec.sra (h : is_sra Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
  := fun cstrs => spec.sra_common Main cstrs h.1

end sra

section srai

lemma spec.srai (h : is_srai Main) :
  List.Forall SP1Constraint.toProp (constraints Main) →
    Word.toBitVec64 #v[Main[32], Main[33], Main[34], Main[35]] = execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[25], Main[26], Main[27], Main[28]] .SRA
  := fun cstrs => spec.sra_common Main cstrs h.1

end srai

section sra_poly

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 400000000 in
-- 400M heartbeats: msb_b case split × 4-way byte_shift × 16-way cb sub-cases.
set_option debug.skipKernelTC true in
-- Skip kernel typechecking: `Word.toBitVec64_poly_toNat_poly` involves `2^N` re-checks
-- that trip kernel deep recursion (mirrors `spec.srl_common_poly`'s use).
/-- Shared proof body for `spec.sra_poly` and `spec.srai_poly`. Structure mirrors
`spec.srl_common_poly` but with two msb_b sub-cases:

- **msb_b = 0**: `BitVec.sshiftRight` reduces to `ushiftRight` at the Nat level
  (`BitVec.toNat_sshiftRight_of_msb_false`); the proof then matches SRL exactly
  (4 byte-shift branches × 16 cb sub-cases via `srl_close_su16_{0,1,2,3}_case`).
- **msb_b = 1**: sign-extension fills the high bits; the correction term
  `msb_b * (65536 - v_0123)` in the a_j constraints is non-trivial. Needs new
  sign-extension wrappers (`sra_close_su16_*_case`) — TODO.

For now, the prologue is set up and msb_b case-split structure laid out;
inner work stubbed with sorry. -/
private lemma spec.sra_common_poly (Main : Vector (ZMod p) 69)
    (cstrs : (constraints Main).allHold_poly) (eq_sra : Main[65] = 1) :
    Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
      execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]] .SRA := by
  -- Setup.
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  have hp : 2 ^ 17 < p := Fact.out
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h_real := is_real_eq_one_of_sra Main cstrs eq_sra
  have ⟨is_U64_b, is_U64_c⟩ := ops_U64_b_c_poly Main cstrs h_real
  obtain ⟨b0_16, b1_16, b2_16, b3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_b
  obtain ⟨c0_16, _c1_16, _c2_16, _c3_16⟩ := Word.lt_cases_of_isU64_poly is_U64_c
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ] at b0_16 b1_16 b2_16 b3_16 c0_16
  obtain ⟨_, sop_2, _, _⟩ := single_op_poly Main cstrs
  have ⟨h_no_srl, h_no_srlw, h_no_sraw⟩ := sop_2 eq_sra
  -- Open the iff_poly.
  change List.Forall SP1Constraint.toProp_poly (constraints Main) at cstrs
  rw [allHold_constraints_iff_poly] at cstrs
  -- Set up local names for Main[i] indices (mirrors SRL).
  set b0 := Main[15]; set b1 := Main[16]; set b2 := Main[17]; set b3 := Main[18]
  set c0 := Main[25]; set c1 := Main[26]; set c2 := Main[27]; set c3 := Main[28]
  set a0 := Main[32]; set a1 := Main[33]; set a2 := Main[34]; set a3 := Main[35]
  set msb_b := Main[36]; set msb_srw := Main[37]
  set cb0 := Main[38]; set cb1 := Main[39]; set cb2 := Main[40]
  set cb3 := Main[41]; set cb4 := Main[42]; set cb5 := Main[43]
  set smv := Main[44]; set v0123 := Main[45]; set v012 := Main[46]; set v01 := Main[47]
  set ll0 := Main[48]; set ll1 := Main[49]; set ll2 := Main[50]; set ll3 := Main[51]
  set hl0 := Main[52]; set hl1 := Main[53]; set hl2 := Main[54]; set hl3 := Main[55]
  set lr0 := Main[56]; set lr1 := Main[57]; set lr2 := Main[58]; set lr3 := Main[59]
  set su160 := Main[60]; set su161 := Main[61]; set su162 := Main[62]; set su163 := Main[63]
  -- Destructure (same shape as SRL prologue; h_msb_b3 has Main[65] = 1 multiplier
  -- which we'll use to extract msb_b via U16MSBOperation.spec_poly).
  obtain ⟨h_msb_b3, _, _, _, _,
           _, _, _, _, _, _,
           b_cb0, b_cb1, b_cb2, b_cb3, b_cb4, b_cb5, diff,
           h_su160, b_su160, h_su161, b_su161, h_su162, b_su162, h_su163, b_su163,
           one_of_su16s,
           eq_v01, eq_v012, eq_v0123,
           lt_ll0', lt_lh0', h_b0_dec, lt_ll1', lt_lh1', h_b1_dec,
           lt_ll2', lt_lh2', h_b2_dec, lt_ll3', lt_lh3', h_b3_dec,
           eq_lr0, eq_lr1, eq_lr2, eq_lr3,
           w_msb_b, eq_smv, w_msb_srv,
           sr_00, sr_01, sr_02, sr_03,
           sr_10, sr_11, sr_12, sr_13,
           sr_20, sr_21, sr_22, sr_23,
           sr_30, sr_31, sr_32, sr_33,
           srw_00, srw_01, srw_10, srw_11,
           srw_w2, srw_w3,
           _h_M13⟩ := cstrs
  -- h_sum_ne and bound specializations.
  have h_v0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h_v1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := by
    intro h; rw [h] at h_v1_val; rw [h_v0_val] at h_v1_val; exact zero_ne_one h_v1_val
  have h_sum_ne : ¬ Main[64] + Main[65] + Main[66] + Main[67] = 0 := by
    intro h
    rw [eq_sra, h_no_srl, h_no_srlw, h_no_sraw] at h
    simp only [add_zero, zero_add] at h
    exact h_one_ne_zero h
  have lt_ll0 := lt_ll0' h_sum_ne
  have lt_lh0 := lt_lh0' h_sum_ne
  have lt_ll1 := lt_ll1' h_sum_ne
  have lt_lh1 := lt_lh1' h_sum_ne
  have lt_ll2 := lt_ll2' h_sum_ne
  have lt_lh2 := lt_lh2' h_sum_ne
  have lt_ll3 := lt_ll3' h_sum_ne
  have lt_lh3 := lt_lh3' h_sum_ne
  -- Derive msb_b ∈ {0, 1} from U16MSBOperation.spec_poly on h_msb_b3.
  -- h_msb_b3 is the U16MSBOperation constraint on b3 with multiplier Main[65] = 1.
  -- For SRA arm, Main[65] = 1 (eq_sra), so the constraint is active.
  have h_msb_b_eq : msb_b = if b3.val ≥ 32768 then 1 else 0 := by
    rw [show msb_b = ({ msb := msb_b } : U16MSBOperation (ZMod p)).msb from rfl]
    apply U16MSBOperation.spec_poly b3_16
    rw [eq_sra] at h_msb_b3
    exact h_msb_b3
  -- Case-split on b3.val ≥ 32768 (equivalently msb_b ∈ {0, 1}).
  by_cases hb3 : b3.val ≥ 32768
  · -- b3.val ≥ 32768 ⇒ msb_b = 1 ⇒ result is sign-extended.
    have h_msb_b_one : msb_b = 1 := by rw [h_msb_b_eq, if_pos hb3]
    -- Establish `(Word.toBitVec64_poly b).msb = true` from `hb3`.
    have h_neg : Word.isNegative_poly #v[b0, b1, b2, b3] := by
      simp only [Word.isNegative_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_succ, List.getElem_cons_zero]
      exact hb3
    have h_msb_true : (Word.toBitVec64_poly #v[b0, b1, b2, b3]).msb = true :=
      (Word.isNegative_poly_msb is_U64_b).mp h_neg
    -- Reduce 64-bit goal to nat arithmetic via the signed-complement form.
    rw [← BitVec.toNat_inj]
    simp only [execute_RTYPE_pure_w_poly, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_true]
    simp only [Nat.shiftRight_eq_div_pow]
    -- Reduce shift count to `c0.val % 64` (same as msb_b=0 arm).
    have h_shift_eq : (Word.toBitVec64_poly #v[c0, c1, c2, c3]).toNat % 2 ^ 6 = c0.val % 64 := by
      rw [Word.toBitVec64_poly_toNat_poly is_U64_c, Word.toNat_poly_def]
      simp; omega
    rw [h_shift_eq]; clear h_shift_eq
    have h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
      have hcb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have h_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
      omega
    have h_val_10 : (10 : ZMod p).val = 10 := by
      rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
      exact ZMod.val_natCast_of_lt (by omega)
    have h_diff := diff h_sum_ne
    rw [h_val_10] at h_diff
    have h_c0_mod : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
      apply is_mod_64_poly (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
      · exact h_cb_sum_lt
      · exact c0_16
      · exact h_diff
    rw [h_c0_mod]; clear h_c0_mod h_diff h_cb_sum_lt
    -- De-gate h_b2_dec, h_b3_dec (multiplier `(srl + sra)` = 0 + 1 = 1).
    rw [h_no_srl, eq_sra] at h_b2_dec h_b3_dec
    simp only [zero_add, mul_one] at h_b2_dec h_b3_dec
    -- Pre-process disjunct gates.
    rw [h_no_srl] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                     sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                     h_su160 h_su161 h_su162 h_su163 one_of_su16s w_msb_b
    rw [h_no_srlw] at w_msb_srv one_of_su16s
    rw [h_no_sraw] at w_msb_srv one_of_su16s
    rw [eq_sra] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                    sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                    h_su160 h_su161 h_su162 h_su163 one_of_su16s
    simp only [add_zero, zero_add] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                                       sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                                       h_su160 h_su161 h_su162 h_su163 one_of_su16s w_msb_srv
    simp only [show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
      at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
         sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
         one_of_su16s
    have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => h_one_ne_zero h.symm
    simp only [show ((0 : ZMod p) = 1) ↔ False from ⟨h_zero_ne_one, False.elim⟩, false_or]
      at w_msb_srv
    -- smv = v0123 (from eq_smv: smv = msb_b * v0123 with msb_b = 1).
    rw [h_msb_b_one, one_mul] at eq_smv
    have h_su_sum : su160 + su161 + su162 + su163 = 1 := one_of_su16s
    simp only [mul_one] at h_su160 h_su161 h_su162 h_su163
    -- Substitute msb_b = 1, smv = v0123 into the chip's a-form disjuncts.
    simp only [h_msb_b_one, eq_smv, one_mul]
      at sr_03 sr_12 sr_13 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
    -- 4-way case-split on cb4, cb5 → byte_shift ∈ {0, 1, 2, 3}.
    rcases b_cb5 with hcb5 | hcb5 <;> rcases b_cb4 with hcb4 | hcb4
    · -- byte_shift = 0: cb4 = 0, cb5 = 0. su160 = 1.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
      have h_su160_eq : su160 = 1 := by
        have := h_su_sum
        rw [h_su161_zero, h_su162_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr0 :=
        sr_00.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a1_eq : a1 = lr1 :=
        sr_01.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a2_eq : a2 = lr2 :=
        sr_02.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a3_eq : a3 = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := sr_03.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
        convert this using 2
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 1: cb4 = 1, cb5 = 0. su161 = 1.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 := h_su160.resolve_right h_one_ne_zero
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su161_eq : su161 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su162_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr1 :=
        sr_10.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      have h_a1_eq : a1 = lr2 :=
        sr_11.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      have h_a2_eq : a2 = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := sr_12.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
        convert this using 2
      have h_a3_eq : a3 = ((65535 : ℕ) : ZMod p) := by
        have := sr_13.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
        convert this using 1
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr1, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 2: cb4 = 0, cb5 = 1. su162 = 1.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 := h_su160.resolve_right val_2_ne_zero
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_eq : su162 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su161_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr2 :=
        sr_20.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
      have h_a1_eq : a1 = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := sr_21.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
        convert this using 2
      have h_a2_eq : a2 = ((65535 : ℕ) : ZMod p) := by
        have := sr_22.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
        convert this using 1
      have h_a3_eq : a3 = ((65535 : ℕ) : ZMod p) := by
        have := sr_23.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
        convert this using 1
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 3: cb4 = 1, cb5 = 1. su163 = 1.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right (fun h => val_3_ne_zero (by linear_combination h))
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => val_2_ne_zero (by linear_combination h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
      have h_su163_eq : su163 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su161_zero, h_su162_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr3 + (((65536 : ℕ) : ZMod p) - v0123) := by
        have := sr_30.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
        convert this using 2
      have h_a1_eq : a1 = ((65535 : ℕ) : ZMod p) := by
        have := sr_31.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
        convert this using 1
      have h_a2_eq : a2 = ((65535 : ℕ) : ZMod p) := by
        have := sr_32.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
        convert this using 1
      have h_a3_eq : a3 = ((65535 : ℕ) : ZMod p) := by
        have := sr_33.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
        convert this using 1
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact sra_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
  · -- b3.val < 32768 ⇒ msb_b = 0 ⇒ result matches SRL (4×16 blast via srl_close_su16_*_case).
    have h_msb_b_zero : msb_b = 0 := by rw [h_msb_b_eq, if_neg hb3]
    -- Establish (Word.toBitVec64_poly b).msb = false from hb3.
    have h_not_neg : ¬ Word.isNegative_poly #v[b0, b1, b2, b3] := by
      simp only [Word.isNegative_poly, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_succ, List.getElem_cons_zero]
      omega
    have h_msb_false : (Word.toBitVec64_poly #v[b0, b1, b2, b3]).msb = false := by
      have h_neg_iff := Word.isNegative_poly_msb is_U64_b
      cases h_eq : (Word.toBitVec64_poly #v[b0, b1, b2, b3]).msb
      · rfl
      · exact absurd (h_neg_iff.mpr h_eq) h_not_neg
    -- Goal manipulation: reduce to nat arithmetic.
    rw [← BitVec.toNat_inj]
    simp only [execute_RTYPE_pure_w_poly, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_false]
    simp only [Nat.shiftRight_eq_div_pow]
    -- Reduce shift count `(toBitVec64_poly c).toNat % 2^6` to `c0.val % 64`.
    have h_shift_eq : (Word.toBitVec64_poly #v[c0, c1, c2, c3]).toNat % 2 ^ 6 = c0.val % 64 := by
      rw [Word.toBitVec64_poly_toNat_poly is_U64_c, Word.toNat_poly_def]
      simp; omega
    rw [h_shift_eq]; clear h_shift_eq
    -- Reduce c0.val % 64 to (cb_sum_zmod).val via is_mod_64_poly.
    have h_cb_sum_lt : (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val < 64 := by
      have hcb0 : cb0.val ≤ 1 := by rcases b_cb0 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb1 : cb1.val ≤ 1 := by rcases b_cb1 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb2 : cb2.val ≤ 1 := by rcases b_cb2 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb3 : cb3.val ≤ 1 := by rcases b_cb3 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb4 : cb4.val ≤ 1 := by rcases b_cb4 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have hcb5 : cb5.val ≤ 1 := by rcases b_cb5 with h | h <;> rw [h] <;> simp [h_v0_val, h_v1_val]
      have h_eq := cb_sum_val_eq_poly b_cb0 b_cb1 b_cb2 b_cb3 b_cb4 b_cb5
      omega
    have h_val_10 : (10 : ZMod p).val = 10 := by
      rw [show (10 : ZMod p) = ((10 : ℕ) : ZMod p) from by push_cast; rfl]
      exact ZMod.val_natCast_of_lt (by omega)
    have h_diff := diff h_sum_ne
    rw [h_val_10] at h_diff
    have h_c0_mod : c0.val % 64 = (cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32 : ZMod p).val := by
      apply is_mod_64_poly (m := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32)
      · exact h_cb_sum_lt
      · exact c0_16
      · exact h_diff
    rw [h_c0_mod]; clear h_c0_mod h_diff h_cb_sum_lt
    -- De-gate h_b2_dec, h_b3_dec (multiplier `(srl + sra)` = 0 + 1 = 1).
    rw [h_no_srl, eq_sra] at h_b2_dec h_b3_dec
    simp only [zero_add, mul_one] at h_b2_dec h_b3_dec
    -- Pre-process disjunct gates: substitute h_no_srl/srlw/sraw and eq_sra.
    rw [h_no_srl] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                     sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                     h_su160 h_su161 h_su162 h_su163 one_of_su16s w_msb_b
    rw [h_no_srlw] at w_msb_srv one_of_su16s
    rw [h_no_sraw] at w_msb_srv one_of_su16s
    rw [eq_sra] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                    sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                    h_su160 h_su161 h_su162 h_su163 one_of_su16s
    -- Reduce `0 + 1 = 0` (False) and `0 + 0 = 1` (False) disjuncts.
    simp only [add_zero, zero_add] at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
                                       sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
                                       h_su160 h_su161 h_su162 h_su163 one_of_su16s w_msb_srv
    -- Drop the False `(1 : ZMod p) = 0` disjunct from sr_**, one_of_su16s.
    simp only [show ((1 : ZMod p) = 0) ↔ False from ⟨h_one_ne_zero, False.elim⟩, false_or]
      at sr_00 sr_01 sr_02 sr_03 sr_10 sr_11 sr_12 sr_13
         sr_20 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
         one_of_su16s
    -- Drop the False `(0 : ZMod p) = 1` disjunct from w_msb_srv.
    have h_zero_ne_one : (0 : ZMod p) ≠ 1 := fun h => h_one_ne_zero h.symm
    simp only [show ((0 : ZMod p) = 1) ↔ False from ⟨h_zero_ne_one, False.elim⟩, false_or]
      at w_msb_srv
    -- smv = 0 (from eq_smv: smv = msb_b * v0123 with msb_b = 0).
    rw [h_msb_b_zero, zero_mul] at eq_smv
    -- Specialize one_of_su16s.
    have h_su_sum : su160 + su161 + su162 + su163 = 1 := one_of_su16s
    -- Simplify mul_one in h_su16k.
    simp only [mul_one] at h_su160 h_su161 h_su162 h_su163
    -- Simplify correction terms in sr_** using msb_b = 0 and eq_smv (smv = 0).
    simp only [h_msb_b_zero, eq_smv, zero_mul, mul_zero, sub_zero, zero_sub, neg_zero,
               add_zero, sub_self] at sr_03 sr_12 sr_13 sr_21 sr_22 sr_23 sr_30 sr_31 sr_32 sr_33
    -- 4-way case-split on cb4, cb5 → byte_shift ∈ {0, 1, 2, 3}.
    rcases b_cb5 with hcb5 | hcb5 <;> rcases b_cb4 with hcb4 | hcb4
    · -- byte_shift = 0: cb4 = 0, cb5 = 0. su160 = 1, others = 0.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero] at h_su160 h_su161 h_su162 h_su163
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_3_ne_zero (by linear_combination -h))
      have h_su160_eq : su160 = 1 := by
        have := h_su_sum
        rw [h_su161_zero, h_su162_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr0 :=
        sr_00.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a1_eq : a1 = lr1 :=
        sr_01.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a2_eq : a2 = lr2 :=
        sr_02.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      have h_a3_eq : a3 = lr3 :=
        sr_03.resolve_left (fun h => h_one_ne_zero (h_su160_eq.symm.trans h))
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr0, eq_lr1, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_0_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 1: cb4 = 1, cb5 = 0. su161 = 1, others = 0.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right h_one_ne_zero
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => val_2_ne_zero (by linear_combination -h))
      have h_su161_eq : su161 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su162_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr1 :=
        sr_10.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      have h_a1_eq : a1 = lr2 :=
        sr_11.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      have h_a2_eq : a2 = lr3 :=
        sr_12.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      have h_a3_eq : a3 = 0 :=
        sr_13.resolve_left (fun h => h_one_ne_zero (h_su161_eq.symm.trans h))
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr1, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_1_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 2: cb5 = 1, cb4 = 0. su162 = 1, others = 0.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right val_2_ne_zero
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
      have h_su163_zero : su163 = 0 :=
        h_su163.resolve_right (fun h => h_one_ne_zero (by linear_combination -h))
      have h_su162_eq : su162 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su161_zero, h_su163_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr2 :=
        sr_20.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
      have h_a1_eq : a1 = lr3 :=
        sr_21.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
      have h_a2_eq : a2 = 0 :=
        sr_22.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
      have h_a3_eq : a3 = 0 :=
        sr_23.resolve_left (fun h => h_one_ne_zero (h_su162_eq.symm.trans h))
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr2, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_2_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
    · -- byte_shift = 3: cb5 = 1, cb4 = 1. su163 = 1, others = 0.
      rw [hcb4, hcb5] at h_su160 h_su161 h_su162 h_su163
      simp only [zero_add, zero_mul, mul_zero, add_zero, one_mul, mul_one] at h_su160 h_su161 h_su162 h_su163
      have h_su160_zero : su160 = 0 :=
        h_su160.resolve_right (fun h => val_3_ne_zero (by linear_combination h))
      have h_su161_zero : su161 = 0 :=
        h_su161.resolve_right (fun h => val_2_ne_zero (by linear_combination h))
      have h_su162_zero : su162 = 0 :=
        h_su162.resolve_right (fun h => h_one_ne_zero (by linear_combination h))
      have h_su163_eq : su163 = 1 := by
        have := h_su_sum
        rw [h_su160_zero, h_su161_zero, h_su162_zero] at this
        linear_combination this
      have h_a0_eq : a0 = lr3 :=
        sr_30.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
      have h_a1_eq : a1 = 0 :=
        sr_31.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
      have h_a2_eq : a2 = 0 :=
        sr_32.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
      have h_a3_eq : a3 = 0 :=
        sr_33.resolve_left (fun h => h_one_ne_zero (h_su163_eq.symm.trans h))
      rw [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq, eq_lr3]
      rcases b_cb0 with hcb0 | hcb0 <;> rcases b_cb1 with hcb1 | hcb1 <;>
        rcases b_cb2 with hcb2 | hcb2 <;> rcases b_cb3 with hcb3 | hcb3
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 0 (by omega) 65536 1 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 8 (by omega) 256 256 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 4 (by omega) 4096 16 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 12 (by omega) 16 4096 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 2 (by omega) 16384 4 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 10 (by omega) 64 1024 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 6 (by omega) 1024 64 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 14 (by omega) 4 16384 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 1 (by omega) 32768 2 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 9 (by omega) 128 512 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 5 (by omega) 2048 32 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 13 (by omega) 8 8192 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 3 (by omega) 8192 8 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 11 (by omega) 32 2048 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 7 (by omega) 512 128 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec
      · exact srl_close_su16_3_case (cb4 := cb4) (cb5 := cb5) 15 (by omega) 2 32768 (by decide) (by omega) rfl rfl (by omega)
          (by rw [eq_v0123, eq_v012, eq_v01, hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3]; push_cast; ring)
          (by rw [hcb0, hcb1, hcb2, hcb3, hcb4, hcb5]; push_cast; ring)
          lt_ll0 lt_lh0 lt_ll1 lt_lh1 lt_ll2 lt_lh2 lt_ll3 lt_lh3
          h_b0_dec h_b1_dec h_b2_dec h_b3_dec

lemma spec.sra_poly (Main : Vector (ZMod p) 69) (h : is_sra_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRA :=
  fun cstrs => spec.sra_common_poly Main cstrs h.1

lemma spec.srai_poly (Main : Vector (ZMod p) 69) (h : is_srai_poly Main) :
    (constraints Main).allHold_poly →
      Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]] =
        execute_RTYPE_pure_w_poly #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]] .SRA :=
  fun cstrs => spec.sra_common_poly Main cstrs h.1

end sra_poly

end ShiftRight
