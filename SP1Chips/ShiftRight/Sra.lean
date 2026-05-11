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

end ShiftRight
