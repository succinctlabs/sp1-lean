import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — unsigned 64-bit evidence extraction

This is the circuit-independent `DIVU`/`REMU` family proof. It consumes the folded whole-row
`DivRemCore.CoreSpec` and `DivRemCompare.CompareSpec`, decodes the selected row's exact Rust
assertion tail once, and produces the Euclidean evidence consumed by `Cases.Unsigned64Evidence`.
No circuit offsets or witness-layout reductions cross this boundary. -/

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemContract

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private theorem unsigned64_word_gate {cols : Columns (ZMod p)} {case : Case}
    (hfamily : case.family = .unsigned64) (hselected : Selected cols case) :
    cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 0 := by
  cases case <;> simp [Case.family] at hfamily
  all_goals
    change Case.divw.flag cols + Case.remw.flag cols + Case.divuw.flag cols +
      Case.remuw.flag cols = 0
    rw [hselected.flag_eq .divw, hselected.flag_eq .remw,
      hselected.flag_eq .divuw, hselected.flag_eq .remuw]
    simp

set_option maxHeartbeats 16000000 in
/-- The folded DivRem row contracts imply the explicit unsigned-64 Euclidean evidence for either
`DIVU` or `REMU`. The output-routing equality is deliberately left to the uniform row assembler. -/
theorem unsigned64Evidence {input : Inputs (ZMod p)} {cols : Columns (ZMod p)} {case : Case}
    (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols)
    (hcompare : DivRemCompare.CompareSpec (DivRemCompare.Inputs.ofCols cols))
    (hreal : input.is_real = 1) (hinputReal : cols.is_real = input.is_real)
    (hadapter : cols.adapter = input.adapter)
    (hselected : Selected cols case) (hfamily : case.family = .unsigned64) :
    Cases.FamilyEvidence case.family (Word.toBitVec64 input.op_b_val)
      (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 cols.quotient)
      (Word.toBitVec64 cols.remainder) := by
  obtain ⟨hproduct, hown, _hselection, hrange⟩ := hcore
  simp only [DivRemCore.OwnAssertsHold, ownAsserts, List.forall_mem_cons] at hown
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23,
    e29, e35, e41, e47, e48, e49, e51, e54,
    e57, e59, e61, e64, e67, e69, e70, e71,
    e73, e76, e79, e81, e83, e86, e89, e91,
    e96, e99, e103, e105, e107, e109, e111, e113,
    e115, e117, e119, e154, e157, e160, e163, e167,
    e171, e175, e179, e184, e189, e194, e199, e204,
    e209, e214, e219, e225, e228, e230, e232, e234,
    e236, e238, e240, e242, e244, e247, e250, e253,
    e256, e259, e262, e265, e268, e270, e272, e274,
    e276, e278, e280, e282, e284, e286, e288, e299,
    e300, e301, e302, e305, e307, e309, e311, e313,
    e315, e317, e319, e321, e323, e325, e327, e329,
    e331, e333, e335, e337, e339, e341, e343, e345,
    e347, e349, e351, e353, e355, e357, e359, e367,
    eopa0⟩ := hown
  have hword : cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 0 :=
    unsigned64_word_gate hfamily hselected
  have hsigned : cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 0 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.div.flag cols + Case.rem.flag cols + Case.divw.flag cols +
        Case.remw.flag cols = 0
      rw [hselected.flag_eq .div, hselected.flag_eq .rem,
        hselected.flag_eq .divw, hselected.flag_eq .remw]
      simp
  have hunsigned : cols.is_divu + cols.is_remu = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divu.flag cols + Case.remu.flag cols = 1
      rw [hselected.flag_eq .divu, hselected.flag_eq .remu]
      simp
  have h64 : cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divu.flag cols + Case.remu.flag cols + Case.div.flag cols +
        Case.rem.flag cols = 1
      rw [hselected.flag_eq .divu, hselected.flag_eq .remu,
        hselected.flag_eq .div, hselected.flag_eq .rem]
      simp
  have hir : cols.is_real = 1 := hinputReal.trans hreal
  have hirnw : cols.is_real_not_word = 1 := by
    rw [hword, hir] at e13
    linear_combination e13
  have hbneg : cols.b_neg = 0 := by
    rw [hsigned] at e15
    linear_combination -e15
  have hrneg : cols.rem_neg = 0 := by
    rw [hsigned] at e17
    linear_combination -e17
  have hcneg : cols.c_neg = 0 := by
    rw [hsigned] at e19
    linear_combination -e19
  have hov : cols.is_overflow = 0 := by
    rw [hsigned] at e96
    linear_combination e96
  rw [hadapter] at e20 e21 e22 e23 e29 e35 e41 e47
  have hb0 : cols.b[0] = input.op_b_val[0] := by linear_combination -e20
  have hb1 : cols.b[1] = input.op_b_val[1] := by linear_combination -e22
  have hb2 : cols.b[2] = input.op_b_val[2] := by
    rw [hword] at e29
    linear_combination e29
  have hb3 : cols.b[3] = input.op_b_val[3] := by
    rw [hword] at e41
    linear_combination e41
  have hc0 : cols.c[0] = input.op_c_val[0] := by linear_combination -e21
  have hc1 : cols.c[1] = input.op_c_val[1] := by linear_combination -e23
  have hc2 : cols.c[2] = input.op_c_val[2] := by
    rw [hword] at e35
    linear_combination e35
  have hc3 : cols.c[3] = input.op_c_val[3] := by
    rw [hword] at e47
    linear_combination e47
  have hbEq : cols.b = input.op_b_val := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> assumption
  have hcEq : cols.c = input.op_c_val := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> assumption
  have hbU : Word.isU64 cols.b := hbEq ▸ hbReadU
  have hcU : Word.isU64 cols.c := hcEq ▸ hcReadU
  obtain ⟨_r0, _r1, _r2, _r3, _r4, _r5, _r6, _r7,
    _habsCU, _habsRU, hquotRange, hremRange, hctqRange⟩ := hrange hir
  have hquotU : Word.isU64 cols.quotient := by
    apply Word.isU64_of_cases
    · exact hquotRange 0 (by norm_num)
    · exact hquotRange 1 (by norm_num)
    · exact hquotRange 2 (by norm_num)
    · exact hquotRange 3 (by norm_num)
  have hremU : Word.isU64 cols.remainder := by
    apply Word.isU64_of_cases
    · exact hremRange 0 (by norm_num)
    · exact hremRange 1 (by norm_num)
    · exact hremRange 2 (by norm_num)
    · exact hremRange 3 (by norm_num)
  have hqc0 : cols.quotient_comp[0] = cols.quotient[0] := by linear_combination e48
  have hqc1 : cols.quotient_comp[1] = cols.quotient[1] := by linear_combination e49
  have hqc2 : cols.quotient_comp[2] = cols.quotient[2] := by
    rw [h64] at e59
    linear_combination e59
  have hqc3 : cols.quotient_comp[3] = cols.quotient[3] := by
    rw [h64] at e69
    linear_combination e69
  have hqcEq : cols.quotient_comp = cols.quotient := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> assumption
  have hqcU : Word.isU64 cols.quotient_comp := hqcEq ▸ hquotU
  have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := by linear_combination e70
  have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := by linear_combination e71
  have hrc2 : cols.remainder_comp[2] = cols.remainder[2] := by
    rw [h64] at e81
    linear_combination e81
  have hrc3 : cols.remainder_comp[3] = cols.remainder[3] := by
    rw [h64] at e91
    linear_combination e91
  have hrcEq : cols.remainder_comp = cols.remainder := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> assumption
  have hrcU : Word.isU64 cols.remainder_comp := hrcEq ▸ hremU
  have hctqLoU : Word.isU64 (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
      cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p)) := by
    apply Word.isU64_of_cases
    · exact hctqRange 0 (by norm_num)
    · exact hctqRange 1 (by norm_num)
    · exact hctqRange 2 (by norm_num)
    · exact hctqRange 3 (by norm_num)
  have hctqHiU : Word.isU64 (#v[cols.c_times_quotient[4], cols.c_times_quotient[5],
      cols.c_times_quotient[6], cols.c_times_quotient[7]] : Word (ZMod p)) := by
    apply Word.isU64_of_cases
    · exact hctqRange 4 (by norm_num)
    · exact hctqRange 5 (by norm_num)
    · exact hctqRange 6 (by norm_num)
    · exact hctqRange 7 (by norm_num)
  unfold DivRemCore.ProductSpec at hproduct
  obtain ⟨hmulLo, hproduct⟩ := hproduct
  obtain ⟨hmulHi, hproduct⟩ := hproduct
  obtain ⟨hglueLo, hglueHi⟩ := hproduct
  rw [DivRemCore.LowerProductPlacement] at hglueLo
  rw [DivRemCore.UpperProductPlacement] at hglueHi
  obtain ⟨hglue0, hglue1, hglue2, hglue3⟩ := hglueLo hir
  have hg64 : cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu = 1 := by
    linear_combination h64
  obtain ⟨hglue4, hglue5, hglue6, hglue7⟩ := hglueHi hg64
  have hlo := rwlo_product (fun _ => hmulLo) hir hglue0 hglue1 hglue2 hglue3
  have hsigned64 : cols.is_div + cols.is_rem = 0 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.div.flag cols + Case.rem.flag cols = 0
      rw [hselected.flag_eq .div, hselected.flag_eq .rem]
      simp
  have hhi := rwhi_product_unsigned (fun _ => hmulHi) hirnw hsigned64 hunsigned
    hglue4 hglue5 hglue6 hglue7
  have hcarry0 := bool_of_mul_pred e309
  have hcarry1 := bool_of_mul_pred e311
  have hcarry2 := bool_of_mul_pred e313
  have hcarry3 := bool_of_mul_pred e315
  have hcarry4 := bool_of_mul_pred e317
  have hcarry5 := bool_of_mul_pred e319
  have hcarry6 := bool_of_mul_pred e321
  have hcarry7 := bool_of_mul_pred e323
  have hchain0 : cols.c_times_quotient[0] + cols.remainder_comp[0] =
      cols.b[0] + cols.carry[0] * 65536 := by
    rw [hov] at e154
    linear_combination e154
  have hchain1 : cols.c_times_quotient[1] + cols.remainder_comp[1] + cols.carry[0] =
      cols.b[1] + cols.carry[1] * 65536 := by
    rw [hov] at e157
    linear_combination e157
  have hchain2 : cols.c_times_quotient[2] + cols.remainder_comp[2] + cols.carry[1] =
      cols.b[2] + cols.carry[2] * 65536 := by
    rw [hov] at e160
    linear_combination e160
  have hchain3 : cols.c_times_quotient[3] + cols.remainder_comp[3] + cols.carry[2] =
      cols.b[3] + cols.carry[3] * 65536 := by
    rw [hov] at e163
    linear_combination e163
  have hchain4 : cols.c_times_quotient[4] + cols.carry[3] = cols.carry[4] * 65536 := by
    rw [hov, hbneg, hrneg] at e167
    linear_combination e167
  have hchain5 : cols.c_times_quotient[5] + cols.carry[4] = cols.carry[5] * 65536 := by
    rw [hov, hbneg, hrneg] at e171
    linear_combination e171
  have hchain6 : cols.c_times_quotient[6] + cols.carry[5] = cols.carry[6] * 65536 := by
    rw [hov, hbneg, hrneg] at e175
    linear_combination e175
  have hchain7 : cols.c_times_quotient[7] + cols.carry[6] = cols.carry[7] * 65536 := by
    rw [hov, hbneg, hrneg] at e179
    linear_combination e179
  have hid := hid_of_carry_chain hcU hbU hqcU hrcU hctqLoU hctqHiU
    hcarry0 hcarry1 hcarry2 hcarry3 hcarry4 hcarry5 hcarry6 hcarry7
    hchain0 hchain1 hchain2 hchain3 hchain4 hchain5 hchain6 hchain7 hlo hhi
  simp only [DivRemCompare.CompareSpec, DivRemCompare.Inputs.ofCols] at hcompare
  obtain ⟨_hovbFull, _hovcFull, _hovbLow, _hovcLow, hisZero, _haddC, _haddR,
    hltSpec, _hmsbB3, _hmsbC3, _hmsbR3, _hmsbB1, _hmsbC1, _hmsbR1, _hmsbQ1⟩ := hcompare
  have hzero : cols.c.toNat = 0 →
      cols.quotient_comp.toNat = 2 ^ 64 - 1 ∧ cols.remainder_comp.toNat = cols.b.toNat := by
    intro hcZero
    have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
    obtain ⟨hcLt0, hcLt1, hcLt2, hcLt3⟩ := Word.lt_cases_of_isU64 hcU
    rw [Word.toNat_def] at hcZero
    have hcz0 : cols.c[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz1 : cols.c[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz2 : cols.c[2] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz3 : cols.c[3] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    rw [if_pos ⟨hcz0, hcz1, hcz2, hcz3⟩] at hzeroResult
    rw [hzeroResult, one_mul] at e230 e232 e234 e236 e238 e240 e242 e244
    refine ⟨?_, ?_⟩
    · rw [hqcEq, Word.toNat_def]
      have hq0 : cols.quotient[0] = 65535 := by linear_combination e230
      have hq1 : cols.quotient[1] = 65535 := by linear_combination e232
      have hq2 : cols.quotient[2] = 65535 := by linear_combination e234
      have hq3 : cols.quotient[3] = 65535 := by linear_combination e236
      rw [hq0, hq1, hq2, hq3]
      simp only [val_65535_zmod_p]
      norm_num
    · have hr0 : cols.remainder_comp[0] = cols.b[0] := by linear_combination e238
      have hr1 : cols.remainder_comp[1] = cols.b[1] := by linear_combination e240
      have hr2 : cols.remainder_comp[2] = cols.b[2] := by linear_combination e242
      have hr3 : cols.remainder_comp[3] = cols.b[3] := by linear_combination e244
      rw [Word.toNat_def, Word.toNat_def, hr0, hr1, hr2, hr3]
  have habsCU : Word.isU64 cols.abs_c := by
    apply Word.isU64_of_cases
    · exact _habsCU 0 (by norm_num)
    · exact _habsCU 1 (by norm_num)
    · exact _habsCU 2 (by norm_num)
    · exact _habsCU 3 (by norm_num)
  have habsRU : Word.isU64 cols.abs_remainder := by
    apply Word.isU64_of_cases
    · exact _habsRU 0 (by norm_num)
    · exact _habsRU 1 (by norm_num)
    · exact _habsRU 2 (by norm_num)
    · exact _habsRU 3 (by norm_num)
  have hlt : cols.c.toNat ≠ 0 → cols.remainder_comp.toNat < cols.c.toNat := by
    intro hcNe
    have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
    have hcnz : ¬ (cols.c[0] = 0 ∧ cols.c[1] = 0 ∧ cols.c[2] = 0 ∧ cols.c[3] = 0) := by
      rintro ⟨z0, z1, z2, z3⟩
      apply hcNe
      rw [Word.toNat_def, z0, z1, z2, z3]
      simp
    rw [if_neg hcnz] at hzeroResult
    have hrcm : cols.remainder_check_multiplicity = 1 := by
      rw [hzeroResult, hir] at e305
      linear_combination -e305
    have hmax0 : cols.max_abs_c_or_1[0] = cols.abs_c[0] := by
      rw [hzeroResult] at e299
      linear_combination e299
    have hmax1 : cols.max_abs_c_or_1[1] = cols.abs_c[1] := by
      rw [hzeroResult] at e300
      linear_combination e300
    have hmax2 : cols.max_abs_c_or_1[2] = cols.abs_c[2] := by
      rw [hzeroResult] at e301
      linear_combination e301
    have hmax3 : cols.max_abs_c_or_1[3] = cols.abs_c[3] := by
      rw [hzeroResult] at e302
      linear_combination e302
    have hmaxEq : cols.max_abs_c_or_1 = cols.abs_c := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> assumption
    have hmaxU : Word.isU64 cols.max_abs_c_or_1 := hmaxEq ▸ habsCU
    have hbit := (LtOperationUnsigned.result_semantic habsRU hmaxU hrcm hltSpec).1
    have hbit1 : cols.remainder_lt_operation.u16_compare_operation.bit = 1 := by
      rw [hrcm] at e307
      linear_combination -e307
    rw [hbit1] at hbit
    have hcmp : cols.abs_remainder.toNat < cols.max_abs_c_or_1.toNat := by
      by_contra hnot
      rw [if_neg hnot] at hbit
      exact one_ne_zero hbit
    have habsR0 : cols.abs_remainder[0] = cols.remainder_comp[0] := by
      rw [hrneg] at e250
      linear_combination e250
    have habsR1 : cols.abs_remainder[1] = cols.remainder_comp[1] := by
      rw [hrneg] at e256
      linear_combination e256
    have habsR2 : cols.abs_remainder[2] = cols.remainder_comp[2] := by
      rw [hrneg] at e262
      linear_combination e262
    have habsR3 : cols.abs_remainder[3] = cols.remainder_comp[3] := by
      rw [hrneg] at e268
      linear_combination e268
    have habsREq : cols.abs_remainder = cols.remainder_comp := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> assumption
    have habsC0 : cols.abs_c[0] = cols.c[0] := by
      rw [hcneg] at e247
      linear_combination e247
    have habsC1 : cols.abs_c[1] = cols.c[1] := by
      rw [hcneg] at e253
      linear_combination e253
    have habsC2 : cols.abs_c[2] = cols.c[2] := by
      rw [hcneg] at e259
      linear_combination e259
    have habsC3 : cols.abs_c[3] = cols.c[3] := by
      rw [hcneg] at e265
      linear_combination e265
    have habsCEq : cols.abs_c = cols.c := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> assumption
    simpa [habsREq, hmaxEq, habsCEq] using hcmp
  rw [hfamily]
  change Cases.Unsigned64Evidence (Word.toBitVec64 input.op_b_val)
    (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 cols.quotient)
    (Word.toBitVec64 cols.remainder)
  refine ⟨?_, ?_, ?_⟩
  · rw [Word.toBitVec64_toNat hbReadU, Word.toBitVec64_toNat hcReadU,
      Word.toBitVec64_toNat hquotU, Word.toBitVec64_toNat hremU]
    simpa [hbEq, hcEq, hqcEq, hrcEq] using hid
  · rw [Word.toBitVec64_toNat hcReadU, Word.toBitVec64_toNat hremU]
    simpa [hcEq, hrcEq] using hlt
  · rw [Word.toBitVec64_toNat hcReadU, Word.toBitVec64_toNat hquotU,
      Word.toBitVec64_toNat hremU, Word.toBitVec64_toNat hbReadU]
    simpa [hbEq, hcEq, hqcEq, hrcEq] using hzero

end SP1Clean.DivRemChip
