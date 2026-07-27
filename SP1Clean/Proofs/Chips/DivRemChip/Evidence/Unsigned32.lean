import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Assembly

/-! # `DivRemChip` — unsigned low-32 evidence extraction

This is the circuit-independent `DIVUW`/`REMUW` family proof. It consumes the folded whole-row
`DivRemCore.CoreSpec` and `DivRemCompare.CompareSpec`, projects the zero-extended arithmetic
columns to their low 32 bits, and proves the sign-extended architectural quotient and remainder.
No circuit offsets or witness-layout reductions cross this boundary. -/

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemContract

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option maxHeartbeats 16000000 in
/-- The folded DivRem row contracts imply the explicit unsigned-word Euclidean evidence for either
`DIVUW` or `REMUW`. The output-routing equality is deliberately left to the uniform row assembler. -/
theorem unsigned32Evidence {input : Inputs (ZMod p)} {cols : Columns (ZMod p)} {case : Case}
    (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols)
    (hcompare : DivRemCompare.CompareSpec (DivRemCompare.Inputs.ofCols cols))
    (hreal : input.is_real = 1) (hinputReal : cols.is_real = input.is_real)
    (hadapter : cols.adapter = input.adapter)
    (hselected : Selected cols case) (hfamily : case.family = .unsigned32) :
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
  have hword : cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divw.flag cols + Case.remw.flag cols + Case.divuw.flag cols +
        Case.remuw.flag cols = 1
      rw [hselected.flag_eq .divw, hselected.flag_eq .remw,
        hselected.flag_eq .divuw, hselected.flag_eq .remuw]
      simp
  have hsigned : cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 0 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.div.flag cols + Case.rem.flag cols + Case.divw.flag cols +
        Case.remw.flag cols = 0
      rw [hselected.flag_eq .div, hselected.flag_eq .rem,
        hselected.flag_eq .divw, hselected.flag_eq .remw]
      simp
  have huword : cols.is_divuw + cols.is_remuw = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divuw.flag cols + Case.remuw.flag cols = 1
      rw [hselected.flag_eq .divuw, hselected.flag_eq .remuw]
      simp
  have hir : cols.is_real = 1 := hinputReal.trans hreal
  have hirnw : cols.is_real_not_word = 0 := by
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
  have hb2 : cols.b[2] = 0 := by
    rw [hword, hbneg] at e29
    linear_combination e29
  have hb3 : cols.b[3] = 0 := by
    rw [hword, hbneg] at e41
    linear_combination e41
  have hc0 : cols.c[0] = input.op_c_val[0] := by linear_combination -e21
  have hc1 : cols.c[1] = input.op_c_val[1] := by linear_combination -e23
  have hc2 : cols.c[2] = 0 := by
    rw [hword, hcneg] at e35
    linear_combination e35
  have hc3 : cols.c[3] = 0 := by
    rw [hword, hcneg] at e47
    linear_combination e47
  obtain ⟨hbR0, hbR1, _, _⟩ := Word.lt_cases_of_isU64 hbReadU
  obtain ⟨hcR0, hcR1, _, _⟩ := Word.lt_cases_of_isU64 hcReadU
  have hbU : Word.isU64 cols.b := Word.isU64_of_cases
    (by rw [hb0]; exact hbR0) (by rw [hb1]; exact hbR1)
    (by rw [hb2]; simp) (by rw [hb3]; simp)
  have hcU : Word.isU64 cols.c := Word.isU64_of_cases
    (by rw [hc0]; exact hcR0) (by rw [hc1]; exact hcR1)
    (by rw [hc2]; simp) (by rw [hc3]; simp)
  obtain ⟨_r0, _r1, _r2, _r3, _r4, _r5, _r6, _r7,
    habsCRange, habsRRange, hquotRange, hremRange, hctqRange⟩ := hrange hir
  have hquotU : Word.isU64 cols.quotient := Word.isU64_of_cases
    (hquotRange 0 (by norm_num)) (hquotRange 1 (by norm_num))
    (hquotRange 2 (by norm_num)) (hquotRange 3 (by norm_num))
  have hremU : Word.isU64 cols.remainder := Word.isU64_of_cases
    (hremRange 0 (by norm_num)) (hremRange 1 (by norm_num))
    (hremRange 2 (by norm_num)) (hremRange 3 (by norm_num))
  have hqc0 : cols.quotient_comp[0] = cols.quotient[0] := by linear_combination e48
  have hqc1 : cols.quotient_comp[1] = cols.quotient[1] := by linear_combination e49
  have hqc2 : cols.quotient_comp[2] = 0 := by
    rw [huword] at e51
    linear_combination e51
  have hqc3 : cols.quotient_comp[3] = 0 := by
    rw [huword] at e61
    linear_combination e61
  have hqcU : Word.isU64 cols.quotient_comp := Word.isU64_of_cases
    (by rw [hqc0]; exact hquotRange 0 (by norm_num))
    (by rw [hqc1]; exact hquotRange 1 (by norm_num))
    (by rw [hqc2]; simp) (by rw [hqc3]; simp)
  have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := by linear_combination e70
  have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := by linear_combination e71
  have hrc2 : cols.remainder_comp[2] = 0 := by
    rw [huword] at e73
    linear_combination e73
  have hrc3 : cols.remainder_comp[3] = 0 := by
    rw [huword] at e83
    linear_combination e83
  have hrcU : Word.isU64 cols.remainder_comp := Word.isU64_of_cases
    (by rw [hrc0]; exact hremRange 0 (by norm_num))
    (by rw [hrc1]; exact hremRange 1 (by norm_num))
    (by rw [hrc2]; simp) (by rw [hrc3]; simp)
  have hctqLoU : Word.isU64 (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
      cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p)) :=
    Word.isU64_of_cases (hctqRange 0 (by norm_num)) (hctqRange 1 (by norm_num))
      (hctqRange 2 (by norm_num)) (hctqRange 3 (by norm_num))
  unfold DivRemCore.ProductSpec at hproduct
  obtain ⟨hmulLo, hproduct⟩ := hproduct
  obtain ⟨_hmulHi, hproduct⟩ := hproduct
  obtain ⟨hglueLo, _hglueHi⟩ := hproduct
  rw [DivRemCore.LowerProductPlacement] at hglueLo
  obtain ⟨hglue0, hglue1, hglue2, hglue3⟩ := hglueLo hir
  have hlo := rwlo_product (fun _ => hmulLo) hir hglue0 hglue1 hglue2 hglue3
  have hcarry0 := bool_of_mul_pred e309
  have hcarry1 := bool_of_mul_pred e311
  have hcarry2 := bool_of_mul_pred e313
  have hcarry3 := bool_of_mul_pred e315
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
  let carryLo : Vector (ZMod p) 4 :=
    #v[cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3]]
  have hcarry0' : carryLo[0] = 0 ∨ carryLo[0] = 1 := by simpa [carryLo] using hcarry0
  have hcarry1' : carryLo[1] = 0 ∨ carryLo[1] = 1 := by simpa [carryLo] using hcarry1
  have hcarry2' : carryLo[2] = 0 ∨ carryLo[2] = 1 := by simpa [carryLo] using hcarry2
  have hcarry3' : carryLo[3] = 0 ∨ carryLo[3] = 1 := by simpa [carryLo] using hcarry3
  have hchain0' :
      (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p))[0] +
          cols.remainder_comp[0] = cols.b[0] + carryLo[0] * 65536 := by
    simpa [carryLo] using hchain0
  have hchain1' :
      (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p))[1] +
          cols.remainder_comp[1] + carryLo[0] = cols.b[1] + carryLo[1] * 65536 := by
    simpa [carryLo] using hchain1
  have hchain2' :
      (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p))[2] +
          cols.remainder_comp[2] + carryLo[1] = cols.b[2] + carryLo[2] * 65536 := by
    simpa [carryLo] using hchain2
  have hchain3' :
      (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p))[3] +
          cols.remainder_comp[3] + carryLo[2] = cols.b[3] + carryLo[3] * 65536 := by
    simpa [carryLo] using hchain3
  have hid := euclid_identity_word_unsigned (carry := carryLo)
    hctqLoU hrcU hbU hqcU hcU hqc2 hqc3 hc2 hc3 hb2 hb3 hrc2 hrc3
    hcarry0' hcarry1' hcarry2' hcarry3' hchain0' hchain1' hchain2' hchain3' hlo
  simp only [DivRemCompare.CompareSpec, DivRemCompare.Inputs.ofCols] at hcompare
  obtain ⟨_hovbFull, _hovcFull, _hovbLow, _hovcLow, hisZero, _haddC, _haddR,
    hltSpec, _hmsbB3, _hmsbC3, _hmsbR3, _hmsbB1, _hmsbC1, hmsbR1, hmsbQ1⟩ := hcompare
  have hzero : cols.c.toNat = 0 →
      cols.quotient_comp.toNat = 2 ^ 32 - 1 ∧ cols.remainder_comp.toNat = cols.b.toNat := by
    intro hcZero
    have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
    rw [Word.toNat_def] at hcZero
    have hcz0 : cols.c[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz1 : cols.c[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz2 : cols.c[2] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    have hcz3 : cols.c[3] = 0 := (ZMod.val_eq_zero _).mp (by omega)
    rw [if_pos ⟨hcz0, hcz1, hcz2, hcz3⟩] at hzeroResult
    rw [hzeroResult, one_mul] at e230 e232 e238 e240 e242 e244
    refine ⟨?_, ?_⟩
    · have hq0 : cols.quotient_comp[0] = 65535 := by
        rw [hqc0]
        linear_combination e230
      have hq1 : cols.quotient_comp[1] = 65535 := by
        rw [hqc1]
        linear_combination e232
      rw [Word.toNat_def, hq0, hq1, hqc2, hqc3]
      simp only [val_65535_zmod_p, ZMod.val_zero]
      norm_num
    · have hr0 : cols.remainder_comp[0] = cols.b[0] := by linear_combination e238
      have hr1 : cols.remainder_comp[1] = cols.b[1] := by linear_combination e240
      have hr2 : cols.remainder_comp[2] = cols.b[2] := by linear_combination e242
      have hr3 : cols.remainder_comp[3] = cols.b[3] := by linear_combination e244
      rw [Word.toNat_def, Word.toNat_def, hr0, hr1, hr2, hr3]
  have habsCU : Word.isU64 cols.abs_c := Word.isU64_of_cases
    (habsCRange 0 (by norm_num)) (habsCRange 1 (by norm_num))
    (habsCRange 2 (by norm_num)) (habsCRange 3 (by norm_num))
  have habsRU : Word.isU64 cols.abs_remainder := Word.isU64_of_cases
    (habsRRange 0 (by norm_num)) (habsRRange 1 (by norm_num))
    (habsRRange 2 (by norm_num)) (habsRRange 3 (by norm_num))
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
  have hqmsb := hmsbQ1.2 hword
  have hrmsb := hmsbR1.2 hword
  have hq2 : cols.quotient[2] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e57
    linear_combination e57
  have hq3 : cols.quotient[3] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e67
    linear_combination e67
  have hr2 : cols.remainder[2] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e79
    linear_combination e79
  have hr3 : cols.remainder[3] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e89
    linear_combination e89
  have hq2sf : cols.quotient[2].val =
      (if 32768 ≤ cols.quotient[1].val then 65535 else 0) := by
    rw [hq2, hqmsb]
    split <;> simp [val_65535_zmod_p]
  have hq3sf : cols.quotient[3].val =
      (if 32768 ≤ cols.quotient[1].val then 65535 else 0) := by
    rw [hq3, hqmsb]
    split <;> simp [val_65535_zmod_p]
  have hr2sf : cols.remainder[2].val =
      (if 32768 ≤ cols.remainder[1].val then 65535 else 0) := by
    rw [hr2, hrmsb]
    split <;> simp [val_65535_zmod_p]
  have hr3sf : cols.remainder[3].val =
      (if 32768 ≤ cols.remainder[1].val then 65535 else 0) := by
    rw [hr3, hrmsb]
    split <;> simp [val_65535_zmod_p]
  have hqLow := extractLsb_lo_congr hqcU hquotU hqc0 hqc1
  have hrLow := extractLsb_lo_congr hrcU hremU hrc0 hrc1
  have hqArch : Word.toBitVec64 cols.quotient = BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (Word.toBitVec64 cols.quotient_comp)) := by
    rw [word_eq_signExtend_lo hquotU hq2sf hq3sf, hqLow]
  have hrArch : Word.toBitVec64 cols.remainder = BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (Word.toBitVec64 cols.remainder_comp)) := by
    rw [word_eq_signExtend_lo hremU hr2sf hr3sf, hrLow]
  have hbLow := toBitVec64_extractLsb hbU hbReadU hb0 hb1
  have hcLow := toBitVec64_extractLsb hcU hcReadU hc0 hc1
  rw [hfamily]
  change ∃ quotient32 remainder32 : BitVec 32,
    Word.toBitVec64 cols.quotient = BitVec.signExtend 64 quotient32 ∧
    Word.toBitVec64 cols.remainder = BitVec.signExtend 64 remainder32 ∧
    Cases.Unsigned32Evidence (Word.toBitVec64 input.op_b_val)
      (Word.toBitVec64 input.op_c_val) quotient32 remainder32
  refine ⟨BitVec.extractLsb 31 0 (Word.toBitVec64 cols.quotient_comp),
    BitVec.extractLsb 31 0 (Word.toBitVec64 cols.remainder_comp), hqArch, hrArch, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hbLow, ← hcLow, extractLsb_toNat_of_hi_zero hbU hb2 hb3,
      extractLsb_toNat_of_hi_zero hcU hc2 hc3,
      extractLsb_toNat_of_hi_zero hqcU hqc2 hqc3,
      extractLsb_toNat_of_hi_zero hrcU hrc2 hrc3]
    exact hid
  · rw [← hcLow, extractLsb_toNat_of_hi_zero hcU hc2 hc3,
      extractLsb_toNat_of_hi_zero hrcU hrc2 hrc3]
    exact hlt
  · rw [← hcLow, ← hbLow, extractLsb_toNat_of_hi_zero hcU hc2 hc3,
      extractLsb_toNat_of_hi_zero hqcU hqc2 hqc3,
      extractLsb_toNat_of_hi_zero hrcU hrc2 hrc3,
      extractLsb_toNat_of_hi_zero hbU hb2 hb3]
    exact hzero

end SP1Clean.DivRemChip
