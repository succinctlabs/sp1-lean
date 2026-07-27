import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Evidence.SignedCommon

/-! # `DivRemChip` — signed low-32 evidence extraction

This is the circuit-independent `DIVW`/`REMW` family proof. It consumes the folded whole-row
contracts, proves that the arithmetic operands and results are sign extensions of their low halves,
and makes the overflow, division-by-zero, and normal signed Euclidean cases explicit. -/

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemContract
open Extracted (DivRemCols)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option maxHeartbeats 16000000 in
/-- The folded DivRem row contracts imply explicit signed-word evidence for either `DIVW` or `REMW`.
The output-routing equality is deliberately left to the uniform row assembler. -/
theorem signed32Evidence {input : Inputs (ZMod p)} {cols : DivRemCols (ZMod p)} {case : Case}
    (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols)
    (hcompare : DivRemCompare.CompareSpec (DivRemCompare.Inputs.ofCols cols))
    (hreal : input.is_real = 1) (hinputReal : cols.is_real = input.is_real)
    (hadapter : cols.adapter = input.adapter)
    (hselected : Selected cols case) (hfamily : case.family = .signed32) :
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
  have hsigned : cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.div.flag cols + Case.rem.flag cols + Case.divw.flag cols +
        Case.remw.flag cols = 1
      rw [hselected.flag_eq .div, hselected.flag_eq .rem,
        hselected.flag_eq .divw, hselected.flag_eq .remw]
      simp
  have hsigned32 : cols.is_divw + cols.is_remw = 1 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divw.flag cols + Case.remw.flag cols = 1
      rw [hselected.flag_eq .divw, hselected.flag_eq .remw]
      simp
  have hsigned64 : cols.is_div + cols.is_rem = 0 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.div.flag cols + Case.rem.flag cols = 0
      rw [hselected.flag_eq .div, hselected.flag_eq .rem]
      simp
  have hunsigned64 : cols.is_divu + cols.is_remu = 0 := by
    cases case <;> simp [Case.family] at hfamily
    all_goals
      change Case.divu.flag cols + Case.remu.flag cols = 0
      rw [hselected.flag_eq .divu, hselected.flag_eq .remu]
      simp
  have hir : cols.is_real = 1 := hinputReal.trans hreal
  have hirnw : cols.is_real_not_word = 0 := by
    rw [hword, hir] at e13
    linear_combination e13
  simp only [DivRemCompare.CompareSpec, DivRemCompare.Inputs.ofCols] at hcompare
  obtain ⟨_hovbFull, _hovcFull, hovbLow, hovcLow, hisZero, haddC, haddR,
    hltSpec, _hmsbB3, _hmsbC3, _hmsbR3, hmsbB1, hmsbC1, hmsbR1, hmsbQ1⟩ := hcompare
  rw [hadapter] at e20 e21 e22 e23 e29 e35 e41 e47
  have hb0 : cols.b[0] = input.op_b_val[0] := by linear_combination -e20
  have hb1 : cols.b[1] = input.op_b_val[1] := by linear_combination -e22
  have hc0 : cols.c[0] = input.op_c_val[0] := by linear_combination -e21
  have hc1 : cols.c[1] = input.op_c_val[1] := by linear_combination -e23
  have hbRawEq : cols.adapter.op_b_memory.prev_value = input.op_b_val := by
    rw [hadapter]
  have hcRawEq : cols.adapter.op_c_memory.prev_value = input.op_c_val := by
    rw [hadapter]
  have hbRaw1 : cols.adapter.op_b_memory.prev_value[1] = cols.b[1] := by
    rw [hbRawEq]
    exact hb1.symm
  have hcRaw1 : cols.adapter.op_c_memory.prev_value[1] = cols.c[1] := by
    rw [hcRawEq]
    exact hc1.symm
  have hbmsb : cols.b_msb.msb = if 32768 ≤ cols.b[1].val then 1 else 0 := by
    have h := hmsbB1.2 hword
    change cols.b_msb.msb =
      (if 32768 ≤ cols.adapter.op_b_memory.prev_value[1].val then 1 else 0) at h
    rw [hbRaw1] at h
    exact h
  have hcmsb : cols.c_msb.msb = if 32768 ≤ cols.c[1].val then 1 else 0 := by
    have h := hmsbC1.2 hword
    change cols.c_msb.msb =
      (if 32768 ≤ cols.adapter.op_c_memory.prev_value[1].val then 1 else 0) at h
    rw [hcRaw1] at h
    exact h
  have hbnegEq : cols.b_neg = cols.b_msb.msb := by
    rw [hsigned] at e15
    linear_combination -e15
  have hcnegEq : cols.c_neg = cols.c_msb.msb := by
    rw [hsigned] at e19
    linear_combination -e19
  have hrnegEq : cols.rem_neg = cols.rem_msb.msb := by
    rw [hsigned] at e17
    linear_combination -e17
  have hb2 : cols.b[2] = cols.b_neg * 65535 := by
    rw [hword] at e29
    linear_combination e29
  have hb3 : cols.b[3] = cols.b_neg * 65535 := by
    rw [hword] at e41
    linear_combination e41
  have hc2 : cols.c[2] = cols.c_neg * 65535 := by
    rw [hword] at e35
    linear_combination e35
  have hc3 : cols.c[3] = cols.c_neg * 65535 := by
    rw [hword] at e47
    linear_combination e47
  obtain ⟨hbR0, hbR1, _, _⟩ := Word.lt_cases_of_isU64 hbReadU
  obtain ⟨hcR0, hcR1, _, _⟩ := Word.lt_cases_of_isU64 hcReadU
  have hbU : Word.isU64 cols.b := Word.isU64_of_cases
    (by rw [hb0]; exact hbR0) (by rw [hb1]; exact hbR1)
    (by rw [hb2, hbnegEq, hbmsb]; split <;> simp [val_65535_zmod_p])
    (by rw [hb3, hbnegEq, hbmsb]; split <;> simp [val_65535_zmod_p])
  have hcU : Word.isU64 cols.c := Word.isU64_of_cases
    (by rw [hc0]; exact hcR0) (by rw [hc1]; exact hcR1)
    (by rw [hc2, hcnegEq, hcmsb]; split <;> simp [val_65535_zmod_p])
    (by rw [hc3, hcnegEq, hcmsb]; split <;> simp [val_65535_zmod_p])
  have hbf2 : cols.b[2].val = if 32768 ≤ cols.b[1].val then 65535 else 0 := by
    rw [hb2, hbnegEq, hbmsb]
    split <;> simp [val_65535_zmod_p]
  have hbf3 : cols.b[3].val = if 32768 ≤ cols.b[1].val then 65535 else 0 := by
    rw [hb3, hbnegEq, hbmsb]
    split <;> simp [val_65535_zmod_p]
  have hcf2 : cols.c[2].val = if 32768 ≤ cols.c[1].val then 65535 else 0 := by
    rw [hc2, hcnegEq, hcmsb]
    split <;> simp [val_65535_zmod_p]
  have hcf3 : cols.c[3].val = if 32768 ≤ cols.c[1].val then 65535 else 0 := by
    rw [hc3, hcnegEq, hcmsb]
    split <;> simp [val_65535_zmod_p]
  obtain ⟨_r0, _r1, _r2, _r3, _r4, _r5, _r6, _r7,
    habsCRange, habsRRange, hquotRange, hremRange, hctqRange⟩ := hrange hir
  have hquotU : Word.isU64 cols.quotient := Word.isU64_of_cases
    (hquotRange 0 (by norm_num)) (hquotRange 1 (by norm_num))
    (hquotRange 2 (by norm_num)) (hquotRange 3 (by norm_num))
  have hremU : Word.isU64 cols.remainder := Word.isU64_of_cases
    (hremRange 0 (by norm_num)) (hremRange 1 (by norm_num))
    (hremRange 2 (by norm_num)) (hremRange 3 (by norm_num))
  have hqmsb := hmsbQ1.2 hword
  have hrmsb := hmsbR1.2 hword
  have hqc0 : cols.quotient_comp[0] = cols.quotient[0] := by linear_combination e48
  have hqc1 : cols.quotient_comp[1] = cols.quotient[1] := by linear_combination e49
  have hqc2 : cols.quotient_comp[2] = cols.quot_msb.msb * 65535 := by
    rw [hsigned32] at e54
    linear_combination e54
  have hqc3 : cols.quotient_comp[3] = cols.quot_msb.msb * 65535 := by
    rw [hsigned32] at e64
    linear_combination e64
  have hqo2 : cols.quotient[2] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e57
    linear_combination e57
  have hqo3 : cols.quotient[3] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e67
    linear_combination e67
  have hqcEq : cols.quotient_comp = cols.quotient := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · exact hqc0
    · exact hqc1
    · rw [hqc2, hqo2]
    · rw [hqc3, hqo3]
  have hqcU : Word.isU64 cols.quotient_comp := hqcEq ▸ hquotU
  have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := by linear_combination e70
  have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := by linear_combination e71
  have hrc2 : cols.remainder_comp[2] = cols.rem_msb.msb * 65535 := by
    rw [hsigned32] at e76
    linear_combination e76
  have hrc3 : cols.remainder_comp[3] = cols.rem_msb.msb * 65535 := by
    rw [hsigned32] at e86
    linear_combination e86
  have hro2 : cols.remainder[2] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e79
    linear_combination e79
  have hro3 : cols.remainder[3] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e89
    linear_combination e89
  have hrcEq : cols.remainder_comp = cols.remainder := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · exact hrc0
    · exact hrc1
    · rw [hrc2, hro2]
    · rw [hrc3, hro3]
  have hrcU : Word.isU64 cols.remainder_comp := hrcEq ▸ hremU
  have hqf2 : cols.quotient_comp[2].val =
      if 32768 ≤ cols.quotient_comp[1].val then 65535 else 0 := by
    rw [hqc2, hqmsb, hqc1]
    split <;> simp [val_65535_zmod_p]
  have hqf3 : cols.quotient_comp[3].val =
      if 32768 ≤ cols.quotient_comp[1].val then 65535 else 0 := by
    rw [hqc3, hqmsb, hqc1]
    split <;> simp [val_65535_zmod_p]
  have hrf2 : cols.remainder_comp[2].val =
      if 32768 ≤ cols.remainder_comp[1].val then 65535 else 0 := by
    rw [hrc2, hrmsb, hrc1]
    split <;> simp [val_65535_zmod_p]
  have hrf3 : cols.remainder_comp[3].val =
      if 32768 ≤ cols.remainder_comp[1].val then 65535 else 0 := by
    rw [hrc3, hrmsb, hrc1]
    split <;> simp [val_65535_zmod_p]
  have hqArch : Word.toBitVec64 cols.quotient = BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (Word.toBitVec64 cols.quotient_comp)) := by
    calc
      Word.toBitVec64 cols.quotient = Word.toBitVec64 cols.quotient_comp :=
        congrArg Word.toBitVec64 hqcEq.symm
      _ = _ := word_eq_signExtend_lo hqcU hqf2 hqf3
  have hrArch : Word.toBitVec64 cols.remainder = BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (Word.toBitVec64 cols.remainder_comp)) := by
    calc
      Word.toBitVec64 cols.remainder = Word.toBitVec64 cols.remainder_comp :=
        congrArg Word.toBitVec64 hrcEq.symm
      _ = _ := word_eq_signExtend_lo hrcU hrf2 hrf3
  have hbLow := toBitVec64_extractLsb hbU hbReadU hb0 hb1
  have hcLow := toBitVec64_extractLsb hcU hcReadU hc0 hc1
  have habsCU : Word.isU64 cols.abs_c := Word.isU64_of_cases
    (habsCRange 0 (by norm_num)) (habsCRange 1 (by norm_num))
    (habsCRange 2 (by norm_num)) (habsCRange 3 (by norm_num))
  have habsRU : Word.isU64 cols.abs_remainder := Word.isU64_of_cases
    (habsRRange 0 (by norm_num)) (habsRRange 1 (by norm_num))
    (habsRRange 2 (by norm_num)) (habsRRange 3 (by norm_num))
  rw [hfamily]
  change ∃ quotient32 remainder32 : BitVec 32,
    Word.toBitVec64 cols.quotient = BitVec.signExtend 64 quotient32 ∧
    Word.toBitVec64 cols.remainder = BitVec.signExtend 64 remainder32 ∧
    Cases.Signed32Evidence (Word.toBitVec64 input.op_b_val)
      (Word.toBitVec64 input.op_c_val) quotient32 remainder32
  refine ⟨BitVec.extractLsb 31 0 (Word.toBitVec64 cols.quotient_comp),
    BitVec.extractLsb 31 0 (Word.toBitVec64 cols.remainder_comp), hqArch, hrArch, ?_⟩
  have hbRaw0 : cols.adapter.op_b_memory.prev_value[0] = cols.b[0] := by
    rw [hbRawEq]
    exact hb0.symm
  have hcRaw0 : cols.adapter.op_c_memory.prev_value[0] = cols.c[0] := by
    rw [hcRawEq]
    exact hc0.symm
  have hbLowVec :
      (#v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1], 0, 0] :
        Word (ZMod p)) = #v[cols.b[0], cols.b[1], 0, 0] := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hbRaw0
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hbRaw1
    · rfl
    · rfl
  have hcLowVec :
      (#v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1], 0, 0] :
        Word (ZMod p)) = #v[cols.c[0], cols.c[1], 0, 0] := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hcRaw0
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hcRaw1
    · rfl
    · rfl
  have hovb : IsEqualWordOperation.Spec
      ⟨#v[cols.b[0], cols.b[1], 0, 0], #v[0, 32768, 0, 0],
        cols.is_overflow_b,
        cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw⟩ := by
    simpa [hbLowVec] using hovbLow
  have hovc : IsEqualWordOperation.Spec
      ⟨#v[cols.c[0], cols.c[1], 0, 0], #v[65535, 65535, 0, 0],
        cols.is_overflow_c,
        cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw⟩ := by
    simpa [hcLowVec] using hovcLow
  by_cases hov : cols.is_overflow = 1
  · have hovProduct : cols.is_overflow_b.is_diff_zero.result *
        cols.is_overflow_c.is_diff_zero.result = 1 := by
      rw [hov, hsigned] at e96
      linear_combination -e96
    obtain ⟨hbMin, hcNegOne⟩ :=
      overflow_of_iseqword_word hbU hcU hword hovb hovc hovProduct
    have hq0 : cols.quotient_comp[0] = cols.b[0] := by
      rw [hov] at e105
      linear_combination hqc0 + e105
    have hq1 : cols.quotient_comp[1] = cols.b[1] := by
      rw [hov] at e109
      linear_combination hqc1 + e109
    have hqLowB := extractLsb_lo_congr hqcU hbU hq0 hq1
    have hr0 : cols.remainder_comp[0] = 0 := by
      rw [hov] at e107
      linear_combination hrc0 + e107
    have hr1 : cols.remainder_comp[1] = 0 := by
      rw [hov] at e111
      linear_combination hrc1 + e111
    have hrLowZero : BitVec.extractLsb 31 0 (Word.toBitVec64 cols.remainder_comp) = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [extractLsb_lo_toNat hrcU, hr0, hr1, BitVec.toNat_zero]
      simp
    apply Cases.Signed32Evidence.overflow
    · rw [← hbLow]
      exact hbMin
    · rw [← hcLow]
      exact hcNegOne
    · rw [hqLowB, hbLow]
    · exact hrLowZero
  · have hov0 : cols.is_overflow = 0 := by
      rcases bool_of_mul_pred e341 with h | h
      · exact h
      · exact absurd h hov
    by_cases hcZero : cols.c.toNat = 0
    · have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
      rw [Word.toNat_def] at hcZero
      have hcz0 : cols.c[0] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hcz1 : cols.c[1] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hcz2 : cols.c[2] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have hcz3 : cols.c[3] = 0 := (ZMod.val_eq_zero _).mp (by omega)
      rw [if_pos ⟨hcz0, hcz1, hcz2, hcz3⟩] at hzeroResult
      rw [hzeroResult, one_mul] at e230 e232 e238 e240
      have hq0 : cols.quotient_comp[0] = 65535 := by
        rw [hqc0]
        linear_combination e230
      have hq1 : cols.quotient_comp[1] = 65535 := by
        rw [hqc1]
        linear_combination e232
      have hqLowNegOne : BitVec.extractLsb 31 0
          (Word.toBitVec64 cols.quotient_comp) = -1#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [extractLsb_lo_toNat hqcU, hq0, hq1, BitVec.neg_one_eq_allOnes,
          BitVec.toNat_allOnes]
        simp only [val_65535_zmod_p]
        norm_num
      have hr0 : cols.remainder_comp[0] = cols.b[0] := by linear_combination e238
      have hr1 : cols.remainder_comp[1] = cols.b[1] := by linear_combination e240
      have hrLowB := extractLsb_lo_congr hrcU hbU hr0 hr1
      have hcLowZero : BitVec.extractLsb 31 0 (Word.toBitVec64 cols.c) = 0#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [extractLsb_lo_toNat hcU, hcz0, hcz1, BitVec.toNat_zero]
        simp
      apply Cases.Signed32Evidence.divisorZero
      · rw [← hcLow]
        exact hcLowZero
      · exact hqLowNegOne
      · rw [hrLowB, hbLow]
    · have hbnegLow : cols.b_neg = if 32768 ≤ cols.b[1].val then 1 else 0 := by
        rw [hbnegEq, hbmsb]
      have hcnegLow : cols.c_neg = if 32768 ≤ cols.c[1].val then 1 else 0 := by
        rw [hcnegEq, hcmsb]
      have hrnegLow : cols.rem_neg =
          if 32768 ≤ cols.remainder_comp[1].val then 1 else 0 := by
        rw [hrnegEq, hrmsb, hrc1]
      have hbnegBit : cols.b_neg = if (Word.toBitVec64 cols.b).msb then 1 else 0 := by
        rw [hbnegLow]
        refine if_congr ?_ rfl rfl
        rw [toBitVec64_msb_iff hbU, hbf3]
        split <;> omega
      have hcnegBit : cols.c_neg = if (Word.toBitVec64 cols.c).msb then 1 else 0 := by
        rw [hcnegLow]
        refine if_congr ?_ rfl rfl
        rw [toBitVec64_msb_iff hcU, hcf3]
        split <;> omega
      have hrnegBit : cols.rem_neg =
          if (Word.toBitVec64 cols.remainder_comp).msb then 1 else 0 := by
        rw [hrnegLow]
        refine if_congr ?_ rfl rfl
        rw [toBitVec64_msb_iff hrcU, hrf3]
        split <;> omega
      have hcPos : cols.c_neg = 0 → cols.abs_c = cols.c := by
        intro hn
        apply Vector.ext
        intro i hi
        interval_cases i
        · rw [hn] at e247
          linear_combination e247
        · rw [hn] at e253
          linear_combination e253
        · rw [hn] at e259
          linear_combination e259
        · rw [hn] at e265
          linear_combination e265
      have hcEvent : cols.abs_c_alu_event = cols.c_neg := by
        rw [hir] at e286
        linear_combination e286
      have hcNegValue : cols.abs_c_alu_event = 1 →
          cols.c_neg_operation.value = #v[0, 0, 0, 0] := by
        intro he
        apply Vector.ext
        intro i hi
        interval_cases i
        all_goals simp only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        · rw [he] at e270
          linear_combination -e270
        · rw [he] at e272
          linear_combination -e272
        · rw [he] at e274
          linear_combination -e274
        · rw [he] at e276
          linear_combination -e276
      obtain ⟨hcAbsPos, hcAbsNeg⟩ :=
        signedAbsBehavior hcnegBit hcPos hcEvent hcNegValue haddC
      have hrPos : cols.rem_neg = 0 → cols.abs_remainder = cols.remainder_comp := by
        intro hn
        apply Vector.ext
        intro i hi
        interval_cases i
        · rw [hn] at e250
          linear_combination e250
        · rw [hn] at e256
          linear_combination e256
        · rw [hn] at e262
          linear_combination e262
        · rw [hn] at e268
          linear_combination e268
      have hrEvent : cols.abs_rem_alu_event = cols.rem_neg := by
        rw [hir] at e288
        linear_combination e288
      have hrNegValue : cols.abs_rem_alu_event = 1 →
          cols.rem_neg_operation.value = #v[0, 0, 0, 0] := by
        intro he
        apply Vector.ext
        intro i hi
        interval_cases i
        all_goals simp only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        · rw [he] at e278
          linear_combination -e278
        · rw [he] at e280
          linear_combination -e280
        · rw [he] at e282
          linear_combination -e282
        · rw [he] at e284
          linear_combination -e284
      obtain ⟨hrAbsPos, hrAbsNeg⟩ :=
        signedAbsBehavior hrnegBit hrPos hrEvent hrNegValue haddR
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
      have hlo := rwlo_product (fun _ => hmulLo) hir
        hglue0 hglue1 hglue2 hglue3
      have hcarry0 := bool_of_mul_pred e309
      have hcarry1 := bool_of_mul_pred e311
      have hcarry2 := bool_of_mul_pred e313
      have hcarry3 := bool_of_mul_pred e315
      have hchain0 : cols.c_times_quotient[0] + cols.remainder_comp[0] =
          cols.b[0] + cols.carry[0] * 65536 := by
        rw [hov0] at e154
        linear_combination e154
      have hchain1 : cols.c_times_quotient[1] + cols.remainder_comp[1] + cols.carry[0] =
          cols.b[1] + cols.carry[1] * 65536 := by
        rw [hov0] at e157
        linear_combination e157
      have hchain2 : cols.c_times_quotient[2] + cols.remainder_comp[2] + cols.carry[1] =
          cols.b[2] + cols.carry[2] * 65536 := by
        rw [hov0] at e160
        linear_combination e160
      have hchain3 : cols.c_times_quotient[3] + cols.remainder_comp[3] + cols.carry[2] =
          cols.b[3] + cols.carry[3] * 65536 := by
        rw [hov0] at e163
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
      have hid := euclid_identity_word_signed (carry := carryLo) hctqLoU hbU hcU hqcU hrcU
        hbf2 hbf3 hcf2 hcf3 hqf2 hqf3 hrf2 hrf3
        hcarry0' hcarry1' hcarry2' hcarry3' hchain0' hchain1' hchain2' hchain3' hlo
      have hzeroResult := IsZeroWordOperation.result_semantic hisZero hir
      have hcnz : ¬ (cols.c[0] = 0 ∧ cols.c[1] = 0 ∧ cols.c[2] = 0 ∧ cols.c[3] = 0) := by
        rintro ⟨z0, z1, z2, z3⟩
        apply hcZero
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
      have hcmp : cols.abs_remainder.toNat < cols.abs_c.toNat := by
        have hcmpMax : cols.abs_remainder.toNat < cols.max_abs_c_or_1.toNat := by
          by_contra hnot
          rw [if_neg hnot] at hbit
          exact one_ne_zero hbit
        simpa [hmaxEq] using hcmpMax
      have hlt := hlt_signed_of_abs habsRU habsCU hrAbsPos hrAbsNeg hcAbsPos hcAbsNeg hcmp
      have hcBVNe : Word.toBitVec64 cols.c ≠ 0#64 := by
        intro hzero
        apply hcZero
        have hnat := congrArg BitVec.toNat hzero
        simpa [Word.toBitVec64_toNat hcU] using hnat
      have hbnegBin := bool_of_mul_pred e345
      have hrnegBin := bool_of_mul_pred e351
      have hE225 : cols.rem_neg = 0 ∨ cols.b_neg = 1 := by
        rcases hrnegBin with hr0 | hr1
        · exact Or.inl hr0
        · rcases hbnegBin with hb0 | hb1
          · rw [hr1, hb0] at e225
            norm_num at e225
          · exact Or.inr hb1
      have hE228 : Word.toBitVec64 cols.remainder = 0#64 ∨
          cols.rem_neg = 1 ∨ cols.b_neg = 0 := by
        rcases hrnegBin with hr0 | hr1
        · rcases hbnegBin with hb0 | hb1
          · exact Or.inr (Or.inr hb0)
          · apply Or.inl
            apply toBitVec64_eq_zero_of_limb_sum_eq_zero hremU
            rw [hr0, hb1] at e228
            linear_combination e228
        · exact Or.inr (Or.inl hr1)
      have hE228Comp : Word.toBitVec64 cols.remainder_comp = 0#64 ∨
          cols.rem_neg = 1 ∨ cols.b_neg = 0 := by
        simpa [hrcEq] using hE228
      have hidentity : (Word.toBitVec64 cols.b).toInt =
          (Word.toBitVec64 cols.c).toInt * (Word.toBitVec64 cols.quotient_comp).toInt +
            (Word.toBitVec64 cols.remainder_comp).toInt := by
        rw [hid]
        ring
      obtain ⟨hsgnPos, hsgnNeg⟩ := sign_conditions hbnegBit hrnegBit hE225 hE228Comp
        hcBVNe hidentity hlt
      have hbp := toInt_eq_extractLsb_of_signfill hbU hbf2 hbf3
      have hcp := toInt_eq_extractLsb_of_signfill hcU hcf2 hcf3
      have hqp := toInt_eq_extractLsb_of_signfill hqcU hqf2 hqf3
      have hrp := toInt_eq_extractLsb_of_signfill hrcU hrf2 hrf3
      have hcLowNe : BitVec.extractLsb 31 0 (Word.toBitVec64 cols.c) ≠ 0#32 := by
        intro hzero
        apply hcBVNe
        rw [word_eq_signExtend_lo hcU hcf2 hcf3, hzero]
        rfl
      apply Cases.Signed32Evidence.normal
      · rw [← hcLow]
        exact hcLowNe
      · rw [← hbLow, ← hcLow, ← hbp, ← hcp, ← hqp, ← hrp]
        exact hidentity
      · rw [← hcLow, ← hcp, ← hrp]
        exact hlt
      · rw [← hbLow, ← hbp, ← hrp]
        exact hsgnPos
      · rw [← hbLow, ← hbp, ← hrp]
        exact hsgnNeg

end SP1Clean.DivRemChip
