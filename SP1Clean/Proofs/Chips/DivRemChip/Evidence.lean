import SP1Clean.Proofs.Chips.DivRemChip.Evidence.Signed64
import SP1Clean.Proofs.Chips.DivRemChip.Evidence.Unsigned64
import SP1Clean.Proofs.Chips.DivRemChip.Evidence.Signed32
import SP1Clean.Proofs.Chips.DivRemChip.Evidence.Unsigned32

/-! # `DivRemChip` — uniform row evidence assembly

The four family proofs deliberately stop at quotient/remainder evidence. This file is the small,
auditable top layer that identifies the row's selected case, invokes exactly one family proof, and
uses the Rust row's output-routing constraints to produce `Cases.RowEvidence`. -/

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemContract

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The selected opcode's output gate routes `cols.a` to the corresponding quotient or remainder
word. This is intentionally separate from all arithmetic reasoning. -/
theorem routedWord {cols : Columns (ZMod p)} {case : Case}
    (hcore : DivRemCore.CoreSpec cols) (hselected : Selected cols case) :
    cols.a = match case.output with
      | .quotient => cols.quotient
      | .remainder => cols.remainder := by
  obtain ⟨_, hown, _, _⟩ := hcore
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
  have hqGate : cols.is_divu + cols.is_div + cols.is_divw + cols.is_divuw =
      if case.output = .quotient then 1 else 0 := by
    cases case
    all_goals
      change Case.divu.flag cols + Case.div.flag cols + Case.divw.flag cols +
        Case.divuw.flag cols = _
      rw [hselected.flag_eq .divu, hselected.flag_eq .div,
        hselected.flag_eq .divw, hselected.flag_eq .divuw]
      simp [Case.output]
  have hrGate : cols.is_remu + cols.is_rem + cols.is_remw + cols.is_remuw =
      if case.output = .remainder then 1 else 0 := by
    cases case
    all_goals
      change Case.remu.flag cols + Case.rem.flag cols + Case.remw.flag cols +
        Case.remuw.flag cols = _
      rw [hselected.flag_eq .remu, hselected.flag_eq .rem,
        hselected.flag_eq .remw, hselected.flag_eq .remuw]
      simp [Case.output]
  cases ho : case.output with
  | quotient =>
      have hg : cols.is_divu + cols.is_div + cols.is_divw + cols.is_divuw = 1 := by
        simpa [ho] using hqGate
      have ha0 : cols.a[0] = cols.quotient[0] := by
        rw [hg] at e184
        linear_combination -e184
      have ha1 : cols.a[1] = cols.quotient[1] := by
        rw [hg] at e194
        linear_combination -e194
      have ha2 : cols.a[2] = cols.quotient[2] := by
        rw [hg] at e204
        linear_combination -e204
      have ha3 : cols.a[3] = cols.quotient[3] := by
        rw [hg] at e214
        linear_combination -e214
      have ha : cols.a = cols.quotient := by
        apply Vector.ext
        intro i hi
        interval_cases i <;> assumption
      simpa [ho] using ha
  | remainder =>
      have hg : cols.is_remu + cols.is_rem + cols.is_remw + cols.is_remuw = 1 := by
        simpa [ho] using hrGate
      have ha0 : cols.a[0] = cols.remainder[0] := by
        rw [hg] at e189
        linear_combination -e189
      have ha1 : cols.a[1] = cols.remainder[1] := by
        rw [hg] at e199
        linear_combination -e199
      have ha2 : cols.a[2] = cols.remainder[2] := by
        rw [hg] at e209
        linear_combination -e209
      have ha3 : cols.a[3] = cols.remainder[3] := by
        rw [hg] at e219
        linear_combination -e219
      have ha : cols.a = cols.remainder := by
        apply Vector.ext
        intro i hi
        interval_cases i <;> assumption
      simpa [ho] using ha

/-- Bit-vector form of `routedWord`, used by the ISA-facing row-evidence contract. -/
theorem routedResult {cols : Columns (ZMod p)} {case : Case}
    (hcore : DivRemCore.CoreSpec cols) (hselected : Selected cols case) :
    Word.toBitVec64 cols.a = case.output.pick (Word.toBitVec64 cols.quotient)
      (Word.toBitVec64 cols.remainder) := by
  have h := congrArg Word.toBitVec64 (routedWord hcore hselected)
  cases ho : case.output <;> simpa [Output.pick, ho] using h

/-- A real DivRem row writes a range-checked quotient or remainder word. This is the exact range
fact needed by the separately composed destination-register write. -/
theorem resultIsU64OfCore {cols : Columns (ZMod p)} (hcore : DivRemCore.CoreSpec cols)
    (hreal : cols.is_real = 1) : Word.isU64 cols.a := by
  have hcoreParts := hcore
  obtain ⟨_, _, hselection, hrange⟩ := hcoreParts
  simp only [DivRemCore.SelectionEvidenceSpec] at hselection
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hselected⟩ := hselection
  obtain ⟨case, hcase⟩ := hselected hreal
  simp only [DivRemCore.RangeSpec] at hrange
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hquot, hrem, _⟩ := hrange hreal
  have hquotU := Word.isU64_of_cases (hquot 0 (by norm_num)) (hquot 1 (by norm_num))
    (hquot 2 (by norm_num)) (hquot 3 (by norm_num))
  have hremU := Word.isU64_of_cases (hrem 0 (by norm_num)) (hrem 1 (by norm_num))
    (hrem 2 (by norm_num)) (hrem 3 (by norm_num))
  rw [routedWord hcore hcase]
  cases case.output <;> assumption

set_option maxHeartbeats 16000000 in
/-- The arithmetic core and the two committed source-register bounds discharge the comparison
cluster's complete external contract. The only cross-cluster equation retained verbatim is the
remainder-check gate equation; `DivRemCompare.soundness` combines it with the internally proved
`IsZeroWordOperation` result to recover the gate's booleanness. -/
theorem compareAssumptionsOfCore {input : Inputs (ZMod p)} {cols : Columns (ZMod p)}
    (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols) (hadapter : cols.adapter = input.adapter)
    (hreal : cols.is_real = 1) :
    DivRemCompare.Assumptions (DivRemCompare.Inputs.ofCols cols) := by
  obtain ⟨_, hown, hselection, hrange⟩ := hcore
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
  simp only [DivRemCore.SelectionEvidenceSpec] at hselection
  obtain ⟨bIr, bIrnw, bDiv, bDivu, bRem, bRemu, bDivw, bRemw, bDivuw, bRemuw,
    hsum, hselected⟩ := hselection
  have hvals := flags_val_sum bDivu bRemu bDiv bRem bDivw bRemw bDivuw bRemuw hsum
  have bE2 := group_binary4 bDivw bRemw bDivuw bRemuw (by omega)
  have bAce := bool_of_mul_pred e357
  have bAre := bool_of_mul_pred e359
  have bCneg := bool_of_mul_pred e353
  have bRneg := bool_of_mul_pred e351
  have hrcmGate : DivRemCompare.RemainderCheckGateSpec
      (DivRemCompare.Inputs.ofCols cols) := by
    simp only [DivRemCompare.RemainderCheckGateSpec, DivRemCompare.Inputs.ofCols]
    linear_combination -e305
  have hbColsU : Word.isU64 cols.adapter.op_b_memory.prev_value := by
    rw [hadapter]
    exact hbReadU
  have hcColsU : Word.isU64 cols.adapter.op_c_memory.prev_value := by
    rw [hadapter]
    exact hcReadU
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hbColsU
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcColsU
  have hcEq0 : cols.c[0] = cols.adapter.op_c_memory.prev_value[0] :=
    (sub_eq_zero.mp e21).symm
  have hcEq1 : cols.c[1] = cols.adapter.op_c_memory.prev_value[1] :=
    (sub_eq_zero.mp e23).symm
  have hcEq2 : cols.c[2] = cols.adapter.op_c_memory.prev_value[2] *
      (1 - (cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw)) +
      cols.c_neg * (cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw) * 65535 :=
    sub_eq_zero.mp e35
  have hcEq3 : cols.c[3] = cols.adapter.op_c_memory.prev_value[3] *
      (1 - (cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw)) +
      cols.c_neg * (cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw) * 65535 :=
    sub_eq_zero.mp e47
  have hcU : Word.isU64 cols.c :=
    operand_isU64 hcEq0 hcEq1 hcEq2 hcEq3 hc0 hc1 hc2 hc3 bE2 bCneg
  simp only [DivRemCore.RangeSpec] at hrange
  have realWordRanges (hr : cols.is_real = 1) :
      Word.isU64 cols.abs_c ∧ Word.isU64 cols.abs_remainder ∧
      Word.isU64 cols.quotient ∧ Word.isU64 cols.remainder := by
    obtain ⟨_, _, _, _, _, _, _, _, habsC, habsR, hquot, hrem, _⟩ := hrange hr
    exact ⟨Word.isU64_of_cases (habsC 0 (by norm_num)) (habsC 1 (by norm_num))
        (habsC 2 (by norm_num)) (habsC 3 (by norm_num)),
      Word.isU64_of_cases (habsR 0 (by norm_num)) (habsR 1 (by norm_num))
        (habsR 2 (by norm_num)) (habsR 3 (by norm_num)),
      Word.isU64_of_cases (hquot 0 (by norm_num)) (hquot 1 (by norm_num))
        (hquot 2 (by norm_num)) (hquot 3 (by norm_num)),
      Word.isU64_of_cases (hrem 0 (by norm_num)) (hrem 1 (by norm_num))
        (hrem 2 (by norm_num)) (hrem 3 (by norm_num))⟩
  have realOfAce (h : cols.abs_c_alu_event = 1) : cols.is_real = 1 := by
    rcases bIr with hr | hr
    · rw [h, hr] at e286
      simp at e286
    · exact hr
  have realOfAre (h : cols.abs_rem_alu_event = 1) : cols.is_real = 1 := by
    rcases bIr with hr | hr
    · rw [h, hr] at e288
      simp at e288
    · exact hr
  have realOfIrnw (h : cols.is_real_not_word = 1) : cols.is_real = 1 := by
    rcases bIr with hr | hr
    · rw [h, hr] at e13
      simp at e13
    · exact hr
  have remainderCompUOfReal (hr : cols.is_real = 1) : Word.isU64 cols.remainder_comp := by
    have hremU := (realWordRanges hr).2.2.2
    obtain ⟨_, _, hremRange, _⟩ := Word.lt_cases_of_isU64 hremU
    have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := sub_eq_zero.mp e70
    have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := sub_eq_zero.mp e71
    obtain ⟨case, hcase⟩ := hselected hr
    have hd := hcase.flag_eq .div
    have hdu := hcase.flag_eq .divu
    have hrem := hcase.flag_eq .rem
    have hremu := hcase.flag_eq .remu
    have hdw := hcase.flag_eq .divw
    have hrw := hcase.flag_eq .remw
    have hduw := hcase.flag_eq .divuw
    have hruw := hcase.flag_eq .remuw
    have hgroups :
        cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem = 1 ∨
        ((cols.is_divw + cols.is_remw = 1) ∧
          cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 1) ∨
        cols.is_divuw + cols.is_remuw = 1 := by
      cases case <;>
        simp [Case.flag] at hd hdu hrem hremu hdw hrw hduw hruw ⊢ <;>
        simp [hd, hdu, hrem, hremu, hdw, hrw, hduw, hruw]
    have hrc2 : cols.remainder_comp[2].val < 2 ^ 16 := by
      rcases hgroups with h64 | hword | huword
      · have heq : cols.remainder_comp[2] = cols.remainder[2] := by
          rw [h64] at e81
          linear_combination e81
        rw [heq]
        exact hremRange
      · rcases hword with ⟨hword, hsigned⟩
        have hmsb : cols.rem_msb.msb = cols.rem_neg := by
          rw [hsigned] at e17
          linear_combination e17
        have heq : cols.remainder_comp[2] = cols.rem_msb.msb * 65535 := by
          rw [hword] at e76
          linear_combination e76
        rw [heq, hmsb]
        rcases bRneg with h | h <;> rw [h] <;> simp [val_65535_zmod_p]
      · have heq : cols.remainder_comp[2] = 0 := by
          rw [huword] at e73
          linear_combination e73
        rw [heq]
        simp
    have hrc3 : cols.remainder_comp[3].val < 2 ^ 16 := by
      rcases hgroups with h64 | hword | huword
      · have heq : cols.remainder_comp[3] = cols.remainder[3] := by
          rw [h64] at e91
          linear_combination e91
        rw [heq]
        exact (Word.lt_cases_of_isU64 hremU).2.2.2
      · rcases hword with ⟨hword, hsigned⟩
        have hmsb : cols.rem_msb.msb = cols.rem_neg := by
          rw [hsigned] at e17
          linear_combination e17
        have heq : cols.remainder_comp[3] = cols.rem_msb.msb * 65535 := by
          rw [hword] at e86
          linear_combination e86
        rw [heq, hmsb]
        rcases bRneg with h | h <;> rw [h] <;> simp [val_65535_zmod_p]
      · have heq : cols.remainder_comp[3] = 0 := by
          rw [huword] at e83
          linear_combination e83
        rw [heq]
        simp
    exact Word.isU64_of_cases (by rw [hrc0]; exact (Word.lt_cases_of_isU64 hremU).1)
      (by rw [hrc1]; exact (Word.lt_cases_of_isU64 hremU).2.1) hrc2 hrc3
  have hUac : cols.abs_c_alu_event = 1 → Word.isU64 cols.c ∧ Word.isU64 cols.abs_c :=
    fun h => ⟨hcU, (realWordRanges (realOfAce h)).1⟩
  have hUar : cols.abs_rem_alu_event = 1 →
      Word.isU64 cols.remainder_comp ∧ Word.isU64 cols.abs_remainder := fun h =>
    ⟨remainderCompUOfReal (realOfAre h), (realWordRanges (realOfAre h)).2.1⟩
  have hUlt : cols.remainder_check_multiplicity = 1 →
      Word.isU64 cols.abs_remainder ∧ Word.isU64 cols.max_abs_c_or_1 := by
    intro hrcm
    have hreal : cols.is_real = 1 := by
      rcases bIr with hr | hr
      · simp only [DivRemCompare.RemainderCheckGateSpec,
          DivRemCompare.Inputs.ofCols, hr, mul_zero] at hrcmGate
        exact absurd (hrcm.symm.trans hrcmGate) (Ne.symm zero_ne_one)
      · exact hr
    have hz : cols.is_c_0.result = 0 := by
      simp only [DivRemCompare.RemainderCheckGateSpec,
        DivRemCompare.Inputs.ofCols, hrcm, hreal, mul_one] at hrcmGate
      linear_combination hrcmGate
    have hm0 : cols.max_abs_c_or_1[0] = cols.abs_c[0] := by
      simpa [hz] using sub_eq_zero.mp e299
    have hm1 : cols.max_abs_c_or_1[1] = cols.abs_c[1] := by
      simpa [hz] using sub_eq_zero.mp e300
    have hm2 : cols.max_abs_c_or_1[2] = cols.abs_c[2] := by
      simpa [hz] using sub_eq_zero.mp e301
    have hm3 : cols.max_abs_c_or_1[3] = cols.abs_c[3] := by
      simpa [hz] using sub_eq_zero.mp e302
    have hmax : cols.max_abs_c_or_1 = cols.abs_c := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> assumption
    exact ⟨(realWordRanges hreal).2.1, hmax ▸ (realWordRanges hreal).1⟩
  have hR3 : cols.is_real_not_word = 1 →
      cols.adapter.op_b_memory.prev_value[3].val < 2 ^ 16 ∧
      cols.adapter.op_c_memory.prev_value[3].val < 2 ^ 16 ∧
      cols.remainder[3].val < 2 ^ 16 := by
    intro hirnw
    exact ⟨hb3, hc3, (Word.lt_cases_of_isU64 (realWordRanges (realOfIrnw hirnw)).2.2.2).2.2.2⟩
  have hR1 : cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1 →
      cols.adapter.op_b_memory.prev_value[1].val < 2 ^ 16 ∧
      cols.adapter.op_c_memory.prev_value[1].val < 2 ^ 16 ∧
      cols.remainder[1].val < 2 ^ 16 ∧ cols.quotient[1].val < 2 ^ 16 := by
    intro _
    have hwordRanges := (realWordRanges hreal).2
    exact ⟨hb1, hc1,
      (Word.lt_cases_of_isU64 hwordRanges.2.2).2.1,
      (Word.lt_cases_of_isU64 hwordRanges.2.1).2.1⟩
  simp only [DivRemCompare.Assumptions, DivRemCompare.Inputs.ofCols]
  exact ⟨bIr, bIrnw, bE2, bAce, bAre, hrcmGate, hUac, hUar, hUlt, hR3, hR1⟩

set_option maxHeartbeats 16000000 in
/-- Dispatch the selected row to its one arithmetic-family evidence theorem. -/
theorem familyEvidenceOfSpecs {input : Inputs (ZMod p)} {cols : Columns (ZMod p)}
    {case : Case} (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols)
    (hcompare : DivRemCompare.CompareSpec (DivRemCompare.Inputs.ofCols cols))
    (hreal : input.is_real = 1) (hinputReal : cols.is_real = input.is_real)
    (hadapter : cols.adapter = input.adapter) (hselected : Selected cols case) :
    Cases.FamilyEvidence case.family (Word.toBitVec64 input.op_b_val)
      (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 cols.quotient)
      (Word.toBitVec64 cols.remainder) := by
  cases hf : case.family with
  | signed64 =>
      simpa [hf] using
        signed64Evidence hbReadU hcReadU hcore hcompare hreal hinputReal hadapter hselected hf
  | unsigned64 =>
      simpa [hf] using
        unsigned64Evidence hbReadU hcReadU hcore hcompare hreal hinputReal hadapter hselected hf
  | signed32 =>
      simpa [hf] using
        signed32Evidence hbReadU hcReadU hcore hcompare hreal hinputReal hadapter hselected hf
  | unsigned32 =>
      simpa [hf] using
        unsigned32Evidence hbReadU hcReadU hcore hcompare hreal hinputReal hadapter hselected hf

set_option maxHeartbeats 16000000 in
/-- Folded comparison/core contracts imply the complete evidence-shaped public row contract. -/
theorem rowEvidenceOfSpecs {input : Inputs (ZMod p)} {cols : Columns (ZMod p)}
    (hbReadU : Word.isU64 input.op_b_val) (hcReadU : Word.isU64 input.op_c_val)
    (hcore : DivRemCore.CoreSpec cols)
    (hcompare : DivRemCompare.Assumptions (DivRemCompare.Inputs.ofCols cols) →
      DivRemCompare.CompareSpec (DivRemCompare.Inputs.ofCols cols))
    (hinputReal : cols.is_real = input.is_real) (hadapter : cols.adapter = input.adapter) :
    Cases.RowEvidence input.is_real input.op_b_val input.op_c_val cols.a cols := by
  have hselectionEvidence := hcore.2.2.1
  simp only [DivRemCore.SelectionEvidenceSpec] at hselectionEvidence
  obtain ⟨hcolsRealBinary, _, _, _, _, _, _, _, _, _, _, hselection⟩ := hselectionEvidence
  refine ⟨?_, ?_, ?_⟩
  · simpa [hinputReal] using hcolsRealBinary
  · simpa [hinputReal] using hselection
  · intro case hreal hflag
    have hcolsReal : cols.is_real = 1 := hinputReal.trans hreal
    have hcompareSpec := hcompare
      (compareAssumptionsOfCore hbReadU hcReadU hcore hadapter hcolsReal)
    obtain ⟨selected, hselected⟩ := hselection hcolsReal
    have hcase : selected = case := by
      by_contra hne
      have hzero := hselected.2 case (Ne.symm hne)
      exact zero_ne_one (hzero.symm.trans hflag)
    subst selected
    refine ⟨Word.toBitVec64 cols.quotient, Word.toBitVec64 cols.remainder,
      familyEvidenceOfSpecs hbReadU hcReadU hcore hcompareSpec hreal hinputReal hadapter hselected,
      ?_⟩
    exact routedResult hcore hselected

end SP1Clean.DivRemChip
