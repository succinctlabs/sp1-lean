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

omit [Fact (2 ^ 24 < p)] in
/-- The companion to `unsigned64_word_gate`: selecting a `DIVU`/`REMU` case also pins the four
signed flags to zero and makes the two unsigned-64 flags sum to one. Hoisting the eight-way case
split out of `unsigned64Evidence` keeps it off that proof's 121-hypothesis assertion context. -/
private lemma unsigned64_flags {cols : Columns (ZMod p)} {case : Case}
    (hselected : Selected cols case) (hfamily : case.family = .unsigned64) :
    cols.is_div = 0 ∧ cols.is_rem = 0 ∧ cols.is_divw = 0 ∧ cols.is_remw = 0 ∧
      cols.is_divu + cols.is_remu = 1 := by
  have hdiv := hselected.flag_eq .div
  have hrem := hselected.flag_eq .rem
  have hdivu := hselected.flag_eq .divu
  have hremu := hselected.flag_eq .remu
  have hdivw := hselected.flag_eq .divw
  have hremw := hselected.flag_eq .remw
  cases case <;>
    simp [Case.family] at hfamily <;>
    simp [Case.flag] at hdiv hrem hdivu hremu hdivw hremw <;>
    simp [hdiv, hrem, hdivu, hremu, hdivw, hremw]

-- The 121-hypothesis `ownAsserts` tail is read through `.1`/`.2` projections instead of a
-- 121-way `obtain` (Clean `doc/performance-problems.md` fix pattern 7): each component's
-- `And.casesOn` motive re-abstracts this very large goal, and dropping 121 of them cut the
-- produced term from 242293 to 188730 nodes. The same treatment is applied to the 15-way
-- `hcompare` and 13-way range destructurings. Re-laddered, the floor bracket tightened from
-- (40000, 400000] to (160000, 200000] — its top now sits under Lean's plain default, so this
-- proof carries no budget directive at all (it was stamped at 2M, and 16M before that).
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
  have e13 := hown.1
  have hw1 := hown.2
  have e15 := hw1.1
  have hw2 := hw1.2
  have e17 := hw2.1
  have hw3 := hw2.2
  have e19 := hw3.1
  have hw4 := hw3.2
  have e20 := hw4.1
  have hw5 := hw4.2
  have e21 := hw5.1
  have hw6 := hw5.2
  have e22 := hw6.1
  have hw7 := hw6.2
  have e23 := hw7.1
  have hw8 := hw7.2
  have e29 := hw8.1
  have hw9 := hw8.2
  have e35 := hw9.1
  have hw10 := hw9.2
  have e41 := hw10.1
  have hw11 := hw10.2
  have e47 := hw11.1
  have hw12 := hw11.2
  have e48 := hw12.1
  have hw13 := hw12.2
  have e49 := hw13.1
  have hw14 := hw13.2
  have hw15 := hw14.2
  have hw16 := hw15.2
  have hw17 := hw16.2
  have e59 := hw17.1
  have hw18 := hw17.2
  have hw19 := hw18.2
  have hw20 := hw19.2
  have hw21 := hw20.2
  have e69 := hw21.1
  have hw22 := hw21.2
  have e70 := hw22.1
  have hw23 := hw22.2
  have e71 := hw23.1
  have hw24 := hw23.2
  have hw25 := hw24.2
  have hw26 := hw25.2
  have hw27 := hw26.2
  have e81 := hw27.1
  have hw28 := hw27.2
  have hw29 := hw28.2
  have hw30 := hw29.2
  have hw31 := hw30.2
  have e91 := hw31.1
  have hw32 := hw31.2
  have e96 := hw32.1
  have hw33 := hw32.2
  have hw34 := hw33.2
  have hw35 := hw34.2
  have hw36 := hw35.2
  have hw37 := hw36.2
  have hw38 := hw37.2
  have hw39 := hw38.2
  have hw40 := hw39.2
  have hw41 := hw40.2
  have hw42 := hw41.2
  have hw43 := hw42.2
  have e154 := hw43.1
  have hw44 := hw43.2
  have e157 := hw44.1
  have hw45 := hw44.2
  have e160 := hw45.1
  have hw46 := hw45.2
  have e163 := hw46.1
  have hw47 := hw46.2
  have e167 := hw47.1
  have hw48 := hw47.2
  have e171 := hw48.1
  have hw49 := hw48.2
  have e175 := hw49.1
  have hw50 := hw49.2
  have e179 := hw50.1
  have hw51 := hw50.2
  have hw52 := hw51.2
  have hw53 := hw52.2
  have hw54 := hw53.2
  have hw55 := hw54.2
  have hw56 := hw55.2
  have hw57 := hw56.2
  have hw58 := hw57.2
  have hw59 := hw58.2
  have hw60 := hw59.2
  have hw61 := hw60.2
  have e230 := hw61.1
  have hw62 := hw61.2
  have e232 := hw62.1
  have hw63 := hw62.2
  have e234 := hw63.1
  have hw64 := hw63.2
  have e236 := hw64.1
  have hw65 := hw64.2
  have e238 := hw65.1
  have hw66 := hw65.2
  have e240 := hw66.1
  have hw67 := hw66.2
  have e242 := hw67.1
  have hw68 := hw67.2
  have e244 := hw68.1
  have hw69 := hw68.2
  have e247 := hw69.1
  have hw70 := hw69.2
  have e250 := hw70.1
  have hw71 := hw70.2
  have e253 := hw71.1
  have hw72 := hw71.2
  have e256 := hw72.1
  have hw73 := hw72.2
  have e259 := hw73.1
  have hw74 := hw73.2
  have e262 := hw74.1
  have hw75 := hw74.2
  have e265 := hw75.1
  have hw76 := hw75.2
  have e268 := hw76.1
  have hw77 := hw76.2
  have hw78 := hw77.2
  have hw79 := hw78.2
  have hw80 := hw79.2
  have hw81 := hw80.2
  have hw82 := hw81.2
  have hw83 := hw82.2
  have hw84 := hw83.2
  have hw85 := hw84.2
  have hw86 := hw85.2
  have hw87 := hw86.2
  have e299 := hw87.1
  have hw88 := hw87.2
  have e300 := hw88.1
  have hw89 := hw88.2
  have e301 := hw89.1
  have hw90 := hw89.2
  have e302 := hw90.1
  have hw91 := hw90.2
  have e305 := hw91.1
  have hw92 := hw91.2
  have e307 := hw92.1
  have hw93 := hw92.2
  have e309 := hw93.1
  have hw94 := hw93.2
  have e311 := hw94.1
  have hw95 := hw94.2
  have e313 := hw95.1
  have hw96 := hw95.2
  have e315 := hw96.1
  have hw97 := hw96.2
  have e317 := hw97.1
  have hw98 := hw97.2
  have e319 := hw98.1
  have hw99 := hw98.2
  have e321 := hw99.1
  have hw100 := hw99.2
  have e323 := hw100.1
  clear hown hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19
    hw20 hw21 hw22 hw23 hw24 hw25 hw26 hw27 hw28 hw29 hw30 hw31 hw32 hw33 hw34 hw35 hw36 hw37
    hw38 hw39 hw40 hw41 hw42 hw43 hw44 hw45 hw46 hw47 hw48 hw49 hw50 hw51 hw52 hw53 hw54 hw55
    hw56 hw57 hw58 hw59 hw60 hw61 hw62 hw63 hw64 hw65 hw66 hw67 hw68 hw69 hw70 hw71 hw72 hw73
    hw74 hw75 hw76 hw77 hw78 hw79 hw80 hw81 hw82 hw83 hw84 hw85 hw86 hw87 hw88 hw89 hw90 hw91
    hw92 hw93 hw94 hw95 hw96 hw97 hw98 hw99 hw100
  have hword : cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 0 :=
    unsigned64_word_gate hfamily hselected
  obtain ⟨hfdiv, hfrem, hfdivw, hfremw, hunsigned⟩ := unsigned64_flags hselected hfamily
  have hsigned : cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 0 := by
    linear_combination hfdiv + hfrem + hfdivw + hfremw
  have h64 : cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem = 1 := by
    linear_combination hunsigned + hfdiv + hfrem
  have hir : cols.is_real = 1 := hinputReal.trans hreal
  have hirnw : cols.is_real_not_word = 1 := by
    rw [hword, hir] at e13; linear_combination e13
  have hbneg : cols.b_neg = 0 := by
    rw [hsigned] at e15; linear_combination -e15
  have hrneg : cols.rem_neg = 0 := by
    rw [hsigned] at e17; linear_combination -e17
  have hcneg : cols.c_neg = 0 := by
    rw [hsigned] at e19; linear_combination -e19
  have hov : cols.is_overflow = 0 := by
    rw [hsigned] at e96; linear_combination e96
  rw [hadapter] at e20 e21 e22 e23 e29 e35 e41 e47
  have hb0 : cols.b[0] = input.op_b_val[0] := by linear_combination -e20
  have hb1 : cols.b[1] = input.op_b_val[1] := by linear_combination -e22
  have hb2 : cols.b[2] = input.op_b_val[2] := by
    rw [hword] at e29; linear_combination e29
  have hb3 : cols.b[3] = input.op_b_val[3] := by
    rw [hword] at e41; linear_combination e41
  have hc0 : cols.c[0] = input.op_c_val[0] := by linear_combination -e21
  have hc1 : cols.c[1] = input.op_c_val[1] := by linear_combination -e23
  have hc2 : cols.c[2] = input.op_c_val[2] := by
    rw [hword] at e35; linear_combination e35
  have hc3 : cols.c[3] = input.op_c_val[3] := by
    rw [hword] at e47; linear_combination e47
  have hbEq : cols.b = input.op_b_val := by
    apply Vector.ext; intro i hi; interval_cases i <;> assumption
  have hcEq : cols.c = input.op_c_val := by
    apply Vector.ext; intro i hi; interval_cases i <;> assumption
  have hbU : Word.isU64 cols.b := hbEq ▸ hbReadU
  have hcU : Word.isU64 cols.c := hcEq ▸ hcReadU
  have hrng := hrange hir
  have habsCRange := hrng.2.2.2.2.2.2.2.2.1
  have habsRRange := hrng.2.2.2.2.2.2.2.2.2.1
  have hquotRange := hrng.2.2.2.2.2.2.2.2.2.2.1
  have hremRange := hrng.2.2.2.2.2.2.2.2.2.2.2.1
  have hctqRange := hrng.2.2.2.2.2.2.2.2.2.2.2.2
  clear hrng hrange
  have hquotU : Word.isU64 cols.quotient := Word.isU64_of_cases
    (hquotRange 0 (by norm_num)) (hquotRange 1 (by norm_num))
    (hquotRange 2 (by norm_num)) (hquotRange 3 (by norm_num))
  have hremU : Word.isU64 cols.remainder := Word.isU64_of_cases
    (hremRange 0 (by norm_num)) (hremRange 1 (by norm_num))
    (hremRange 2 (by norm_num)) (hremRange 3 (by norm_num))
  have hqc0 : cols.quotient_comp[0] = cols.quotient[0] := by linear_combination e48
  have hqc1 : cols.quotient_comp[1] = cols.quotient[1] := by linear_combination e49
  have hqc2 : cols.quotient_comp[2] = cols.quotient[2] := by
    rw [h64] at e59; linear_combination e59
  have hqc3 : cols.quotient_comp[3] = cols.quotient[3] := by
    rw [h64] at e69; linear_combination e69
  have hqcEq : cols.quotient_comp = cols.quotient := by
    apply Vector.ext; intro i hi; interval_cases i <;> assumption
  have hqcU : Word.isU64 cols.quotient_comp := hqcEq ▸ hquotU
  have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := by linear_combination e70
  have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := by linear_combination e71
  have hrc2 : cols.remainder_comp[2] = cols.remainder[2] := by
    rw [h64] at e81; linear_combination e81
  have hrc3 : cols.remainder_comp[3] = cols.remainder[3] := by
    rw [h64] at e91; linear_combination e91
  have hrcEq : cols.remainder_comp = cols.remainder := by
    apply Vector.ext; intro i hi; interval_cases i <;> assumption
  have hrcU : Word.isU64 cols.remainder_comp := hrcEq ▸ hremU
  have hctqLoU : Word.isU64 (#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
      cols.c_times_quotient[2], cols.c_times_quotient[3]] : Word (ZMod p)) := Word.isU64_of_cases
    (hctqRange 0 (by norm_num)) (hctqRange 1 (by norm_num))
    (hctqRange 2 (by norm_num)) (hctqRange 3 (by norm_num))
  have hctqHiU : Word.isU64 (#v[cols.c_times_quotient[4], cols.c_times_quotient[5],
      cols.c_times_quotient[6], cols.c_times_quotient[7]] : Word (ZMod p)) := Word.isU64_of_cases
    (hctqRange 4 (by norm_num)) (hctqRange 5 (by norm_num))
    (hctqRange 6 (by norm_num)) (hctqRange 7 (by norm_num))
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
  have hsigned64 : cols.is_div + cols.is_rem = 0 := by linear_combination hfdiv + hfrem
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
    rw [hov] at e154; linear_combination e154
  have hchain1 : cols.c_times_quotient[1] + cols.remainder_comp[1] + cols.carry[0] =
      cols.b[1] + cols.carry[1] * 65536 := by
    rw [hov] at e157; linear_combination e157
  have hchain2 : cols.c_times_quotient[2] + cols.remainder_comp[2] + cols.carry[1] =
      cols.b[2] + cols.carry[2] * 65536 := by
    rw [hov] at e160; linear_combination e160
  have hchain3 : cols.c_times_quotient[3] + cols.remainder_comp[3] + cols.carry[2] =
      cols.b[3] + cols.carry[3] * 65536 := by
    rw [hov] at e163; linear_combination e163
  have hchain4 : cols.c_times_quotient[4] + cols.carry[3] = cols.carry[4] * 65536 := by
    rw [hov, hbneg, hrneg] at e167; linear_combination e167
  have hchain5 : cols.c_times_quotient[5] + cols.carry[4] = cols.carry[5] * 65536 := by
    rw [hov, hbneg, hrneg] at e171; linear_combination e171
  have hchain6 : cols.c_times_quotient[6] + cols.carry[5] = cols.carry[6] * 65536 := by
    rw [hov, hbneg, hrneg] at e175; linear_combination e175
  have hchain7 : cols.c_times_quotient[7] + cols.carry[6] = cols.carry[7] * 65536 := by
    rw [hov, hbneg, hrneg] at e179; linear_combination e179
  have hid := hid_of_carry_chain hcU hbU hqcU hrcU hctqLoU hctqHiU
    hcarry0 hcarry1 hcarry2 hcarry3 hcarry4 hcarry5 hcarry6 hcarry7
    hchain0 hchain1 hchain2 hchain3 hchain4 hchain5 hchain6 hchain7 hlo hhi
  simp only [DivRemCompare.CompareSpec, DivRemCompare.Inputs.ofCols] at hcompare
  have hisZero := hcompare.2.2.2.2.1
  have hltSpec := hcompare.2.2.2.2.2.2.2.1
  clear hcompare
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
      rw [hzeroResult, hir] at e305; linear_combination -e305
    have hmax0 : cols.max_abs_c_or_1[0] = cols.abs_c[0] := by
      rw [hzeroResult] at e299; linear_combination e299
    have hmax1 : cols.max_abs_c_or_1[1] = cols.abs_c[1] := by
      rw [hzeroResult] at e300; linear_combination e300
    have hmax2 : cols.max_abs_c_or_1[2] = cols.abs_c[2] := by
      rw [hzeroResult] at e301; linear_combination e301
    have hmax3 : cols.max_abs_c_or_1[3] = cols.abs_c[3] := by
      rw [hzeroResult] at e302; linear_combination e302
    have hmaxEq : cols.max_abs_c_or_1 = cols.abs_c := by
      apply Vector.ext; intro i hi; interval_cases i <;> assumption
    have hmaxU : Word.isU64 cols.max_abs_c_or_1 := hmaxEq ▸ habsCU
    have hbit := (LtOperationUnsigned.result_semantic habsRU hmaxU hrcm hltSpec).1
    have hbit1 : cols.remainder_lt_operation.u16_compare_operation.bit = 1 := by
      rw [hrcm] at e307; linear_combination -e307
    rw [hbit1] at hbit
    have hcmp : cols.abs_remainder.toNat < cols.max_abs_c_or_1.toNat := by
      by_contra hnot
      rw [if_neg hnot] at hbit
      exact one_ne_zero hbit
    have habsR0 : cols.abs_remainder[0] = cols.remainder_comp[0] := by
      rw [hrneg] at e250; linear_combination e250
    have habsR1 : cols.abs_remainder[1] = cols.remainder_comp[1] := by
      rw [hrneg] at e256; linear_combination e256
    have habsR2 : cols.abs_remainder[2] = cols.remainder_comp[2] := by
      rw [hrneg] at e262; linear_combination e262
    have habsR3 : cols.abs_remainder[3] = cols.remainder_comp[3] := by
      rw [hrneg] at e268; linear_combination e268
    have habsREq : cols.abs_remainder = cols.remainder_comp := by
      apply Vector.ext; intro i hi; interval_cases i <;> assumption
    have habsC0 : cols.abs_c[0] = cols.c[0] := by
      rw [hcneg] at e247; linear_combination e247
    have habsC1 : cols.abs_c[1] = cols.c[1] := by
      rw [hcneg] at e253; linear_combination e253
    have habsC2 : cols.abs_c[2] = cols.c[2] := by
      rw [hcneg] at e259; linear_combination e259
    have habsC3 : cols.abs_c[3] = cols.c[3] := by
      rw [hcneg] at e265; linear_combination e265
    have habsCEq : cols.abs_c = cols.c := by
      apply Vector.ext; intro i hi; interval_cases i <;> assumption
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
