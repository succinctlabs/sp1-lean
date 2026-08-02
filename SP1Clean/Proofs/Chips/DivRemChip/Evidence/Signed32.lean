import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Cases
import SP1Clean.Proofs.Chips.DivRemChip.Evidence.SignedCommon

/-! # `DivRemChip` — signed low-32 evidence extraction

This is the circuit-independent `DIVW`/`REMW` family proof. It consumes the folded whole-row
contracts, proves that the arithmetic operands and results are sign extensions of their low halves,
and makes the overflow, division-by-zero, and normal signed Euclidean cases explicit. -/

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemContract

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Selecting a `DIVW`/`REMW` case pins every one of the eight case flags: the six other-family
flags vanish and the two word-signed flags sum to one. Hoisting the eight-way case split out of
`signed32Evidence` keeps it off that proof's 121-hypothesis assertion context, and returning the
three *derived* gate sums the row equations are actually rewritten by — rather than the eight raw
flag values — keeps the `linear_combination` recombination off it too. -/
private lemma signed32_flags {cols : Columns (ZMod p)} {case : Case}
    (hselected : Selected cols case) (hfamily : case.family = .signed32) :
    cols.is_divw + cols.is_remw = 1 ∧
      cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1 ∧
      cols.is_div + cols.is_rem + cols.is_divw + cols.is_remw = 1 := by
  have hdiv := hselected.flag_eq .div
  have hrem := hselected.flag_eq .rem
  have hdivu := hselected.flag_eq .divu
  have hremu := hselected.flag_eq .remu
  have hdivw := hselected.flag_eq .divw
  have hremw := hselected.flag_eq .remw
  have hdivuw := hselected.flag_eq .divuw
  have hremuw := hselected.flag_eq .remuw
  cases case <;>
    simp [Case.family] at hfamily <;>
    simp [Case.flag] at hdiv hrem hdivu hremu hdivw hremw hdivuw hremuw <;>
    simp [hdiv, hrem, hdivw, hremw, hdivuw, hremuw]

-- The 121-hypothesis `ownAsserts` tail is read through `.1`/`.2` projections instead of a
-- 121-way `obtain` (Clean `doc/performance-problems.md` fix pattern 7), as are the 15-way
-- `hcompare` and 13-way range destructurings: each component's `And.casesOn` motive
-- re-abstracts this very large goal. That was the first halving. An earlier note here called the
-- remaining three-branch body irreducible; that was wrong. The former 800k ceiling came off
-- entirely (measured 332,635 -> 169,718 heartbeats) by moving work *out of* the branch bodies
-- rather than reorganising them in place: the two `Vector.ext` absolute-value sweeps, the
-- remainder-magnitude bound and the `E225`/`E228` sign gates now live in
-- `Evidence/SignedCommon.lean` stated over opaque arguments; `signed32_flags` returns the three
-- derived gate sums the row equations are actually rewritten by instead of the eight raw flag
-- values; and each `gate * (x - y) = 0` row constraint is discharged by the *term*
-- `eq_of_gate_eq_one` rather than a `rw`/`linear_combination` pair that renormalises the whole
-- context. This now runs on the default budget, with more headroom than `Unsigned64` (198,211).
/-- The folded DivRem row contracts imply explicit signed-word evidence for either `DIVW` or `REMW`.
The output-routing equality is deliberately left to the uniform row assembler. -/
theorem signed32Evidence {input : Inputs (ZMod p)} {cols : Columns (ZMod p)} {case : Case}
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
  have e54 := hw15.1
  have hw16 := hw15.2
  have e57 := hw16.1
  have hw17 := hw16.2
  have hw18 := hw17.2
  have hw19 := hw18.2
  have e64 := hw19.1
  have hw20 := hw19.2
  have e67 := hw20.1
  have hw21 := hw20.2
  have hw22 := hw21.2
  have e70 := hw22.1
  have hw23 := hw22.2
  have e71 := hw23.1
  have hw24 := hw23.2
  have hw25 := hw24.2
  have e76 := hw25.1
  have hw26 := hw25.2
  have e79 := hw26.1
  have hw27 := hw26.2
  have hw28 := hw27.2
  have hw29 := hw28.2
  have e86 := hw29.1
  have hw30 := hw29.2
  have e89 := hw30.1
  have hw31 := hw30.2
  have hw32 := hw31.2
  have e96 := hw32.1
  have hw33 := hw32.2
  have hw34 := hw33.2
  have hw35 := hw34.2
  have e105 := hw35.1
  have hw36 := hw35.2
  have e107 := hw36.1
  have hw37 := hw36.2
  have e109 := hw37.1
  have hw38 := hw37.2
  have e111 := hw38.1
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
  have hw48 := hw47.2
  have hw49 := hw48.2
  have hw50 := hw49.2
  have hw51 := hw50.2
  have hw52 := hw51.2
  have hw53 := hw52.2
  have hw54 := hw53.2
  have hw55 := hw54.2
  have hw56 := hw55.2
  have hw57 := hw56.2
  have hw58 := hw57.2
  have hw59 := hw58.2
  have e225 := hw59.1
  have hw60 := hw59.2
  have e228 := hw60.1
  have hw61 := hw60.2
  have e230 := hw61.1
  have hw62 := hw61.2
  have e232 := hw62.1
  have hw63 := hw62.2
  have hw64 := hw63.2
  have hw65 := hw64.2
  have e238 := hw65.1
  have hw66 := hw65.2
  have e240 := hw66.1
  have hw67 := hw66.2
  have hw68 := hw67.2
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
  have e270 := hw77.1
  have hw78 := hw77.2
  have e272 := hw78.1
  have hw79 := hw78.2
  have e274 := hw79.1
  have hw80 := hw79.2
  have e276 := hw80.1
  have hw81 := hw80.2
  have e278 := hw81.1
  have hw82 := hw81.2
  have e280 := hw82.1
  have hw83 := hw82.2
  have e282 := hw83.1
  have hw84 := hw83.2
  have e284 := hw84.1
  have hw85 := hw84.2
  have e286 := hw85.1
  have hw86 := hw85.2
  have e288 := hw86.1
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
  have hw98 := hw97.2
  have hw99 := hw98.2
  have hw100 := hw99.2
  have hw101 := hw100.2
  have hw102 := hw101.2
  have hw103 := hw102.2
  have hw104 := hw103.2
  have hw105 := hw104.2
  have hw106 := hw105.2
  have hw107 := hw106.2
  have hw108 := hw107.2
  have hw109 := hw108.2
  have e341 := hw109.1
  have hw110 := hw109.2
  have hw111 := hw110.2
  have e345 := hw111.1
  have hw112 := hw111.2
  have hw113 := hw112.2
  have hw114 := hw113.2
  have e351 := hw114.1
  clear hown hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19
    hw20 hw21 hw22 hw23 hw24 hw25 hw26 hw27 hw28 hw29 hw30 hw31 hw32 hw33 hw34 hw35 hw36 hw37
    hw38 hw39 hw40 hw41 hw42 hw43 hw44 hw45 hw46 hw47 hw48 hw49 hw50 hw51 hw52 hw53 hw54 hw55
    hw56 hw57 hw58 hw59 hw60 hw61 hw62 hw63 hw64 hw65 hw66 hw67 hw68 hw69 hw70 hw71 hw72 hw73
    hw74 hw75 hw76 hw77 hw78 hw79 hw80 hw81 hw82 hw83 hw84 hw85 hw86 hw87 hw88 hw89 hw90 hw91
    hw92 hw93 hw94 hw95 hw96 hw97 hw98 hw99 hw100 hw101 hw102 hw103 hw104 hw105 hw106 hw107
    hw108 hw109 hw110 hw111 hw112 hw113 hw114
  obtain ⟨hsigned32, hword, hsigned⟩ := signed32_flags hselected hfamily
  have hir : cols.is_real = 1 := hinputReal.trans hreal
  simp only [DivRemCompare.CompareSpec, DivRemCompare.Inputs.ofCols] at hcompare
  have hovbLow := hcompare.2.2.1
  have hovcLow := hcompare.2.2.2.1
  have hisZero := hcompare.2.2.2.2.1
  have haddC := hcompare.2.2.2.2.2.1
  have haddR := hcompare.2.2.2.2.2.2.1
  have hltSpec := hcompare.2.2.2.2.2.2.2.1
  have hmsbB1 := hcompare.2.2.2.2.2.2.2.2.2.2.2.1
  have hmsbC1 := hcompare.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmsbR1 := hcompare.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmsbQ1 := hcompare.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hcompare
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
    rw [hsigned] at e15; linear_combination -e15
  have hcnegEq : cols.c_neg = cols.c_msb.msb := by
    rw [hsigned] at e19; linear_combination -e19
  have hrnegEq : cols.rem_neg = cols.rem_msb.msb := by
    rw [hsigned] at e17; linear_combination -e17
  have hb2 : cols.b[2] = cols.b_neg * 65535 := by
    rw [hword] at e29; linear_combination e29
  have hb3 : cols.b[3] = cols.b_neg * 65535 := by
    rw [hword] at e41; linear_combination e41
  have hc2 : cols.c[2] = cols.c_neg * 65535 := by
    rw [hword] at e35; linear_combination e35
  have hc3 : cols.c[3] = cols.c_neg * 65535 := by
    rw [hword] at e47; linear_combination e47
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
    rw [hb2, hbnegEq, hbmsb]; split <;> simp [val_65535_zmod_p]
  have hbf3 : cols.b[3].val = if 32768 ≤ cols.b[1].val then 65535 else 0 := by
    rw [hb3, hbnegEq, hbmsb]; split <;> simp [val_65535_zmod_p]
  have hcf2 : cols.c[2].val = if 32768 ≤ cols.c[1].val then 65535 else 0 := by
    rw [hc2, hcnegEq, hcmsb]; split <;> simp [val_65535_zmod_p]
  have hcf3 : cols.c[3].val = if 32768 ≤ cols.c[1].val then 65535 else 0 := by
    rw [hc3, hcnegEq, hcmsb]; split <;> simp [val_65535_zmod_p]
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
  have hqmsb := hmsbQ1.2 hword
  have hrmsb := hmsbR1.2 hword
  have hqc0 : cols.quotient_comp[0] = cols.quotient[0] := by linear_combination e48
  have hqc1 : cols.quotient_comp[1] = cols.quotient[1] := by linear_combination e49
  have hqc2 : cols.quotient_comp[2] = cols.quot_msb.msb * 65535 := by
    rw [hsigned32] at e54; linear_combination e54
  have hqc3 : cols.quotient_comp[3] = cols.quot_msb.msb * 65535 := by
    rw [hsigned32] at e64; linear_combination e64
  have hqo2 : cols.quotient[2] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e57; linear_combination e57
  have hqo3 : cols.quotient[3] = cols.quot_msb.msb * 65535 := by
    rw [hword] at e67; linear_combination e67
  have hqcEq : cols.quotient_comp = cols.quotient := by
    apply Vector.ext; intro i hi; interval_cases i
    · exact hqc0
    · exact hqc1
    · rw [hqc2, hqo2]
    · rw [hqc3, hqo3]
  have hqcU : Word.isU64 cols.quotient_comp := hqcEq ▸ hquotU
  have hrc0 : cols.remainder_comp[0] = cols.remainder[0] := by linear_combination e70
  have hrc1 : cols.remainder_comp[1] = cols.remainder[1] := by linear_combination e71
  have hrc2 : cols.remainder_comp[2] = cols.rem_msb.msb * 65535 := by
    rw [hsigned32] at e76; linear_combination e76
  have hrc3 : cols.remainder_comp[3] = cols.rem_msb.msb * 65535 := by
    rw [hsigned32] at e86; linear_combination e86
  have hro2 : cols.remainder[2] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e79; linear_combination e79
  have hro3 : cols.remainder[3] = cols.rem_msb.msb * 65535 := by
    rw [hword] at e89; linear_combination e89
  have hrcEq : cols.remainder_comp = cols.remainder := by
    apply Vector.ext; intro i hi; interval_cases i
    · exact hrc0
    · exact hrc1
    · rw [hrc2, hro2]
    · rw [hrc3, hro3]
  have hrcU : Word.isU64 cols.remainder_comp := hrcEq ▸ hremU
  have hqf2 : cols.quotient_comp[2].val =
      if 32768 ≤ cols.quotient_comp[1].val then 65535 else 0 := by
    rw [hqc2, hqmsb, hqc1]; split <;> simp [val_65535_zmod_p]
  have hqf3 : cols.quotient_comp[3].val =
      if 32768 ≤ cols.quotient_comp[1].val then 65535 else 0 := by
    rw [hqc3, hqmsb, hqc1]; split <;> simp [val_65535_zmod_p]
  have hrf2 : cols.remainder_comp[2].val =
      if 32768 ≤ cols.remainder_comp[1].val then 65535 else 0 := by
    rw [hrc2, hrmsb, hrc1]; split <;> simp [val_65535_zmod_p]
  have hrf3 : cols.remainder_comp[3].val =
      if 32768 ≤ cols.remainder_comp[1].val then 65535 else 0 := by
    rw [hrc3, hrmsb, hrc1]; split <;> simp [val_65535_zmod_p]
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
    apply Vector.ext; intro i hi; interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hbRaw0
    · simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] using hbRaw1
    · rfl
    · rfl
  have hcLowVec :
      (#v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1], 0, 0] :
        Word (ZMod p)) = #v[cols.c[0], cols.c[1], 0, 0] := by
    apply Vector.ext; intro i hi; interval_cases i
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
      rw [hov, hsigned] at e96; linear_combination -e96
    obtain ⟨hbMin, hcNegOne⟩ :=
      overflow_of_iseqword_word hbU hcU hword hovb hovc hovProduct
    have hq0 : cols.quotient_comp[0] = cols.b[0] := hqc0.trans (eq_of_gate_eq_one hov e105)
    have hq1 : cols.quotient_comp[1] = cols.b[1] := hqc1.trans (eq_of_gate_eq_one hov e109)
    have hqLowB := extractLsb_lo_congr hqcU hbU hq0 hq1
    have hr0 : cols.remainder_comp[0] = 0 := hrc0.trans (eq_of_gate_eq_one hov e107)
    have hr1 : cols.remainder_comp[1] = 0 := hrc1.trans (eq_of_gate_eq_one hov e111)
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
      have hq0 : cols.quotient_comp[0] = 65535 :=
        hqc0.trans (eq_of_gate_eq_one hzeroResult e230)
      have hq1 : cols.quotient_comp[1] = 65535 :=
        hqc1.trans (eq_of_gate_eq_one hzeroResult e232)
      have hqLowNegOne : BitVec.extractLsb 31 0
          (Word.toBitVec64 cols.quotient_comp) = -1#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [extractLsb_lo_toNat hqcU, hq0, hq1, BitVec.neg_one_eq_allOnes,
          BitVec.toNat_allOnes]
        simp only [val_65535_zmod_p]
        norm_num
      have hr0 : cols.remainder_comp[0] = cols.b[0] := eq_of_gate_eq_one hzeroResult e238
      have hr1 : cols.remainder_comp[1] = cols.b[1] := eq_of_gate_eq_one hzeroResult e240
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
      obtain ⟨hcAbsPos, hcAbsNeg⟩ :=
        signedAbs_of_asserts hcnegBit hir e247 e253 e259 e265 e286 e270 e272 e274 e276 haddC
      obtain ⟨hrAbsPos, hrAbsNeg⟩ :=
        signedAbs_of_asserts hrnegBit hir e250 e256 e262 e268 e288 e278 e280 e282 e284 haddR
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
        rw [hov0] at e154; linear_combination e154
      have hchain1 : cols.c_times_quotient[1] + cols.remainder_comp[1] + cols.carry[0] =
          cols.b[1] + cols.carry[1] * 65536 := by
        rw [hov0] at e157; linear_combination e157
      have hchain2 : cols.c_times_quotient[2] + cols.remainder_comp[2] + cols.carry[1] =
          cols.b[2] + cols.carry[2] * 65536 := by
        rw [hov0] at e160; linear_combination e160
      have hchain3 : cols.c_times_quotient[3] + cols.remainder_comp[3] + cols.carry[2] =
          cols.b[3] + cols.carry[3] * 65536 := by
        rw [hov0] at e163; linear_combination e163
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
      have hcnz : ¬ (cols.c[0] = 0 ∧ cols.c[1] = 0 ∧ cols.c[2] = 0 ∧ cols.c[3] = 0) := by
        rintro ⟨z0, z1, z2, z3⟩
        apply hcZero
        rw [Word.toNat_def, z0, z1, z2, z3]
        simp
      have hcmp := absRemainder_lt_absC hir hcnz habsRU habsCU hisZero hltSpec
        e299 e300 e301 e302 e305 e307
      have hlt := hlt_signed_of_abs habsRU habsCU hrAbsPos hrAbsNeg hcAbsPos hcAbsNeg hcmp
      have hcBVNe : Word.toBitVec64 cols.c ≠ 0#64 := by
        intro hzero
        apply hcZero
        have hnat := congrArg BitVec.toNat hzero
        simpa [Word.toBitVec64_toNat hcU] using hnat
      obtain ⟨hE225, hE228Comp⟩ := signGates_of_asserts hremU hrcEq e225 e228 e345 e351
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
