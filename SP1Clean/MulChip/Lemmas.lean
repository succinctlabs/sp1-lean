import SP1Clean.MulChip.Cols
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Mul.Common

/-! # `MulChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas. Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on the chip's
aggregate `is_real` sum (5-way) matching the adapter's trust marker. -/
lemma fromMain_toMain (cols : MulCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Mul.constraints Main` is the conjunction of `MulOp.Spec`, `cpuStateSpec`,
`rtypeReaderSpec`, and the 7 trailing scalar gates, under `is_real =
sum = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 82)
    (h_is_real : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1) :
    (_root_.Mul.constraints Main).allHold ↔
      (SP1Clean.MulOp.Spec
          ⟨#v[Main[28], Main[29], Main[30], Main[31]],
           #v[Main[15], Main[16], Main[17], Main[18]],
           #v[Main[22], Main[23], Main[24], Main[25]],
           #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
              Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
              Main[46], Main[47]],
           #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
              Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
              Main[62], Main[63]],
           #v[Main[64], Main[65], Main[66], Main[67]],
           #v[Main[68], Main[69], Main[70], Main[71]],
           Main[72], Main[73], Main[74], Main[75], Main[76],
           Main[77], Main[78], Main[79], Main[80], Main[81]⟩ ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536)
          (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24)
          #v[Main[3], Main[4], Main[5]]
          #v[Main[28], Main[29], Main[30], Main[31]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp :=
                  { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp :=
                  { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := Main[21],
            op_c_memory :=
              { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                access_timestamp :=
                  { prev_low := Main[26], diff_low_limb := Main[27] } } } ∧
       Main[77] * (Main[77] - 1) = 0 ∧
       Main[78] * (Main[78] - 1) = 0 ∧
       Main[79] * (Main[79] - 1) = 0 ∧
       Main[80] * (Main[80] - 1) = 0 ∧
       Main[81] * (Main[81] - 1) = 0 ∧
       (Main[77] + Main[78] + Main[79] + Main[80] + Main[81]) *
         (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] - 1) = 0 ∧
       Main[13] = 0) := by
  sorry

end SP1Clean.MulChip
