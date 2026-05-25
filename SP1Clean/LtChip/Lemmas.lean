import SP1Clean.LtChip.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common

/-! # `LtChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas: `fromMain_toMain` (round-trip) and
`allHold_iff_structural` (the chip-level constraint bridge). Bodies are
`sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on the chip's
aggregate `is_real` sum matching the adapter's trust marker. -/
lemma fromMain_toMain (cols : LtCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is the conjunction of `LtSignedOp.Spec`,
`cpuStateSpec`, `aluTypeReaderSpec`, and the 4 trailing scalar gates,
under `is_real = Main[32] + Main[33] = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44)
    (h_is_real : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔
      (SP1Clean.LtSignedOp.Spec
          ⟨#v[Main[15], Main[16], Main[17], Main[18]],
           #v[Main[25], Main[26], Main[27], Main[28]],
           Main[32],
           Main[34],
           #v[Main[35], Main[36], Main[37], Main[38]],
           Main[39],
           #v[Main[40], Main[41]],
           Main[42], Main[43]⟩ ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.ALUTypeReader.aluTypeReaderSpec
          (Main[2] + Main[1] * 65536)
          (Main[32] * 9 + Main[33] * 10)
          #v[Main[3], Main[4], Main[5]]
          #v[Main[34], 0, 0, 0]
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
            op_c := #v[Main[21], Main[22], Main[23], Main[24]],
            op_c_memory :=
              { prev_value := #v[Main[25], Main[26], Main[27], Main[28]],
                access_timestamp :=
                  { prev_low := Main[29], diff_low_limb := Main[30] } },
            imm_c := Main[31] } ∧
       Main[32] * (Main[32] - 1) = 0 ∧
       Main[33] * (Main[33] - 1) = 0 ∧
       (Main[32] + Main[33] = 0 ∨ Main[32] + Main[33] - 1 = 0) ∧
       Main[13] = 0) := by
  sorry

end SP1Clean.LtChip
