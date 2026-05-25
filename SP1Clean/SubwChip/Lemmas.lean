import SP1Clean.SubwChip.Cols
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Clean.Operations.SubwOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Subw.Common

/-! # `SubwChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas. Mirrors `SP1Clean/AddwChip/Lemmas.lean` but with
`RTypeReader.rtypeReaderSpec` in place of `aluTypeReaderSpec` (no
`imm_c` switch — Subw is RType-only). Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubwChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on
`cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : SubwCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Subw.constraints Main` is exactly the conjunction of `SubwOp.Spec`,
`cpuStateSpec`, and `rtypeReaderSpec` over `fromMain Main`, under
`is_real = Main[31] = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 32) (h_is_real : Main[31] = 1) :
    (_root_.Subw.constraints Main).allHold ↔
      (SP1Clean.SubwOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          { value := #v[Main[28], Main[29]], msb := { msb := Main[30] } } ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536) 20 #v[Main[3], Main[4], Main[5]]
          #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535]
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
       Main[31] * (Main[31] - 1) = 0 ∧
       Main[13] = 0) := by
  sorry

end SP1Clean.SubwChip
