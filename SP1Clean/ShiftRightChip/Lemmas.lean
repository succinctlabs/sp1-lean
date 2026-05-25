import SP1Clean.ShiftRightChip.Cols
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Common

/-! # `ShiftRightChip` cols-level lemmas (stub). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (cols : ShiftRightCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) :
    fromMain (toMain cols) = cols := by
  sorry

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 69)
    (h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (_root_.ShiftRight.constraints Main).allHold ↔ True := by
  sorry

end SP1Clean.ShiftRightChip
