import SP1Clean.Chips.ALU.ShiftRightChip.Cols
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Common

/-! # `ShiftRightChip` cols-level lemmas (4-lemma scaffold, all sorry'd) -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : ShiftRightCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 69)
    (_h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (_root_.ShiftRight.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

lemma formalSpec_of_subcircuit_specs
    (cols : ShiftRightCols (ZMod p))
    (_h_is_real_sum :
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_is_real_sum :
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.ShiftRight
