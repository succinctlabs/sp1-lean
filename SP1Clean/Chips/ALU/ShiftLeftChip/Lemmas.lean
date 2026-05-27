import SP1Clean.Chips.ALU.ShiftLeftChip.Cols
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Common

/-! # `ShiftLeftChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

2-variant chip (`sll`/`sllw`). The shift operation is inline (no
separate `ShiftLeftOperation` module); the chip-level
`_root_.ShiftLeft.allHold_constraints_iff` exposes the byte-level
internals directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : ShiftLeftCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 65)
    (_h_is_real : Main[63] + Main[64] = 1) :
    (_root_.ShiftLeft.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

lemma formalSpec_of_subcircuit_specs
    (cols : ShiftLeftCols (ZMod p))
    (_h_is_real_sum : cols.is_sll + cols.is_sllw = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_is_real_sum : cols.is_sll + cols.is_sllw = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.ShiftLeft
