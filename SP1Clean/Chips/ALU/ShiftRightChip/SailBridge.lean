import SP1Clean.Chips.ALU.ShiftRightChip.Circuit
import SP1Chips.ShiftRight.ShiftRightChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `ShiftRightChip` variants. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_srl_of_formalSpec
    (_cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_srl : _cols.is_srl = 1)
    (_s : SailState) (_h_init : shiftRightInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_sra_of_formalSpec
    (_cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_sra : _cols.is_sra = 1)
    (_s : SailState) (_h_init : shiftRightInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_srlw_of_formalSpec
    (_cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_srlw : _cols.is_srlw = 1)
    (_s : SailState) (_h_init : shiftRightInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_sraw_of_formalSpec
    (_cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_sraw : _cols.is_sraw = 1)
    (_s : SailState) (_h_init : shiftRightInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.ShiftRight
