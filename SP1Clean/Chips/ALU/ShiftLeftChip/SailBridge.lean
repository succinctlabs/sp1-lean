import SP1Clean.Chips.ALU.ShiftLeftChip.Circuit
import SP1Chips.ShiftLeft.ShiftLeftChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `ShiftLeftChip` variants
(`sll`, `sllw`). All stubbed `True` — depends on Lemmas (sorry'd). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_sll_of_formalSpec
    (_cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_sll : _cols.is_sll = 1)
    (_s : SailState) (_h_init : shiftLeftInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_sllw_of_formalSpec
    (_cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_sllw : _cols.is_sllw = 1)
    (_s : SailState) (_h_init : shiftLeftInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.ShiftLeft
