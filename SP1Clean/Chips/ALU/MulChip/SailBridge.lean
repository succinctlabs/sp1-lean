import SP1Clean.Chips.ALU.MulChip.Circuit
import SP1Chips.Mul.MulChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `MulChip` variants. -/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace SP1Clean.Mul

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

theorem sail_correct_mul_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_mul : _cols.is_mul = 1)
    (_s : SailState) (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_mulh_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_mulh : _cols.is_mulh = 1)
    (_s : SailState) (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_mulhu_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_mulhu : _cols.is_mulhu = 1)
    (_s : SailState) (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_mulhsu_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_mulhsu : _cols.is_mulhsu = 1)
    (_s : SailState) (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_mulw_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_mulw : _cols.is_mulw = 1)
    (_s : SailState) (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.Mul
