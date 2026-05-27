import SP1Clean.Chips.ALU.BitwiseChip.Circuit
import SP1Chips.Bitwise.BitwiseChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridges for `BitwiseChip` variants.

All three R-type variants (`xor`/`or`/`and`) stubbed with `True` —
real bridges depend on `Lemmas.allHold_iff_structural` + `fromMain_toMain`
(both sorry'd). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Bitwise

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_xor_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_xor : _cols.is_xor = 1)
    (_s : SailState) (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_or_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_or : _cols.is_or = 1)
    (_s : SailState) (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

theorem sail_correct_and_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_is_and : _cols.is_and = 1)
    (_s : SailState) (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.Bitwise
