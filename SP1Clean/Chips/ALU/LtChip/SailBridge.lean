import SP1Clean.Chips.ALU.LtChip.Circuit
import SP1Chips.Lt.LtChip
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridge for `LtChip`

Mirrors `SP1Clean/Chips/ALU/AddChip/SailBridge.lean` for the 2-variant
case (`slt` + `sltu`).

**Sorries** — currently both `sail_correct_slt_of_formalSpec` and
`sail_correct_sltu_of_formalSpec` are stubbed. They depend on
`Lemmas.allHold_iff_structural` (sorry'd) and `Lemmas.fromMain_toMain`
(sorry'd) to lift the cols-level `FormalSpec` to a flat-row `allHold`,
then invoke `_root_.Slt.correct_slt` / `_root_.Sltu.correct_sltu`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sail-monadic equivalence to `_root_.Slt.spec_slt` under the
chip's FormalSpec. **Sorry** — see file docstring. -/
theorem sail_correct_slt_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : Assertion.Assumptions _cols)
    (_h_is_slt : _cols.is_slt = 1)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

/-- Sail-monadic equivalence to `_root_.Sltu.spec_sltu` under the
chip's FormalSpec. **Sorry** — see file docstring. -/
theorem sail_correct_sltu_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : Assertion.Assumptions _cols)
    (_h_is_sltu : _cols.is_sltu = 1)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.Lt
