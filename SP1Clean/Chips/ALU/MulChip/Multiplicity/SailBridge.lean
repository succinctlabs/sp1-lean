import SP1Clean.Chips.ALU.MulChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `MulChip` (directory-form scaffold)

MulChip is a fan-out chip — one constraint surface, **5 Sail variants**:
MUL / MULH / MULHU / MULHSU / MULW.

**Status (2026-05-27, Phase 3A landing):** All 5 bridges are stubbed
`: True := by trivial`, mirroring the legacy bundled-chip convention
established by `SP1Clean/Chips/ALU/MulChip/SailBridge.lean`. The
genuine `(sp1_mul_cols cols).run s = (...).run s` form requires upstream
`Lemmas.allHold_iff_structural` + the variant-specific Main-level
`correct_*` proofs from `SP1Chips/Mul/MulChip.lean`, and is deferred to
a future cleanup. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_mul_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_mul + _cols.is_mulh + _cols.is_mulhu + _cols.is_mulhsu + _cols.is_mulw)
    (_h_is_mul : _cols.is_mul = 1)
    (_s : SailState)
    (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_mulh_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_mul + _cols.is_mulh + _cols.is_mulhu + _cols.is_mulhsu + _cols.is_mulw)
    (_h_is_mulh : _cols.is_mulh = 1)
    (_s : SailState)
    (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_mulhu_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_mul + _cols.is_mulh + _cols.is_mulhu + _cols.is_mulhsu + _cols.is_mulw)
    (_h_is_mulhu : _cols.is_mulhu = 1)
    (_s : SailState)
    (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_mulhsu_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_mul + _cols.is_mulh + _cols.is_mulhu + _cols.is_mulhsu + _cols.is_mulw)
    (_h_is_mulhsu : _cols.is_mulhsu = 1)
    (_s : SailState)
    (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_mulw_of_formalSpec
    (_cols : MulCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_mul + _cols.is_mulh + _cols.is_mulhu + _cols.is_mulhsu + _cols.is_mulw)
    (_h_is_mulw : _cols.is_mulw = 1)
    (_s : SailState)
    (_h_init : mulInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.MulChip
