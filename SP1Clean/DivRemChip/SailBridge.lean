import SP1Clean.DivRemChip.Circuit
import SP1Chips.Soundness

/-! # `DivRemChip` Sail bridges (stubs).

8 variants: DIV / DIVU / DIVW / DIVUW / REM / REMU / REMW / REMUW. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_div_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_div : cols.aux_post.mode_flags[0] = 1) : True := by sorry

theorem sail_correct_divu_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_divu : cols.aux_post.mode_flags[1] = 1) : True := by sorry

theorem sail_correct_rem_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_rem : cols.aux_post.mode_flags[2] = 1) : True := by sorry

theorem sail_correct_remu_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_remu : cols.aux_post.mode_flags[3] = 1) : True := by sorry

theorem sail_correct_divw_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_divw : cols.aux_post.mode_flags[4] = 1) : True := by sorry

theorem sail_correct_remw_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_remw : cols.aux_post.mode_flags[5] = 1) : True := by sorry

theorem sail_correct_divuw_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_divuw : cols.aux_post.mode_flags[6] = 1) : True := by sorry

theorem sail_correct_remuw_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_remuw : cols.aux_post.mode_flags[7] = 1) : True := by sorry

end SP1Clean.DivRemChip
