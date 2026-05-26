import SP1Clean.Chips.ALU.ShiftLeftChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # `ShiftLeftChip` Sail bridges (stubs).

4 variants: SLL / SLLI / SLLW / SLLIW. Theorem bodies + signatures are
deferred to the proof phase. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeftChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_sll_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sll : cols.is_sll = 1)
    (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by sorry

theorem sail_correct_slli_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sll : cols.is_sll = 1)
    (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by sorry

theorem sail_correct_sllw_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sllw : cols.is_sllw = 1)
    (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by sorry

theorem sail_correct_slliw_of_formalSpec
    (cols : ShiftLeftCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sllw : cols.is_sllw = 1)
    (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by sorry

end SP1Clean.ShiftLeftChip
