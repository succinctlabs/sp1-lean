import SP1Clean.Chips.ALU.ShiftRightChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # `ShiftRightChip` Sail bridges (stubs).

8 variants: SRL/SRLI/SRA/SRAI/SRLW/SRLIW/SRAW/SRAIW. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_srl_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_srl : cols.is_srl = 1) (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_srli_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_srl : cols.is_srl = 1) (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_sra_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sra : cols.is_sra = 1) (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_srai_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sra : cols.is_sra = 1) (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_srlw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_srlw : cols.is_srlw = 1) (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_srliw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_srlw : cols.is_srlw = 1) (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_sraw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sraw : cols.is_sraw = 1) (_h_imm_c : cols.adapter.imm_c = 0) :
    True := by trivial

omit [Fact (2 ^ 17 < p)] in
theorem sail_correct_sraiw_of_formalSpec
    (cols : ShiftRightCols (ZMod p))
    (_h_spec : Assertion.FormalSpec cols)
    (_h_is_sraw : cols.is_sraw = 1) (_h_imm_c : cols.adapter.imm_c = 1) :
    True := by trivial

end SP1Clean.ShiftRightChip
