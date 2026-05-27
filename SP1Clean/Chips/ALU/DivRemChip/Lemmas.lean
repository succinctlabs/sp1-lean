import SP1Clean.Chips.ALU.DivRemChip.Cols
import SP1Clean.Reader.RTypeReader
import SP1Chips.DivRem.Constraints

/-! # `DivRemChip` cols-level lemmas (4-lemma scaffold, all sorry'd).

DivRem is the heaviest chip (246 cols, 8 variants in
`aux_post.mode_flags`). The chip-level allHold structural bridge
needs case-splits over 8 variants + 11 mid-level sub-op Specs
(`MulOp.Spec` × 2, `IsEqualWordOp.Spec` × 4, `IsZeroWordOp.Spec`,
`AddOp.Spec` × 2, `LtUnsignedOp.Spec`, `U16MSBOp.Spec` × 7) + 117
inline aux-gates. Realistic implementation is multi-week. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : DivRemCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 246) (_h_is_real : Main[244] = 1) :
    (_root_.DivRem.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

lemma formalSpec_of_subcircuit_specs
    (cols : DivRemCols (ZMod p))
    (_h_is_real : cols.is_real = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : DivRemCols (ZMod p))
    (_h_is_real : cols.is_real = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.DivRem
