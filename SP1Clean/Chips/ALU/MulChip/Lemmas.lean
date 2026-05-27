import SP1Clean.Chips.ALU.MulChip.Cols
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Mul.Common

/-! # `MulChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

Mul is closer to fully provable than the other 5 chips — its `main`
already composes `SP1Clean.MulOp.assertion` as a Clean subcircuit
(canonical (a) shape). The sorries reduce to `MulOperation.iff_sp1_full`
(operation-level sorry'd) once the full lemma chain is in place. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Mul

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
lemma fromMain_toMain (_cols : MulCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 82)
    (_h_is_real :
      Main[78] + Main[79] + Main[80] + Main[81] + (1 : ZMod p) = 1) :
    (_root_.Mul.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

lemma formalSpec_of_subcircuit_specs
    (cols : MulCols (ZMod p))
    (_h_is_real_sum :
      cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : MulCols (ZMod p))
    (_h_is_real_sum :
      cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.Mul
