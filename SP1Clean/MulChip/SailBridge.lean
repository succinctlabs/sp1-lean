import SP1Clean.MulChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `MulChip` (directory-form scaffold)

MulChip is a fan-out chip — one constraint surface, **5 Sail variants**:
MUL / MULH / MULHU / MULHSU / MULW. Each variant has its own bridge
theorem composing `fromMain_toMain` + `allHold_iff_structural` + the
corresponding Main-level `correct_*` from `SP1Chips/Mul/MulChip.lean`.

Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- MUL (low 64 bits of unsigned×unsigned product). -/
theorem sail_correct_mul_of_formalSpec
    (cols : MulCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
    (h_is_mul : cols.is_mul = 1)
    (s : SailState)
    (h_init : mulInitialState_cols cols s) :
    (sp1_mul_cols cols).run s =
      (_root_.Mul.Poly.spec_mul (.Regidx (sp1_op_c_cols cols))
                                (.Regidx (sp1_op_b_cols cols))
                                (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- MULH (high 64 bits of signed×signed product). -/
theorem sail_correct_mulh_of_formalSpec
    (cols : MulCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
    (h_is_mulh : cols.is_mulh = 1)
    (s : SailState)
    (h_init : mulInitialState_cols cols s) :
    (sp1_mul_cols cols).run s =
      (_root_.Mulh.Poly.spec_mulh (.Regidx (sp1_op_c_cols cols))
                                  (.Regidx (sp1_op_b_cols cols))
                                  (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- MULHU (high 64 bits of unsigned×unsigned product). -/
theorem sail_correct_mulhu_of_formalSpec
    (cols : MulCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
    (h_is_mulhu : cols.is_mulhu = 1)
    (s : SailState)
    (h_init : mulInitialState_cols cols s) :
    (sp1_mul_cols cols).run s =
      (_root_.Mulhu.Poly.spec_mulhu (.Regidx (sp1_op_c_cols cols))
                                    (.Regidx (sp1_op_b_cols cols))
                                    (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- MULHSU (high 64 bits of signed×unsigned product). -/
theorem sail_correct_mulhsu_of_formalSpec
    (cols : MulCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
    (h_is_mulhsu : cols.is_mulhsu = 1)
    (s : SailState)
    (h_init : mulInitialState_cols cols s) :
    (sp1_mul_cols cols).run s =
      (_root_.Mulhsu.Poly.spec_mulhsu (.Regidx (sp1_op_c_cols cols))
                                      (.Regidx (sp1_op_b_cols cols))
                                      (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- MULW (32-bit signed product, sign-extended to 64 bits). -/
theorem sail_correct_mulw_of_formalSpec
    (cols : MulCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw)
    (h_is_mulw : cols.is_mulw = 1)
    (s : SailState)
    (h_init : mulInitialState_cols cols s) :
    (sp1_mul_cols cols).run s =
      (_root_.Mulw.Poly.spec_mulw (.Regidx (sp1_op_c_cols cols))
                                  (.Regidx (sp1_op_b_cols cols))
                                  (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

end SP1Clean.MulChip
