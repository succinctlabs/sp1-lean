import SP1Clean.LtChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `LtChip` (directory-form scaffold)

LtChip is a fan-out chip — one constraint surface, **4 Sail variants**:
SLT / SLTU / SLTI / SLTIU. Each variant has its own bridge theorem
composing `fromMain_toMain` + `allHold_iff_structural` + the
corresponding Main-level `correct_*` from `SP1Chips/Lt/LtChip.lean`.

Selector hypotheses per variant:
- SLT   : `is_slt = 1`, `imm_c = 0`
- SLTU  : `is_sltu = 1`, `imm_c = 0`
- SLTI  : `is_slt = 1`, `imm_c = 1`
- SLTIU : `is_sltu = 1`, `imm_c = 1`

Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SLT (R-type signed, `is_slt = 1`, `imm_c = 0`). -/
theorem sail_correct_slt_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu)
    (h_is_slt : cols.is_slt = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Slt.spec_slt (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- SLTU (R-type unsigned, `is_sltu = 1`, `imm_c = 0`). -/
theorem sail_correct_sltu_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu)
    (h_is_sltu : cols.is_sltu = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Sltu.spec_sltu (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- SLTI (I-type signed, `is_slt = 1`, `imm_c = 1`). -/
theorem sail_correct_slti_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu)
    (h_is_slt : cols.is_slt = 1)
    (h_imm_c : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Slti.spec_slti (sp1_op_c_cols cols)
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- SLTIU (I-type unsigned, `is_sltu = 1`, `imm_c = 1`). -/
theorem sail_correct_sltiu_of_formalSpec
    (cols : LtCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu)
    (h_is_sltu : cols.is_sltu = 1)
    (h_imm_c : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : ltInitialState_cols cols s) :
    (sp1_lt_cols cols).run s =
      (_root_.Sltiu.spec_sltiu (sp1_op_c_cols cols)
                               (.Regidx (sp1_op_b_cols cols))
                               (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

end SP1Clean.LtChip
