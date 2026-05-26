import SP1Clean.Chips.ALU.BitwiseChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `BitwiseChip` (directory-form scaffold)

BitwiseChip is a fan-out chip — one constraint surface, **6 Sail variants**:
XOR/OR/AND × R/I (the latter three are XORI/ORI/ANDI). Each variant has
its own monadic Sail bridge composing `fromMain_toMain` +
`allHold_iff_structural` + the corresponding Main-level `correct_*` proof
from `SP1Chips/Bitwise/BitwiseChip.lean`.

Selector hypotheses per variant:
- XOR  : `is_xor = 1`, `imm_c = 0`
- OR   : `is_or  = 1`, `imm_c = 0`
- AND  : `is_and = 1`, `imm_c = 0`
- XORI : `is_xor = 1`, `imm_c = 1`
- ORI  : `is_or  = 1`, `imm_c = 1`
- ANDI : `is_and = 1`, `imm_c = 1`

Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- XOR (R-type, `imm_c = 0`). -/
theorem sail_correct_xor_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_xor : cols.is_xor = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.Xor.spec_xor (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- OR (R-type, `imm_c = 0`). -/
theorem sail_correct_or_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_or : cols.is_or = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.Or.spec_or (.Regidx (sp1_op_c_cols cols))
                         (.Regidx (sp1_op_b_cols cols))
                         (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- AND (R-type, `imm_c = 0`). -/
theorem sail_correct_and_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_and : cols.is_and = 1)
    (h_imm_c : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.And.spec_and (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- XORI (I-type, `imm_c = 1`). -/
theorem sail_correct_xori_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_xor : cols.is_xor = 1)
    (h_imm_c : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.Xori.spec_xori (sp1_op_c_cols cols)
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- ORI (I-type, `imm_c = 1`). -/
theorem sail_correct_ori_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_or : cols.is_or = 1)
    (h_imm_c : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.Ori.spec_ori (sp1_op_c_cols cols)
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

/-- ANDI (I-type, `imm_c = 1`). -/
theorem sail_correct_andi_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted =
      cols.is_xor + cols.is_or + cols.is_and)
    (h_is_and : cols.is_and = 1)
    (h_imm_c : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : bitwiseInitialState_cols cols s) :
    (sp1_bitwise_cols cols).run s =
      (_root_.Andi.spec_andi (sp1_op_c_cols cols)
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

end SP1Clean.BitwiseChip
