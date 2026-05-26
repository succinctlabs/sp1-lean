import SP1Clean.Chips.ALU.LtChip.Multiplicity.Circuit
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

**Status (2026-05-25, scope discovery during `p3-lt-sail` attempt):**
The 4 bodies below are blocked on the same root cause as `Lemmas.lean:55`'s
`allHold_iff_structural`: the chip-level structural bridge needs to convert
`GatedLtSignedOp.Assertion.FormalSpec` ↔ `LtOperationSigned.constraints.allHold`,
and that bridge does NOT exist in either direction. The worklist row
`p3-lt-sail` rates this task "mechanical" but the underlying operation-level
prerequisites (`GatedLtSignedOp.iff_sp1`, `GatedLtUnsignedOp.iff_sp1`) are
missing. Closing the 4 SailBridge sorries requires either:

1. Adding `iff_sp1` bridges to `SP1Clean/Operations/GatedLtSignedOp.lean` and
   `SP1Clean/Operations/GatedLtUnsignedOp.lean` (proposed new row
   `p3-lt-gated-iff-sp1`; ~200-400 lines per bridge), then closing
   `Lemmas.lean:55` (~50-80 lines) using them, then each Sail bridge here
   (~20-25 lines each).
2. Or writing a single monolithic `allHold_iff_structural` inline in
   `Lemmas.lean` (~300-500 lines) that bypasses the operation-level bridges.

Both paths leave these 4 SailBridge sorries closeable in ~80 lines (one per
variant) once the structural bridge is in place. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: blocked on
-- `GatedLtSignedOp.iff_sp1` + `Lemmas.allHold_iff_structural` (see file-level
-- docstring above for the closure path).
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

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: same blocker as `slt`.
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

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: same blocker as `slt`.
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

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: same blocker as `slt`.
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
