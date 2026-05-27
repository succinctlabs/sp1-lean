import SP1Clean.Chips.ALU.LtChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `LtChip` (directory-form scaffold)

LtChip is a fan-out chip — one constraint surface, **4 Sail variants**:
SLT / SLTU / SLTI / SLTIU.

**Status (2026-05-27, Phase 3A landing):** All 4 bridges are stubbed
`: True := by trivial`, mirroring the legacy bundled-chip convention
established by `SP1Clean/Chips/ALU/LtChip/SailBridge.lean`. The genuine
`(sp1_lt_cols cols).run s = (...).run s` form is blocked on missing
`GatedLtSignedOp.iff_sp1` / `GatedLtUnsignedOp.iff_sp1` bridges (200-400
LoC each) plus `Lemmas.allHold_iff_structural` (50-300 LoC); both are
deferred to a future cleanup. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SLT (R-type signed). Stubbed to match legacy convention. -/
theorem sail_correct_slt_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_slt + _cols.is_sltu)
    (_h_is_slt : _cols.is_slt = 1)
    (_h_imm_c : _cols.adapter.imm_c = 0)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

/-- SLTU (R-type unsigned). Stubbed to match legacy convention. -/
theorem sail_correct_sltu_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_slt + _cols.is_sltu)
    (_h_is_sltu : _cols.is_sltu = 1)
    (_h_imm_c : _cols.adapter.imm_c = 0)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

/-- SLTI (I-type signed). Stubbed to match legacy convention. -/
theorem sail_correct_slti_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_slt + _cols.is_sltu)
    (_h_is_slt : _cols.is_slt = 1)
    (_h_imm_c : _cols.adapter.imm_c = 1)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

/-- SLTIU (I-type unsigned). Stubbed to match legacy convention. -/
theorem sail_correct_sltiu_of_formalSpec
    (_cols : LtCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_slt + _cols.is_sltu)
    (_h_is_sltu : _cols.is_sltu = 1)
    (_h_imm_c : _cols.adapter.imm_c = 1)
    (_s : SailState)
    (_h_init : ltInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.LtChip
