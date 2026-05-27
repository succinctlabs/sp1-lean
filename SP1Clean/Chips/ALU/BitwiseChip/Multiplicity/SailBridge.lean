import SP1Clean.Chips.ALU.BitwiseChip.Multiplicity.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridges for `BitwiseChip` (directory-form scaffold)

BitwiseChip is a fan-out chip — one constraint surface, **6 Sail variants**:
XOR/OR/AND × R/I (the latter three are XORI/ORI/ANDI). Each variant has
its own monadic Sail bridge.

**Status (2026-05-27, Phase 3A landing):** All 6 bridges are stubbed
`: True := by trivial`, mirroring the legacy bundled-chip convention
established by `SP1Clean/Chips/ALU/BitwiseChip/SailBridge.lean` (R-type)
and `SP1Clean/Chips/ALU/ShiftRightChip/SailBridge.lean` (4-variant). The
genuine `(sp1_bitwise_cols cols).run s = (...).run s` form requires
upstream `Lemmas.allHold_iff_structural` + the variant-specific
Main-level `correct_*` proofs from `SP1Chips/Bitwise/BitwiseChip.lean`,
and is deferred to a future cleanup. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- XOR (R-type, `imm_c = 0`). Stubbed to match legacy convention. -/
theorem sail_correct_xor_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_xor : _cols.is_xor = 1)
    (_h_imm_c : _cols.adapter.imm_c = 0)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

/-- OR (R-type, `imm_c = 0`). Stubbed to match legacy convention. -/
theorem sail_correct_or_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_or : _cols.is_or = 1)
    (_h_imm_c : _cols.adapter.imm_c = 0)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

/-- AND (R-type, `imm_c = 0`). Stubbed to match legacy convention. -/
theorem sail_correct_and_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_and : _cols.is_and = 1)
    (_h_imm_c : _cols.adapter.imm_c = 0)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

/-- XORI (I-type, `imm_c = 1`). Stubbed to match legacy convention. -/
theorem sail_correct_xori_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_xor : _cols.is_xor = 1)
    (_h_imm_c : _cols.adapter.imm_c = 1)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

/-- ORI (I-type, `imm_c = 1`). Stubbed to match legacy convention. -/
theorem sail_correct_ori_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_or : _cols.is_or = 1)
    (_h_imm_c : _cols.adapter.imm_c = 1)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

/-- ANDI (I-type, `imm_c = 1`). Stubbed to match legacy convention. -/
theorem sail_correct_andi_of_formalSpec
    (_cols : BitwiseCols (ZMod p))
    (_h_spec : Assertion.FormalSpec _cols)
    (_h_assumptions : _cols.adapter_cols.is_trusted =
      _cols.is_xor + _cols.is_or + _cols.is_and)
    (_h_is_and : _cols.is_and = 1)
    (_h_imm_c : _cols.adapter.imm_c = 1)
    (_s : SailState)
    (_h_init : bitwiseInitialState_cols _cols _s) :
    True := by trivial

end SP1Clean.BitwiseChip
