import SP1Clean.SubChip.Circuit
import SP1Chips.Soundness
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridge for `SubChip` (directory-form scaffold)

Composes `fromMain_toMain` + `allHold_iff_structural` + the Main-level
`_root_.Sub.correct_sub` to bridge the chip's cols-level `FormalSpec` to
the Sail-monadic equivalence `_root_.Sub.spec_sub (sp1_*).run s =
(sp1_sub_cols cols).run s`. Mirrors `SP1Clean/AddChip/SailBridge.lean`
1-for-1.

Proof body is `sorry` for the scaffolding phase — the AddChip proof
recipe ports directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : SubCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : subInitialState_cols cols s) :
    (sp1_sub_cols cols).run s =
      (_root_.Sub.spec_sub (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

end SP1Clean.SubChip
