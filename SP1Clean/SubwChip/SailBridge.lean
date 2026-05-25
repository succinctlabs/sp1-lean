import SP1Clean.SubwChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `SubwChip` (directory-form scaffold)

Unlike AddwChip (which bundles ADDW + ADDIW), SubwChip is single-variant
(no SUBIW in RV64I), so this file exports a single bridge theorem. Body
is `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubwChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : SubwCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : subwInitialState_cols cols s) :
    (sp1_subw_cols cols).run s =
      (_root_.Subw.spec_subw (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  sorry

end SP1Clean.SubwChip
