import SP1Clean.LtChip.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Operations.GatedLtSignedOp
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common
import RISCV.Instructions

/-! # `LtChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas: `fromMain_toMain` (round-trip) and
`allHold_iff_structural` (the chip-level constraint bridge). Bodies are
`sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on the chip's
aggregate `is_real` sum matching the adapter's trust marker. -/
lemma fromMain_toMain (cols : LtCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is the chip's canonical `FormalSpec`, under
`is_real = Main[32] + Main[33] = 1`. The RHS mirrors `LtChip.FormalSpec`
applied to `fromMain Main` and is exposed in flat-row form so soundness
can structurally destructure the chip Spec into SP1-native `allHold`
emissions. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44)
    (h_is_real : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔ FormalSpec (fromMain Main) := by
  sorry

end SP1Clean.LtChip
