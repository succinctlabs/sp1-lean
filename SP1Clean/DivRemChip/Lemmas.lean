import SP1Clean.DivRemChip.Cols
import SP1Chips.DivRem.Common

/-! # `DivRemChip` cols-level lemmas (stub).

`fromMain_toMain` and `allHold_iff_structural` deferred — DivRem's
246-column struct makes both lemmas substantial. Stubs only. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

lemma fromMain_toMain_stub (cols : DivRemCols (ZMod p)) :
    True := by
  sorry

lemma allHold_iff_structural_stub
    (Main : Vector (ZMod p) 246) (h_is_real : Main[244] = 1) :
    (_root_.DivRem.constraints Main).allHold ↔ True := by
  sorry

end SP1Clean.DivRemChip
