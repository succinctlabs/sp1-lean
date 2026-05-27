import SP1Clean.Chips.ALU.BitwiseChip.Cols
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Bitwise.BitwiseChip

/-! # `BitwiseChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

Mirrors `AddChip/Lemmas.lean` for the 3-variant XOR/OR/AND chip.

- `fromMain_toMain` — sorry-stub (`BitwiseCols`'s `toMain` not yet
  defined; mechanical follow-up).
- `allHold_iff_structural` — sorry; needs 3-way variant case-split
  + `BitwiseU16Operation.iff_sp1_full` (operation-level sorry'd).
- `formalSpec_of_subcircuit_specs` / `subcircuit_specs_of_formalSpec`
  — sorry; chip's Path-2 main drops `BitwiseU16Operation` byte
  lookups, so per-sub Specs don't surface RV64 fact directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Bitwise

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : BitwiseCols (ZMod p))
    (_h_trusted : True) :
    True := by
  trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 51)
    (_h_is_real : Main[32] + Main[33] + Main[34] = 1) :
    (_root_.Bitwise.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

lemma formalSpec_of_subcircuit_specs
    (cols : BitwiseCols (ZMod p))
    (_h_is_real_sum : cols.is_xor + cols.is_or + cols.is_and = 1) :
    Assertion.FormalSpec cols := by
  sorry

lemma subcircuit_specs_of_formalSpec
    (cols : BitwiseCols (ZMod p))
    (_h_is_real_sum : cols.is_xor + cols.is_or + cols.is_and = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.Bitwise
