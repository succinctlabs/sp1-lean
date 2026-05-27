import SP1Foundations
import SP1Operations.Operation.MulOperation.Operation
import SP1Operations.Operation.MulOperation.Constraints
import RISCV.Instructions

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace MulOperation

/-- Bidirectional bridge between `MulOperation.allHold` (multiplicity
fixed to `1`) and the selector-dispatched BitVec semantic: under
operand bounds, the constraints hold iff the result equals one of the
five RV64 multiply variants (`mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`)
selected by the five `is_mul*` selector flags.

Forward direction reduces to the existing `spec.mul`/`spec.mulh`/
`spec.mulhu`/`spec.mulhsu`/`spec.mulw` per-selector forward specs. The
backward direction (constructing `carry`, `product`, byte-witnesses
from the BitVec equation) is left as `sorry` — it's a substantial
existence proof over the 16-limb multiply carry chain (~500–1000
LoC; the existence is implicit in `core_mul` but the direct
construction has not been performed).

The full proof requires `Fact (2 ^ 24 < p)` (per `spec.mul.*` lemmas)
to accommodate the 16-limb product range. -/
theorem iff_sp1_full {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    [Fact (2 ^ 24 < p)]
    {aw bw cw : Word (ZMod p)} {cols : MulOperation (ZMod p)}
    {is_mul is_mulh is_mulw is_mulhu is_mulhsu : ZMod p}
    (_h_isU64_bw : Word.isU64 bw) (_h_isU64_cw : Word.isU64 cw) :
    (MulOperation.constraints aw bw cw cols 1
        is_mul is_mulh is_mulw is_mulhu is_mulhsu).allHold ↔
      (Word.isU64 aw ∧
       ((is_mul    = 1 → Word.toBitVec64 aw = RV64.mul    (Word.toBitVec64 cw) (Word.toBitVec64 bw)) ∧
        (is_mulh   = 1 → Word.toBitVec64 aw = RV64.mulh   (Word.toBitVec64 cw) (Word.toBitVec64 bw)) ∧
        (is_mulhu  = 1 → Word.toBitVec64 aw = RV64.mulhu  (Word.toBitVec64 cw) (Word.toBitVec64 bw)) ∧
        (is_mulhsu = 1 → Word.toBitVec64 aw = RV64.mulhsu (Word.toBitVec64 cw) (Word.toBitVec64 bw)) ∧
        (is_mulw   = 1 → Word.toBitVec64 aw = RV64.mulw   (Word.toBitVec64 cw) (Word.toBitVec64 bw)))) := by
  -- Forward: dispatch on selector flags to apply spec.mul/mulh/mulhu/mulhsu/mulw.
  -- Backward: construct carry/product/byte-witness from the BitVec eq — TBD (sorry).
  sorry

end MulOperation
