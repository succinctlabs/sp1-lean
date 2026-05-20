import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.SubwOperation
import SP1Operations.Operation.U16MSBOperation
import SP1Clean.ByteOpcodeTable

/-! # `SubwOperation` gadget mirror — Assertion style

SP1's `SubwOperation` is a 2-limb borrow-chain 32-bit subtract plus a
`U16MSBOperation` sub-fragment that pins the msb of the second result limb.
The natural-form iff lemma `SubwOperation.allHold_constraints_iff_poly`
exposes both: a `List.Forall ... U16MSBOperation.constraints` clause on
`(cols.value[1], cols.msb)` plus the carry+limb-bound clauses for the two
result limbs.

The Clean mirror keeps the same shape: `main` emits the borrow-form
asserts, the two Range(16) lookups, and inlines the `U16MSBOperation`
constraints — `iff_sp1` is then a one-line re-export of the SP1 lemma.
-/

namespace SP1Clean.SubwOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the 2-limb borrow chain, byte-bounds each
result limb, and emits the `U16MSBOperation` sub-fragment for `value[1]`
with witnessed `msb`. -/
def main (a b : Vector (Expression (ZMod p)) 4)
    (result : Vector (Expression (ZMod p)) 2)
    (msb : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  d0 * (d0 - 1) === 0
  d1 * (d1 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  -- U16MSBOperation sub-fragment on `result[1]` with witness `msb`.
  msb * (msb - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)),
        (2 : Expression (ZMod p)) * result[1] - msb * 65536, 16, 0]
      : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, mirroring `SubwOperation.allHold_constraints_iff_poly` RHS
verbatim: a `U16MSBOperation` constraints clause plus 2 natural-form
carries are boolean plus each result limb fits in `< 65536`. The
U16MSBOperation clause is left as `List.Forall ...` (matching the SP1
lemma) — promoting to the `SP1Clean.U16MSBOp.Spec` form is a follow-up. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.SubwOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
  let carry1 : ZMod p := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
  List.Forall SP1Constraint.toProp_poly
      (_root_.U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } 1) ∧
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536

/-- The bridge to SP1: SP1's `allHold_poly` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`SubwOperation.allHold_constraints_iff_poly`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.SubwOperation (ZMod p)) :
    (_root_.SubwOperation.constraints a b cols 1).allHold_poly ↔
      Spec a b cols :=
  _root_.SubwOperation.allHold_constraints_iff_poly a b cols

end SP1Clean.SubwOp
