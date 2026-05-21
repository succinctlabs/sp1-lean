import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.AddwOperation
import SP1Operations.Operation.U16MSBOperation
import SP1Clean.ByteOpcodeTable

/-! # `AddwOperation` gadget mirror — Assertion style

SP1's `AddwOperation` is a 2-limb carry-chain 32-bit add plus a
`U16MSBOperation` sub-fragment on the high result limb. The natural-form
iff lemma `AddwOperation.allHold_constraints_iff` exposes both: a
`List.Forall ... U16MSBOperation.constraints` clause on `(cols.value[1],
cols.msb)` plus the carry+limb-bound clauses for the two result limbs.
-/

namespace SP1Clean.AddwOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the 2-limb carry chain, byte-bounds each
result limb, and emits the `U16MSBOperation` sub-fragment for `value[1]`
with witnessed `msb`. -/
def main (a b : Vector (Expression (ZMod p)) 4)
    (result : Vector (Expression (ZMod p)) 2)
    (msb : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  let c0 := (a[0] + b[0] - result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - result[1] + c0) * (65536 : ZMod p)⁻¹
  c0 * (c0 - 1) === 0
  c1 * (c1 - 1) === 0
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

/-- Pilot Spec, mirroring `AddwOperation.allHold_constraints_iff` RHS
verbatim: a `U16MSBOperation` constraints clause plus 2 natural-form
carries are boolean plus each result limb fits in `< 65536`. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.AddwOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
  List.Forall SP1Constraint.toProp
      (_root_.U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } 1) ∧
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`AddwOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.AddwOperation (ZMod p)) :
    (_root_.AddwOperation.constraints a b cols 1).allHold ↔
      Spec a b cols :=
  _root_.AddwOperation.allHold_constraints_iff a b cols

end SP1Clean.AddwOp
