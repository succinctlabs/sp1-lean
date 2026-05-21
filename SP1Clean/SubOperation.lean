import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Gadgets.Equality
import Clean.Utils.Field
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.SubOperation
import SP1Clean.ByteOpcodeTable

/-! # `SubOperation` gadget mirror — Assertion style

The borrow-chain twin of `SP1Clean.AddOperation`. SP1's `SubOperation` is a
4-limb borrow-chain 64-bit subtract; its auto-gen carries `d_i` are in
inverse/borrow form, while the natural-form iff lemma
`SubOperation.allHold_constraints_iff` re-phrases them as the
natural-form carries `c_i`.

The Clean-side `main` matches SP1's auto-gen RHS (borrow form) verbatim,
keeping the `iff_sp1` bridge a one-line re-export. The `Spec` uses the
natural-form carries so it reads symmetrically with `AddOp.Spec`.
-/

namespace SP1Clean.SubOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the borrow chain holds between the operand
limbs `a`, `b` and the result limbs `result`, and that each result limb
fits in `< 2^16`. The borrow expression matches SP1's auto-gen
`SubOperation.constraints` verbatim. -/
def main (a b result : Vector (Expression (ZMod p)) 4) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  let d2 := (a[2] + k65536 - k1 - b[2] - result[2] + d1) * (65536 : ZMod p)⁻¹
  let d3 := (a[3] + k65536 - k1 - b[3] - result[3] + d2) * (65536 : ZMod p)⁻¹
  d0 * (d0 - 1) === 0
  d1 * (d1 - 1) === 0
  d2 * (d2 - 1) === 0
  d3 * (d3 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[3], 16, 0] : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, mirroring `SubOperation.allHold_constraints_iff` RHS
verbatim: each of the 4 natural-form carries is boolean and each result
limb fits in `< 65536`. -/
def Spec (a b result : Word (ZMod p)) : Prop :=
  let carry0 : ZMod p := (b[0] + result[0] - a[0]) * 65536⁻¹
  let carry1 : ZMod p := (b[1] + result[1] - a[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (b[2] + result[2] - a[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (b[3] + result[3] - a[3] + carry2) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  (carry2 = 0 ∨ carry2 = 1) ∧
  (carry3 = 0 ∨ carry3 = 1) ∧
  result[0].val < 65536 ∧
  result[1].val < 65536 ∧
  result[2].val < 65536 ∧
  result[3].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`SubOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : SubOperation (ZMod p)) :
    (SubOperation.constraints a b cols 1).allHold ↔
      Spec a b cols.value :=
  SubOperation.allHold_constraints_iff a b cols

end SP1Clean.SubOp
