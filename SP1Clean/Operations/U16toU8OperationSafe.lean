import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.U16toU8OperationSafe.U16toU8OperationSafe
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.U16toU8OperationUnsafe

/-! # `U16toU8OperationSafe` Clean mirror (scaffold)

SP1's `U16toU8OperationSafe` enforces the byte-range invariant on the
4-limb u16 → 8-byte decomposition that the Unsafe variant only
algebraically describes. The constraint list under `is_real = 1`:
```
[ .send (.byte U8Range 0 low_bytes[0] (u16_values[0]-low_bytes[0])/256) is_real
, .send (.byte U8Range 0 low_bytes[1] (u16_values[1]-low_bytes[1])/256) is_real
, .send (.byte U8Range 0 low_bytes[2] (u16_values[2]-low_bytes[2])/256) is_real
, .send (.byte U8Range 0 low_bytes[3] (u16_values[3]-low_bytes[3])/256) is_real ]
```
(opcode is `ByteOpcode.ofNat 3` = `U8Range`).

Rust nesting: `U16toU8OperationSafe::eval` composes
`U16toU8OperationUnsafe::eval` (for the algebraic decomposition) then
adds the 4 U8-range byte lookups. The Clean mirror does the same:
`Assertion.main` calls `U16toU8OpUnsafe.assertion` as a subcircuit and
then emits the 4 byte lookups. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.U16toU8OpSafe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input: the 4-limb u16 word + 4 low-byte
witnesses. Matches `U16toU8OpUnsafe.Inputs`. -/
structure Inputs (F : Type) where
  u16_values : fields 4 F
  low_bytes : fields 4 F
deriving ProvableStruct

/-- Clean-side circuit. Composes `U16toU8OpUnsafe.assertion` (the
algebraic decomposition, trivially empty) and emits the 4 U8-range byte
lookups for both low and high bytes of each u16 limb. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit: algebraic byte decomposition (Unsafe variant — no constraints).
  SP1Clean.U16toU8OpUnsafe.assertion
    (⟨input.u16_values, input.low_bytes⟩ : Var SP1Clean.U16toU8OpUnsafe.Inputs (ZMod p))
  -- 4 U8-range byte lookups (opcode 3 = U8Range).
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[0],
        (input.u16_values[0] - input.low_bytes[0]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[1],
        (input.u16_values[1] - input.low_bytes[1]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[2],
        (input.u16_values[2] - input.low_bytes[2]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[3],
        (input.u16_values[3] - input.low_bytes[3]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16toU8OpSafe"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: each `low_bytes[i].val < 256` AND
`((u16_values[i] - low_bytes[i]) * 256⁻¹).val < 256` (i.e., low and high
bytes of each u16 limb are both u8). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.low_bytes[0].val < 256 ∧
  ((input.u16_values[0] - input.low_bytes[0]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[1].val < 256 ∧
  ((input.u16_values[1] - input.low_bytes[1]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[2].val < 256 ∧
  ((input.u16_values[2] - input.low_bytes[2]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[3].val < 256 ∧
  ((input.u16_values[3] - input.low_bytes[3]) * (256 : ZMod p)⁻¹).val < 256

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- The full Clean `FormalAssertion` for `U16toU8OperationSafe`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: under `is_real = 1`, `Spec input` is equivalent to
SP1's `U16toU8OperationSafe.constraints` `allHold` form. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      List.Forall SP1Constraint.toProp
        (U16toU8OperationSafe.constraints input.u16_values
          { low_bytes := input.low_bytes } 1).2 := by
  sorry

end SP1Clean.U16toU8OpSafe
