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
import SP1Clean.ByteOpcodeTable

/-! # `AddressShape` sub-circuit (stubbed) — shared by Load and Store chips

Wraps the constraints SP1's `AddressOperation` emits beyond the inner
`AddrAddOp` carry chain:
- `offset_bit_2`, `offset_bit_1`, `offset_bit_0` are each in `{0, 1}`
- `top_two_limb_inv * (addr[1] + addr[2]) = 1`
  (forces the upper two limbs of the 3-limb address to be zero whenever
  the address falls below 2^16, with `top_two_limb_inv` the inverse witness)
- `((addr[0] - 4 * offset_bit_0 - 2 * offset_bit_1 - offset_bit_2) * 8⁻¹).val < 2 ^ 13`
  (low-limb bit decomposition: `addr[0] mod 8` equals the 3-bit offset value)

This is the "address shape" portion that sits alongside `AddrAddOp.assertion`
inside SP1's `AddressOperation.constraints`. Load and Store chips compose
both as sub-circuits.

**Status:** structural stub. `main := pure ()`, `Spec` is the real contract,
proofs are `sorry`. Future work: emit the boolean gates / bit-decomp lookup
in `main` and discharge soundness/completeness. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.AddressShape

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled input: the 3-limb address, the inverse witness for the
upper-two-limb-zero check, and the 3 offset bits. -/
structure Inputs (F : Type) where
  addr : Vector F 3
  top_two_limb_inv : F
  offset_bit_2 : F
  offset_bit_1 : F
  offset_bit_0 : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddressShape"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Per-row spec: the 4 facts SP1 surfaces alongside the AddrAddOp carry
chain inside `AddressOperation.constraints`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.offset_bit_2 = 0 ∨ input.offset_bit_2 = 1) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_1 = 1) ∧
  (input.offset_bit_0 = 0 ∨ input.offset_bit_0 = 1) ∧
  input.top_two_limb_inv * (input.addr[1] + input.addr[2]) = 1 ∧
  ((input.addr[0] - 4 * input.offset_bit_0 - 2 * input.offset_bit_1
        - input.offset_bit_2) * (8 : ZMod p)⁻¹).val
    < 2 ^ ZMod.val (13 : ZMod p)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.AddressShape
