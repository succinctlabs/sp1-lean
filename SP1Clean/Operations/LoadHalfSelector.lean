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
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable

/-! # `LoadHalfSelector` sub-circuit (stubbed)

Half-word (16-bit) analogue of `LoadByteSelector`: selects one of 4 16-bit
limbs from `load_prev_value` (gated by `offset_bit_1`) — `offset_bit_0`
is constrained to 0 (halfword-aligned loads), and `signed_extension_flag`
captures the MSB of the selected limb when `is_unsigned = 0`.

**Status:** structural stub. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadHalfSelector

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  load_prev_value : Vector F 4
  offset_bit_2 : F
  offset_bit_1 : F
  offset_bit_0 : F
  selected_limb : F
  signed_extension_flag : F
  is_unsigned : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LoadHalfSelector"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  input.offset_bit_0 = 0 ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_2 = 1 ∨
    input.selected_limb = input.load_prev_value[0]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_2 = 1 ∨
    input.selected_limb = input.load_prev_value[1]) ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_2 = 0 ∨
    input.selected_limb = input.load_prev_value[2]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_2 = 0 ∨
    input.selected_limb = input.load_prev_value[3]) ∧
  input.selected_limb.val < 65536 ∧
  (input.signed_extension_flag = 0 ∨ input.signed_extension_flag = 1) ∧
  (input.is_unsigned = 1 → input.signed_extension_flag = 0)

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

end SP1Clean.LoadHalfSelector
