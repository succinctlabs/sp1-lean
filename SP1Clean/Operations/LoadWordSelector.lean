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

/-! # `LoadWordSelector` sub-circuit (stubbed)

Word (32-bit) analogue of `LoadByteSelector`. Selects 2 adjacent 16-bit
limbs from `load_prev_value` (gated by `offset_bit_2`); `offset_bit_0`
and `offset_bit_1` are constrained to 0 (word-aligned loads).
`signed_extension_flag` captures the high-byte MSB when `is_unsigned = 0`.

**Status:** structural stub. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadWordSelector

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  load_prev_value : Vector F 4
  offset_bit_2 : F
  offset_bit_1 : F
  offset_bit_0 : F
  selected_low : F
  selected_high : F
  signed_extension_flag : F
  is_unsigned : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LoadWordSelector"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  input.offset_bit_0 = 0 ∧
  input.offset_bit_1 = 0 ∧
  (input.offset_bit_2 = 1 ∨
    (input.selected_low = input.load_prev_value[0] ∧
     input.selected_high = input.load_prev_value[1])) ∧
  (input.offset_bit_2 = 0 ∨
    (input.selected_low = input.load_prev_value[2] ∧
     input.selected_high = input.load_prev_value[3])) ∧
  input.selected_low.val < 65536 ∧
  input.selected_high.val < 65536 ∧
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

end SP1Clean.LoadWordSelector
