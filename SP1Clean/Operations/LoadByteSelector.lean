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

/-! # `LoadByteSelector` sub-circuit (stubbed)

Wraps the per-row byte-selection equations SP1's LoadByte chip emits:
- `selected_limb = load_prev_value[i]` for the limb selected by
  `(offset_bit_1, offset_bit_0)` (four 2-way disjunctions, one per limb)
- `selected_limb_low_byte.val < 256` and
  `(selected_limb - selected_limb_low_byte) * 256⁻¹` is also `< 256`
  (byte split of the selected limb)
- `selected_byte = offset_bit_2 * high_byte + (1 - offset_bit_2) * low_byte`
- For signed loads only: `signed_extension_flag ∈ {0,1}` and
  `signed_extension_flag = 1 ↔ 128 ≤ selected_byte` via the MSB byte lookup
- For unsigned loads: `signed_extension_flag = 0`. Toggled by `is_unsigned`.

**Status:** structural stub. `main := pure ()`, `Spec` is real, `sorry` proofs. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadByteSelector

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  load_prev_value : Vector F 4
  offset_bit_2 : F
  offset_bit_1 : F
  offset_bit_0 : F
  selected_limb : F
  selected_limb_low_byte : F
  selected_byte : F
  signed_extension_flag : F
  is_unsigned : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LoadByteSelector"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[0]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[1]) ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[2]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[3]) ∧
  input.selected_limb_low_byte.val < 256 ∧
  ((input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.selected_byte = input.offset_bit_2 *
      ((input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹) +
    (1 - input.offset_bit_2) * input.selected_limb_low_byte ∧
  input.selected_byte.val < 256 ∧
  (input.signed_extension_flag = 0 ∨ input.signed_extension_flag = 1) ∧
  (input.is_unsigned = 1 → input.signed_extension_flag = 0) ∧
  (input.is_unsigned = 0 →
    (input.signed_extension_flag = 1 ↔ (128 : ZMod p) ≤ input.selected_byte))

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

end SP1Clean.LoadByteSelector
