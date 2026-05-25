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

/-! # `StoreByteAssembler` sub-circuit (stubbed)

For Store Byte: assembles the new 64-bit memory word `write_value` from
the existing `prev_value` (3 unchanged limbs) and the inserted single
byte at the position selected by the offset bits.

`store_byte` is `op_a_value[0]`'s low byte for SP1's StoreByte. The
selected limb (one of 4 in `write_value`) is constructed by replacing
the appropriate half (low or high byte, gated by `offset_bit_2`) of the
corresponding `prev_value` limb with `store_byte`.

**Status:** structural stub. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreByteAssembler

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  prev_value : Vector F 4
  write_value : Vector F 4
  store_byte : F
  prev_byte : F
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
  name := "SP1Clean.StoreByteAssembler"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  input.store_byte.val < 256 ∧
  input.prev_byte.val < 256 ∧
  Word.isU64 input.write_value ∧
  -- The 3 limbs not selected by (offset_bit_1, offset_bit_0) are unchanged.
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 1 ∨
    -- limb 0 is the active limb; limbs 1,2,3 unchanged
    (input.write_value[1] = input.prev_value[1] ∧
     input.write_value[2] = input.prev_value[2] ∧
     input.write_value[3] = input.prev_value[3])) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 1 ∨
    (input.write_value[0] = input.prev_value[0] ∧
     input.write_value[2] = input.prev_value[2] ∧
     input.write_value[3] = input.prev_value[3])) ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 0 ∨
    (input.write_value[0] = input.prev_value[0] ∧
     input.write_value[1] = input.prev_value[1] ∧
     input.write_value[3] = input.prev_value[3])) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 0 ∨
    (input.write_value[0] = input.prev_value[0] ∧
     input.write_value[1] = input.prev_value[1] ∧
     input.write_value[2] = input.prev_value[2]))

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

end SP1Clean.StoreByteAssembler
