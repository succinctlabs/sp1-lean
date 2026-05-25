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

/-! # `StoreWordAssembler` sub-circuit (stubbed)

For Store Word: replaces 2 adjacent 16-bit limbs of `prev_value` with
the 32-bit word being stored. `offset_bit_0` and `offset_bit_1` must
both be 0 (word-aligned).

**Status:** structural stub. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreWordAssembler

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  prev_value : Vector F 4
  write_value : Vector F 4
  store_low : F
  store_high : F
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
  name := "SP1Clean.StoreWordAssembler"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  input.offset_bit_0 = 0 ∧
  input.offset_bit_1 = 0 ∧
  input.store_low.val < 65536 ∧
  input.store_high.val < 65536 ∧
  Word.isU64 input.write_value ∧
  -- offset_bit_2 = 0 → write to limbs 0,1; offset_bit_2 = 1 → write to limbs 2,3
  (input.offset_bit_2 = 1 ∨
    (input.write_value[0] = input.store_low ∧
     input.write_value[1] = input.store_high ∧
     input.write_value[2] = input.prev_value[2] ∧
     input.write_value[3] = input.prev_value[3])) ∧
  (input.offset_bit_2 = 0 ∨
    (input.write_value[0] = input.prev_value[0] ∧
     input.write_value[1] = input.prev_value[1] ∧
     input.write_value[2] = input.store_low ∧
     input.write_value[3] = input.store_high))

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

end SP1Clean.StoreWordAssembler
