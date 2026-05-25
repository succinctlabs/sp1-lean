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

/-! # `StoreHalfAssembler` sub-circuit (placeholder)

For Store Half: replaces one 16-bit limb of `prev_value` with the
half-word being stored. `offset_bit_0` must be 0 (half-aligned).

**Status:** structural placeholder following the StoreByteAssembler /
AddwChip Phase-5 pattern (`main := pure ()`, `Spec := True`). The
faithful contract (`offset_bit_0 = 0`, `store_halfword < 65536`,
`Word.isU64 write_value`, and the 4 limb-selection conjuncts) is a
follow-up that adds the actual assertZero gates + byte lookups to `main`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreHalfAssembler

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  prev_value : Vector F 4
  write_value : Vector F 4
  store_halfword : F
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
  name := "SP1Clean.StoreHalfAssembler"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Placeholder `Spec := True`. The faithful half-selection contract
(`offset_bit_0 = 0`, `store_halfword < 65536`, `Word.isU64 write_value`,
4 limb-selection conjuncts) is left for a follow-up that strengthens
`main` to emit the byte lookups + limb-equality gates. Marked
`@[reducible]` so chip-level proofs auto-unfold to `True`. -/
@[reducible]
def Spec (_input : Inputs (ZMod p)) : Prop := True

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ _ _; trivial

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ _ _ _; trivial

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.StoreHalfAssembler
