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

/-! # `StoreWordAssembler` sub-circuit (placeholder)

For Store Word: replaces 2 adjacent 16-bit limbs of `prev_value` with
the 32-bit word being stored. `offset_bit_0` and `offset_bit_1` must
both be 0 (word-aligned).

**Status:** structural placeholder following the StoreByteAssembler /
AddwChip Phase-5 pattern (`main := pure ()`, `Spec := True`). The
faithful contract (alignment, `store_{low,high} < 65536`,
`Word.isU64 write_value`, and the 2 limb-pair selection conjuncts) is
a follow-up that emits the actual gates in `main`. -/

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

/-- Placeholder `Spec := True`. The faithful word-selection contract
(word alignment, byte bounds, `Word.isU64 write_value`, and the 2
limb-pair selection conjuncts) is left for a follow-up. Marked
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

end SP1Clean.StoreWordAssembler
