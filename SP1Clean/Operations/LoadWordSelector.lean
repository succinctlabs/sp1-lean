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

**Status:** structural placeholder (AddwChip Phase-5 pattern):
`main := pure ()`, `Spec := True` marked `@[reducible]`. Faithful
contract (word-alignment, limb-pair selection, MSB sign-extension) is
a follow-up. -/

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

/-- Placeholder `Spec := True` (AddwChip Phase-5 pattern). Marked
`@[reducible]` so chip-level proofs auto-unfold. -/
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

end SP1Clean.LoadWordSelector
