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

**Status:** structural placeholder (AddwChip Phase-5 pattern):
`main := pure ()`, `Spec := True` marked `@[reducible]`. The faithful
contract (limb selection, byte split bounds, signed-extension flag) is
a follow-up that adds gated byte lookups + assertZero gates to `main`. -/

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

/-- Placeholder `Spec := True` (AddwChip Phase-5 pattern). Faithful
contract — limb selection, byte split bounds, signed-extension flag —
is left for a follow-up. Marked `@[reducible]` so chip-level proofs
auto-unfold to `True`. -/
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

end SP1Clean.LoadByteSelector
