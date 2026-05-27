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

/-! # `LoadByteSelector` sub-circuit

Wraps the per-row byte-selection equations SP1's LoadByte chip emits.
Four-way limb selection (gated by `(offset_bit_1, offset_bit_0)`), high/low
byte split of the selected limb, low-vs-high byte selection (gated by
`offset_bit_2`), and signed/unsigned extension flag determination.

## Status: Phase-1 "contract marker" form

Same Phase-1 design as `LoadMemoryAccessGated`: `main := pure ()` with the
faithful contract lifted into both `Assumptions` and `Spec`. The chip-level
`AssertionGated.soundness` derives the contract from the per-chip
`iff_sp1_of_*` bridge facts (`LoadByteChip.SpecForIff_of_is_lb` lines
251-268 / `_is_lbu` lines 318-332) and passes it back via `Assumptions`. -/

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

/-- The faithful byte-selection contract for LoadByte:
- 4-way limb selection via `(offset_bit_1, offset_bit_0)`
- byte split of the selected limb (low byte + high byte)
- byte selection within the limb gated by `offset_bit_2`
- `selected_byte < 256` (byte range)
- sign-extension flag boolean; for signed loads, the MSB iff
- for unsigned loads, `signed_extension_flag = 0` directly.

`is_unsigned ∈ {0, 1}` is enforced by the chip's external boolean gates;
the contract dispatches on it without re-asserting it. -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  -- 4-way limb selection: (offset_bit_1, offset_bit_0) picks one of 4 limbs
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[0]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[1]) ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[2]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[3]) ∧
  -- Byte split of the selected limb (low byte + high byte, both < 256)
  input.selected_limb_low_byte < (256 : ZMod p) ∧
  (input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹ <
    (256 : ZMod p) ∧
  -- Byte selection: offset_bit_2 picks high byte (1) vs low byte (0)
  input.selected_byte = input.offset_bit_2 *
      ((input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹) +
    (1 - input.offset_bit_2) * input.selected_limb_low_byte ∧
  input.selected_byte < (256 : ZMod p) ∧
  -- Sign-extension flag boolean
  (input.signed_extension_flag = 0 ∨ input.signed_extension_flag = 1) ∧
  -- Conditional semantics: unsigned forces flag=0; signed enforces MSB iff
  (input.is_unsigned = 1 → input.signed_extension_flag = 0) ∧
  (input.is_unsigned = 0 →
    (input.signed_extension_flag = 1 ↔ (128 : ZMod p) ≤ input.selected_byte))

/-- Phase-1 caller obligation: the chip composing this sub-circuit must
discharge the contract from its own `iff_sp1` bridge facts. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := Contract input

/-- Spec is the contract verbatim — soundness is a trivial copy from
`Assumptions`. -/
def Spec (input : Inputs (ZMod p)) : Prop := Contract input

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ h_assumptions _
  exact h_assumptions

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ _ _ _
  trivial

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadByteSelector
