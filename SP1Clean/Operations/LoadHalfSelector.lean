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

/-! # `LoadHalfSelector` sub-circuit

Half-word (16-bit) analogue of `LoadByteSelector`: selects one of 4 16-bit
limbs from `load_prev_value` (gated by `(offset_bit_1, offset_bit_0)` —
`offset_bit_2 = 0` for halfword-aligned loads), and `signed_extension_flag`
captures the MSB of the selected limb via U16MSB semantics when `is_unsigned = 0`.

## Status: Phase-1 "contract marker" form

Same Phase-1 design as `LoadMemoryAccessGated`: `main := pure ()` with the
faithful contract lifted into both `Assumptions` and `Spec`. The contract
mirrors `LoadHalfChip.SpecForIff_of_is_lh` lines 157-164, 222 / `_is_lhu`
lines 214-222. See `SP1Clean/Operations/LoadMemoryAccessGated.lean` for
the rationale and future-work pointers. -/

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

/-- The faithful half-word selection contract:
- 4-way limb selection via `(offset_bit_1, offset_bit_0)`
- U16MSB semantics on the selected limb when `is_unsigned = 0` (signed LH)
- forced `signed_extension_flag = 0` when `is_unsigned = 1` (unsigned LHU). -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  -- 4-way limb selection from (offset_bit_1, offset_bit_0); offset_bit_2 unused
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[0]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 1 ∨
    input.selected_limb = input.load_prev_value[1]) ∧
  (input.offset_bit_1 = 1 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[2]) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_0 = 0 ∨
    input.selected_limb = input.load_prev_value[3]) ∧
  -- U16MSB on selected_limb when signed (is_unsigned = 0): bounds + msb-iff
  (input.is_unsigned = 0 →
    input.selected_limb.val < 65536 ∧
    (input.signed_extension_flag = 0 ∨ input.signed_extension_flag = 1) ∧
    (input.signed_extension_flag = 1 ↔ (32768 : ZMod p) ≤ input.selected_limb)) ∧
  -- Unsigned: signed_extension_flag = 0 directly
  (input.is_unsigned = 1 → input.signed_extension_flag = 0)

def Assumptions (input : Inputs (ZMod p)) : Prop := Contract input
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

end SP1Clean.LoadHalfSelector
