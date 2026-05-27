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

/-! # `LoadWordSelector` sub-circuit

Word (32-bit) analogue of `LoadByteSelector`. Selects 2 adjacent 16-bit
limbs from `load_prev_value` (gated by `offset_bit_2` — `offset_bit_0` and
`offset_bit_1` are constrained to 0 for word-aligned loads).
`signed_extension_flag` captures the U16MSB of the high limb when
`is_unsigned = 0`.

The chip wires `offset_bit_2` as the LoadWord selector — the convention
matches `Spec.lean:954-957`: `⟨..., cols.offset_bit, 0, 0, ...⟩`, where
the first positional field is `offset_bit_2`.

## Status: Phase-1 "contract marker" form

Same Phase-1 design as `LoadMemoryAccessGated`: `main := pure ()` with the
faithful contract lifted into both `Assumptions` and `Spec`. The contract
mirrors `LoadWordChip.SpecForIff_of_is_lw` lines 156-159, 210 / `_is_lwu`
lines 206-210. -/

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

/-- The faithful word selection contract:
- 2-way limb-pair selection via `offset_bit_2` (low pair vs high pair)
- U16MSB on the selected high limb when signed (`is_unsigned = 0`)
- forced `signed_extension_flag = 0` when unsigned (`is_unsigned = 1`). -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  -- 2-way limb-pair selection (offset_bit_2 selects between [0..2] and [2..4])
  (input.offset_bit_2 = 1 ∨ input.selected_low = input.load_prev_value[0]) ∧
  (input.offset_bit_2 = 1 ∨ input.selected_high = input.load_prev_value[1]) ∧
  (input.offset_bit_2 = 0 ∨ input.selected_low = input.load_prev_value[2]) ∧
  (input.offset_bit_2 = 0 ∨ input.selected_high = input.load_prev_value[3]) ∧
  -- U16MSB on the selected high limb when signed (is_unsigned = 0)
  (input.is_unsigned = 0 →
    input.selected_high.val < 65536 ∧
    (input.signed_extension_flag = 0 ∨ input.signed_extension_flag = 1) ∧
    (input.signed_extension_flag = 1 ↔ (32768 : ZMod p) ≤ input.selected_high)) ∧
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

end SP1Clean.LoadWordSelector
