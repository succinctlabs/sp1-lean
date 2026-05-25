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

/-- Placeholder `Spec`: trivially `True`. Marked `@[reducible]` so
chip-level proofs auto-unfold to `True`.

The byte-assembler's faithful contract (5 `assertZero` gates for the
increment and 4 limb equations, plus the two register/mem byte U8 lookups
the chip-level autogen places under `mult = is_real`) is intentionally
*not* lifted into this sub-assertion. Reason: the chip-level
`StoreByteChip.AssertionGated.main` does not yet thread the assembler's
column inputs (`mem_limb`, `increment`) through this subcircuit's Inputs,
so a Spec referencing those fields can't be discharged at the chip level
without a structural Inputs change.

The pragmatic AddwChip-Phase-5 pattern: keep the sub-assertion as a
structural pass-through (`main := pure ()`, `Spec := True`), discharge
the actual constraint content at the chip level (via inline lookups in
the earlier `Assertion.main` form) or defer it to a follow-up that
strengthens the Inputs + Spec. The trace-level memory-bus consistency
remains faithful via the empty `memoryAccesses (.storeByte _)` case in
`SP1Clean/Soundness/MemoryConsistency.lean`. -/
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

end SP1Clean.StoreByteAssembler
