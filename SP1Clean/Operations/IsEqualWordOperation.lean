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
import SP1Operations.Compare.IsEqualWordOperation.IsEqualWordOperation
import SP1Clean.Operations.IsZeroWordOperation

/-! # `IsEqualWordOperation` Clean mirror (scaffold)

SP1's `IsEqualWordOperation` checks whether two 4-limb words are equal,
by delegating to `IsZeroWordOperation` on their elementwise difference.

Rust source: `SP1Operations/Compare/IsEqualWordOperation/Constraints.lean`.
Composes 1 `IsZeroWordOperation.constraints` call (on `a - b`) + 1
trailing `is_real * (is_real - 1) === 0` gate.

This wrapper faithfully composes `IsZeroWordOp.assertion` per the Rust
source. Proof bodies `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.IsEqualWordOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `IsEqualWordOperation<T>`:
the two compared words and the embedded `IsZeroWordOp`-cols
(`is_diff_zero` sub-struct). -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  is_zero_limb_inverse : fields 4 F
  is_zero_limb_result : fields 4 F
  is_zero_first_half : F
  is_zero_second_half : F
  result : F
deriving ProvableStruct

/-- Clean-side circuit. Composes `IsZeroWordOp.assertion` on `a - b`
(elementwise difference) per Rust nesting. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit: IsZeroWord on (a - b) elementwise.
  SP1Clean.IsZeroWordOp.assertion
    (⟨#v[input.a[0] - input.b[0], input.a[1] - input.b[1],
         input.a[2] - input.b[2], input.a[3] - input.b[3]],
       input.is_zero_limb_inverse, input.is_zero_limb_result,
       input.is_zero_first_half, input.is_zero_second_half,
       input.result⟩ : Var SP1Clean.IsZeroWordOp.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.IsEqualWordOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: composes the IsZeroWordOp Spec on the elementwise difference. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.IsZeroWordOp.Spec
    ⟨#v[input.a[0] - input.b[0], input.a[1] - input.b[1],
        input.a[2] - input.b[2], input.a[3] - input.b[3]],
     input.is_zero_limb_inverse, input.is_zero_limb_result,
     input.is_zero_first_half, input.is_zero_second_half,
     input.result⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- The full Clean `FormalAssertion` for `IsEqualWordOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: under `is_real = 1`, `Spec input` is equivalent to
SP1's `IsEqualWordOperation.constraints` `allHold`. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (IsEqualWordOperation.constraints input.a input.b
        { is_diff_zero := {
            is_zero_limb := #v[
              ⟨input.is_zero_limb_inverse[0], input.is_zero_limb_result[0]⟩,
              ⟨input.is_zero_limb_inverse[1], input.is_zero_limb_result[1]⟩,
              ⟨input.is_zero_limb_inverse[2], input.is_zero_limb_result[2]⟩,
              ⟨input.is_zero_limb_inverse[3], input.is_zero_limb_result[3]⟩],
            is_zero_first_half := input.is_zero_first_half,
            is_zero_second_half := input.is_zero_second_half,
            result := input.result } } 1).allHold := by
  sorry

end SP1Clean.IsEqualWordOp
