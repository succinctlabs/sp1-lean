import SP1Clean.Extracted.WitnessVectors.U16MSBOperation
import SP1Clean.Operations.U16MSBOperation.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `U16MSBOperation`.

Checks that `U16MSBOperation.populate_msb` — the native witness generator the composing gadget uses
to assign the `msb` column — reproduces, at SP1's concrete field, the bit SP1's real
`U16MSBOperation::populate_msb` wrote (`(a >> 15) & 1`) on every dumped u16 vector. See
`WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native `populate_msb`, at SP1's concrete prime, reproduces the `msb`
SP1's real `populate_msb` wrote for the dumped u16 operand. -/
def u16MSBConforms (v : ℕ × ℕ) : Bool :=
  U16MSBOperation.populate_msb (toField v.1) == toField v.2

/-- Build-checked: the native `populate_msb` reproduces every dumped `U16MSBOperation::populate_msb`
vector at SP1's field. Corrupting any vector fails the build. -/
theorem u16MSB_conforms :
    U16MSBOperationWitnessVectors.all u16MSBConforms = true := by native_decide

end SP1Clean.WitnessTests
