import SP1CleanTest.WitnessTests.Vectors.U16CompareOperation
import SP1Clean.Native.Operations.U16CompareOperation.Populate
import SP1CleanTest.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `U16CompareOperation`.

Checks that `U16CompareOperation.populate_bit` — the native witness generator that computes the
`b < c` comparison bit the composing gadget assigns to `bit` — reproduces, at SP1's concrete field,
the bit SP1's real `U16CompareOperation::populate` stored on every dumped u16 pair. SP1's `populate`
echoes the result bit it is fed (`a = (b < c)`); the dumper passes that true comparison, so the
conformance check is that the native recomputation `populate_bit b c` agrees. See
`WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native `populate_bit`, at SP1's concrete prime, reproduces the `bit`
(the `b < c` flag) SP1's real `populate` stored for the dumped u16 pair `(b, c)`. -/
def u16CompareConforms (v : ℕ × ℕ × ℕ) : Bool :=
  U16CompareOperation.populate_bit (toField v.1) (toField v.2.1) == toField v.2.2

/-- Build-checked: the native `populate_bit` reproduces every dumped `U16CompareOperation::populate`
vector at SP1's field. Corrupting any vector fails the build. -/
theorem u16Compare_conforms :
    U16CompareOperationWitnessVectors.all u16CompareConforms = true := by native_decide

end SP1Clean.WitnessTests
