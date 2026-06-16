import SP1Clean.Extracted.WitnessVectors.AddOperation
import SP1Clean.Operations.AddOperation.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `AddOperation`.

Checks that `AddOperation.populate` — the native witness generator the composing chip uses to assign
`value` — reproduces, at SP1's concrete field, the limbs SP1's real `AddOperation::populate` wrote on
every dumped vector. See `WitnessTests/WitnessConformance.lean` for the shared scaffolding and the
rationale (conformance vs. all-inputs proof; why the check lives at the concrete prime). -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native (field-generic) `populate`, instantiated at SP1's concrete
prime, reproduces the limbs SP1's real `populate` wrote. Compared via `.toList` (structural `BEq`). -/
def populateConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 4) : Bool :=
  (SP1Clean.AddOperation.populate (toWord v.1) (toWord v.2.1)).toList == (toWord v.2.2).toList

/-- Build-checked: the native `populate` reproduces every dumped `AddOperation::populate` vector at
SP1's field. Corrupting any vector fails the build. -/
theorem populate_conforms :
    AddOperationWitnessVectors.all populateConforms = true := by native_decide

end SP1Clean.WitnessTests
