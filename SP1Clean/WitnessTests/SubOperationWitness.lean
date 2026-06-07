import SP1Clean.WitnessTests.SubOperationWitnessVectors
import SP1Clean.Operations.SubOperation.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `SubOperation`.

Checks that `SubOperation.populate` — the native witness function the composing chip uses to assign
`value` — reproduces, at SP1's concrete field, the limbs SP1's real `SubOperation::populate` wrote on
every dumped vector. See `WitnessTests/WitnessConformance.lean` for the shared scaffolding. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native (field-generic) `populate`, instantiated at SP1's concrete
prime, reproduces the limbs SP1's real `populate` wrote. Compared via `.toList` (structural `BEq`). -/
def subWitnessConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 4) : Bool :=
  (SP1Clean.SubOperation.populate (toWord v.1) (toWord v.2.1)).toList == (toWord v.2.2).toList

/-- Build-checked: the native witness reproduces every dumped `SubOperation::populate` vector at
SP1's field. Corrupting any vector fails the build. -/
theorem subWitness_conforms :
    SubOperationWitnessVectors.all subWitnessConforms = true := by native_decide

end SP1Clean.WitnessTests
