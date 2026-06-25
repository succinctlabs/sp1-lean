import SP1CleanTest.WitnessTests.Vectors.IsZeroOperation
import SP1Clean.Native.Operations.IsZeroOperation.Populate
import SP1CleanTest.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `IsZeroOperation`.

Checks that `IsZeroOperation.isZeroWitness` — the native witness function `IsZeroOperation.main` uses
to assign the `inverse` and `result` columns — reproduces, at SP1's concrete field, the column values
SP1's real `IsZeroOperation::populate` wrote on every dumped vector.

This is the second **inverse-column** test (after `LtOperationUnsigned`): `inverse = a⁻¹` (off zero,
else `0`) is a genuine field element with no ℕ analogue, so it is checked against SP1's dumped
canonical value at SP1's actual prime (KoalaBear). The dumped `a_field` is the input residue SP1's
`populate` consumed (`from_canonical_u64`). See `WitnessTests/WitnessConformance.lean` for the shared
scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native (field-generic) `isZeroWitness`, instantiated at SP1's concrete
prime, reproduces the `(inverse, result)` columns SP1's real `populate` wrote. Compared via `.toList`
(structural `BEq`). -/
def isZeroConforms (v : ℕ × ℕ × ℕ) : Bool :=
  (IsZeroOperation.isZeroWitness (toField v.1)).toList == [toField v.2.1, toField v.2.2]

/-- Build-checked: the native witness — including the `a⁻¹` field inverse — reproduces every dumped
`IsZeroOperation::populate` vector at SP1's field. Corrupting any vector fails the build. -/
theorem isZero_conforms :
    IsZeroOperationWitnessVectors.all isZeroConforms = true := by native_decide

end SP1Clean.WitnessTests
