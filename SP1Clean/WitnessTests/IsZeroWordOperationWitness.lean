import SP1Clean.WitnessTests.IsZeroWordOperationWitnessVectors
import SP1Clean.Operations.IsZeroWordOperation.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `IsZeroWordOperation`.

Checks that `IsZeroWordOperation.isZeroWordWitness` — which composes the per-limb
`IsZeroOperation.isZeroWitness` the gadget routes through four `IsZeroOperation.circuit` subcircuits —
reproduces, at SP1's concrete field, the columns SP1's real `IsZeroWordOperation::populate` wrote on
every dumped vector: the four per-limb `inverse`/`result` columns, the two half-products, and the
final `result`.

The four per-limb inverses are genuine field elements with no ℕ analogue (the IsZero inverse trick),
so the check lives at SP1's concrete prime (KoalaBear). See `WitnessTests/WitnessConformance.lean` for the
shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff `isZeroWordWitness`, at SP1's concrete prime, reproduces all eight per-limb
columns (4 inverses + 4 results), both half-products, and the final result that SP1's real `populate`
wrote. Limb vectors compared via `.toList` (structural `BEq`); scalars via field `==`. -/
def isZeroWordConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 4 × ℕ × ℕ × ℕ) : Bool :=
  let a := toWord v.1
  let (inv, res, fh, sh, r) := IsZeroWordOperation.isZeroWordWitness a
  inv.toList == (toFieldVec v.2.1).toList &&
  res.toList == (toFieldVec v.2.2.1).toList &&
  fh == toField v.2.2.2.1 &&
  sh == toField v.2.2.2.2.1 &&
  r == toField v.2.2.2.2.2

/-- Build-checked: the native witness — including the four `a[i]⁻¹` field inverses — reproduces every
dumped `IsZeroWordOperation::populate` vector at SP1's field. Corrupting any vector fails the build. -/
theorem isZeroWord_conforms :
    IsZeroWordOperationWitnessVectors.all isZeroWordConforms = true := by native_decide

end SP1Clean.WitnessTests
