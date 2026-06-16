import SP1Clean.Extracted.WitnessVectors.IsEqualWordOperation
import SP1Clean.Native.Operations.IsEqualWordOperation.Populate
import SP1Clean.Proofs.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `IsEqualWordOperation`.

Checks that `IsEqualWordOperation.populate` — which runs the nested `IsZeroWordOperation.populate` on
the per-limb field differences `a[i] - b[i]` — reproduces, at SP1's concrete field, the `is_diff_zero`
columns SP1's real `IsEqualWordOperation::populate` wrote on every dumped pair: the four per-limb
`inverse`/`result` columns, the two half-products, and the final `result`. The per-limb inverses are
genuine field elements with no ℕ analogue (the IsZero inverse trick), so the check lives at SP1's
concrete prime (KoalaBear). Vectors include equal pairs (`result = 1`) and single-limb-difference
pairs. See `WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native `populate`'s `is_diff_zero` block, at SP1's concrete prime,
reproduces all eight per-limb columns (4 inverses + 4 results), both half-products, and the final
result SP1's real `populate` wrote for the dumped operand pair. Limb vectors compared via `.toList`
(structural `BEq`); scalars via field `==`. -/
def isEqualWordConforms
    (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 4 × ℕ × ℕ × ℕ) : Bool :=
  let z := (SP1Clean.IsEqualWordOperation.populate (toWord v.1) (toWord v.2.1)).is_diff_zero
  #v[z.is_zero_limb_0.inverse, z.is_zero_limb_1.inverse,
     z.is_zero_limb_2.inverse, z.is_zero_limb_3.inverse].toList == (toFieldVec v.2.2.1).toList &&
  #v[z.is_zero_limb_0.result, z.is_zero_limb_1.result,
     z.is_zero_limb_2.result, z.is_zero_limb_3.result].toList == (toFieldVec v.2.2.2.1).toList &&
  z.is_zero_first_half == toField v.2.2.2.2.1 &&
  z.is_zero_second_half == toField v.2.2.2.2.2.1 &&
  z.result == toField v.2.2.2.2.2.2

/-- Build-checked: the native `populate` — including the four per-limb-difference field inverses —
reproduces every dumped `IsEqualWordOperation::populate` vector at SP1's field. Corrupting any vector
fails the build. -/
theorem isEqualWord_conforms :
    IsEqualWordOperationWitnessVectors.all isEqualWordConforms = true := by native_decide

end SP1Clean.WitnessTests
