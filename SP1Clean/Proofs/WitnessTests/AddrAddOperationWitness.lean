import SP1Clean.Extracted.WitnessVectors.AddrAddOperation
import SP1Clean.Native.Operations.AddrAddOperation.Populate
import SP1Clean.Proofs.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `AddrAddOperation`.

Checks that `AddrAddOperation.populate` — the native witness generator the composing gadget uses to
assign the three-limb u48 `value` column — reproduces, at SP1's concrete field, the limbs SP1's real
`AddrAddOperation::populate` wrote on every dumped vector. The vectors are sampled over `< 2^47`
address operands (SP1's `populate` `assert!`s the sum fits in 48 bits). See
`WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native `populate`, at SP1's concrete prime, reproduces the three
u48-address limbs SP1's real `populate` wrote. Compared via `.toList` (structural `BEq`). -/
def addrAddConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 3) : Bool :=
  (SP1Clean.AddrAddOperation.populate (toWord v.1) (toWord v.2.1)).toList
    == (toFieldVec v.2.2).toList

/-- Build-checked: the native `populate` reproduces every dumped `AddrAddOperation::populate` vector
at SP1's field. Corrupting any vector fails the build. -/
theorem addrAdd_conforms :
    AddrAddOperationWitnessVectors.all addrAddConforms = true := by native_decide

end SP1Clean.WitnessTests
