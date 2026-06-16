import SP1Clean.Extracted.WitnessVectors.SubwOperation
import SP1Clean.Operations.SubwOperation.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `SubwOperation`.

Checks that the native witness functions `SubwOperation.{subwValueWitness, subwMsbWitness}` — the ones
`SubwOperation.main` uses to assign the low-two `value` limbs and (via the nested `U16MSBOperation`
subcircuit) the `msb` column — reproduce, at SP1's concrete field, the columns SP1's real
`SubwOperation::populate` wrote on every dumped vector. Both columns are genuinely computed
(`value` = limbs of `(a-b) mod 2^32`; `msb` = bit 15 of `value[1]`), not passthroughs. See
`WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native witnesses, at SP1's concrete prime, reproduce the low-two
`value` limbs and the `msb` sign bit SP1's real `populate` wrote. -/
def subwConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 2 × ℕ) : Bool :=
  let a := toWord v.1
  let b := toWord v.2.1
  (SubwOperation.subwValueWitness a b).toList == (toFieldVec v.2.2.1).toList &&
  SubwOperation.subwMsbWitness a b == toField v.2.2.2

/-- Build-checked: the native witnesses reproduce every dumped `SubwOperation::populate` vector at
SP1's field. Corrupting any vector fails the build. -/
theorem subw_conforms :
    SubwOperationWitnessVectors.all subwConforms = true := by native_decide

end SP1Clean.WitnessTests
