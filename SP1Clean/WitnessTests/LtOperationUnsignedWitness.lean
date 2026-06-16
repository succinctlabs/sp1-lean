import SP1Clean.Extracted.WitnessVectors.LtOperationUnsigned
import SP1Clean.Operations.LtOperationUnsigned.Populate
import SP1Clean.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `LtOperationUnsigned`.

Checks that the native witness functions `LtOperationUnsigned.{comparisonLimbsWitness, flagsWitness,
notEqInvWitness}` — the ones `LtOperationUnsigned.main` uses to assign the `comparison_limbs`,
`u16_flags`, and `not_eq_inv` columns — reproduce, at SP1's concrete field, the column values SP1's
real `LtOperationUnsigned::populate_unsigned` wrote on every dumped vector.

This is the **inverse-column** test: `not_eq_inv = (b_limb - c_limb)⁻¹` is a genuine field element
with no ℕ analogue, so it can only be checked against SP1's dumped canonical value at SP1's actual
prime (KoalaBear) — exactly what the uniform-`ZMod p`-witness design buys us. See
`WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff all three native witness functions (comparison limbs, one-hot flags, and
the `(b-c)⁻¹` inverse column), instantiated at SP1's concrete prime, reproduce what the real
`populate_unsigned` wrote. Compared via `.toList` (structural `BEq`). -/
def ltUnsignedConforms (v : Vector ℕ 4 × Vector ℕ 4 × Vector ℕ 2 × Vector ℕ 4 × ℕ) : Bool :=
  let b := toWord v.1
  let cc := toWord v.2.1
  (LtOperationUnsigned.comparisonLimbsWitness b cc).toList == (toFieldVec v.2.2.1).toList &&
  (LtOperationUnsigned.flagsWitness b cc).toList == (toFieldVec v.2.2.2.1).toList &&
  (LtOperationUnsigned.notEqInvWitness b cc).toList == [toField v.2.2.2.2]

/-- Build-checked: the native witnesses — including the `(b-c)⁻¹` field inverse — reproduce every
dumped `populate_unsigned` vector at SP1's field. Corrupting any vector fails the build. -/
theorem ltUnsigned_conforms :
    LtOperationUnsignedWitnessVectors.all ltUnsignedConforms = true := by native_decide

end SP1Clean.WitnessTests
