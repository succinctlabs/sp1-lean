import SP1Clean.Foundations.Word
import SP1Clean.Operations.IsZeroOperation.Populate
import SP1Clean.Extracted.IsZeroWordOperation

/-! # `IsZeroWordOperation` — `populate` (the witness generator)

SP1's `IsZeroWordOperation::populate` ported natively. `isZeroWordWitness` (vector form) is retained for
the conformance check in `WitnessTests/IsZeroWordOperationWitness.lean`. `spec_populate` lives in
`Formal` to avoid an import cycle. -/

namespace SP1Clean.IsZeroWordOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The witnessed column struct: per-limb `IsZeroOperation.populate`, the two half-products, and
`result = first_half * second_half`. -/
def populate (a : Word (ZMod p)) : Extracted.IsZeroWordOperation (ZMod p) :=
  let l0 := IsZeroOperation.populate a[0]
  let l1 := IsZeroOperation.populate a[1]
  let l2 := IsZeroOperation.populate a[2]
  let l3 := IsZeroOperation.populate a[3]
  let fh := l0.result * l1.result
  let sh := l2.result * l3.result
  ⟨l0, l1, l2, l3, fh, sh, fh * sh⟩

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (gated `IsZeroWord`/`IsEqualWord` composition on padding rows). `spec_zero`
(in `Formal`) discharges the composed assertion's obligation at this value. -/
def zeroCols : Extracted.IsZeroWordOperation (ZMod p) :=
  ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0, 0, 0⟩

/-- Vector form of the witness, used only for the conformance check in
`WitnessTests/IsZeroWordOperationWitness.lean`. Returns
`(limb inverses, limb results, first_half, second_half, result)`. -/
def isZeroWordWitness (a : Word (ZMod p)) :
    Vector (ZMod p) 4 × Vector (ZMod p) 4 × ZMod p × ZMod p × ZMod p :=
  let z0 := IsZeroOperation.isZeroWitness a[0]
  let z1 := IsZeroOperation.isZeroWitness a[1]
  let z2 := IsZeroOperation.isZeroWitness a[2]
  let z3 := IsZeroOperation.isZeroWitness a[3]
  let inv := #v[z0[0], z1[0], z2[0], z3[0]]
  let res := #v[z0[1], z1[1], z2[1], z3[1]]
  let fh := res[0] * res[1]
  let sh := res[2] * res[3]
  (inv, res, fh, sh, fh * sh)

end SP1Clean.IsZeroWordOperation
