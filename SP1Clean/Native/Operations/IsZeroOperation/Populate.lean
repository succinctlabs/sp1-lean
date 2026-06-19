import SP1Clean.Math.Word
import SP1Clean.Extracted.IsZeroOperation

/-! # `IsZeroOperation` — `populate` (the witness generator)

SP1's `IsZeroOperation::populate` ported natively. `isZeroWitness` (vector form) is retained for the
conformance check in `WitnessTests/IsZeroOperationWitness.lean`. `spec_populate` lives in `Formal` to
avoid an import cycle through the composing ops. -/

namespace SP1Clean.IsZeroOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native port of SP1's `IsZeroOperation::populate`: `#v[inverse, result]`.
On `a = 0`, returns `[0, 1]`; on `a ≠ 0`, returns `[a⁻¹, 0]`. -/
def isZeroWitness (a : ZMod p) : Vector (ZMod p) 2 :=
  if a = 0 then #v[0, 1] else #v[a⁻¹, 0]

/-- The witnessed column struct `⟨inverse, result⟩` — `isZeroWitness` packaged as the extracted
`IsZeroOperation` columns the composing op threads in. -/
def populate (a : ZMod p) : Extracted.IsZeroOperation (ZMod p) :=
  if a = 0 then ⟨0, 1⟩ else ⟨a⁻¹, 0⟩

end SP1Clean.IsZeroOperation
