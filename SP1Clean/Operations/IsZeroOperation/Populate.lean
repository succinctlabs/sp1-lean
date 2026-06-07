import SP1Clean.Foundations.Word
import SP1Clean.Extracted.IsZeroOperation

/-! # `IsZeroOperation` — `populate` (the witness generator)

SP1's `IsZeroOperation::populate` ported natively: the witnessed columns `⟨inverse, result⟩`. On
`a = 0`, `inverse = 0` and `result = 1`; otherwise `inverse = a⁻¹` and `result = 0`. The composing
word-level op witnesses the whole nested column struct with this (the gadget itself is a pure
assertion). `isZeroWitness` (the `Vector` form) is retained for the conformance check in
`WitnessTests/IsZeroOperationWitness.lean`; `spec_populate` (the result satisfies the gadget `Spec`) lives
in `Formal` (it references `Spec`, which — to avoid an import cycle through the composing ops — also
lives in `Formal`). -/

namespace SP1Clean.IsZeroOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness function ported from SP1's `IsZeroOperation::populate`: returns the two witnessed
columns `#v[inverse, result]`. On `a = 0`, `inverse = 0` and `result = 1`; otherwise `inverse = a⁻¹`
and `result = 0`. -/
def isZeroWitness (a : ZMod p) : Vector (ZMod p) 2 :=
  if a = 0 then #v[0, 1] else #v[a⁻¹, 0]

/-- The witnessed column struct `⟨inverse, result⟩` — `isZeroWitness` packaged as the extracted
`IsZeroOperation` columns the composing op threads in. -/
def populate (a : ZMod p) : Extracted.IsZeroOperation (ZMod p) :=
  if a = 0 then ⟨0, 1⟩ else ⟨a⁻¹, 0⟩

end SP1Clean.IsZeroOperation
