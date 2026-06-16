import SP1Clean.Math.Word
import SP1Clean.Operations.IsZeroWordOperation.Populate
import SP1Clean.Extracted.IsEqualWordOperation

/-! # `IsEqualWordOperation` — `populate` (the witness generator)

SP1's `IsEqualWordOperation::populate` ported natively: runs `IsZeroWordOperation.populate` on the
limb-wise difference `a - b` and packages the `IsEqualWordOperation` column struct (a single
`is_diff_zero` field). The composing chip witnesses the columns with this. `spec_populate` lives in
`Formal` (it references `Spec`, which also lives there to avoid an import cycle). -/

namespace SP1Clean.IsEqualWordOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The witnessed column struct: `IsZeroWordOperation.populate` on the limb-wise difference `a - b`. -/
def populate (a b : Word (ZMod p)) : Extracted.IsEqualWordOperation (ZMod p) :=
  ⟨IsZeroWordOperation.populate #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]⟩

end SP1Clean.IsEqualWordOperation
