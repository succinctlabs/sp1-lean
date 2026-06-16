import SP1Clean.Math.Word
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Operations.U16CompareOperation.Populate

/-! # `LtOperationUnsigned` — native witness generation

SP1's `LtOperationUnsigned::populate_unsigned` ported to Lean: the one-hot `u16_flags`, the
`comparison_limbs`, and the non-equality inverse `not_eq_inv` at the most-significant differing limb
(all-equal ⇒ zero), plus the composed `U16CompareOperation` bit on the selected limb pair. A composing
circuit (`LtOperationSigned`) witnesses the whole block with `populate`; `spec_populate` (that the
witness satisfies the gadget `Spec`) lives in `Formal.lean`. -/

namespace SP1Clean.LtOperationUnsigned

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness for the `comparison_limbs` column, **field-generic** over `ZMod p`: the
`(bᵢ, ccᵢ)` pair at the most-significant differing limb (all-equal ⇒ `0`). This is SP1's
`LtOperationUnsigned::populate_unsigned` limb-scan ported to Lean. -/
def comparisonLimbsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 2 :=
  if b[3] ≠ cc[3] then #v[b[3], cc[3]] else if b[2] ≠ cc[2] then #v[b[2], cc[2]]
  else if b[1] ≠ cc[1] then #v[b[1], cc[1]] else if b[0] ≠ cc[0] then #v[b[0], cc[0]]
  else (#v[0, 0] : Vector (ZMod p) 2)

/-- Native witness for the `u16_flags` column: the one-hot flag at the most-significant differing
limb (all-equal ⇒ all zero). -/
def flagsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 4 :=
  if b[3] ≠ cc[3] then #v[0, 0, 0, 1] else if b[2] ≠ cc[2] then #v[0, 0, 1, 0]
  else if b[1] ≠ cc[1] then #v[0, 1, 0, 0] else if b[0] ≠ cc[0] then #v[1, 0, 0, 0]
  else (#v[0, 0, 0, 0] : Vector (ZMod p) 4)

/-- Native witness for the `not_eq_inv` column: the **field inverse** `(bᵢ - ccᵢ)⁻¹` at the
most-significant differing limb (all-equal ⇒ `0`). This is the column with no ℕ analogue — SP1's
`(b_limb - c_limb).inverse()` — so its conformance can only be checked at SP1's concrete field. -/
def notEqInvWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 1 :=
  if b[3] ≠ cc[3] then #v[(b[3] - cc[3])⁻¹] else if b[2] ≠ cc[2] then #v[(b[2] - cc[2])⁻¹]
  else if b[1] ≠ cc[1] then #v[(b[1] - cc[1])⁻¹] else if b[0] ≠ cc[0] then #v[(b[0] - cc[0])⁻¹]
  else (#v[0] : Vector (ZMod p) 1)

/-- Fully witnessed `LtOperationUnsigned` column struct (SP1's `populate_unsigned`): one-hot flags,
comparison limbs, non-equality inverse, and the composed `U16CompareOperation` bit. -/
def populate (b cc : Word (ZMod p)) : Extracted.LtOperationUnsigned (ZMod p) :=
  let cl := comparisonLimbsWitness b cc
  let f := flagsWitness b cc
  let ni := notEqInvWitness b cc
  ⟨⟨U16CompareOperation.populate_bit cl[0] cl[1]⟩, f, ni[0], cl⟩

end SP1Clean.LtOperationUnsigned
