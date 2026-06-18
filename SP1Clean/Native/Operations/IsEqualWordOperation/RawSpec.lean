import SP1Clean.Math.Word
import SP1Clean.Native.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Extracted.IsEqualWordOperation

/-! # `IsEqualWordOperation` — the arithmetic core (`RawSpec` + the equality lemma)

`IsEqualWord` is a thin wrapper running `IsZeroWordOperation` on the limb-wise difference `a - b`, so
`is_diff_zero.result = (a - b = 0) = (a = b)`. `RawSpec` **composes** `IsZeroWordOperation.RawSpec` on
the difference; `isEqualWord_of_raw` derives the semantic equality indicator. The auto-generated circuit
(`Inputs`/`main`/`elaborated`) lives in the sibling `Extracted` module; the `populate` witness in
`Populate`; the `FormalAssertion` contract in `Formal`.

`Faithful/IsEqualWordOperation.lean` anchors `RawSpec` to the extracted `asserts` list. -/

namespace SP1Clean.IsEqualWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Literal meaning of SP1's `IsEqualWordOperation` constraint list at `is_real = 1`: the
`IsZeroWordOperation.RawSpec` on the limb-wise difference `a - b`. -/
def RawSpec (a b : Word (ZMod p)) (cols : Extracted.IsEqualWordOperation (ZMod p)) : Prop :=
  IsZeroWordOperation.RawSpec #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
    cols.is_diff_zero

omit [Fact (2 ^ 17 < p)] in
/-- Soundness core: the `IsZeroWordOperation` zero-test on the limb-wise difference, plus
`aᵢ - bᵢ = 0 ↔ aᵢ = bᵢ`, gives the equality indicator. -/
theorem isEqualWord_of_raw {a b : Word (ZMod p)} {cols : Extracted.IsEqualWordOperation (ZMod p)}
    (h_raw : RawSpec a b cols) :
    cols.is_diff_zero.result =
      if (a[0] = b[0] ∧ a[1] = b[1] ∧ a[2] = b[2] ∧ a[3] = b[3]) then 1 else 0 := by
  have h := IsZeroWordOperation.isZeroWord_of_raw h_raw
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, sub_eq_zero] at h
  exact h

end SP1Clean.IsEqualWordOperation
