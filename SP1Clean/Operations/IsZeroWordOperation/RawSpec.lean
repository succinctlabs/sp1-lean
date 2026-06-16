import SP1Clean.Math.Word
import SP1Clean.Operations.IsZeroOperation.RawSpec
import SP1Clean.Extracted.IsZeroWordOperation

/-! # `IsZeroWordOperation` — the arithmetic core (`RawSpec` + the AND-tree lemma)

The literal `is_real = 1` meaning of SP1's `IsZeroWordOperation` `asserts` list (`RawSpec`, composing
the four per-limb `IsZeroOperation.RawSpec`s plus the half-product gluings), the AND-tree collapse
lemma `result_collapse`, and the native soundness core `isZeroWord_of_raw` the gadget routes through.
The auto-generated circuit (`Inputs`/`main`/`elaborated`) lives in the sibling `Extracted` module; the
`populate` witness in `Populate`; the `FormalAssertion` contract (Spec/soundness/completeness/`circuit`)
in `Formal`.

`Faithful/IsZeroWordOperation.lean` anchors `RawSpec` to the extracted `asserts` list. -/

namespace SP1Clean.IsZeroWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Literal meaning of SP1's `IsZeroWordOperation` constraint list at `is_real = 1`: the four
per-limb `IsZeroOperation.RawSpec`s, `result` boolean, and the half-product gluing equalities. -/
def RawSpec (a : Word (ZMod p)) (cols : Extracted.IsZeroWordOperation (ZMod p)) : Prop :=
  IsZeroOperation.RawSpec a[0] cols.is_zero_limb_0 ∧
  IsZeroOperation.RawSpec a[1] cols.is_zero_limb_1 ∧
  IsZeroOperation.RawSpec a[2] cols.is_zero_limb_2 ∧
  IsZeroOperation.RawSpec a[3] cols.is_zero_limb_3 ∧
  (cols.result = 0 ∨ cols.result = 1) ∧
  (cols.is_zero_first_half - cols.is_zero_limb_0.result * cols.is_zero_limb_1.result = 0) ∧
  (cols.is_zero_second_half - cols.is_zero_limb_2.result * cols.is_zero_limb_3.result = 0) ∧
  (cols.result - cols.is_zero_first_half * cols.is_zero_second_half = 0)

omit [Fact (2 ^ 17 < p)] in
/-- The AND-tree collapse, stated over **loose field values** with the gluing equalities in the exact
`x - y = 0` form they appear: given each limb's is-zero indicator, `result` is the 4-way zero
conjunction. -/
theorem result_collapse {a0 a1 a2 a3 z0 z1 z2 z3 first second result : ZMod p}
    (hz0 : z0 = if a0 = 0 then 1 else 0) (hz1 : z1 = if a1 = 0 then 1 else 0)
    (hz2 : z2 = if a2 = 0 then 1 else 0) (hz3 : z3 = if a3 = 0 then 1 else 0)
    (hfirst : first = z0 * z1) (hsecond : second = z2 * z3)
    (hresult : result = first * second) :
    result = if (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0) then 1 else 0 := by
  rw [hresult, hfirst, hsecond, hz0, hz1, hz2, hz3]
  by_cases h0 : a0 = 0 <;> by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;>
    by_cases h3 : a3 = 0 <;> simp [h0, h1, h2, h3]

omit [Fact (2 ^ 17 < p)] in
/-- Soundness core: the per-limb `IsZeroOperation.RawSpec`s + AND-tree gluing force the word
zero-indicator. -/
theorem isZeroWord_of_raw {a : Word (ZMod p)} {cols : Extracted.IsZeroWordOperation (ZMod p)}
    (h_raw : RawSpec a cols) :
    cols.result = if (a[0] = 0 ∧ a[1] = 0 ∧ a[2] = 0 ∧ a[3] = 0) then 1 else 0 := by
  obtain ⟨r0, r1, r2, r3, _, hf, hs, hr⟩ := h_raw
  exact result_collapse (IsZeroOperation.isZero_of_raw r0) (IsZeroOperation.isZero_of_raw r1)
    (IsZeroOperation.isZero_of_raw r2) (IsZeroOperation.isZero_of_raw r3)
    (eq_of_sub_eq_zero hf) (eq_of_sub_eq_zero hs) (eq_of_sub_eq_zero hr)

end SP1Clean.IsZeroWordOperation
