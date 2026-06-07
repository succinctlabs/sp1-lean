import SP1Clean.Foundations.Word
import SP1Clean.Extracted.IsZeroOperation
import Mathlib.Tactic.LinearCombination

/-! # `IsZeroOperation` — the arithmetic core (`AssertSpec` + the zero-test lemma)

The literal `is_real = 1` meaning of SP1's `IsZeroOperation` `asserts` list (`AssertSpec`, stated
against the result columns), the trivial interaction half (`IsZero` has no bus sends), and the native
soundness core `isZero_of_assert` the gadget routes through: the defining equation + `result * a = 0`
force `result` to be the zero indicator of `a`. The auto-generated circuit (`Inputs`/`main`/
`elaborated`) lives in the sibling `Extracted` module; the `populate` witness in `Populate`; the
`FormalAssertion` contract (soundness/completeness/`circuit`) in `Formal`.

`Faithful/IsZeroOperation.lean` anchors `AssertSpec` to the extracted `asserts` list. The transitional
`RawSpec`/`isZero_of_raw` aliases are kept so the composing word-level ops' `RawSpec`s (which reference
`IsZeroOperation.RawSpec` directly) and their faithfulness anchors still build. -/

namespace SP1Clean.IsZeroOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Assertion half** — the literal meaning of SP1's `IsZeroOperation` `asserts` list at
`is_real = 1`, stated against the result columns: `result = 1 - inverse*a`, `result` boolean, and
`result * a = 0`. (`IsZero` has no bus interactions, so this is the whole structural spec.) -/
def AssertSpec (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) : Prop :=
  ((1 - cols.inverse * a) - cols.result = 0) ∧
  (cols.result = 0 ∨ cols.result = 1) ∧
  (cols.result * a = 0)

/-- **Interaction half** — trivial: `IsZeroOperation` emits no bus interactions. -/
def InteractSpec (_a : ZMod p) (_cols : Extracted.IsZeroOperation (ZMod p)) : Prop := True

omit [Fact (2 ^ 17 < p)] in
/-- Soundness core: `AssertSpec` forces `result` to be the zero indicator of `a`. On `a = 0` the
defining equation gives `result = 1`; on `a ≠ 0` the `result * a = 0` constraint forces `result = 0`
(via `mul_inv_cancel₀`, since `mul_eq_zero` won't fire on `ZMod p`). -/
theorem isZero_of_assert {a : ZMod p} {cols : Extracted.IsZeroOperation (ZMod p)}
    (h_assert : AssertSpec a cols) :
    cols.result = if a = 0 then 1 else 0 := by
  obtain ⟨h_eq, _, h_mul⟩ := h_assert
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    linear_combination -h_eq
  · rw [if_neg ha]
    calc cols.result = cols.result * (a * a⁻¹) := by rw [mul_inv_cancel₀ ha, mul_one]
      _ = cols.result * a * a⁻¹ := by ring
      _ = 0 := by rw [h_mul, zero_mul]

omit [Fact (2 ^ 17 < p)] in
/-- On `a ≠ 0`, `AssertSpec` pins `inverse` to `a⁻¹` (the defining equation with `result = 0`). The
composing word-level completeness needs this to reconstruct the gated inverse column. -/
theorem inverse_of_assert {a : ZMod p} {cols : Extracted.IsZeroOperation (ZMod p)}
    (h_assert : AssertSpec a cols) (ha : a ≠ 0) : cols.inverse * a = 1 := by
  have hr : cols.result = 0 := by
    have := isZero_of_assert h_assert; rwa [if_neg ha] at this
  obtain ⟨h_eq, _, _⟩ := h_assert
  rw [hr] at h_eq
  linear_combination -h_eq

/-- Transitional alias for `AssertSpec` — kept so the not-yet-fully-migrated composed ops still
build (they `simp` on `IsZeroOperation.RawSpec`). Defeq to `AssertSpec` (`IsZero` has no
interactions). -/
def RawSpec (a : ZMod p) (cols : Extracted.IsZeroOperation (ZMod p)) : Prop :=
  ((1 - cols.inverse * a) - cols.result = 0) ∧
  (cols.result = 0 ∨ cols.result = 1) ∧
  (cols.result * a = 0)

omit [Fact (2 ^ 17 < p)] in
/-- Transitional alias for `isZero_of_assert` (see `RawSpec`). Returns the semantic `Spec`. -/
theorem isZero_of_raw {a : ZMod p} {cols : Extracted.IsZeroOperation (ZMod p)}
    (h_raw : RawSpec a cols) : cols.result = if a = 0 then 1 else 0 := isZero_of_assert h_raw

end SP1Clean.IsZeroOperation
