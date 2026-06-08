import SP1Clean.Specs.Operation
import SP1Clean.Operations.U16MSBOperation.Extracted

/-! # `U16MSBOperation` — `populate` (the witness generator)

The witness assignment `populate_msb` (the high bit of `a`, threaded in by the composing operation),
and `spec_populate` (the witnessed `msb` satisfies the gadget `Spec`). The elaborated `eval` circuit
is the auto-generated sibling `Extracted` module; the arithmetic core is in `RawSpec`; the
`FormalAssertion` contract in `Formal`. -/

namespace SP1Clean.U16MSBOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's `eval_msb` witness: the high bit of `a` (`a.val / 2^15`). -/
def populate_msb (a : ZMod p) : ZMod p := ((a.val / 32768 : ℕ) : ZMod p)

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb` is always boolean (for a genuine 16-bit `a`) — the composing operation uses this to
discharge the gadget's (now unconditional) `msb` booleanness obligation on every row. -/
theorem populate_msb_bool {a : ZMod p} (ha : a.val < 2 ^ 16) :
    populate_msb a = 0 ∨ populate_msb a = 1 := by
  simp only [populate_msb]
  by_cases hge : a.val ≥ 32768
  · right; have : a.val / 32768 = 1 := by omega
    rw [this, Nat.cast_one]
  · left; have : a.val / 32768 = 0 := by omega
    rw [this, Nat.cast_zero]

omit [Fact (2 ^ 17 < p)] in
/-- `populate_msb a` satisfies the gadget `Spec` for any `is_real`. The composing operation uses this
to discharge its assertion obligation. -/
theorem spec_populate {a : ZMod p} (ha : a.val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨a, ⟨populate_msb a⟩, is_real⟩ : Inputs (ZMod p)) := by
  refine ⟨populate_msb_bool ha, ?_⟩
  intro _
  simp only [populate_msb]
  by_cases hge : a.val ≥ 32768
  · rw [if_pos hge]
    have : a.val / 32768 = 1 := by omega
    rw [this, Nat.cast_one]
  · rw [if_neg hge]
    have : a.val / 32768 = 0 := by omega
    rw [this, Nat.cast_zero]

end SP1Clean.U16MSBOperation
