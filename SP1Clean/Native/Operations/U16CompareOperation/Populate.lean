import SP1Clean.FormalModel.Contracts.Operations

/-! # `U16CompareOperation` — `populate` (the witness generator)

The witness assignment `populate_bit` (the strict-less-than indicator the composing operation threads
in), its booleanness lemma `populate_bit_bool`, and `spec_populate` (the witnessed `bit` satisfies the
gadget `Spec`). The elaborated `eval` circuit is hand-maintained in the sibling `Defs.lean`; the
arithmetic core is in `RawSpec`; the `FormalAssertion` contract in `Formal`. -/

namespace SP1Clean.U16CompareOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The witness assignment: the strict-less-than indicator. -/
def populate_bit (a b : ZMod p) : ZMod p := if a.val < b.val then 1 else 0

set_option linter.unusedSectionVars false in
/-- `populate_bit` is always boolean — the composing operation uses this to discharge the gadget's
(ungated) `bit` booleanness obligation on every row. -/
theorem populate_bit_bool (a b : ZMod p) : populate_bit a b = 0 ∨ populate_bit a b = 1 := by
  simp only [populate_bit]; split <;> simp

/-- The witnessed `bit = populate_bit a b` satisfies the gadget `Spec` for any `is_real`. -/
theorem spec_populate {a b : ZMod p} (_ha : a.val < 2 ^ 16) (_hb : b.val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨a, b, ⟨populate_bit a b⟩, is_real⟩ : Inputs (ZMod p)) :=
  ⟨populate_bit_bool a b, fun _ => rfl⟩

end SP1Clean.U16CompareOperation
