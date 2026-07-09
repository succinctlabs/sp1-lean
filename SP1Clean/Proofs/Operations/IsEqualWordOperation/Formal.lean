import SP1Clean.Native.Operations.IsEqualWordOperation.RawSpec
import SP1Clean.Native.Operations.IsEqualWordOperation.Populate
import SP1Clean.Extracted.Circuit.IsEqualWordOperation

/-! # `IsEqualWordOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `IsEqualWordOperation::eval` as a Clean `FormalAssertion` that **composes `IsZeroWordOperation`**
as a true Clean `assertion` on the limb-wise difference `a - b`. Its faithful `Spec` is exactly
`IsZeroWordOperation.Spec` on that difference (referenced by direct field application); the semantic
`is_diff_zero.result = (a = b)` is recovered by `result_semantic`.

`Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle: this op tops the
`IsEqualWord → IsZeroWord → IsZero` composition chain. -/

namespace SP1Clean.IsEqualWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The limb-wise difference word `a - b` (as the operand the sub-operation runs on). -/
def diff (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.a[0] - input.b[0], input.a[1] - input.b[1], input.a[2] - input.b[2], input.a[3] - input.b[3]]

/-- `is_real` is binary (discharged by the composing chip's gate). No operand precondition. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Faithful semantic contract: `IsEqualWord` is `IsZeroWord` on the limb-wise difference, so its
`Spec` is exactly `IsZeroWordOperation.Spec` on that difference word. The semantic
`is_diff_zero.result = (a = b)` is recovered by `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  IsZeroWordOperation.Spec ⟨diff input, input.cols.is_diff_zero, input.is_real⟩

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hsub, _hbool⟩ := h_holds
  obtain ⟨hia, hib, -⟩ := h_input
  have S := hsub h_assumptions
  refine ⟨?_, Or.inl rfl⟩
  simpa only [diff, ← hia, ← hib, Vector.getElem_map, sub_eq_add_neg] using S

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hia, hib, -⟩ := h_input
  refine ⟨⟨h_assumptions, ?_⟩, ?_⟩
  · have hs := h_spec
    simp only [diff] at hs
    simpa only [← hia, ← hib, Vector.getElem_map] using hs
  · rcases h_assumptions with h | h <;> simp [h]

omit [Fact (2 ^ 17 < p)] in
/-- The witnessed columns `populate a b` satisfy the gadget `Spec` for any `is_real` — it delegates to
`IsZeroWordOperation.spec_populate` on the difference word. -/
theorem spec_populate (a b : Word (ZMod p)) (is_real : ZMod p) :
    Spec (⟨a, b, populate a b, is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_populate _ is_real

omit [Fact (2 ^ 17 < p)] in
/-- Semantic exposure: on a real row the `Spec` forces `is_diff_zero.result` to be the equality
indicator of `a` and `b`. -/
theorem result_semantic {input : Inputs (ZMod p)} (h : Spec input) (hr : input.is_real = 1) :
    input.cols.is_diff_zero.result =
      if (input.a[0] = input.b[0] ∧ input.a[1] = input.b[1] ∧
          input.a[2] = input.b[2] ∧ input.a[3] = input.b[3]) then 1 else 0 := by
  have hz := IsZeroWordOperation.result_semantic h hr
  simp only [diff, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, sub_eq_zero] at hz
  exact hz

omit [Fact (2 ^ 17 < p)] in
/-- `Spec` at the all-zero column struct with the gate off (`is_real = 0`) — the inactive-row
discharge for composing chips whose populate leaves the struct zero (`DivRemChip`'s
`is_overflow_b`/`is_overflow_c` on padding rows). The operands are arbitrary. -/
theorem spec_zero (a b : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, b, ⟨IsZeroWordOperation.zeroCols⟩, is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_zero _ hr

omit [Fact (2 ^ 17 < p)] in
/-- `Spec` with the gate off (`is_real = 0`) holds at the populate of **any** word pair — the
shared-struct discharge for a composing chip whose one witnessed struct serves two
differently-gated assertions with different operand words (`DivRemChip`'s `is_overflow_b/c`:
full-word @ `is_real_not_word` vs truncated @ the word-variant gate). -/
theorem spec_populate_offGate (a b w w' : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨a, b, populate w w', is_real⟩ : Inputs (ZMod p)) :=
  IsZeroWordOperation.spec_populate_offGate _ _ hr

/-- SP1's `IsEqualWordOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.IsEqualWordOperation
