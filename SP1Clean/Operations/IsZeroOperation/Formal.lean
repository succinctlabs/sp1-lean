import SP1Clean.Operations.IsZeroOperation.RawSpec
import SP1Clean.Operations.IsZeroOperation.Populate
import SP1Clean.Operations.IsZeroOperation.Extracted

/-! # `IsZeroOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `IsZeroOperation::eval` as a Clean `FormalAssertion`: the `Assumptions` (just `is_real` binary —
no operand precondition), the `is_real`-gated semantic `Spec` (faithful to the constraints: `result`
is the zero indicator and, off zero, `inverse` is pinned to `a⁻¹`), the soundness/completeness proofs
(routing through `RawSpec`'s `isZero_of_assert`/`inverse_of_assert`), the `spec_populate`
reconstruction lemma the composing word-level op uses, and the bundled `circuit`.

The `Spec` and `spec_populate` live here (rather than in `Specs.Operation`) to avoid an import cycle:
the composing `IsZeroWordOperation.Extracted` imports this module for `.circuit`. -/

namespace SP1Clean.IsZeroOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `is_real` is binary (discharged by the composing op's `is_real * (is_real - 1) = 0` gate). No
operand precondition — `IsZero` works on any field element. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Semantic contract (`is_real`-gated, faithful — a `FormalAssertion`'s `Spec` must be equivalent to
its constraints): on a real row `result` is the zero indicator of `a`, and off zero the witnessed
`inverse` is pinned to `a⁻¹` (on `a = 0` the constraints leave `inverse` free, so the `Spec` does too).
On padding the gated constraints impose nothing. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (input.cols.result = if input.a = 0 then 1 else 0) ∧
    (input.a ≠ 0 → input.cols.inverse * input.a = 1)

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  intro hr1
  simp only [circuit_norm, hr1, one_mul] at h_holds
  obtain ⟨h_eq, h_bool, h_mul⟩ := h_holds
  have hA : AssertSpec input_a ⟨input_cols_inverse, input_cols_result⟩ := by
    refine ⟨?_, bool_of_mul_pred h_bool, h_mul⟩
    show (1 : ZMod p) - input_cols_inverse * input_a - input_cols_result = 0
    simp only [sub_eq_add_neg]; exact h_eq
  exact ⟨isZero_of_assert hA, fun ha => inverse_of_assert hA ha⟩

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  rcases h_assumptions with h0 | h1
  · simp [circuit_norm, h0]
  · obtain ⟨hres, hinv⟩ := h_spec h1
    simp only [circuit_norm, h1, one_mul]
    refine ⟨?_, ?_, ?_⟩
    · -- 1 - inverse*a - result = 0
      by_cases ha : input_a = 0
      · simp [hres, ha]
      · rw [hres, if_neg ha, hinv ha]; simp
    · rw [hres]; by_cases ha : input_a = 0 <;> simp [ha]
    · rw [hres]; by_cases ha : input_a = 0 <;> simp [ha]

omit [Fact (2 ^ 17 < p)] in
/-- The result `populate a` satisfies the gadget `Spec` for any `is_real`. The composing word-level
op uses this (per limb) to discharge the `assertion IsZeroOperation.circuit` prover obligation. -/
theorem spec_populate (a is_real : ZMod p) :
    Spec (⟨a, populate a, is_real⟩ : Inputs (ZMod p)) := by
  intro _
  by_cases ha : a = 0
  · subst ha; refine ⟨by simp [populate], ?_⟩; intro hne; exact absurd rfl hne
  · refine ⟨by simp [populate, ha], ?_⟩
    intro _; simp only [populate, if_neg ha]; exact inv_mul_cancel₀ ha

/-- SP1's `IsZeroOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.IsZeroOperation
