import SP1Clean.Native.Operations.IsZeroOperation.RawSpec
import SP1Clean.Native.Operations.IsZeroOperation.Populate
import SP1Clean.Extracted.Circuit.IsZeroOperation

/-! # `IsZeroOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `IsZeroOperation::eval` as a Clean `FormalAssertion`. The semantic `Spec` is `is_real`-gated:
`result` is the zero indicator, and off zero `inverse = a⁻¹`. `Spec`/`spec_populate` live here (not
in `Specs.Operation`) to avoid an import cycle through `IsZeroWordOperation.Extracted`. -/

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
  have hA : AssertSpec input_a ⟨input_cols_inverse, input_cols_result⟩ :=
    ⟨by simpa [sub_eq_add_neg] using h_eq, bool_of_mul_pred h_bool, h_mul⟩
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
    · by_cases ha : input_a = 0
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
  · subst ha; exact ⟨by simp [populate], fun hne => absurd rfl hne⟩
  · refine ⟨by simp [populate, ha], fun _ => ?_⟩
    simp only [populate, if_neg ha]; exact inv_mul_cancel₀ ha

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
