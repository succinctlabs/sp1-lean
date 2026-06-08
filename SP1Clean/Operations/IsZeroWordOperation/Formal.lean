import SP1Clean.Operations.IsZeroWordOperation.RawSpec
import SP1Clean.Operations.IsZeroWordOperation.Populate
import SP1Clean.Operations.IsZeroWordOperation.Extracted

/-! # `IsZeroWordOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `IsZeroWordOperation::eval` as a Clean `FormalAssertion`. Composes `IsZeroOperation` on each
limb; the `Spec` references the four per-limb `IsZeroOperation.Spec`s by direct field application
plus the ungated booleanness/half-product clauses and the gated AND-tree. `spec_populate` lets the
composing operation discharge its `assertion`-side obligation; `result_semantic` exposes the semantic
readout. `Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle. -/

namespace SP1Clean.IsZeroWordOperation

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `is_real` is binary (discharged by the composing op's gate). No operand precondition. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Faithful semantic contract (equivalent to the constraints). `result` booleanness and the two
half-product gluings are ungated (hold on padding too); the four per-limb `IsZeroOperation.Spec`s
are referenced by direct field application; the AND-tree `result = first·second` is `is_real`-gated.
The semantic `result = (a = 0)` is recovered by `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.result = 0 ∨ input.cols.result = 1) ∧
  (input.cols.is_zero_first_half =
      input.cols.is_zero_limb_0.result * input.cols.is_zero_limb_1.result) ∧
  (input.cols.is_zero_second_half =
      input.cols.is_zero_limb_2.result * input.cols.is_zero_limb_3.result) ∧
  IsZeroOperation.Spec ⟨input.a[0], input.cols.is_zero_limb_0, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[1], input.cols.is_zero_limb_1, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[2], input.cols.is_zero_limb_2, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[3], input.cols.is_zero_limb_3, input.is_real⟩ ∧
  (input.is_real = 1 →
      input.cols.result = input.cols.is_zero_first_half * input.cols.is_zero_second_half)

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hs0, hs1, hs2, hs3, _hbreal, hbres, hf, hsec, hg⟩ := h_holds
  obtain ⟨hia, -⟩ := h_input
  have ea0 : Expression.eval env input_var_a[0] = input_a[0] := by rw [← hia]; simp [Vector.getElem_map]
  have ea1 : Expression.eval env input_var_a[1] = input_a[1] := by rw [← hia]; simp [Vector.getElem_map]
  have ea2 : Expression.eval env input_var_a[2] = input_a[2] := by rw [← hia]; simp [Vector.getElem_map]
  have ea3 : Expression.eval env input_var_a[3] = input_a[3] := by rw [← hia]; simp [Vector.getElem_map]
  have S0 := hs0 h_assumptions; rw [ea0] at S0
  have S1 := hs1 h_assumptions; rw [ea1] at S1
  have S2 := hs2 h_assumptions; rw [ea2] at S2
  have S3 := hs3 h_assumptions; rw [ea3] at S3
  rw [← sub_eq_add_neg] at hf hsec
  refine ⟨⟨bool_of_mul_pred hbres, eq_of_sub_eq_zero hf, eq_of_sub_eq_zero hsec,
      S0, S1, S2, S3, ?_⟩, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro hr1
  rw [hr1, one_mul, ← sub_eq_add_neg] at hg
  exact eq_of_sub_eq_zero hg

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbres, hf, hsec, hS0, hS1, hS2, hS3, hg⟩ := h_spec
  obtain ⟨hia, -⟩ := h_input
  have ea0 : Expression.eval env.toEnvironment input_var_a[0] = input_a[0] := by rw [← hia]; simp [Vector.getElem_map]
  have ea1 : Expression.eval env.toEnvironment input_var_a[1] = input_a[1] := by rw [← hia]; simp [Vector.getElem_map]
  have ea2 : Expression.eval env.toEnvironment input_var_a[2] = input_a[2] := by rw [← hia]; simp [Vector.getElem_map]
  have ea3 : Expression.eval env.toEnvironment input_var_a[3] = input_a[3] := by rw [← hia]; simp [Vector.getElem_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨h_assumptions, by rw [ea0]; exact hS0⟩
  · exact ⟨h_assumptions, by rw [ea1]; exact hS1⟩
  · exact ⟨h_assumptions, by rw [ea2]; exact hS2⟩
  · exact ⟨h_assumptions, by rw [ea3]; exact hS3⟩
  · rcases h_assumptions with h | h <;> simp [h]
  · rcases hbres with h | h <;> simp [h]
  · simp [hf]
  · simp [hsec]
  · rcases h_assumptions with h | h
    · simp [h]
    · rw [h, one_mul, hg h]; simp

omit [Fact (2 ^ 17 < p)] in
/-- The witnessed columns `populate a` satisfy the gadget `Spec` for any `is_real`. The composing op
(`IsEqualWord`) / top-level chip uses this to discharge the `assertion IsZeroWordOperation.circuit`
prover obligation. -/
theorem spec_populate (a : Word (ZMod p)) (is_real : ZMod p) :
    Spec (⟨a, populate a, is_real⟩ : Inputs (ZMod p)) := by
  refine ⟨?_, rfl, rfl, IsZeroOperation.spec_populate a[0] is_real,
    IsZeroOperation.spec_populate a[1] is_real, IsZeroOperation.spec_populate a[2] is_real,
    IsZeroOperation.spec_populate a[3] is_real, fun _ => rfl⟩
  simp only [populate, IsZeroOperation.populate]
  by_cases h0 : a[0] = 0 <;> by_cases h1 : a[1] = 0 <;> by_cases h2 : a[2] = 0 <;>
    by_cases h3 : a[3] = 0 <;> simp [h0, h1, h2, h3]

omit [Fact (2 ^ 17 < p)] in
/-- Semantic exposure: on a real row the `Spec` forces `result` to be the word zero-indicator. -/
theorem result_semantic {input : Inputs (ZMod p)} (h : Spec input) (hr : input.is_real = 1) :
    input.cols.result =
      if (input.a[0] = 0 ∧ input.a[1] = 0 ∧ input.a[2] = 0 ∧ input.a[3] = 0) then 1 else 0 := by
  obtain ⟨_, hf, hs, hS0, hS1, hS2, hS3, hg⟩ := h
  exact result_collapse (hS0 hr).1 (hS1 hr).1 (hS2 hr).1 (hS3 hr).1 hf hs (hg hr)

/-- SP1's `IsZeroWordOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.IsZeroWordOperation
