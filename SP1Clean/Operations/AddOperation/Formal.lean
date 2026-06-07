import SP1Clean.Operations.AddOperation.RawSpec
import SP1Clean.Operations.AddOperation.Populate

/-! # `AddOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `AddOperation::eval` as a Clean `FormalAssertion`: the `Assumptions`, the soundness/completeness
proofs (routing through `RawSpec`'s `addSemantics_of_carries`/`carries_of_addSemantics`), the
`populate_spec` reconstruction lemma the composing chip uses to discharge its `assertion`-side
obligation, and the bundled `circuit`. The arithmetic core lives in `RawSpec`, the `populate` + elaborated
circuit in `Extracted`, the `populate` witness in `Populate`. -/

namespace SP1Clean.AddOperation

open Circuit
open SP1Clean.Channels (byteChannel binary_gate_req_vacuous)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- On a real row (`is_real = 1`) the operand words fit in 64 bits, and `is_real` is binary (the latter
discharged by the composing chip's `is_real * (is_real - 1) = 0` gate — it lets soundness clear each
gated receive's padding requirement via `binary_gate_req_vacuous`). The `isU64` precondition is **gated
on `is_real`**: a padding row owes nothing, so a chip feeding a *witnessed* operand (whose range check
is itself `is_real`-gated, e.g. DivRem's `abs_remainder`) can still discharge this assumption. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b) ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  -- Vector-indexed inputs (`a/b/value[i]`) are not auto-converted by `circuit_norm` (only scalar
  -- `is_real` is), so feed these `eval input_var_*[i] = input_*[i]` rewrites into the normalization.
  have ea0 : Expression.eval env input_var_a[0] = input_a[0] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env input_var_a[1] = input_a[1] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env input_var_a[2] = input_a[2] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env input_var_a[3] = input_a[3] := by rw [← hia]; simp only [Vector.getElem_map]
  have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
  have ev0 : Expression.eval env input_var_cols_value[0] = input_cols_value[0] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env input_var_cols_value[1] = input_cols_value[1] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev2 : Expression.eval env input_var_cols_value[2] = input_cols_value[2] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev3 : Expression.eval env input_var_cols_value[3] = input_cols_value[3] := by rw [← hiv]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3, ev0, ev1, ev2, ev3]
    at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- `circuit_norm` already discharged the carry asserts' (empty) requirements, so the goal is exactly
  -- `Spec` + the four byte padding requirements.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `Spec`: on a real row, feed `addSemantics_of_carries` its two halves separately — the
    -- carry-bools (`AssertSpec`) from the gated carry asserts, the byte ranges (`InteractSpec`) from
    -- the pull guarantees.
    intro hr1eq
    obtain ⟨ha, hb⟩ := hab_imp hr1eq
    have hneg : -input_is_real = -1 := by rw [hr1eq]
    have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
    rw [← c16] at R0 R1 R2 R3
    rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
    refine addSemantics_of_carries ha hb ?_ ?_
    · -- `AssertSpec` (carry-bools, from the gated carry asserts)
      simp only [AssertSpec, sub_eq_add_neg]
      exact ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2, bool_of_mul_pred hgc3⟩
    · -- `InteractSpec` (byte ranges, from the pull guarantees)
      simp only [InteractSpec]
      rw [← h65536]
      exact ⟨(byteRowSpec_range _ h16p).mp R0, (byteRowSpec_range _ h16p).mp R1,
        (byteRowSpec_range _ h16p).mp R2, (byteRowSpec_range _ h16p).mp R3⟩
  -- the four byte padding requirements are vacuous: for a binary `is_real`, the `toRawGated` antecedents
  -- `-is_real ≠ -1` and `-is_real ≠ 0` are jointly contradictory (faithful to SP1's multiplicity gating).
  · exact binary_gate_req_vacuous hbin _
  · exact binary_gate_req_vacuous hbin _
  · exact binary_gate_req_vacuous hbin _
  · exact binary_gate_req_vacuous hbin _

set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have ea0 : Expression.eval env.toEnvironment input_var_a[0] = input_a[0] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env.toEnvironment input_var_a[1] = input_a[1] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env.toEnvironment input_var_a[2] = input_a[2] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env.toEnvironment input_var_a[3] = input_a[3] := by rw [← hia]; simp only [Vector.getElem_map]
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb2 : Expression.eval env.toEnvironment input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb3 : Expression.eval env.toEnvironment input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
  have ev0 : Expression.eval env.toEnvironment input_var_cols_value[0] = input_cols_value[0] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env.toEnvironment input_var_cols_value[1] = input_cols_value[1] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev2 : Expression.eval env.toEnvironment input_var_cols_value[2] = input_cols_value[2] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev3 : Expression.eval env.toEnvironment input_var_cols_value[3] = input_cols_value[3] := by rw [← hiv]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3, ev0, ev1, ev2, ev3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- the four byte pull completeness obligations (fire only on real rows, `is_real = 1`).
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hv, _⟩ := h_spec hr1
    obtain ⟨hv0, _, _, _⟩ := Word.lt_cases_of_isU64 hv
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hv0
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hv, _⟩ := h_spec hr1
    obtain ⟨_, hv1, _, _⟩ := Word.lt_cases_of_isU64 hv
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hv1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hv, _⟩ := h_spec hr1
    obtain ⟨_, _, hv2, _⟩ := Word.lt_cases_of_isU64 hv
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hv2
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hv, _⟩ := h_spec hr1
    obtain ⟨_, _, _, hv3⟩ := Word.lt_cases_of_isU64 hv
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hv3
  -- the four gated carry asserts (already expanded + converted to input form by the top-level simp):
  -- vacuous on padding / from `carries_of_addSemantics` on real rows. The carries arrive in `+ -`
  -- form, so normalise `carries_of_addSemantics`'s `-` form with `sub_eq_add_neg` before rewriting.
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨hv, hbv⟩ := h_spec h1
      obtain ⟨ha, hb⟩ := hab_imp h1
      obtain ⟨⟨hc0, hc1, hc2, hc3⟩, _⟩ := carries_of_addSemantics ha hb hv hbv
      simp only [sub_eq_add_neg] at hc0 hc1 hc2 hc3
      rw [h1]
      -- Five conjuncts now: SP1's `is_real` boolean gate (`1 * (1 + -1) = 0`) then the four carries.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc3 with h | h <;> rw [h] <;> simp

/-- SP1's `AddOperation::eval` as a Clean-native `FormalAssertion`: `is_real`-gated semantic spec,
native carry-chain proofs, byte-bus range checks, no SP1Operations borrow. -/
def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.AddOperation
