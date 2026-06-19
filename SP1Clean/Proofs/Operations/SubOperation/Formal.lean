import SP1Clean.Native.Operations.SubOperation.RawSpec
import SP1Clean.Native.Operations.SubOperation.Populate

/-! # `SubOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `SubOperation::eval` as a Clean `FormalAssertion`: the `Assumptions`, the soundness/completeness
proofs (routing through `RawSpec`'s `subSemantics_of_carries`/`carries_of_subSemantics`), and the bundled
`circuit`. The arithmetic core lives in `RawSpec`, the elaborated circuit in `Extracted`, the `populate`
witness in `Populate`. -/

namespace SP1Clean.SubOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operand words fit in 64 bits, and `is_real` is binary (the latter discharged by the composing
chip's `is_real * (is_real - 1) = 0` gate). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.a ∧ Word.isU64 input.b ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, _hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
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
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3,
    ev0, ev1, ev2, ev3] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- post-#398 the byte receives owe no padding requirement, so the goal is exactly `Spec`.
  intro hr1eq
  have hneg : -input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [← c16] at R0 R1 R2 R3
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  -- The generated `main` decomposes the borrow constant as `+ 65536 - 1`; fold to RawSpec's `65535`.
  have c65535 : ∀ x : ZMod p, x + 65536 + -1 = x + 65535 := fun x => by ring
  simp only [c65535] at hgc0 hgc1 hgc2 hgc3
  refine subSemantics_of_carries ha hb ?_
  simp only [RawSpec, Nat.cast_ofNat, sub_eq_add_neg]
  refine ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2, bool_of_mul_pred hgc3,
    ?_, ?_, ?_, ?_⟩
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R0
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R1
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R2
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R3

set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
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
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3,
    ev0, ev1, ev2, ev3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨hv, hbv⟩ := h_spec h1
      obtain ⟨hc0, hc1, hc2, hc3, _, _, _, _⟩ := carries_of_subSemantics ha hb hv hbv
      simp only [Nat.cast_ofNat, sub_eq_add_neg] at hc0 hc1 hc2 hc3
      rw [h1]
      -- The generated `main` decomposes the borrow constant as `+ 65536 - 1`; fold to RawSpec's `65535`.
      have c65535 : ∀ x : ZMod p, x + 65536 + -1 = x + 65535 := fun x => by ring
      simp only [c65535]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc3 with h | h <;> rw [h] <;> simp

/-- SP1's `SubOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.SubOperation
