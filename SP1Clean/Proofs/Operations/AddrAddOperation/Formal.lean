import SP1Clean.Native.Operations.AddrAddOperation.RawSpec
import SP1Clean.Native.Operations.AddrAddOperation.Populate
import SP1Clean.Native.Operations.AddrAddOperation.Defs

/-! # `AddrAddOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `AddrAddOperation::eval` (48-bit/3-limb address add) as a Clean `FormalAssertion`: the
`Assumptions`, the soundness/completeness proofs (routing through `RawSpec`'s
`addrAddSemantics_of_carries`/`carries_of_addrAddSemantics`), and the bundled `circuit`. The high
carry runs against `0`: its booleanity proves the address-fits fact in soundness, while completeness
recovers the same fact from the semantic `Spec`. The arithmetic core lives in `RawSpec`, the native
circuit (`main`/`elaborated`) in `Defs`, and the `populate` witness in `Populate`. -/

namespace SP1Clean.AddrAddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operand words fit in 64 bits and `is_real` is binary (discharged by the composing chip's gate).
The address-fits fact is not an assumption: the AIR's boolean high carry against zero proves it. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.a ∧ Word.isU64 input.b ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
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
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3, ev0, ev1, ev2]
    at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- The three trailing conjuncts are the limb byte pulls' own `Requirements` — vacuous off-gate.
  refine ⟨fun hr1eq => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg
  rw [← c16] at R0 R1 R2
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  simp only [sub_zero] at hgc3
  have Rb0 := (byteRowSpec_range _ h16p).mp R0
  have Rb1 := (byteRowSpec_range _ h16p).mp R1
  have Rb2 := (byteRowSpec_range _ h16p).mp R2
  have hraw : RawSpec input_a input_b (⟨input_cols_value⟩ : Extracted.AddrAddOperation (ZMod p)) := by
    simp only [RawSpec]
    exact ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2,
    bool_of_mul_pred hgc3, by rw [← h65536]; exact Rb0, by rw [← h65536]; exact Rb1,
    by rw [← h65536]; exact Rb2⟩
  exact ⟨addrAddSemantics_of_carries ha hb hraw, Rb0, Rb1, Rb2,
    addrAddFits_of_carries ha hb hraw⟩

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
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, eb0, eb1, eb2, eb3, ev0, ev1, ev2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨_, hrng0, _, _, _⟩ := h_spec hr1
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hrng0
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨_, _, hrng1, _, _⟩ := h_spec hr1
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hrng1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨_, _, _, hrng2, _⟩ := h_spec hr1
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hrng2
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨heq, hrng0, hrng1, hrng2, hfit⟩ := h_spec h1
      have hraw : RawSpec input_a input_b (⟨input_cols_value⟩ : Extracted.AddrAddOperation (ZMod p)) :=
        carries_of_addrAddSemantics ha hb hfit hrng0 hrng1 hrng2 heq
      simp only [RawSpec] at hraw
      obtain ⟨hc0, hc1, hc2, hc3, _, _, _⟩ := hraw
      rw [h1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · simp only [sub_zero]
        rw [one_mul]
        rcases hc3 with h | h <;> rw [h] <;> simp

/-- SP1's `AddrAddOperation::eval` as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.AddrAddOperation
