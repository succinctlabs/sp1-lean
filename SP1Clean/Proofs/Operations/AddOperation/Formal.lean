import SP1Clean.Native.Operations.AddOperation.RawSpec
import SP1Clean.Native.Operations.AddOperation.Populate
import SP1Clean.Native.Operations.AddOperation.Defs

/-! # `AddOperation` — the `FormalAssertion` (soundness / completeness / contract)

The local addition gadget as a Clean `FormalAssertion`. Soundness/completeness route through
`RawSpec`'s `addSemantics_of_carries`/`carries_of_addSemantics`; `populate_spec` lets the composing
chip discharge its `assertion`-side obligation. Arithmetic core in `RawSpec`, circuit in `Defs`, and
witness in `Populate`; no Rust operation artifact is part of this proof. -/

namespace SP1Clean.AddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- On a real row (`is_real = 1`) the operand words fit in 64 bits, and `is_real` is binary (the latter
discharged by the composing chip's `is_real * (is_real - 1) = 0` gate). The `isU64` precondition is **gated
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
  have ev {w : Word (Expression (ZMod p))} {v : Word (ZMod p)} (h : Vector.map (Expression.eval env) w = v) :
      ∀ i (_ : i < 4), Expression.eval env w[i] = v[i] := fun i _ => by rw [← h, Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- The four trailing conjuncts are the limb byte pulls' own `Requirements` — vacuous off-gate (`cedc171b`).
  refine ⟨fun hr1eq => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  obtain ⟨ha, hb⟩ := hab_imp hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [← c16] at R0 R1 R2 R3
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  refine addSemantics_of_carries ha hb ?_ ?_
  · simp only [AssertSpec]
    exact ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2, bool_of_mul_pred hgc3⟩
  · simp only [InteractSpec]
    rw [← h65536]
    exact ⟨(byteRowSpec_range _ sixteen_lt).mp R0, (byteRowSpec_range _ sixteen_lt).mp R1,
      (byteRowSpec_range _ sixteen_lt).mp R2, (byteRowSpec_range _ sixteen_lt).mp R3⟩

set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have ev {w : Word (Expression (ZMod p))} {v : Word (ZMod p)}
      (h : Vector.map (Expression.eval env.toEnvironment) w = v) :
      ∀ i (_ : i < 4), Expression.eval env.toEnvironment w[i] = v[i] :=
    fun i _ => by rw [← h, Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hneg; rw [← c16]
    exact (byteRowSpec_range _ sixteen_lt).mpr (Word.lt_cases_of_isU64 (h_spec (neg_inj.mp hneg)).1).1
  · intro hneg; rw [← c16]
    exact (byteRowSpec_range _ sixteen_lt).mpr (Word.lt_cases_of_isU64 (h_spec (neg_inj.mp hneg)).1).2.1
  · intro hneg; rw [← c16]
    exact (byteRowSpec_range _ sixteen_lt).mpr (Word.lt_cases_of_isU64 (h_spec (neg_inj.mp hneg)).1).2.2.1
  · intro hneg; rw [← c16]
    exact (byteRowSpec_range _ sixteen_lt).mpr (Word.lt_cases_of_isU64 (h_spec (neg_inj.mp hneg)).1).2.2.2
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨hv, hbv⟩ := h_spec h1
      obtain ⟨ha, hb⟩ := hab_imp h1
      obtain ⟨⟨hc0, hc1, hc2, hc3⟩, _⟩ := carries_of_addSemantics ha hb hv hbv
      rw [h1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc3 with h | h <;> rw [h] <;> simp

/-- The proof-oriented local addition gadget as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := []
  requirementsChannelsLawful input_var i₀ := by
    simp only [circuit_norm, main, byteChannel]
    intro env h_constraints
    have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
        (ProvableStruct.eval env input_var).is_real = 1 :=
      bool_of_mul_pred h_constraints.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h1 h0 <;>
      exact off_gate_vacuous h_bool h1 h0

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    circuit.channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.AddOperation
