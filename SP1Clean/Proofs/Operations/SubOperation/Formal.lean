import SP1Clean.Native.Operations.SubOperation.RawSpec
import SP1Clean.Native.Operations.SubOperation.Populate
import SP1Clean.Native.Operations.SubOperation.Defs

/-! # `SubOperation` — the `FormalAssertion` (soundness / completeness / contract)

The local subtraction gadget as a Clean `FormalAssertion`. Soundness/completeness route through
`RawSpec`'s `subSemantics_of_carries`/`carries_of_subSemantics`; no Rust operation artifact is part of
this proof. -/

namespace SP1Clean.SubOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- On a real row (`is_real = 1`) the operand words fit in 64 bits, and `is_real` is binary (the latter
discharged by the composing chip's `is_real * (is_real - 1) = 0` gate). The `isU64` precondition is **gated
on `is_real`** (mirroring `AddOperation`): a padding row owes nothing, so a chip feeding operands whose
range check is itself `is_real`-gated (the Option-B reader-derived operand `isU64`) can discharge it. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b) ∧ (input.is_real = 0 ∨ input.is_real = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have ev {w : Word (Expression (ZMod p))} {v : Word (ZMod p)} (h : Vector.map (Expression.eval env) w = v) :
      ∀ i (_ : i < 4), Expression.eval env w[i] = v[i] := fun i _ => by rw [← h, Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- The four trailing conjuncts are the limb byte pulls' own `Requirements` — vacuous off-gate.
  refine ⟨fun hr1eq => ?_, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0,
    fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  obtain ⟨ha, hb⟩ := hab_imp hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [← c16] at R0 R1 R2 R3
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  have c65535 : ∀ x : ZMod p, x + 65536 - 1 = x + 65535 := fun x => by ring
  simp only [c65535] at hgc0 hgc1 hgc2 hgc3
  refine subSemantics_of_carries ha hb ?_
  simp only [RawSpec, Nat.cast_ofNat]
  refine ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, bool_of_mul_pred hgc2, bool_of_mul_pred hgc3,
    ?_, ?_, ?_, ?_⟩
  · rw [← h65536]; exact (byteRowSpec_range _ sixteen_lt).mp R0
  · rw [← h65536]; exact (byteRowSpec_range _ sixteen_lt).mp R1
  · rw [← h65536]; exact (byteRowSpec_range _ sixteen_lt).mp R2
  · rw [← h65536]; exact (byteRowSpec_range _ sixteen_lt).mp R3

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, hiv, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  have ev {w : Word (Expression (ZMod p))} {v : Word (ZMod p)}
      (h : Vector.map (Expression.eval env.toEnvironment) w = v) :
      ∀ i (_ : i < 4), Expression.eval env.toEnvironment w[i] = v[i] :=
    fun i _ => by rw [← h, Vector.getElem_map]
  have key (hneg : - input_is_real = -1) :=
    Word.lt_cases_of_isU64 (h_spec (neg_inj.mp hneg)).1
  simp only [circuit_norm, byteChannel, ev hia, ev hib, ev hiv]
  refine ⟨fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, ?_⟩
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).1
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.1
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.2.1
  · rw [← c16]; exact (byteRowSpec_range _ sixteen_lt).mpr (key hneg).2.2.2
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨hv, hbv⟩ := h_spec h1
      obtain ⟨ha, hb⟩ := hab_imp h1
      obtain ⟨hc0, hc1, hc2, hc3, _, _, _, _⟩ := carries_of_subSemantics ha hb hv hbv
      simp only [Nat.cast_ofNat, sub_eq_add_neg] at hc0 hc1 hc2 hc3
      rw [h1]
      have c65535 : ∀ x : ZMod p, x + 65536 + -1 = x + 65535 := fun x => by ring
      simp only [sub_eq_add_neg, c65535]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]; rcases hc0 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc1 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc2 with h | h <;> rw [h] <;> simp
      · rw [one_mul]; rcases hc3 with h | h <;> rw [h] <;> simp

/-- The proof-oriented local subtraction gadget as a Clean-native `FormalAssertion`. -/
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

end SP1Clean.SubOperation
