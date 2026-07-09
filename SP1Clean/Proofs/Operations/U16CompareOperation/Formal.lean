import SP1Clean.Native.Operations.U16CompareOperation.RawSpec
import SP1Clean.Native.Operations.U16CompareOperation.Populate

/-! # `U16CompareOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `U16CompareOperation::eval` as a Clean `FormalAssertion`: the `Assumptions`, the
soundness/completeness proofs (routing through `RawSpec`'s `compare_of_raw`), and the bundled `circuit`.
The semantic `Spec` carries `bit`'s booleanness unconditionally (SP1's `eval` asserts it **ungated**) plus
the `is_real`-gated order equation. The arithmetic core lives in `RawSpec`, the elaborated circuit in
`Extracted`, the `populate_bit` witness in `Populate`. -/

namespace SP1Clean.U16CompareOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `a`, `b` are genuine 16-bit values on a real row (gated), and `is_real` is binary (the latter
discharged by the composing operation's gate). `bit`'s booleanness is carried by the `Spec`, not here, since SP1's
`eval` asserts it ungated (so it must hold on padding too, where the `Spec`'s order equation is vacuous). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → input.a.val < 2 ^ 16 ∧ input.b.val < 2 ^ 16) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 2000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  obtain ⟨hr, _hbool, hgc⟩ := h_holds
  simp only [sub_eq_add_neg] at hgc
  refine ⟨⟨bool_of_mul_pred hgc, ?_⟩, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  intro hr1eq
  obtain ⟨ha, hb⟩ := hab hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R := hr hneg
  rw [← c16] at R
  refine compare_of_raw ha hb ?_
  simp only [RawSpec]
  exact ⟨bool_of_mul_pred hgc, (byteRowSpec_range _ h16p).mp R⟩

set_option maxHeartbeats 2000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hab, hbin⟩ := h_assumptions
  obtain ⟨hbitbool, hbiteq⟩ := h_spec
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨ha, hb⟩ := hab hr1
    have hbit := hbiteq hr1
    rw [← c16]
    apply (byteRowSpec_range _ h16p).mpr
    rw [hbit]
    by_cases hlt : input_a.val < input_b.val
    · rw [if_pos hlt]
      have hle : input_b.val ≤ input_a.val + 65536 := by omega
      have key : input_a - input_b + (1 : ZMod p) * 65536
          = ((input_a.val + 65536 - input_b.val : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hle]; push_cast [ZMod.natCast_zmod_val]; ring
      rw [key, ZMod.val_natCast_of_lt (show input_a.val + 65536 - input_b.val < p by omega)]; omega
    · rw [if_neg hlt]
      have hle : input_b.val ≤ input_a.val := by omega
      have key : input_a - input_b + (0 : ZMod p) * 65536
          = ((input_a.val - input_b.val : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hle]; push_cast [ZMod.natCast_zmod_val]; ring
      rw [key, ZMod.val_natCast_of_lt (show input_a.val - input_b.val < p by omega)]; omega
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hbitbool with h | h <;> rw [h] <;> simp

/-- The `U16CompareOperation` gadget as a Clean-native `FormalAssertion`. -/
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

end SP1Clean.U16CompareOperation
