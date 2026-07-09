import SP1Clean.Native.Operations.U16MSBOperation.RawSpec
import SP1Clean.Native.Operations.U16MSBOperation.Populate

/-! # `U16MSBOperation` — the `FormalAssertion` (soundness / completeness / contract)

SP1's `U16MSBOperation::eval_msb` as a Clean `FormalAssertion`: the `Assumptions`, the
soundness/completeness proofs (routing through `RawSpec`'s `msb_of_raw`), the `spec_populate`
reconstruction lemma the composing operation uses, and the bundled `circuit`. The semantic `Spec`
carries `msb`'s booleanness **unconditionally** (SP1's `eval_msb` asserts it ungated) plus the
`is_real`-gated high-bit equation. The arithmetic core lives in `RawSpec`, the elaborated circuit in
`Extracted`, the `populate_msb` witness in `Populate`. -/

namespace SP1Clean.U16MSBOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `a` is a genuine 16-bit value on a real row (gated), and `is_real` is binary (the latter
discharged by the composing operation's gate). `msb`'s booleanness is carried by the `Spec`, not here,
since SP1's `eval_msb` asserts it ungated (so it must hold on padding too, where the `Spec`'s high-bit
equation is vacuous). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → input.a.val < 2 ^ 16) ∧ (input.is_real = 0 ∨ input.is_real = 1)

set_option maxHeartbeats 2000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  obtain ⟨hr, _hbool, hgc⟩ := h_holds
  simp only [sub_eq_add_neg] at hgc
  refine ⟨⟨bool_of_mul_pred hgc, ?_⟩, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  intro hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R := hr hneg
  rw [← c16] at R
  refine msb_of_raw (ha hr1eq) ?_
  simp only [RawSpec]
  exact ⟨bool_of_mul_pred hgc, (byteRowSpec_range _ h16p).mp R⟩

set_option maxHeartbeats 2000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha, hbin⟩ := h_assumptions
  obtain ⟨hmsbbool, hmsbeq⟩ := h_spec
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hav := ha hr1
    have hin_cast : ((input_a.val : ℕ) : ZMod p) = input_a := ZMod.natCast_zmod_val input_a
    have h2 : (2 * input_a : ZMod p).val = 2 * input_a.val := by
      rw [two_mul, ZMod.val_add_of_lt (by omega)]; omega
    have hmsb := hmsbeq hr1
    rw [← c16]
    apply (byteRowSpec_range _ h16p).mpr
    rw [hmsb]
    by_cases hge : input_a.val ≥ 32768
    · rw [if_pos hge, one_mul]
      have hsub : (2 * input_a - 65536 : ZMod p) = (((2 * input_a.val - 65536 : ℕ) : ZMod p)) := by
        rw [Nat.cast_sub (by omega)]; push_cast; rw [hin_cast]
      rw [hsub, ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [if_neg hge, zero_mul, sub_zero, h2]; omega
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hmsbbool with h | h <;> rw [h] <;> simp

/-- SP1's `U16MSBOperation::eval_msb` as a Clean-native `FormalAssertion`. -/
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

end SP1Clean.U16MSBOperation
