import SP1Clean.Native.Operations.AddwOperation.RawSpec
import SP1Clean.Native.Operations.AddwOperation.Populate
import SP1Clean.Extracted.Circuit.AddwOperation

/-! # `AddwOperation` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `AddwOperation::eval` as a Clean `FormalAssertion`. Composes `U16MSBOperation` on the high
result limb `value[1]`, pulls two limb ranges from the byte bus, asserts the two gated carries.
Soundness routes through `addwSemantics_of_carries`; completeness through `carries_of_addwSemantics`.
`Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle. -/

namespace SP1Clean.AddwOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- Operand words fit in 64 bits, and `is_real` is binary. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.a ∧ Word.isU64 input.b ∧ (input.is_real = 0 ∨ input.is_real = 1)

/-- `msb` booleanness holds unconditionally (the composed `U16MSBOperation` asserts it ungated).
On a real row the result is the 64-bit sign extension of the low-32 add. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.msb.msb = 0 ∨ input.cols.msb.msb = 1) ∧
  (input.is_real = 1 →
    (resultWord input.cols).isU64 ∧
    Word.toBitVec64 (resultWord input.cols) =
      (BitVec.setWidth 32 (Word.toBitVec64 input.a + Word.toBitVec64 input.b)).signExtend 64)

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, ⟨hiv, _⟩, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have ea0 : Expression.eval env input_var_a[0] = input_a[0] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env input_var_a[1] = input_a[1] := by rw [← hia]; simp only [Vector.getElem_map]
  have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have ev0 : Expression.eval env input_var_cols_value[0] = input_cols_value[0] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env input_var_cols_value[1] = input_cols_value[1] := by rw [← hiv]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea0, ea1, eb0, eb1, ev0, ev1] at h_holds ⊢
  obtain ⟨h_msb, hr0, hr1, _hgate, hgc0, hgc1⟩ := h_holds
  -- the U16MSB sub-assertion's `Assumptions` (gated `value[1] < 2^16` from the `value[1]` byte pull).
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_cols_value[1], ⟨input_cols_msb_msb⟩, input_is_real⟩ : U16MSBOperation.Inputs (ZMod p)) := by
    refine ⟨fun hr1eq => ?_, hbin⟩
    have hr1' : input_is_real = 1 := hr1eq
    have hneg : -input_is_real = -1 := by rw [hr1']
    have R1 := hr1 hneg
    rw [← c16] at R1
    show input_cols_value[1].val < 2 ^ 16
    exact (byteRowSpec_range _ h16p).mp R1
  -- post-#398 the two byte receives owe no padding requirement.
  refine ⟨⟨(h_msb h_msb_as).1, ?_⟩, Or.inr h_msb_as⟩
  intro hr1eq
  have hneg : -input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg
  rw [← c16] at R0 R1
  rw [hr1eq, one_mul] at hgc0 hgc1
  refine addwSemantics_of_carries ha hb ?_ ((h_msb h_msb_as).2 hr1eq)
  simp only [RawSpec, sub_eq_add_neg]
  refine ⟨bool_of_mul_pred hgc0, bool_of_mul_pred hgc1, ?_, ?_⟩
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R0
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R1

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, ⟨hiv, _⟩, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have ev0 : Expression.eval env.toEnvironment input_var_cols_value[0] = input_cols_value[0] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env.toEnvironment input_var_cols_value[1] = input_cols_value[1] := by rw [← hiv]; simp only [Vector.getElem_map]
  have ea0 : Expression.eval env.toEnvironment input_var_a[0] = input_a[0] := by rw [← hia]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env.toEnvironment input_var_a[1] = input_a[1] := by rw [← hia]; simp only [Vector.getElem_map]
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  -- the converse facts, all valid only on real rows
  have key : input_is_real = 1 →
      (input_cols_value[0].val < 2 ^ 16 ∧ input_cols_value[1].val < 2 ^ 16) ∧
      RawSpec input_a input_b ⟨input_cols_value, ⟨input_cols_msb_msb⟩⟩ ∧
      input_cols_msb_msb = if input_cols_value[1].val ≥ 32768 then 1 else 0 := by
    intro hr1
    obtain ⟨hU, hbveq⟩ := h_spec.2 hr1
    obtain ⟨hUv0, hUv1, _, _⟩ := Word.lt_cases_of_isU64 hU
    simp only [resultWord, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at hUv0 hUv1
    obtain ⟨h_raw, h_msbval⟩ := carries_of_addwSemantics ha hb hU hbveq
    exact ⟨⟨hUv0, hUv1⟩, h_raw, h_msbval⟩
  simp only [circuit_norm, byteChannel, ea0, ea1, eb0, eb1, ev0, ev1]
  refine ⟨⟨⟨fun hr1 => (key hr1).1.2, hbin⟩, ⟨h_spec.1, fun hr1 => (key hr1).2.2⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr (key hr1).1.1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    rw [← c16]; exact (byteRowSpec_range _ h16p).mpr (key hr1).1.2
  · -- SP1's ungated `is_real` boolean gate `is_real * (is_real - 1) = 0`
    rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨_, h_raw, _⟩ := key h1
      obtain ⟨hc0, _, _, _⟩ := h_raw
      simp only [sub_eq_add_neg] at hc0
      rw [h1, one_mul]
      rcases hc0 with h | h <;> rw [h] <;> simp
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨_, h_raw, _⟩ := key h1
      obtain ⟨_, hc1, _, _⟩ := h_raw
      simp only [sub_eq_add_neg] at hc1
      rw [h1, one_mul]
      rcases hc1 with h | h <;> rw [h] <;> simp

set_option maxHeartbeats 8000000 in
/-- The witnessed columns `populate a b` satisfy the gadget `Spec` for any `is_real`. The composing
`AddwChip` uses this to discharge the `assertion AddwOperation.circuit` prover obligation. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64) (is_real : ZMod p) :
    Spec (⟨a, b, populate a b, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  -- nat carry chain over the low two limbs
  set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
  have hq0 : q0 ≤ 1 := by rw [hq0_def]; omega
  have hq1 : q1 ≤ 1 := by rw [hq1_def]; omega
  -- the witnessed limbs as nat-cast mods
  have hval0 : (addwValueWitness a b)[0] = (((a[0].val + b[0].val) % 65536 : ℕ) : ZMod p) := by
    simp only [addwValueWitness, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  have hval1 : (addwValueWitness a b)[1] = (((a[1].val + b[1].val + q0) % 65536 : ℕ) : ZMod p) := by
    simp only [addwValueWitness, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, hq0_def]
  have hv0 : (addwValueWitness a b)[0].val < 65536 := by
    rw [hval0, ZMod.val_natCast_of_lt (by omega)]; omega
  have hv1 : (addwValueWitness a b)[1].val < 65536 := by
    rw [hval1, ZMod.val_natCast_of_lt (by omega)]; omega
  -- ZMod-level carry equations.
  have e0n : a[0].val + b[0].val = (a[0].val + b[0].val) % 65536 + q0 * 65536 := by rw [hq0_def]; omega
  have e1n : a[1].val + b[1].val + q0
      = (a[1].val + b[1].val + q0) % 65536 + q1 * 65536 := by rw [hq1_def]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ val_65536_ne_zero
  have hc0_lift : (a[0] : ZMod p) + b[0] = (addwValueWitness a b)[0] + (q0 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
    push_cast at hcast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    rw [hval0]; linear_combination hcast
  have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p)
      = (addwValueWitness a b)[1] + (q1 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
    push_cast at hcast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    rw [hval1]; linear_combination hcast
  have hc0_eq : (a[0] + b[0] - (addwValueWitness a b)[0]) * (65536 : ZMod p)⁻¹ = (q0 : ZMod p) := by
    have h : a[0] + b[0] - (addwValueWitness a b)[0] = (q0 : ZMod p) * 65536 := by
      linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + b[1] - (addwValueWitness a b)[1] +
      (a[0] + b[0] - (addwValueWitness a b)[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹
      = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + b[1] - (addwValueWitness a b)[1] + (q0 : ZMod p) = (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  -- the raw spec for the witnessed `value`
  have h_raw : RawSpec a b (populate a b) := by
    refine ⟨?_, ?_, hv0, hv1⟩
    · rw [show (populate a b).value = addwValueWitness a b from rfl, hc0_eq]; interval_cases q0 <;> simp
    · rw [show (populate a b).value = addwValueWitness a b from rfl, hc1_eq]
      interval_cases q1 <;> simp
  -- the sign bit, via the demoted `U16MSBOperation.spec_populate`
  have h_msb : (populate a b).msb.msb
      = if (populate a b).value[1].val ≥ 32768 then 1 else 0 := by
    show addwMsbWitness a b = if (addwValueWitness a b)[1].val ≥ 32768 then 1 else 0
    simp only [addwMsbWitness]
    by_cases h : (addwValueWitness a b)[1].val ≥ 32768
    · rw [if_pos h]; have : (addwValueWitness a b)[1].val / 32768 = 1 := by omega
      rw [this, Nat.cast_one]
    · rw [if_neg h]; have : (addwValueWitness a b)[1].val / 32768 = 0 := by omega
      rw [this, Nat.cast_zero]
  have hbool : addwMsbWitness a b = 0 ∨ addwMsbWitness a b = 1 := by
    have hm : addwMsbWitness a b = if (addwValueWitness a b)[1].val ≥ 32768 then 1 else 0 := h_msb
    rw [hm]; split <;> simp
  exact ⟨hbool, fun _ => addwSemantics_of_carries ha hb h_raw h_msb⟩

/-- SP1's `AddwOperation::eval` as a Clean-native `FormalAssertion`: composes the demoted `U16MSBOperation`,
byte-bus range checks, native carry chain + sign-extension keystone, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.AddwOperation
