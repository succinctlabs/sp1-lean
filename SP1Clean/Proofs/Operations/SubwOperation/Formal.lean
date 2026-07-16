import SP1Clean.Native.Operations.SubwOperation.RawSpec
import SP1Clean.Native.Operations.SubwOperation.Populate
import SP1Clean.Extracted.Circuit.SubwOperation

/-! # `SubwOperation` — the `FormalAssertion` (borrow-form analog of `AddwOperation`)

SP1's `SubwOperation::eval` as a Clean `FormalAssertion`. Composes `U16MSBOperation` on the high
result limb, pulls two limb ranges from the byte bus, asserts the two gated borrows. `Spec`/
`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle. -/

namespace SP1Clean.SubwOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` byte-row width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

omit [Fact (2 ^ 17 < p)] in
/-- Close a gated carry assert `x * (x + -1) = 0` from a carry-bool `c = 0 ∨ c = 1` and `x = c`
(by `ring`). Bridges the auto-extracted `main`'s `65536 + -1` borrow spelling to `RawSpec`'s `65535`. -/
private lemma carry_zero {x c : ZMod p} (h : c = 0 ∨ c = 1) (hxc : x = c) : x * (x - 1) = 0 := by
  rw [hxc]; rcases h with h | h <;> rw [h] <;> ring

/-- On a real row (`is_real = 1`) the operand words fit in 64 bits, and `is_real` is binary. The `isU64`
precondition is **gated on `is_real`** (mirroring `AddOperation`/`SubOperation`): a padding row owes
nothing, so a chip feeding reader-derived (Option-B, `is_real`-gated) operand `isU64` can discharge it. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b) ∧ (input.is_real = 0 ∨ input.is_real = 1)

/-- Semantic contract: the sign bit `msb`'s booleanness holds **unconditionally** (the composed
`U16MSBOperation` asserts it ungated), and on a real row (`is_real`-gated) the reconstructed result is
the 64-bit sign extension of the low-32 subtract. On padding (`is_real = 0`) the latter is vacuous. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.msb.msb = 0 ∨ input.cols.msb.msb = 1) ∧
  (input.is_real = 1 →
    (resultWord input.cols).isU64 ∧
    Word.toBitVec64 (resultWord input.cols) =
      (BitVec.setWidth 32 (Word.toBitVec64 input.a - Word.toBitVec64 input.b)).signExtend 64)

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, ⟨hiv, _⟩, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have h65536 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have ea : ∀ i (hi : i < 4), Expression.eval env input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  have eb : ∀ i (hi : i < 4), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ev : ∀ i (hi : i < 2),
      Expression.eval env input_var_cols_value[i] = input_cols_value[i] := by
    intro i hi; rw [← hiv]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea, eb, ev] at h_holds ⊢
  obtain ⟨h_msb, hr0, hr1, _hgate, hgc0, hgc1⟩ := h_holds
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_cols_value[1], ⟨input_cols_msb_msb⟩, input_is_real⟩ : U16MSBOperation.Inputs (ZMod p)) := by
    refine ⟨fun hr1eq => ?_, hbin⟩
    have hr1' : input_is_real = 1 := hr1eq
    have hneg : - input_is_real = -1 := by rw [hr1']
    have R1 := hr1 hneg
    rw [← c16] at R1
    show input_cols_value[1].val < 2 ^ 16
    exact (byteRowSpec_range _ h16p).mp R1
  -- The two direct byte pulls are vacuous off-gate. The composed MSB gadget now exposes its empty
  -- requirement list through canonical metadata, so its local assumption does not leak into this tail.
  refine ⟨⟨(h_msb h_msb_as).1, ?_⟩,
    fun h1 h0 => off_gate_vacuous hbin h1 h0, fun h1 h0 => off_gate_vacuous hbin h1 h0⟩
  intro hr1eq
  obtain ⟨ha, hb⟩ := hab_imp hr1eq
  have hneg : - input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg
  rw [← c16] at R0 R1
  rw [hr1eq, one_mul] at hgc0 hgc1
  refine subwSemantics_of_carries ha hb ?_ ((h_msb h_msb_as).2 hr1eq)
  simp only [RawSpec, Nat.cast_ofNat, sub_eq_add_neg]
  -- The auto-extracted `main` spells the borrow constant as `65536 + -1`; `RawSpec` uses `65535`.
  -- They agree in `ZMod p` (ring numeral normalization), so bridge each carry bool with
  -- `linear_combination` rather than a syntactic `refine`/`rw`.
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases bool_of_mul_pred hgc0 with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rcases bool_of_mul_pred hgc1 with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R0
  · rw [← h65536]; exact (byteRowSpec_range _ h16p).mp R1

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  obtain ⟨hia, hib, ⟨hiv, _⟩, _⟩ := h_input
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  have ev : ∀ i (hi : i < 2),
      Expression.eval env.toEnvironment input_var_cols_value[i] = input_cols_value[i] := by
    intro i hi; rw [← hiv]; simp only [Vector.getElem_map]
  have ea : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_a[i] = input_a[i] := by
    intro i hi; rw [← hia]; simp only [Vector.getElem_map]
  have eb : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have key : input_is_real = 1 →
      (input_cols_value[0].val < 2 ^ 16 ∧ input_cols_value[1].val < 2 ^ 16) ∧
      RawSpec input_a input_b ⟨input_cols_value, ⟨input_cols_msb_msb⟩⟩ ∧
      input_cols_msb_msb = if input_cols_value[1].val ≥ 32768 then 1 else 0 := by
    intro hr1
    obtain ⟨ha, hb⟩ := hab_imp hr1
    obtain ⟨hU, hbveq⟩ := h_spec.2 hr1
    obtain ⟨hUv0, hUv1, _, _⟩ := Word.lt_cases_of_isU64 hU
    simp only [resultWord, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at hUv0 hUv1
    obtain ⟨h_raw, h_msbval⟩ := carries_of_subwSemantics ha hb hU hbveq
    exact ⟨⟨hUv0, hUv1⟩, h_raw, h_msbval⟩
  simp only [circuit_norm, byteChannel, ea, eb, ev]
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
      simp only [Nat.cast_ofNat] at hc0
      rw [h1, one_mul]
      exact carry_zero hc0 (by linear_combination)
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨_, h_raw, _⟩ := key h1
      obtain ⟨_, hc1, _, _⟩ := h_raw
      simp only [Nat.cast_ofNat] at hc1
      rw [h1, one_mul]
      exact carry_zero hc1 (by linear_combination)

set_option maxHeartbeats 8000000 in
/-- The witnessed columns `populate a b` satisfy the gadget `Spec` for any `is_real`. -/
theorem spec_populate {a b : Word (ZMod p)} (ha : a.isU64) (hb : b.isU64) (is_real : ZMod p) :
    Spec (⟨a, b, populate a b, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨ha0, ha1, _, _⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hb0, hb1, _, _⟩ := Word.lt_cases_of_isU64 hb
  set q0 : ℕ := (a[0].val + (65535 - b[0].val) + 1) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + (65535 - b[1].val) + q0) / 65536 with hq1_def
  have hq0 : q0 ≤ 1 := by rw [hq0_def]; omega
  have hq1 : q1 ≤ 1 := by rw [hq1_def]; omega
  have hval0 : (subwValueWitness a b)[0] = (((a[0].val + (65535 - b[0].val) + 1) % 65536 : ℕ) : ZMod p) := by
    simp only [subwValueWitness, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  have hval1 : (subwValueWitness a b)[1]
      = (((a[1].val + (65535 - b[1].val) + q0) % 65536 : ℕ) : ZMod p) := by
    simp only [subwValueWitness, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, hq0_def]
  have hv0 : (subwValueWitness a b)[0].val < 65536 := by
    rw [hval0, ZMod.val_natCast_of_lt (by omega)]; omega
  have hv1 : (subwValueWitness a b)[1].val < 65536 := by
    rw [hval1, ZMod.val_natCast_of_lt (by omega)]; omega
  have e0n : a[0].val + 65535 + 1
      = (a[0].val + (65535 - b[0].val) + 1) % 65536 + q0 * 65536 + b[0].val := by rw [hq0_def]; omega
  have e1n : a[1].val + 65535 + q0
      = (a[1].val + (65535 - b[1].val) + q0) % 65536 + q1 * 65536 + b[1].val := by rw [hq1_def]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ val_65536_ne_zero
  have hc0_lift : (a[0] : ZMod p) + 65535 + 1
      = (subwValueWitness a b)[0] + (q0 : ZMod p) * 65536 + b[0] := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
    push_cast at hcast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    rw [hval0]; linear_combination hcast
  have hc1_lift : (a[1] : ZMod p) + 65535 + (q0 : ZMod p)
      = (subwValueWitness a b)[1] + (q1 : ZMod p) * 65536 + b[1] := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
    push_cast at hcast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    rw [hval1]; linear_combination hcast
  have hc0_eq : (a[0] + 65535 - b[0] - (subwValueWitness a b)[0] + 1) * (65536 : ZMod p)⁻¹
      = (q0 : ZMod p) := by
    have h : a[0] + 65535 - b[0] - (subwValueWitness a b)[0] + 1 = (q0 : ZMod p) * 65536 := by
      linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + 65535 - b[1] - (subwValueWitness a b)[1] +
      (a[0] + 65535 - b[0] - (subwValueWitness a b)[0] + 1) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹
      = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + 65535 - b[1] - (subwValueWitness a b)[1] + (q0 : ZMod p) = (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have h_raw : RawSpec a b (populate a b) := by
    refine ⟨?_, ?_, hv0, hv1⟩
    · rw [show (populate a b).value = subwValueWitness a b from rfl, hc0_eq]; interval_cases q0 <;> simp
    · rw [show (populate a b).value = subwValueWitness a b from rfl, hc1_eq]; interval_cases q1 <;> simp
  have h_msb : (populate a b).msb.msb
      = if (populate a b).value[1].val ≥ 32768 then 1 else 0 := by
    show subwMsbWitness a b = if (subwValueWitness a b)[1].val ≥ 32768 then 1 else 0
    simp only [subwMsbWitness]
    by_cases h : (subwValueWitness a b)[1].val ≥ 32768
    · rw [if_pos h]; have : (subwValueWitness a b)[1].val / 32768 = 1 := by omega
      rw [this, Nat.cast_one]
    · rw [if_neg h]; have : (subwValueWitness a b)[1].val / 32768 = 0 := by omega
      rw [this, Nat.cast_zero]
  have hbool : subwMsbWitness a b = 0 ∨ subwMsbWitness a b = 1 := by
    have hm : subwMsbWitness a b = if (subwValueWitness a b)[1].val ≥ 32768 then 1 else 0 := h_msb
    rw [hm]; split <;> simp
  exact ⟨hbool, fun _ => subwSemantics_of_carries ha hb h_raw h_msb⟩

/-- SP1's `SubwOperation::eval` as a Clean-native `FormalAssertion`. -/
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

end SP1Clean.SubwOperation
