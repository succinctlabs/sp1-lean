import SP1Clean.Native.Operations.LtOperationUnsigned.RawSpec
import SP1Clean.Native.Operations.LtOperationUnsigned.Populate
import SP1Clean.Extracted.Circuit.LtOperationUnsigned

/-! # `LtOperationUnsigned` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `LtOperationUnsigned::eval` as a Clean `FormalAssertion` that **composes `U16CompareOperation`**
as a true Clean `assertion` on the selected limb pair — witnessing nothing (the comparison columns are
an input `cols`, threaded in by the composing `LtOperationSigned` via `populate`). The semantic `Spec`
is **structural** (equivalent to the constraint list: the flag booleans, sum-bound, prefix-sum
selectors, limb extractions, and non-equality witness, plus the composed `U16Compare` bit's booleanness
and gated order). The semantic readout (`bit = unsigned-less-than`, `Σflags = 0 ↔ equal`) is exposed by
`result_semantic`, routing through the `RawSpec` cores in `RawSpec.lean`.

`Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle: the `Extracted`
`main` imports `U16CompareOperation.Formal` for `.circuit`. -/

namespace SP1Clean.LtOperationUnsigned

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- On a real row (`is_real = 1`) the operands are genuine 64-bit values, and `is_real` is binary. The
`isU64` precondition is **gated on `is_real`**: a padding row owes nothing, so a chip feeding *witnessed*
operands whose range checks are themselves `is_real`-gated (e.g. DivRem's `abs_remainder`/`max_abs_c_or_1`)
can still discharge this assumption. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.b ∧ Word.isU64 input.cc) ∧ (input.is_real = 0 ∨ input.is_real = 1)

/-- Structural contract, **equivalent to the constraint list** (so completeness `Assumptions ∧ Spec →
constraints` holds): the four `u16_flags` are boolean and sum to `0`/`1`; the four prefix-sum
selectors `(is_real − Σflags≥i)·(bᵢ − ccᵢ)` vanish; the two comparison limbs extract `Σ bᵢ·flagᵢ` /
`Σ ccᵢ·flagᵢ`; the non-equality gate holds; and the composed `U16Compare` `bit` is boolean
(unconditionally) and, on a real row, the strict-less-than indicator of the two limbs. The semantic
whole-word order is derived from this by `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let cols := input.cols
  let f0 := cols.u16_flags[0]; let f1 := cols.u16_flags[1]
  let f2 := cols.u16_flags[2]; let f3 := cols.u16_flags[3]
  let cl0 := cols.comparison_limbs[0]; let cl1 := cols.comparison_limbs[1]
  let sumf := f0 + f1 + f2 + f3
  let ir := input.is_real
  (f0 = 0 ∨ f0 = 1) ∧ (f1 = 0 ∨ f1 = 1) ∧ (f2 = 0 ∨ f2 = 1) ∧ (f3 = 0 ∨ f3 = 1) ∧
  (sumf = 0 ∨ sumf = 1) ∧
  ((ir - f3) * (input.b[3] - input.cc[3]) = 0) ∧
  ((ir - (f3 + f2)) * (input.b[2] - input.cc[2]) = 0) ∧
  ((ir - (f3 + f2 + f1)) * (input.b[1] - input.cc[1]) = 0) ∧
  ((ir - (f3 + f2 + f1 + f0)) * (input.b[0] - input.cc[0]) = 0) ∧
  ((input.b[3] * f3 + input.b[2] * f2 + input.b[1] * f1 + input.b[0] * f0) - cl0 = 0) ∧
  ((input.cc[3] * f3 + input.cc[2] * f2 + input.cc[1] * f1 + input.cc[0] * f0) - cl1 = 0) ∧
  ((-sumf) * (cols.not_eq_inv * (cl0 - cl1) - ir) = 0) ∧
  (cols.u16_compare_operation.bit = 0 ∨ cols.u16_compare_operation.bit = 1) ∧
  (ir = 1 → cols.u16_compare_operation.bit = if cl0.val < cl1.val then 1 else 0)

set_option linter.unusedSectionVars false in
/-- On a real row (`is_real = 1`), the structural `Spec` collapses to the `is_real = 1`-form
`Selectors` the soundness cores consume. -/
theorem selectors_of_spec_real {input : Inputs (ZMod p)} (hs : Spec input)
    (hir : input.is_real = 1) : Selectors input.b input.cc input.cols := by
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0, hcl1, hinv, _, _⟩ := hs
  rw [hir] at hs3 hs2 hs1 hs0 hinv
  exact ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
    by linear_combination hs1, by linear_combination hs0, hcl0, hcl1, by linear_combination hinv⟩

/-- Semantic readout (used by `LtOperationSigned` soundness): on a real row, the compare `bit` is the
unsigned-less-than indicator of the whole words and the flags sum to `0` exactly when they are equal. -/
theorem result_semantic {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc) (hir : input.is_real = 1)
    (hs : Spec input) :
    (input.cols.u16_compare_operation.bit
        = if Word.toNat input.b < Word.toNat input.cc then 1 else 0) ∧
    ((input.cols.u16_flags[0] + input.cols.u16_flags[1] + input.cols.u16_flags[2]
        + input.cols.u16_flags[3] = 0) ↔ Word.toNat input.b = Word.toNat input.cc) := by
  have h_sel := selectors_of_spec_real hs hir
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbitbool, hbitord⟩ := hs
  exact ⟨ltUnsigned_core input.b input.cc hb hcc
      (fun _ => ⟨hbitbool, fun _ => hbitord hir⟩) h_sel,
    flags_sum_zero_iff_eq input.b input.cc hb hcc h_sel⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
/-- The witnessed columns `populate b cc` satisfy the `is_real = 1`-form `Selectors`: the one-hot flag
at the most-significant differing limb makes every prefix selector vanish, the comparison limbs are the
selected pair, and the non-equality inverse closes the gate. (SP1's `populate_unsigned` correctness.) -/
theorem sel_populate {b cc : Word (ZMod p)} :
    Selectors b cc (populate b cc) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Selectors, populate, comparisonLimbsWitness, flagsWitness, notEqInvWitness]
  by_cases h3 : b[3] = cc[3]
  · by_cases h2 : b[2] = cc[2]
    · by_cases h1 : b[1] = cc[1]
      · by_cases h0 : b[0] = cc[0]
        · -- all limbs equal
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [ne_eq, h3, h2, h1, h0, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
              true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
              List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
              zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero]
        · -- limb 0 differs
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [ne_eq, h3, h2, h1, h0, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
              true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
              List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
              zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
            first | linear_combination inv_mul_cancel₀ (sub_ne_zero.mpr h0) | linear_combination -inv_mul_cancel₀ (sub_ne_zero.mpr h0) | ring
      · -- limb 1 differs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, h3, h2, h1, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
            true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
            List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
            zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
          first | linear_combination inv_mul_cancel₀ (sub_ne_zero.mpr h1) | linear_combination -inv_mul_cancel₀ (sub_ne_zero.mpr h1) | ring
    · -- limb 2 differs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [ne_eq, h3, h2, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
          true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
          zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
        first | linear_combination inv_mul_cancel₀ (sub_ne_zero.mpr h2) | linear_combination -inv_mul_cancel₀ (sub_ne_zero.mpr h2) | ring
  · -- limb 3 differs (most significant)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ne_eq, h3, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
        true_or, or_true, if_true, if_false, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, sub_self, sub_zero, zero_sub, mul_zero,
        zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero] <;>
      first | linear_combination inv_mul_cancel₀ (sub_ne_zero.mpr h3) | linear_combination -inv_mul_cancel₀ (sub_ne_zero.mpr h3) | ring

set_option maxHeartbeats 2000000 in
set_option linter.unusedSectionVars false in
/-- The witnessed columns `populate b cc` satisfy the gadget `Spec` on a real row. The composing
`LtOperationSigned` uses this to discharge the `assertion LtOperationUnsigned.circuit` obligation
(its `Assumptions` — the operand `isU64`s — are supplied separately by the composer). -/
theorem spec_populate {b cc : Word (ZMod p)} :
    Spec (⟨b, cc, populate b cc, 1⟩ : Inputs (ZMod p)) := by
  have h_sel : Selectors b cc (populate b cc) := sel_populate
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0, hcl1, hinv⟩ := h_sel
  have hbit : (populate b cc).u16_compare_operation.bit
      = if (populate b cc).comparison_limbs[0].val < (populate b cc).comparison_limbs[1].val
        then 1 else 0 := rfl
  refine ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
    by linear_combination hs1, by linear_combination hs0, hcl0, hcl1, by linear_combination hinv,
    U16CompareOperation.populate_bit_bool _ _, fun _ => hbit⟩

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbcc_imp, hbin⟩ := h_assumptions
  obtain ⟨hib, hicc, hicols, hir⟩ := h_input
  obtain ⟨_hibit, hiflags, _hineinv, hicl⟩ := hicols
  have eb : ∀ i (hi : i < 4), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_u16_flags[i] = input_cols_u16_flags[i] := by
    intro i hi; rw [← hiflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env input_var_cols_comparison_limbs[i] = input_cols_comparison_limbs[i] := by
    intro i hi; rw [← hicl]; simp only [Vector.getElem_map]
  simp only [id_eq, eb, ec, ef, ecl] at h_holds ⊢
  obtain ⟨h_cmp, hE1, hE6, hE8, hE10, hE12, hE14, hE19, hE27, hE35, hE43, hE48, hE49, hE54⟩ := h_holds
  -- the composed `U16Compare` assertion's `Assumptions` (cl ranges on a real row, via the cores).
  have hCmpAs : U16CompareOperation.circuit.Assumptions
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ := by
    refine ⟨fun hir1 => ?_, hbin⟩
    have hr1 : input_is_real = 1 := hir1
    obtain ⟨hb, hcc⟩ := hbcc_imp hr1
    have h_sel : Selectors input_b input_cc
        ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags, input_cols_not_eq_inv,
          input_cols_comparison_limbs⟩ := by
      simp only [Selectors]
      exact ⟨bool_of_mul_pred hE6, bool_of_mul_pred hE8, bool_of_mul_pred hE10,
        bool_of_mul_pred hE12, bool_of_mul_pred hE14,
        by linear_combination hE19 - (input_b[3] - input_cc[3]) * hr1,
        by linear_combination hE27 - (input_b[2] - input_cc[2]) * hr1,
        by linear_combination hE35 - (input_b[1] - input_cc[1]) * hr1,
        by linear_combination hE43 - (input_b[0] - input_cc[0]) * hr1,
        by linear_combination hE48, by linear_combination hE49,
        by linear_combination hE54 + (1 - (input_cols_u16_flags[0] + input_cols_u16_flags[1]
          + input_cols_u16_flags[2] + input_cols_u16_flags[3]) - 1) * hr1⟩
    exact comparison_limbs_lt input_b input_cc hb hcc h_sel
  obtain ⟨hbitbool, hbitord⟩ := h_cmp hCmpAs
  exact ⟨⟨bool_of_mul_pred hE6, bool_of_mul_pred hE8, bool_of_mul_pred hE10, bool_of_mul_pred hE12,
      bool_of_mul_pred hE14, by linear_combination hE19, by linear_combination hE27,
      by linear_combination hE35, by linear_combination hE43, by linear_combination hE48,
      by linear_combination hE49, by linear_combination -hE54, hbitbool, hbitord⟩, Or.inr hCmpAs⟩

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbcc_imp, hbin⟩ := h_assumptions
  obtain ⟨hib, hicc, hicols, hir⟩ := h_input
  obtain ⟨_hibit, hiflags, _hineinv, hicl⟩ := hicols
  have eb : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_cols_u16_flags[i] = input_cols_u16_flags[i] := by
    intro i hi; rw [← hiflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env.toEnvironment input_var_cols_comparison_limbs[i]
        = input_cols_comparison_limbs[i] := by
    intro i hi; rw [← hicl]; simp only [Vector.getElem_map]
  obtain ⟨hf0, hf1, hf2, hf3, hsum, hs3, hs2, hs1, hs0, hcl0eq, hcl1eq, hinv, hbitbool, hbitord⟩ := h_spec
  -- the composed `U16Compare` assertion's `Assumptions` ∧ `Spec` (cl ranges via the cores on a real row).
  have h_sel_real : input_is_real = 1 → Selectors input_b input_cc
      ⟨⟨input_cols_u16_compare_operation_bit⟩, input_cols_u16_flags, input_cols_not_eq_inv,
        input_cols_comparison_limbs⟩ := by
    intro hir1
    rw [hir1] at hs3 hs2 hs1 hs0 hinv
    simp only [Selectors]
    exact ⟨hf0, hf1, hf2, hf3, hsum, by linear_combination hs3, by linear_combination hs2,
      by linear_combination hs1, by linear_combination hs0, hcl0eq, hcl1eq, by linear_combination -hinv⟩
  have hCmpAs : U16CompareOperation.circuit.Assumptions
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ :=
    ⟨fun hir1 => comparison_limbs_lt input_b input_cc (hbcc_imp hir1).1 (hbcc_imp hir1).2
      (h_sel_real hir1), hbin⟩
  have hCmpSpec : U16CompareOperation.circuit.Spec
      ⟨input_cols_comparison_limbs[0], input_cols_comparison_limbs[1],
        ⟨input_cols_u16_compare_operation_bit⟩, input_is_real⟩ := ⟨hbitbool, hbitord⟩
  simp only [id_eq, eb, ec, ef, ecl]
  refine ⟨⟨hCmpAs, hCmpSpec⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> ring
  · rcases hf0 with h | h <;> rw [h] <;> ring
  · rcases hf1 with h | h <;> rw [h] <;> ring
  · rcases hf2 with h | h <;> rw [h] <;> ring
  · rcases hf3 with h | h <;> rw [h] <;> ring
  · rcases hsum with h | h <;> rw [h] <;> ring
  · linear_combination hs3
  · linear_combination hs2
  · linear_combination hs1
  · linear_combination hs0
  · linear_combination hcl0eq
  · linear_combination hcl1eq
  · linear_combination -hinv

set_option linter.unusedSectionVars false in
/-- `Spec` at the all-zero column struct with the gate off (`is_real = 0`) — the inactive-row
discharge for composing chips whose populate leaves the struct zero (`DivRemChip`'s
`remainder_lt_operation` when the remainder-check multiplicity is `0`). Operands arbitrary. -/
theorem spec_zero (b cc : Word (ZMod p)) {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨b, cc, zeroCols, is_real⟩ : Inputs (ZMod p)) := by
  subst hr
  simp [Spec, zeroCols]

/-- SP1's `LtOperationUnsigned::eval` as a Clean-native `FormalAssertion`: composes
`U16CompareOperation` as a sub-assertion, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.LtOperationUnsigned
