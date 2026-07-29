import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.SubSpecs
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.OwnComplete
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes

/-! # `DivRemChip` — honest arithmetic-core completeness

This file keeps the generated forty-five-cell Mul witness blocks opaque while proving the
value-level contracts used by `DivRemCore.CoreSpec`.  A parent chip proof supplies only the flat
witness pins dumped by the populate closure; it never unfolds a generated Mul struct in a theorem
type.
-/

namespace SP1Clean.DivRemChip.CoreComplete

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option linter.unusedSectionVars false in
/-- Cell readback for the opaque evaluated Mul block.  The small `Eq.trans` is intentional: it
crosses the component-wise evaluator spelling to Clean's generic `varFromOffset` theorem without
asking unification to unfold the generated struct. -/
theorem evaluatedMulBlock_cell (env : Environment (ZMod p)) (off i : ℕ)
    (hi : i < size Extracted.MulOperation) :
    (ProvableType.toElements (evaluatedMulBlock env off))[i] = env.get (off + i) := by
  rw [evaluatedMulBlock]
  refine Eq.trans ?_ (getElem_toElements_eval_varFromOffset env off i hi)
  simp [circuit_norm]

set_option linter.unusedSectionVars false in
/-- Flat populate pins identify the opaque evaluated Mul block. -/
theorem evaluatedMulBlock_eq_of_pins (env : Environment (ZMod p)) (off : ℕ)
    (wit : Extracted.MulOperation (ZMod p))
    (hpop : ∀ i : Fin 45, env.get (off + ↑i) = (SubSpecs.mulWitnessElements wit).get i) :
    evaluatedMulBlock env off = wit := by
  apply SubSpecs.mul_cols_eq_of_pins env off _ wit
  · exact evaluatedMulBlock_cell env off
  · exact hpop

/-- The honestly populated lower product satisfies the exact Mul semantic contract embedded in
`DivRemCore.CoreSpec`. -/
theorem mulLowerSpec (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1) :
    MulOperation.Spec
      ⟨populateQuotComp B C f, cComp C f, populateMulLower ir B C f,
        ir, ir, 0, 0, 0, 0⟩ := by
  have hsumArg : ir + 0 + 0 + 0 + 0 = 0 ∨ ir + 0 + 0 + 0 + 0 = 1 := by
    simpa only [add_zero] using hbin
  rcases hbin with h0 | h1
  · rw [populateMulLower, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
    exact MulOperation.spec_zero (populateQuotComp B C f) (cComp C f) ir 0 0 0 0 h0
  · rw [populateMulLower, if_pos h1]
    exact MulOperation.spec_populate (populateQuotComp_isU64 B C f) (cComp_isU64 hcU f)
      ir 0 0 0 0 ir (Or.inr h1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      hsumArg

/-- The honestly populated upper product satisfies the high-half Mul contract.  The gate is one
exactly on real 64-bit variants and zero otherwise; the flag hypotheses are the chip's one-hot
prover contract. -/
theorem mulUpperSpec (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    MulOperation.Spec
      ⟨populateQuotComp B C f, cComp C f, populateMulUpper ir B C f,
        ir * (1 - (f[4] + f[5] + f[6] + f[7])), 0,
        f[0] + f[2], f[1] + f[3], 0, 0⟩ := by
  have hsums := flagSums_bool hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have he2sum := hsums.1
  have hg64 := hsums.2.2.1
  have hd_r := hsums.2.2.2.1
  have hdu_r := hsums.2.2.2.2
  have hsumArg : (0 : ZMod p) + (f[0] + f[2]) + (f[1] + f[3]) + 0 + 0 = 0
      ∨ (0 : ZMod p) + (f[0] + f[2]) + (f[1] + f[3]) + 0 + 0 = 1 := by
    rcases hg64 with h0 | h1
    · left
      linear_combination h0
    · right
      linear_combination h1
  by_cases hcond : ir = 1 ∧ f[0] + f[1] + f[2] + f[3] = 1
  · have he2zero : f[4] + f[5] + f[6] + f[7] = 0 := by
      linear_combination hsum - hcond.2
    have hgate : ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 1 := by
      rw [hcond.1, he2zero]
      ring_nf
    rw [populateMulUpper, if_pos hcond]
    exact MulOperation.spec_populate (populateQuotComp_isU64 B C f) (cComp_isU64 hcU f)
      0 (f[0] + f[2]) (f[1] + f[3]) 0 0
      (ir * (1 - (f[4] + f[5] + f[6] + f[7]))) (Or.inl rfl) hd_r hdu_r
      (Or.inl rfl) (Or.inl rfl) hsumArg
  · have hgate : ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 0 := by
      rcases hbin with h0 | h1
      · rw [h0, zero_mul]
      · rcases he2sum with he20 | he21
        · exact absurd ⟨h1, by linear_combination hsum - he20⟩ hcond
        · rw [h1, he21]
          ring_nf
    rw [populateMulUpper, if_neg hcond]
    exact MulOperation.spec_zero (populateQuotComp B C f) (cComp C f)
      0 (f[0] + f[2]) (f[1] + f[3]) 0 0 hgate

/-- The four low product limbs are glued to the honest `c_times_quotient` witness on both real and
canonical padding rows. -/
theorem lowerGlue (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hpad : ir = 0 → B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧
      f = #v[0, 1, 0, 0, 0, 0, 0, 0]) :
    (populateCtq B C f)[0] = (populateMulLower ir B C f).product[0]
        + (populateMulLower ir B C f).product[1] * 256 ∧
    (populateCtq B C f)[1] = (populateMulLower ir B C f).product[2]
        + (populateMulLower ir B C f).product[3] * 256 ∧
    (populateCtq B C f)[2] = (populateMulLower ir B C f).product[4]
        + (populateMulLower ir B C f).product[5] * 256 ∧
    (populateCtq B C f)[3] = (populateMulLower ir B C f).product[6]
        + (populateMulLower ir B C f).product[7] * 256 := by
  have hzero := populateCtq_padding_of_template hpad
  have hone := populateMulLower_product_pair B C f ir hcU
  rcases hbin with h0 | h1
  · rw [hzero h0 0 (by norm_num), hzero h0 1 (by norm_num), hzero h0 2 (by norm_num),
      hzero h0 3 (by norm_num), populateMulLower,
      if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
    simp [MulOperation.zeroCols]
  · exact ⟨hone h1 0 (by norm_num), hone h1 1 (by norm_num), hone h1 2 (by norm_num),
      hone h1 3 (by norm_num)⟩

/-- The four high product limbs are glued whenever the row selects a 64-bit variant. -/
theorem upperGlue (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hpad : ir = 0 → B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧
      f = #v[0, 1, 0, 0, 0, 0, 0, 0])
    (hg64 : f[0] + f[1] + f[2] + f[3] = 1) :
    (populateCtq B C f)[4] = (populateMulUpper ir B C f).product[8]
        + (populateMulUpper ir B C f).product[9] * 256 ∧
    (populateCtq B C f)[5] = (populateMulUpper ir B C f).product[10]
        + (populateMulUpper ir B C f).product[11] * 256 ∧
    (populateCtq B C f)[6] = (populateMulUpper ir B C f).product[12]
        + (populateMulUpper ir B C f).product[13] * 256 ∧
    (populateCtq B C f)[7] = (populateMulUpper ir B C f).product[14]
        + (populateMulUpper ir B C f).product[15] * 256 := by
  have hzero := populateCtq_padding_of_template hpad
  have hone := populateMulUpper_product_pair B C f ir hcU
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  rcases hbin with h0 | h1
  · rw [hzero h0 4 (by norm_num), hzero h0 5 (by norm_num), hzero h0 6 (by norm_num),
      hzero h0 7 (by norm_num), populateMulUpper,
      if_neg (fun hx => absurd (h0.symm.trans hx.1) zero_ne_one)]
    simp [MulOperation.zeroCols]
  · exact ⟨hone h1 hg64 0 (by norm_num), hone h1 hg64 1 (by norm_num),
      hone h1 hg64 2 (by norm_num), hone h1 hg64 3 (by norm_num)⟩

/-- Flat witness pins imply the folded product cluster for the evaluated chip row.  This is the
parent-proof boundary: its result keeps `ProductSpec` opaque, and only this small theorem crosses
from explicit row offsets to semantic Mul/glue facts. -/
theorem evaluatedProductSpec (env : ProverEnvironment (ZMod p)) (input : Var Inputs (ZMod p))
    (off : ℕ) (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hQC : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + i }) = populateQuotComp B C f)
    (hC : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + i }) = cComp C f)
    (hCtq : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 8 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + i }) = populateCtq B C f)
    (hMulLo : ∀ i : Fin 45, env.get (off + 8 + 4 + 4 + 4 + 4 + ↑i) =
      (SubSpecs.mulWitnessElements (populateMulLower ir B C f)).get i)
    (hMulUp : ∀ i : Fin 45, env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + ↑i) =
      (SubSpecs.mulWitnessElements (populateMulUpper ir B C f)).get i)
    (hIR : Expression.eval env.toEnvironment input.is_real = ir)
    (hIRNW : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (hF0 : env.get off = f[0]) (hF1 : env.get (off + 1) = f[1])
    (hF2 : env.get (off + 2) = f[2]) (hF3 : env.get (off + 3) = f[3])
    (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hpad : ir = 0 → B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧
      f = #v[0, 1, 0, 0, 0, 0, 0, 0]) :
    DivRemCore.ProductSpec (Eval.eval env (populatedRowAt input off)) := by
  have eQC : (Eval.eval env (populatedRowAt input off)).quotient_comp =
      populateQuotComp B C f := by
    rw [eval_divRemCols_quotientComp, populatedRowAt_quotientComp_eq]
    simpa +instances only [circuit_norm] using hQC
  have eC : (Eval.eval env (populatedRowAt input off)).c = cComp C f := by
    rw [eval_divRemCols_c, populatedRowAt_c_eq]
    simpa +instances only [circuit_norm] using hC
  have eCtq : (Eval.eval env (populatedRowAt input off)).c_times_quotient =
      populateCtq B C f := by
    rw [eval_divRemCols_ctq, populatedRowAt_ctq_eq]
    simpa +instances only [circuit_norm] using hCtq
  have eLo : (Eval.eval env (populatedRowAt input off)).c_times_quotient_lower =
      populateMulLower ir B C f :=
    (eval_populatedRowAt_mulLower env input off).trans
      (evaluatedMulBlock_eq_of_pins env.toEnvironment
        (off + 8 + 4 + 4 + 4 + 4) (populateMulLower ir B C f) hMulLo)
  have eUp : (Eval.eval env (populatedRowAt input off)).c_times_quotient_upper =
      populateMulUpper ir B C f :=
    (eval_populatedRowAt_mulUpper env input off).trans
      (evaluatedMulBlock_eq_of_pins env.toEnvironment
        (off + 8 + 4 + 4 + 4 + 4 + 45) (populateMulUpper ir B C f) hMulUp)
  have eIR : (Eval.eval env (populatedRowAt input off)).is_real = ir :=
    (eval_populatedRowAt_isReal env input off).trans hIR
  have eIRNW : (Eval.eval env (populatedRowAt input off)).is_real_not_word =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])) :=
    (eval_populatedRowAt_isRealNotWord env input off).trans hIRNW
  have eF0 : (Eval.eval env (populatedRowAt input off)).is_div = f[0] :=
    (eval_populatedRowAt_isDiv env input off).trans hF0
  have eF1 : (Eval.eval env (populatedRowAt input off)).is_divu = f[1] :=
    (eval_populatedRowAt_isDivu env input off).trans hF1
  have eF2 : (Eval.eval env (populatedRowAt input off)).is_rem = f[2] :=
    (eval_populatedRowAt_isRem env input off).trans hF2
  have eF3 : (Eval.eval env (populatedRowAt input off)).is_remu = f[3] :=
    (eval_populatedRowAt_isRemu env input off).trans hF3
  unfold DivRemCore.ProductSpec
  rw [eQC, eC, eLo, eUp, eIR, eIRNW, eF0, eF1, eF2, eF3]
  refine And.intro (mulLowerSpec ir B C f hcU hbin)
    (And.intro
      (mulUpperSpec ir B C f hcU hbin hf0 hf1 hf2 hf3
        hf4 hf5 hf6 hf7 hsum)
      (And.intro ?_ ?_))
  · rw [DivRemCore.LowerProductPlacement]
    rw [eIR, eCtq, eLo]; exact fun _ => lowerGlue ir B C f hcU hbin hpad
  · rw [DivRemCore.UpperProductPlacement]
    rw [eF0, eF1, eF2, eF3, eCtq, eUp]; exact upperGlue ir B C f hcU hbin hf0 hf1 hf2 hf3
      hf4 hf5 hf6 hf7 hsum hpad

/-! ## Own-assert evaluator boundary

These small projection lemmas deliberately evaluate only the nested generated column block named in
their result.  Running `circuit_norm` on the corresponding projection of the complete 246-column row
causes the simplifier to traverse every sibling block; the local lemmas avoid that normalization fanout.
-/

set_option linter.unusedSectionVars false in
private theorem evalU16MSB_msb (env : Environment (ZMod p))
    (cols : Extracted.U16MSBOperation (Expression (ZMod p))) :
    (Eval.eval env cols).msb = Expression.eval env cols.msb := by
  provable_struct_simp

set_option linter.unusedSectionVars false in
private theorem evalIsEqualWord_result (env : Environment (ZMod p))
    (cols : Extracted.IsEqualWordOperation (Expression (ZMod p))) :
    (Eval.eval env cols).is_diff_zero.result =
      Expression.eval env cols.is_diff_zero.result := by
  provable_struct_simp

set_option linter.unusedSectionVars false in
private theorem evalIsZeroWord_result (env : Environment (ZMod p))
    (cols : Extracted.IsZeroWordOperation (Expression (ZMod p))) :
    (Eval.eval env cols).result = Expression.eval env cols.result := by
  provable_struct_simp

set_option linter.unusedSectionVars false in
private theorem evalLtUnsigned_bit (env : Environment (ZMod p))
    (cols : Extracted.LtOperationUnsigned (Expression (ZMod p))) :
    (Eval.eval env cols).u16_compare_operation.bit =
      Expression.eval env cols.u16_compare_operation.bit := by
  provable_struct_simp

set_option linter.unusedSectionVars false in
private theorem evalAdd_value (env : Environment (ZMod p))
    (cols : Extracted.AddOperation (Expression (ZMod p))) :
    (Eval.eval env cols).value =
      Vector.map (Expression.eval env) cols.value := by
  provable_struct_simp
  exact ProvableType.eval_fields env _

set_option linter.unusedSectionVars false in
private theorem evalRType_opA0 (env : Environment (ZMod p))
    (cols : Extracted.RTypeReader (Expression (ZMod p))) :
    (Eval.eval env cols).op_a_0 = Expression.eval env cols.op_a_0 := by
  provable_struct_simp

set_option linter.unusedSectionVars false in
private theorem evalRType_opBPrev (env : Environment (ZMod p))
    (cols : Extracted.RTypeReader (Expression (ZMod p))) :
    (Eval.eval env cols).op_b_memory.prev_value =
      Vector.map (Expression.eval env) cols.op_b_memory.prev_value := by
  provable_struct_simp
  exact ProvableType.eval_fields env _

set_option linter.unusedSectionVars false in
private theorem evalRType_opCPrev (env : Environment (ZMod p))
    (cols : Extracted.RTypeReader (Expression (ZMod p))) :
    (Eval.eval env cols).op_c_memory.prev_value =
      Vector.map (Expression.eval env) cols.op_c_memory.prev_value := by
  provable_struct_simp
  exact ProvableType.eval_fields env _

/-- Raw satisfaction of the Rust own-assert list transports to the folded value-row contract without
unfolding `populatedRowAt` or the complete derived `ProvableStruct` evaluator. -/
theorem evaluatedOwnAssertsHold (env : ProverEnvironment (ZMod p))
    (colsV : Var DivRemChip.Columns (ZMod p))
    (h : ∀ e ∈ ownAsserts colsV,
      Expression.eval env.toEnvironment e = 0) :
    DivRemCore.OwnAssertsHold (Eval.eval env colsV) := by
  have hEval := (eval_divRemCols env colsV).symm
  apply DivRemCore.ownAssertsHold_of_forall env.toEnvironment h
  case pDiv => simpa only [CircuitType.eval_expr] using congrArg (·.is_div) hEval
  case pDivu => simpa only [CircuitType.eval_expr] using congrArg (·.is_divu) hEval
  case pRem => simpa only [CircuitType.eval_expr] using congrArg (·.is_rem) hEval
  case pRemu => simpa only [CircuitType.eval_expr] using congrArg (·.is_remu) hEval
  case pDivw => simpa only [CircuitType.eval_expr] using congrArg (·.is_divw) hEval
  case pRemw => simpa only [CircuitType.eval_expr] using congrArg (·.is_remw) hEval
  case pDivuw => simpa only [CircuitType.eval_expr] using congrArg (·.is_divuw) hEval
  case pRemuw => simpa only [CircuitType.eval_expr] using congrArg (·.is_remuw) hEval
  case pIr => simpa only [CircuitType.eval_expr] using congrArg (·.is_real) hEval
  case pIrnw => simpa only [CircuitType.eval_expr] using congrArg (·.is_real_not_word) hEval
  case pOv => simpa only [CircuitType.eval_expr] using congrArg (·.is_overflow) hEval
  case pBn => simpa only [CircuitType.eval_expr] using congrArg (·.b_neg) hEval
  case pBnno => simpa only [CircuitType.eval_expr] using congrArg (·.b_neg_not_overflow) hEval
  case pBnnno => simpa only [CircuitType.eval_expr] using congrArg (·.b_not_neg_not_overflow) hEval
  case pRn => simpa only [CircuitType.eval_expr] using congrArg (·.rem_neg) hEval
  case pCn => simpa only [CircuitType.eval_expr] using congrArg (·.c_neg) hEval
  case pAce => simpa only [CircuitType.eval_expr] using congrArg (·.abs_c_alu_event) hEval
  case pAre => simpa only [CircuitType.eval_expr] using congrArg (·.abs_rem_alu_event) hEval
  case pRcm =>
    simpa only [CircuitType.eval_expr] using congrArg (·.remainder_check_multiplicity) hEval
  case pBm =>
    exact (evalU16MSB_msb env.toEnvironment colsV.b_msb).symm.trans (congrArg (·.b_msb.msb) hEval)
  case pRm =>
    exact (evalU16MSB_msb env.toEnvironment colsV.rem_msb).symm.trans
      (congrArg (·.rem_msb.msb) hEval)
  case pCm =>
    exact (evalU16MSB_msb env.toEnvironment colsV.c_msb).symm.trans (congrArg (·.c_msb.msb) hEval)
  case pQm =>
    exact (evalU16MSB_msb env.toEnvironment colsV.quot_msb).symm.trans
      (congrArg (·.quot_msb.msb) hEval)
  case pOvb =>
    exact (evalIsEqualWord_result env.toEnvironment colsV.is_overflow_b).symm.trans
      (congrArg (·.is_overflow_b.is_diff_zero.result) hEval)
  case pOvc =>
    exact (evalIsEqualWord_result env.toEnvironment colsV.is_overflow_c).symm.trans
      (congrArg (·.is_overflow_c.is_diff_zero.result) hEval)
  case pIsc0 =>
    exact (evalIsZeroWord_result env.toEnvironment colsV.is_c_0).symm.trans
      (congrArg (·.is_c_0.result) hEval)
  case pLtb =>
    exact (evalLtUnsigned_bit env.toEnvironment colsV.remainder_lt_operation).symm.trans
      (congrArg (·.remainder_lt_operation.u16_compare_operation.bit) hEval)
  case pOpa0 =>
    exact (evalRType_opA0 env.toEnvironment colsV.adapter).symm.trans
      (congrArg (·.adapter.op_a_0) hEval)
  case vBpv =>
    exact (evalRType_opBPrev env.toEnvironment colsV.adapter).symm.trans
      (congrArg (·.adapter.op_b_memory.prev_value) hEval)
  case vCpv =>
    exact (evalRType_opCPrev env.toEnvironment colsV.adapter).symm.trans
      (congrArg (·.adapter.op_c_memory.prev_value) hEval)
  case vA => simpa only [ProvableType.eval_fields] using congrArg (·.a) hEval
  case vB => simpa only [ProvableType.eval_fields] using congrArg (·.b) hEval
  case vC => simpa only [ProvableType.eval_fields] using congrArg (·.c) hEval
  case vQ => simpa only [ProvableType.eval_fields] using congrArg (·.quotient) hEval
  case vQC => simpa only [ProvableType.eval_fields] using congrArg (·.quotient_comp) hEval
  case vR => simpa only [ProvableType.eval_fields] using congrArg (·.remainder) hEval
  case vRC => simpa only [ProvableType.eval_fields] using congrArg (·.remainder_comp) hEval
  case vAR => simpa only [ProvableType.eval_fields] using congrArg (·.abs_remainder) hEval
  case vAC => simpa only [ProvableType.eval_fields] using congrArg (·.abs_c) hEval
  case vMax => simpa only [ProvableType.eval_fields] using congrArg (·.max_abs_c_or_1) hEval
  case vCnegV =>
    exact (evalAdd_value env.toEnvironment colsV.c_neg_operation).symm.trans
      (congrArg (·.c_neg_operation.value) hEval)
  case vRnegV =>
    exact (evalAdd_value env.toEnvironment colsV.rem_neg_operation).symm.trans
      (congrArg (·.rem_neg_operation.value) hEval)
  case vCtq => simpa only [ProvableType.eval_fields] using congrArg (·.c_times_quotient) hEval
  case vCarry => simpa only [ProvableType.eval_fields] using congrArg (·.carry) hEval

/-- Honest populate pins imply the folded own-assert contract directly.  Keeping the raw
`∀ e ∈ ownAsserts ...` proposition internal is essential: substituting the 246-column
`populatedRowAt` expression into that proposition in the parent completeness proof crosses Lean's
kernel-size cliff.  (Its former 64M heartbeat ceiling was ~1600× over; floor ≤ 40000.) -/
theorem evaluatedOwnAssertsComplete (env : ProverEnvironment (ZMod p))
    (colsV : Var DivRemChip.Columns (ZMod p))
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hbU : B.isU64) (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hsr : f[0] + f[2] + f[4] + f[5] = 1 → ir = 1)
    (eF0 : Expression.eval env.toEnvironment colsV.is_div = f[0])
    (eF1 : Expression.eval env.toEnvironment colsV.is_divu = f[1])
    (eF2 : Expression.eval env.toEnvironment colsV.is_rem = f[2])
    (eF3 : Expression.eval env.toEnvironment colsV.is_remu = f[3])
    (eF4 : Expression.eval env.toEnvironment colsV.is_divw = f[4])
    (eF5 : Expression.eval env.toEnvironment colsV.is_remw = f[5])
    (eF6 : Expression.eval env.toEnvironment colsV.is_divuw = f[6])
    (eF7 : Expression.eval env.toEnvironment colsV.is_remuw = f[7])
    (eIR : Expression.eval env.toEnvironment colsV.is_real = ir)
    (eIRNW : Expression.eval env.toEnvironment colsV.is_real_not_word =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (eOV : Expression.eval env.toEnvironment colsV.is_overflow =
      populateIsOverflow ir B C f)
    (eBN : Expression.eval env.toEnvironment colsV.b_neg = populateBNeg B f)
    (eBNNO : Expression.eval env.toEnvironment colsV.b_neg_not_overflow =
      populateBNeg B f * (1 - populateIsOverflow ir B C f))
    (eBNNNO : Expression.eval env.toEnvironment colsV.b_not_neg_not_overflow =
      (1 - populateBNeg B f) * (1 - populateIsOverflow ir B C f))
    (eRN : Expression.eval env.toEnvironment colsV.rem_neg = populateRemNeg B C f)
    (eCN : Expression.eval env.toEnvironment colsV.c_neg = populateCNeg C f)
    (eACE : Expression.eval env.toEnvironment colsV.abs_c_alu_event =
      populateCNeg C f * ir)
    (eARE : Expression.eval env.toEnvironment colsV.abs_rem_alu_event =
      populateRemNeg B C f * ir)
    (eRCM : Expression.eval env.toEnvironment colsV.remainder_check_multiplicity =
      ltGate ir C f)
    (eBM : Expression.eval env.toEnvironment colsV.b_msb.msb = bMsbCell B f)
    (eCM : Expression.eval env.toEnvironment colsV.c_msb.msb = cMsbCell C f)
    (eRM : Expression.eval env.toEnvironment colsV.rem_msb.msb = remMsbCell B C f)
    (eQM : Expression.eval env.toEnvironment colsV.quot_msb.msb = quotMsbCell B C f)
    (eBvec : Vector.map (Expression.eval env.toEnvironment) colsV.b = bComp B f)
    (eCvec : Vector.map (Expression.eval env.toEnvironment) colsV.c = cComp C f)
    (eQvec : Vector.map (Expression.eval env.toEnvironment) colsV.quotient =
      populateQuotient B C f)
    (eQCvec : Vector.map (Expression.eval env.toEnvironment) colsV.quotient_comp =
      populateQuotComp B C f)
    (eRvec : Vector.map (Expression.eval env.toEnvironment) colsV.remainder =
      populateRemainder B C f)
    (eRCvec : Vector.map (Expression.eval env.toEnvironment) colsV.remainder_comp =
      populateRemComp B C f)
    (eAvec : Vector.map (Expression.eval env.toEnvironment) colsV.a = populateA B C f)
    (eABSCvec : Vector.map (Expression.eval env.toEnvironment) colsV.abs_c = populateAbsC C f)
    (eABSRvec : Vector.map (Expression.eval env.toEnvironment) colsV.abs_remainder =
      populateAbsRem B C f)
    (eMAXvec : Vector.map (Expression.eval env.toEnvironment) colsV.max_abs_c_or_1 =
      populateMaxAbsCOr1 C f)
    (eCTQvec : Vector.map (Expression.eval env.toEnvironment) colsV.c_times_quotient =
      populateCtq B C f)
    (eCARRYvec : Vector.map (Expression.eval env.toEnvironment) colsV.carry =
      populateCarry B C f)
    (eCNEGVvec : Vector.map (Expression.eval env.toEnvironment) colsV.c_neg_operation.value =
      wCnegWitness ir C f)
    (eRNEGVvec : Vector.map (Expression.eval env.toEnvironment) colsV.rem_neg_operation.value =
      wRnegWitness ir B C f)
    (eBPVvec : Vector.map (Expression.eval env.toEnvironment)
      colsV.adapter.op_b_memory.prev_value = B)
    (eCPVvec : Vector.map (Expression.eval env.toEnvironment)
      colsV.adapter.op_c_memory.prev_value = C)
    (eOVBR : Expression.eval env.toEnvironment colsV.is_overflow_b.is_diff_zero.result =
      (ovbWitness ir B f).is_diff_zero.result)
    (eOVCR : Expression.eval env.toEnvironment colsV.is_overflow_c.is_diff_zero.result =
      (ovcWitness ir C f).is_diff_zero.result)
    (eISC0 : Expression.eval env.toEnvironment colsV.is_c_0.result =
      (isC0Witness C f).result)
    (eLTBIT : Expression.eval env.toEnvironment
      colsV.remainder_lt_operation.u16_compare_operation.bit = (ltBitWitness ir B C f)[0])
    (eOPA0 : Expression.eval env.toEnvironment colsV.adapter.op_a_0 = 0) :
    DivRemCore.OwnAssertsHold (Eval.eval env colsV) := by
  apply evaluatedOwnAssertsHold env colsV
  exact ownAsserts_complete env.toEnvironment colsV ir B C f hbU hcU hbin
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hsr eF0 eF1 eF2 eF3 eF4 eF5 eF6 eF7
    eIR eIRNW eOV eBN eBNNO eBNNNO eRN eCN eACE eARE eRCM eBM eCM eRM eQM
    eBvec eCvec eQvec eQCvec eRvec eRCvec eAvec eABSCvec eABSRvec eMAXvec
    eCTQvec eCARRYvec eCNEGVvec eRNEGVvec eBPVvec eCPVvec eOVBR eOVCR eISC0
    eLTBIT eOPA0

/-- Flat witness-layout form of `evaluatedOwnAssertsComplete`.  Its hypotheses mention only input
expressions and local-witness offsets, so the parent chip proof never has to elaborate a projection
through the complete `populatedRowAt` term.  (Its former 64M heartbeat ceiling was ~1600× over.) -/
theorem evaluatedPopulatedOwnAssertsComplete
    (env : ProverEnvironment (ZMod p)) (input : Var Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hbU : B.isU64) (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hsr : f[0] + f[2] + f[4] + f[5] = 1 → ir = 1)
    (hF0 : env.get off = f[0]) (hF1 : env.get (off + 1) = f[1])
    (hF2 : env.get (off + 2) = f[2]) (hF3 : env.get (off + 3) = f[3])
    (hF4 : env.get (off + 4) = f[4]) (hF5 : env.get (off + 5) = f[5])
    (hF6 : env.get (off + 6) = f[6]) (hF7 : env.get (off + 7) = f[7])
    (hIR : Expression.eval env.toEnvironment input.is_real = ir)
    (hIRNW : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (hOV : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45) =
      populateIsOverflow ir B C f)
    (hBN : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 1) = populateBNeg B f)
    (hBNNO : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 2) =
      populateBNeg B f * (1 - populateIsOverflow ir B C f))
    (hBNNNO : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 3) =
      (1 - populateBNeg B f) * (1 - populateIsOverflow ir B C f))
    (hRN : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5) = populateRemNeg B C f)
    (hCN : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 6) = populateCNeg C f)
    (hACE : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4) = populateCNeg C f * ir)
    (hARE : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 1) = populateRemNeg B C f * ir)
    (hRCM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 2) = ltGate ir C f)
    (hBM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4) = bMsbCell B f)
    (hCM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1) = cMsbCell C f)
    (hRM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1) =
      remMsbCell B C f)
    (hQM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 + 1) =
      quotMsbCell B C f)
    (hBvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + i }) = bComp B f)
    (hCvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + i }) = cComp C f)
    (hQvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + i }) =
      populateQuotient B C f)
    (hQCvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + i }) = populateQuotComp B C f)
    (hRvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + i }) =
      populateRemainder B C f)
    (hRCvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + i }) = populateRemComp B C f)
    (hAvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + i }) = populateA B C f)
    (hABSCvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + i }) = populateAbsC C f)
    (hABSRvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) = populateAbsRem B C f)
    (hMAXvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + i }) = populateMaxAbsCOr1 C f)
    (hCTQvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 8 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + i }) =
      populateCtq B C f)
    (hCARRYvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 8 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + i }) =
      populateCarry B C f)
    (hCNEGVvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + i }) = wCnegWitness ir C f)
    (hRNEGVvec : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + i }) = wRnegWitness ir B C f)
    (hBPVvec : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_b_memory.prev_value = B)
    (hCPVvec : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_c_memory.prev_value = C)
    (hOVB : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + ↑i) =
        (SubSpecs.eqWordWitnessElements (ovbWitness ir B f)).get i)
    (hOVC : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + ↑i) =
        (SubSpecs.eqWordWitnessElements (ovcWitness ir C f)).get i)
    (hISC0 : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + ↑i) =
        (SubSpecs.isZeroWitnessElements (p := p) (isC0Witness C f)).get i)
    (hLTBIT : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1) = (ltBitWitness ir B C f)[0])
    (hOPA0 : Expression.eval env.toEnvironment input.adapter.op_a_0 = 0) :
    DivRemCore.OwnAssertsHold (Eval.eval env (populatedRowAt input off)) := by
  apply evaluatedOwnAssertsComplete env (populatedRowAt input off) ir B C f hbU hcU hbin
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hsr
  · rw [populatedRowAt_isDiv_eq]; simpa only [circuit_norm] using hF0
  · rw [populatedRowAt_isDivu_eq]; simpa only [circuit_norm] using hF1
  · rw [populatedRowAt_isRem_eq]; simpa only [circuit_norm] using hF2
  · rw [populatedRowAt_isRemu_eq]; simpa only [circuit_norm] using hF3
  · rw [populatedRowAt_isDivw_eq]; simpa only [circuit_norm] using hF4
  · rw [populatedRowAt_isRemw_eq]; simpa only [circuit_norm] using hF5
  · rw [populatedRowAt_isDivuw_eq]; simpa only [circuit_norm] using hF6
  · rw [populatedRowAt_isRemuw_eq]; simpa only [circuit_norm] using hF7
  · rw [populatedRowAt_isReal_eq]; exact hIR
  · rw [populatedRowAt_isRealNotWord_eq]; simpa only [circuit_norm] using hIRNW
  · rw [populatedRowAt_isOverflow_eq]; simpa only [circuit_norm] using hOV
  · rw [populatedRowAt_bNeg_eq]; simpa only [circuit_norm] using hBN
  · rw [populatedRowAt_bNegNotOverflow_eq]; simpa only [circuit_norm] using hBNNO
  · rw [populatedRowAt_bNotNegNotOverflow_eq]; simpa only [circuit_norm] using hBNNNO
  · rw [populatedRowAt_remNeg_eq]; simpa only [circuit_norm] using hRN
  · rw [populatedRowAt_cNeg_eq]; simpa only [circuit_norm] using hCN
  · rw [populatedRowAt_absCEvent_eq]; simpa only [circuit_norm] using hACE
  · rw [populatedRowAt_absRemEvent_eq]; simpa only [circuit_norm] using hARE
  · rw [populatedRowAt_remainderCheckMultiplicity_eq]; simpa only [circuit_norm] using hRCM
  · rw [populatedRowAt_bMsb_eq]; simpa only [circuit_norm] using hBM
  · rw [populatedRowAt_cMsb_eq]; simpa only [circuit_norm] using hCM
  · rw [populatedRowAt_remMsb_eq]; simpa only [circuit_norm] using hRM
  · rw [populatedRowAt_quotMsb_eq]; simpa only [circuit_norm] using hQM
  · rw [populatedRowAt_b_eq]; exact hBvec
  · rw [populatedRowAt_c_eq]; exact hCvec
  · rw [populatedRowAt_quotient_eq]; exact hQvec
  · rw [populatedRowAt_quotientComp_eq]; exact hQCvec
  · rw [populatedRowAt_remainder_eq]; exact hRvec
  · rw [populatedRowAt_remainderComp_eq]; exact hRCvec
  · rw [populatedRowAt_a_eq]; exact hAvec
  · rw [populatedRowAt_absC_eq]; exact hABSCvec
  · rw [populatedRowAt_absRemainder_eq]; exact hABSRvec
  · rw [populatedRowAt_maxAbsCOr1_eq]; exact hMAXvec
  · rw [populatedRowAt_ctq_eq]; exact hCTQvec
  · rw [populatedRowAt_carry_eq]; exact hCARRYvec
  · rw [populatedRowAt_cNegValue_eq]; exact hCNEGVvec
  · rw [populatedRowAt_remNegValue_eq]; exact hRNEGVvec
  · rw [populatedRowAt_adapter_eq]; exact hBPVvec
  · rw [populatedRowAt_adapter_eq]; exact hCPVvec
  · rw [populatedRowAt_isOverflowB_eq]
    have hS : (ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
          (Vector.mapRange 11 fun j =>
            env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + j))) =
        ovbWitness ir B f := by
      refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
      rw [ProvableType.toElements_fromElements]
      exact (Vector.getElem_mapRange i hi).trans (hOVB ⟨i, hi⟩)
    rw [← hS]
    simp only [iseqword_result_proj, circuit_norm]
  · rw [populatedRowAt_isOverflowC_eq]
    have hS : (ProvableType.fromElements (M := Extracted.IsEqualWordOperation)
          (Vector.mapRange 11 fun j =>
            env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + j))) =
        ovcWitness ir C f := by
      refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
      rw [ProvableType.toElements_fromElements]
      exact (Vector.getElem_mapRange i hi).trans (hOVC ⟨i, hi⟩)
    rw [← hS]
    simp only [iseqword_result_proj, circuit_norm]
  · rw [populatedRowAt_isC0_eq]
    have hS : (ProvableType.fromElements (M := Extracted.IsZeroWordOperation)
          (Vector.map (fun x => Expression.eval env.toEnvironment x)
            (Vector.mapRange 11 fun j => var { index :=
              off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + j }))) =
        isC0Witness C f := by
      exact SubSpecs.eval_isZeroBlock_eq env.toEnvironment
        (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11)
        (isC0Witness C f) hISC0
    rw [← hS]
    simp only [iszeroword_result_proj, circuit_norm]
  · rw [populatedRowAt_ltBit_eq]; simpa only [circuit_norm] using hLTBIT
  · rw [populatedRowAt_adapter_eq]; exact hOPA0

/-- Honest flag pins imply the complete folded selection contract. -/
theorem evaluatedSelectionEvidenceSpec
    (env : ProverEnvironment (ZMod p)) (input : Var Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (f : Vector (ZMod p) 8)
    (hIR : Expression.eval env.toEnvironment input.is_real = ir)
    (hIRNW : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (hF0 : env.get off = f[0]) (hF1 : env.get (off + 1) = f[1])
    (hF2 : env.get (off + 2) = f[2]) (hF3 : env.get (off + 3) = f[3])
    (hF4 : env.get (off + 4) = f[4]) (hF5 : env.get (off + 5) = f[5])
    (hF6 : env.get (off + 6) = f[6]) (hF7 : env.get (off + 7) = f[7])
    (hbin : ir = 0 ∨ ir = 1)
    (hirnwbin : ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 0 ∨
      ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    DivRemCore.SelectionEvidenceSpec (Eval.eval env (populatedRowAt input off)) := by
  let cols := Eval.eval env (populatedRowAt input off)
  have eIR : cols.is_real = ir := (eval_populatedRowAt_isReal env input off).trans hIR
  have eIRNW : cols.is_real_not_word = ir * (1 - (f[4] + f[5] + f[6] + f[7])) :=
    (eval_populatedRowAt_isRealNotWord env input off).trans hIRNW
  have eF0 : cols.is_div = f[0] := (eval_populatedRowAt_isDiv env input off).trans hF0
  have eF1 : cols.is_divu = f[1] := (eval_populatedRowAt_isDivu env input off).trans hF1
  have eF2 : cols.is_rem = f[2] := (eval_populatedRowAt_isRem env input off).trans hF2
  have eF3 : cols.is_remu = f[3] := (eval_populatedRowAt_isRemu env input off).trans hF3
  have eF4 : cols.is_divw = f[4] := (eval_populatedRowAt_isDivw env input off).trans hF4
  have eF5 : cols.is_remw = f[5] := (eval_populatedRowAt_isRemw env input off).trans hF5
  have eF6 : cols.is_divuw = f[6] := (eval_populatedRowAt_isDivuw env input off).trans hF6
  have eF7 : cols.is_remuw = f[7] := (eval_populatedRowAt_isRemuw env input off).trans hF7
  have hsumField : cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem +
      cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1 := by
    rw [eF0, eF1, eF2, eF3, eF4, eF5, eF6, eF7]
    linear_combination hsum
  have hsumFlags : f[1] + f[3] + f[0] + f[2] + f[4] + f[5] + f[6] + f[7] = 1 := by
    linear_combination hsum
  have hvals := flags_val_sum hf1 hf3 hf0 hf2 hf4 hf5 hf6 hf7 hsumFlags
  have hsumVal : cols.is_div.val + cols.is_divu.val + cols.is_rem.val + cols.is_remu.val +
      cols.is_divw.val + cols.is_remw.val + cols.is_divuw.val + cols.is_remuw.val = 1 := by
    rw [eF0, eF1, eF2, eF3, eF4, eF5, eF6, eF7]
    omega
  change DivRemCore.SelectionEvidenceSpec cols
  simp only [DivRemCore.SelectionEvidenceSpec]
  exact ⟨by simpa only [eIR] using hbin, by simpa only [eIRNW] using hirnwbin,
    by simpa only [eF0] using hf0, by simpa only [eF1] using hf1,
    by simpa only [eF2] using hf2, by simpa only [eF3] using hf3,
    by simpa only [eF4] using hf4, by simpa only [eF5] using hf5,
    by simpa only [eF6] using hf6, by simpa only [eF7] using hf7, hsumField,
    fun _ => DivRemCore.selection_of_flags
      (by simpa only [eF0] using hf0) (by simpa only [eF1] using hf1)
      (by simpa only [eF2] using hf2) (by simpa only [eF3] using hf3)
      (by simpa only [eF4] using hf4) (by simpa only [eF5] using hf5)
      (by simpa only [eF6] using hf6) (by simpa only [eF7] using hf7) hsumVal⟩

/-- Honest arithmetic witness vectors satisfy every range fact exposed by the folded core
contract.  The populate values are all in range unconditionally; the AIR-facing gates only weaken
these facts for non-real or non-word rows. -/
theorem evaluatedRangeSpec
    (env : ProverEnvironment (ZMod p)) (input : Var Inputs (ZMod p)) (off : ℕ)
    (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) (hcU : C.isU64)
    (hCTQ : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 8 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + i }) =
      populateCtq B C f)
    (hCarry : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 8 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + i }) =
      populateCarry B C f)
    (hRC : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + i }) = populateRemComp B C f)
    (hAC : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + i }) = populateAbsC C f)
    (hAR : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) = populateAbsRem B C f)
    (hQ : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + i }) =
      populateQuotient B C f)
    (hR : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45
        + 7 + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + i }) =
      populateRemainder B C f)
    (hRN : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 5) = populateRemNeg B C f) :
    DivRemCore.RangeSpec (Eval.eval env (populatedRowAt input off)) := by
  let cols := Eval.eval env (populatedRowAt input off)
  have eCTQ : cols.c_times_quotient = populateCtq B C f := by
    dsimp only [cols]; rw [eval_divRemCols_ctq, populatedRowAt_ctq_eq]
    simpa +instances only [circuit_norm] using hCTQ
  have eCarry : cols.carry = populateCarry B C f := by
    dsimp only [cols]; rw [eval_divRemCols_carry, populatedRowAt_carry_eq]
    simpa +instances only [circuit_norm] using hCarry
  have eRC : cols.remainder_comp = populateRemComp B C f := by
    dsimp only [cols]; rw [eval_divRemCols_remainderComp, populatedRowAt_remainderComp_eq]
    simpa +instances only [circuit_norm] using hRC
  have eAC : cols.abs_c = populateAbsC C f := by
    dsimp only [cols]; rw [eval_divRemCols_absC, populatedRowAt_absC_eq]
    simpa +instances only [circuit_norm] using hAC
  have eAR : cols.abs_remainder = populateAbsRem B C f := by
    dsimp only [cols]; rw [eval_divRemCols_absRemainder, populatedRowAt_absRemainder_eq]
    simpa +instances only [circuit_norm] using hAR
  have eQ : cols.quotient = populateQuotient B C f := by
    dsimp only [cols]; rw [eval_divRemCols_quotient, populatedRowAt_quotient_eq]
    simpa +instances only [circuit_norm] using hQ
  have eR : cols.remainder = populateRemainder B C f := by
    dsimp only [cols]; rw [eval_divRemCols_remainder, populatedRowAt_remainder_eq]
    simpa +instances only [circuit_norm] using hR
  have eRN : cols.rem_neg = populateRemNeg B C f :=
    (eval_populatedRowAt_remNeg env input off).trans hRN
  change DivRemCore.RangeSpec cols
  simp only [DivRemCore.RangeSpec, Nat.cast_ofNat]
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eCTQ, eRC, eCarry, chain_residue_field_0]; exact chainResidue_field_val_lt B C f 0
  · rw [eCTQ, eRC, eCarry]
    have hcr := chain_residue_field_1 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 1
  · rw [eCTQ, eRC, eCarry]
    have hcr := chain_residue_field_2 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 2
  · rw [eCTQ, eRC, eCarry]
    have hcr := chain_residue_field_3 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 3
  · rw [eCTQ, eRN, eCarry]
    have hcr := chain_residue_field_4 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 4
  · rw [eCTQ, eRN, eCarry]
    have hcr := chain_residue_field_5 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 5
  · rw [eCTQ, eRN, eCarry]
    have hcr := chain_residue_field_6 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 6
  · rw [eCTQ, eRN, eCarry]
    have hcr := chain_residue_field_7 B C f
    push_cast at hcr; rw [hcr]; exact chainResidue_field_val_lt B C f 7
  · intro i hi
    rw [eAC]; exact (populateAbsC_isU64 hcU f) ⟨i, hi⟩
  · intro i hi
    rw [eAR]; exact (populateAbsRem_isU64 B C f) ⟨i, hi⟩
  · intro i hi
    rw [eQ]; exact (populateQuotient_isU64 B C f) ⟨i, hi⟩
  · intro i hi
    rw [eR]; exact (populateRemainder_isU64 B C f) ⟨i, hi⟩
  · intro i hi
    rw [eCTQ]; exact populateCtq_val_lt B C f i hi
end SP1Clean.DivRemChip.CoreComplete
