import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Completeness.SubSpecs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Abs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Signs

/-! # `DivRemChip` — honest comparison-view completeness

This file isolates the semantic half of the comparison/sign cluster's completeness proof from the
large chip theorem. `honestInputs` is the value-level view produced by the DivRem populate
functions; `honestSpec` proves its fifteen folded sub-operation contracts. The parent proof only
has to show that the witness cells evaluate to this view.
-/

namespace SP1Clean.DivRemChip.CompareComplete

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

-- Keep the three nested eleven-cell blocks flat while evaluating the compact view, matching the
-- parent completeness driver's selective witness-block normalization.
attribute [local circuit_norm ↓ 100000] ProvableType.eval_fromElements

/-- The comparison/sign child input assembled from the honest DivRem populate values. -/
def honestInputs (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8) :
    DivRemCompare.Inputs (ZMod p) :=
  { op_b_prev_value := B,
    op_c_prev_value := C,
    c := cComp C f,
    quotient := populateQuotient B C f,
    remainder_comp := populateRemComp B C f,
    remainder := populateRemainder B C f,
    abs_remainder := populateAbsRem B C f,
    abs_c := populateAbsC C f,
    max_abs_c_or_1 := populateMaxAbsCOr1 C f,
    is_c_0 := isC0Witness C f,
    is_overflow_b := ovbWitness ir B f,
    is_overflow_c := ovcWitness ir C f,
    c_neg_operation := ⟨wCnegWitness ir C f⟩,
    rem_neg_operation := ⟨wRnegWitness ir B C f⟩,
    remainder_lt_operation :=
      ⟨⟨(ltBitWitness ir B C f)[0]⟩, ltFlagsWitness ir B C f,
        (ltNotEqInvWitness ir B C f)[0], ltClWitness ir B C f⟩,
    b_msb := ⟨bMsbCell B f⟩,
    rem_msb := ⟨remMsbCell B C f⟩,
    c_msb := ⟨cMsbCell C f⟩,
    quot_msb := ⟨quotMsbCell B C f⟩,
    is_divw := f[4],
    is_remw := f[5],
    is_divuw := f[6],
    is_remuw := f[7],
    is_real_not_word := ir * (1 - (f[4] + f[5] + f[6] + f[7])),
    abs_c_alu_event := populateCNeg C f * ir,
    abs_rem_alu_event := populateRemNeg B C f * ir,
    is_real := ir,
    remainder_check_multiplicity := ltGate ir C f }

private structure WordView (F : Type) where
  op_b_prev_value : Word F
  op_c_prev_value : Word F
  c : Word F
  quotient : Word F
  remainder_comp : Word F
  remainder : Word F
  abs_remainder : Word F
  abs_c : Word F
  max_abs_c_or_1 : Word F

private structure OperationView (F : Type) where
  is_c_0 : Extracted.IsZeroWordOperation F
  is_overflow_b : Extracted.IsEqualWordOperation F
  is_overflow_c : Extracted.IsEqualWordOperation F
  c_neg_operation : Extracted.AddOperation F
  rem_neg_operation : Extracted.AddOperation F
  remainder_lt_operation : Extracted.LtOperationUnsigned F

private structure MsbView (F : Type) where
  b_msb : Extracted.U16MSBOperation F
  rem_msb : Extracted.U16MSBOperation F
  c_msb : Extracted.U16MSBOperation F
  quot_msb : Extracted.U16MSBOperation F

private structure ScalarView (F : Type) where
  is_divw : F
  is_remw : F
  is_divuw : F
  is_remuw : F
  is_real_not_word : F
  abs_c_alu_event : F
  abs_rem_alu_event : F
  is_real : F
  remainder_check_multiplicity : F

private def wordView {F : Type} (x : DivRemCompare.Inputs F) : WordView F :=
  ⟨x.op_b_prev_value, x.op_c_prev_value, x.c, x.quotient, x.remainder_comp,
    x.remainder, x.abs_remainder, x.abs_c, x.max_abs_c_or_1⟩

private def operationView {F : Type} (x : DivRemCompare.Inputs F) : OperationView F :=
  ⟨x.is_c_0, x.is_overflow_b, x.is_overflow_c, x.c_neg_operation,
    x.rem_neg_operation, x.remainder_lt_operation⟩

/-- Evaluate only the six components used by `operationView`.  This generic projection lemma is
the important performance boundary: reducing `Eval.eval` on the concrete populated row would
otherwise evaluate every component of the compact comparison input before projecting these six. -/
private theorem operationView_eval {F : Type} [FiniteField F]
    (env : Environment F) (x : DivRemCompare.Inputs (Expression F)) :
    operationView (Eval.eval env x) =
      ({ is_c_0 := Eval.eval env x.is_c_0,
         is_overflow_b := Eval.eval env x.is_overflow_b,
         is_overflow_c := Eval.eval env x.is_overflow_c,
         c_neg_operation := Eval.eval env x.c_neg_operation,
         rem_neg_operation := Eval.eval env x.rem_neg_operation,
         remainder_lt_operation := Eval.eval env x.remainder_lt_operation } :
        OperationView F) := by
  rw [SP1Clean.DivRemCompare.eval_inputs]
  rfl

private theorem operationView_ext {F : Type} {x y : OperationView F}
    (h0 : x.is_c_0 = y.is_c_0)
    (h1 : x.is_overflow_b = y.is_overflow_b)
    (h2 : x.is_overflow_c = y.is_overflow_c)
    (h3 : x.c_neg_operation = y.c_neg_operation)
    (h4 : x.rem_neg_operation = y.rem_neg_operation)
    (h5 : x.remainder_lt_operation = y.remainder_lt_operation) : x = y := by
  rcases x with ⟨⟩
  rcases y with ⟨⟩
  simp_all only

private def msbView {F : Type} (x : DivRemCompare.Inputs F) : MsbView F :=
  ⟨x.b_msb, x.rem_msb, x.c_msb, x.quot_msb⟩

private def scalarView {F : Type} (x : DivRemCompare.Inputs F) : ScalarView F :=
  ⟨x.is_divw, x.is_remw, x.is_divuw, x.is_remuw, x.is_real_not_word,
    x.abs_c_alu_event, x.abs_rem_alu_event, x.is_real, x.remainder_check_multiplicity⟩

private theorem inputs_eq_of_views {F : Type} {x y : DivRemCompare.Inputs F}
    (hw : wordView x = wordView y) (ho : operationView x = operationView y)
    (hm : msbView x = msbView y) (hs : scalarView x = scalarView y) : x = y := by
  rcases x with ⟨⟩
  rcases y with ⟨⟩
  simp only [wordView, operationView, msbView, scalarView] at hw ho hm hs ⊢
  aesop

private theorem evaluatedWordView_eq (env : ProverEnvironment (ZMod p))
    (input : Var SP1Clean.DivRemChip.Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hbpv : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_b_memory.prev_value = B)
    (hcpv : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_c_memory.prev_value = C)
    (hCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + i }) :
        Word (ZMod p)) = cComp C f)
    (hABSCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + i }) :
        Word (ZMod p)) = populateAbsC C f)
    (hABSRvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) :
        Word (ZMod p)) = populateAbsRem B C f)
    (hRCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + i }) : Word (ZMod p)) = populateRemComp B C f)
    (hMAXvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + i }) : Word (ZMod p)) = populateMaxAbsCOr1 C f)
    (hRvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7
        + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + i }) :
        Word (ZMod p)) = populateRemainder B C f)
    (hQvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7
        + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + i }) :
        Word (ZMod p)) = populateQuotient B C f) :
    wordView (Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt input off))) =
      wordView (honestInputs ir B C f) := by
  unfold wordView
  simp +instances only [DivRemCompare.Inputs.ofCols, populatedRowAt,
    honestInputs, circuit_norm, hbpv, hcpv, hCvec, hABSCvec, hABSRvec, hRCvec,
    hMAXvec, hRvec, hQvec]

private theorem evaluatedMsbView_eq (env : ProverEnvironment (ZMod p))
    (input : Var SP1Clean.DivRemChip.Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hBM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4) = bMsbCell B f)
    (hCM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1) = cMsbCell C f)
    (hRM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1) =
        remMsbCell B C f)
    (hQM : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + 4 + 1 + 1 + 1) =
        quotMsbCell B C f) :
    msbView (Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt input off))) =
      msbView (honestInputs ir B C f) := by
  unfold msbView
  simp +instances only [DivRemCompare.Inputs.ofCols, populatedRowAt,
    honestInputs, circuit_norm, hBM, hCM, hRM, hQM]

private theorem evaluatedScalarView_eq (env : ProverEnvironment (ZMod p))
    (input : Var SP1Clean.DivRemChip.Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hir : Expression.eval env.toEnvironment input.is_real = ir)
    (hfl4 : env.get (off + 4) = f[4]) (hfl5 : env.get (off + 5) = f[5])
    (hfl6 : env.get (off + 6) = f[6]) (hfl7 : env.get (off + 7) = f[7])
    (hSC4 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (hMISC0 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4) = populateCNeg C f * ir)
    (hMISC1 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 1) = populateRemNeg B C f * ir)
    (hMISC2 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 2) = ltGate ir C f) :
    scalarView (Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt input off))) =
      scalarView (honestInputs ir B C f) := by
  unfold scalarView
  simp +instances only [DivRemCompare.Inputs.ofCols, populatedRowAt,
    honestInputs, circuit_norm, hir, hfl4, hfl5, hfl6, hfl7, hSC4,
    hMISC0, hMISC1, hMISC2]

private theorem evaluatedOperationView_eq (env : ProverEnvironment (ZMod p))
    (input : Var SP1Clean.DivRemChip.Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hWCNEGvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = wCnegWitness ir C f)
    (hWRNEGvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = wRnegWitness ir B C f)
    (hLTCLvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 2 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + i }) : Vector (ZMod p) 2) =
        ltClWitness ir B C f)
    (hLTFvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + i }) : Vector (ZMod p) 4) =
        ltFlagsWitness ir B C f)
    (hNEI : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4) = (ltNotEqInvWitness ir B C f)[0])
    (hBIT : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1) = (ltBitWitness ir B C f)[0])
    (hOVB : ∀ i : Fin 11, env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + ↑i) =
      (SubSpecs.eqWordWitnessElements (ovbWitness ir B f)).get i)
    (hOVC : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + ↑i) =
        (SubSpecs.eqWordWitnessElements (ovcWitness ir C f)).get i)
    (hISC0 : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + ↑i) =
        (SubSpecs.isZeroWitnessElements (isC0Witness C f)).get i) :
    operationView (Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt input off))) =
      operationView (honestInputs ir B C f) := by
  have hEvalOVB := SubSpecs.eval_eqWordFieldsBlock_eq env.toEnvironment
    (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8) (ovbWitness ir B f) hOVB
  have hEvalOVC := SubSpecs.eval_eqWordFieldsBlock_eq env.toEnvironment
    (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11) (ovcWitness ir C f) hOVC
  have hEvalISC0 := SubSpecs.eval_isZeroFieldsBlock_eq env.toEnvironment
    (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11)
    (isC0Witness C f) hISC0
  rw [CircuitType.eval_expression_prover_to_verifier, operationView_eval]
  apply operationView_ext
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt, honestInputs]
    exact hEvalISC0
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt, honestInputs]
    exact hEvalOVB
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt, honestInputs]
    exact hEvalOVC
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt,
      honestInputs, circuit_norm, hWCNEGvec]
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt,
      honestInputs, circuit_norm, hWRNEGvec]
  · simp +instances only [operationView, DivRemCompare.Inputs.ofCols, populatedRowAt,
      honestInputs, circuit_norm, hLTCLvec, hLTFvec, hNEI, hBIT]

/-- The compact comparison view evaluated from the chip's witnessed row is exactly the honest
populate view. The parent chip supplies only the already-projected witness pins; keeping all
`Eval.eval`/`fromElements` normalization in this declaration gives the kernel a fresh, small proof
term instead of appending it to the large chip completeness preamble. -/
theorem evaluatedInputs_eq (env : ProverEnvironment (ZMod p))
    (input : Var SP1Clean.DivRemChip.Inputs (ZMod p)) (off : ℕ)
    (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hir : Expression.eval env.toEnvironment input.is_real = ir)
    (hbpv : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_b_memory.prev_value = B)
    (hcpv : Vector.map (Expression.eval env.toEnvironment)
      input.adapter.op_c_memory.prev_value = C)
    (hfl4 : env.get (off + 4) = f[4]) (hfl5 : env.get (off + 5) = f[5])
    (hfl6 : env.get (off + 6) = f[6]) (hfl7 : env.get (off + 7) = f[7])
    (hSC4 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 4) =
      ir * (1 - (f[4] + f[5] + f[6] + f[7])))
    (hCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + i }) :
        Word (ZMod p)) = cComp C f)
    (hABSCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + i }) :
        Word (ZMod p)) = populateAbsC C f)
    (hABSRvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11 + 4 + i }) :
        Word (ZMod p)) = populateAbsRem B C f)
    (hRCvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + i }) : Word (ZMod p)) = populateRemComp B C f)
    (hMAXvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + i }) : Word (ZMod p)) = populateMaxAbsCOr1 C f)
    (hWCNEGvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = wCnegWitness ir C f)
    (hWRNEGvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + i }) : Word (ZMod p)) = wRnegWitness ir B C f)
    (hLTCLvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 2 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + i }) : Vector (ZMod p) 2) =
        ltClWitness ir B C f)
    (hLTFvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i =>
        var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
          + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + i }) : Vector (ZMod p) 4) =
        ltFlagsWitness ir B C f)
    (hNEI : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4) = (ltNotEqInvWitness ir B C f)[0])
    (hBIT : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1) = (ltBitWitness ir B C f)[0])
    (hRvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7
        + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + i }) :
        Word (ZMod p)) = populateRemainder B C f)
    (hQvec : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7
        + 8 + 8 + 11 + 11 + 11 + 4 + 4 + 4 + 4 + 4 + 4 + 3 + 2 + 4 + 1 + 1 + 4 + i }) :
        Word (ZMod p)) = populateQuotient B C f)
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
    (hMISC0 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4) = populateCNeg C f * ir)
    (hMISC1 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 1) = populateRemNeg B C f * ir)
    (hMISC2 : env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + 11
      + 4 + 4 + 4 + 4 + 4 + 4 + 2) = ltGate ir C f)
    (hOVB : ∀ i : Fin 11, env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + ↑i) =
      (SubSpecs.eqWordWitnessElements (ovbWitness ir B f)).get i)
    (hOVC : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + ↑i) =
        (SubSpecs.eqWordWitnessElements (ovcWitness ir C f)).get i)
    (hISC0 : ∀ i : Fin 11,
      env.get (off + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 + 8 + 8 + 11 + 11 + ↑i) =
        (SubSpecs.isZeroWitnessElements (isC0Witness C f)).get i) :
    Eval.eval env (DivRemCompare.Inputs.ofCols (populatedRowAt input off)) =
      honestInputs ir B C f := by
  apply inputs_eq_of_views
  · exact evaluatedWordView_eq env input off ir B C f hbpv hcpv hCvec
      hABSCvec hABSRvec hRCvec hMAXvec hRvec hQvec
  · exact evaluatedOperationView_eq env input off ir B C f hWCNEGvec hWRNEGvec
      hLTCLvec hLTFvec hNEI hBIT hOVB hOVC hISC0
  · exact evaluatedMsbView_eq env input off ir B C f hBM hCM hRM hQM
  · exact evaluatedScalarView_eq env input off ir B C f hir hfl4 hfl5 hfl6 hfl7
      hSC4 hMISC0 hMISC1 hMISC2

/-- The honest comparison input satisfies every external precondition of the composed comparison
cluster.  Keeping this value-level theorem beside `honestInputs` prevents the parent completeness
proof from unfolding the three nested `fromElements` blocks merely to establish range and gate
facts. -/
theorem honestAssumptions (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hbU : Word.isU64 B) (hcU : Word.isU64 C)
    (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1) :
    DivRemCompare.Assumptions (honestInputs ir B C f) := by
  have hsums := flagSums_bool hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have he2sum := hsums.1
  have hsig := hsums.2.1
  have hirnwbin : ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 0 ∨
      ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 1 := by
    rcases hbin with hir | hir <;> rcases he2sum with h2 | h2 <;> simp [hir, h2]
  have hgcneg : populateCNeg C f * ir = 0 ∨ populateCNeg C f * ir = 1 := by
    rcases hbin with h0 | h1
    · left
      rw [h0, mul_zero]
    · rw [h1, mul_one]
      exact populateCNeg_bool hcU hsig
  have hgrneg : populateRemNeg B C f * ir = 0 ∨ populateRemNeg B C f * ir = 1 := by
    rcases hbin with h0 | h1
    · left
      rw [h0, mul_zero]
    · rw [h1, mul_one]
      exact populateRemNeg_bool B C hsig
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hbU
  obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hcU
  obtain ⟨hRb0, hRb1, hRb2, hRb3⟩ :=
    Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  obtain ⟨hQb0, hQb1, hQb2, hQb3⟩ :=
    Word.lt_cases_of_isU64 (populateQuotient_isU64 B C f)
  unfold DivRemCompare.Assumptions
  dsimp only [honestInputs]
  refine ⟨hbin, hirnwbin, he2sum, hgcneg, hgrneg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [DivRemCompare.RemainderCheckGateSpec, ltGate]
    exact mul_comm _ _
  · intro _
    exact ⟨cComp_isU64 hcU f, populateAbsC_isU64 hcU f⟩
  · intro _
    exact ⟨populateRemComp_isU64 B C f, populateAbsRem_isU64 B C f⟩
  · intro _
    exact ⟨populateAbsRem_isU64 B C f, populateMaxAbsCOr1_isU64 hcU f⟩
  · intro _
    exact ⟨hbU3, hcU3, hRb3⟩
  · intro _
    exact ⟨hbU1, hcU1, hRb1, hQb1⟩

/-- Every semantic sub-operation contract in the comparison/sign cluster holds at the honest
populate values. Keeping this theorem value-level and standalone prevents its case splits from
being duplicated into the already-large chip completeness proof term. -/
theorem honestSpec (ir : ZMod p) (B C : Word (ZMod p)) (f : Vector (ZMod p) 8)
    (hbU : Word.isU64 B) (hcU : Word.isU64 C)
    (hbin : ir = 0 ∨ ir = 1)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hf4 : f[4] = 0 ∨ f[4] = 1) (hf5 : f[5] = 0 ∨ f[5] = 1)
    (hf6 : f[6] = 0 ∨ f[6] = 1) (hf7 : f[7] = 0 ∨ f[7] = 1)
    (hsum : f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + f[7] = 1)
    (hpad : ir = 0 →
      B = #v[0, 0, 0, 0] ∧ C = #v[1, 0, 0, 0] ∧ f = #v[0, 1, 0, 0, 0, 0, 0, 0]) :
    DivRemCompare.CompareSpec (honestInputs ir B C f) := by
  have hsums := flagSums_bool hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have he2sum := hsums.1
  have hsig := hsums.2.1
  clear hsums
  have hirnw_cases : ir * (1 - (f[4] + f[5] + f[6] + f[7])) = 1 →
      ir = 1 ∧ f[4] + f[5] + f[6] + f[7] = 0 := by
    intro hx
    rcases hbin with h0 | h1
    · rw [h0, zero_mul] at hx
      exact absurd hx zero_ne_one
    · rcases he2sum with h2 | h2
      · exact ⟨h1, h2⟩
      · rw [h1, h2] at hx
        exact absurd hx (by simp)
  have hgcneg : populateCNeg C f * ir = 0 ∨ populateCNeg C f * ir = 1 := by
    rcases hbin with h0 | h1
    · left
      rw [h0, mul_zero]
    · rw [h1, mul_one]
      exact populateCNeg_bool hcU hsig
  have hgrneg : populateRemNeg B C f * ir = 0 ∨ populateRemNeg B C f * ir = 1 := by
    rcases hbin with h0 | h1
    · left
      rw [h0, mul_zero]
    · rw [h1, mul_one]
      exact populateRemNeg_bool B C hsig
  have hltgbool : ltGate ir C f = 0 ∨ ltGate ir C f = 1 := ltGate_bool C f hbin
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hbU
  obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hcU
  obtain ⟨hRb0, hRb1, hRb2, hRb3⟩ :=
    Word.lt_cases_of_isU64 (populateRemainder_isU64 B C f)
  obtain ⟨hQb0, hQb1, hQb2, hQb3⟩ :=
    Word.lt_cases_of_isU64 (populateQuotient_isU64 B C f)
  unfold DivRemCompare.CompareSpec
  dsimp only [honestInputs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hbin with h0 | h1
    · rw [h0, zero_mul, ovbWitness]
      simp only [if_neg zero_ne_one]
      exact IsEqualWordOperation.spec_zero B #v[0, 0, 0, 32768] rfl
    · rcases he2sum with hw0 | hw1
      · rw [h1, hw0]
        norm_num
        rw [ovbWitness]
        simp only [if_true, hw0, if_neg zero_ne_one]
        exact IsEqualWordOperation.spec_populate B #v[0, 0, 0, 32768] 1
      · rw [h1, hw1]
        norm_num
        rw [ovbWitness]
        simp only [if_true, hw1]
        exact IsEqualWordOperation.spec_populate_offGate B #v[0, 0, 0, 32768]
          #v[B[0], B[1], 0, 0] #v[0, 32768, 0, 0] rfl
  · rcases hbin with h0 | h1
    · rw [h0, zero_mul, ovcWitness]
      simp only [if_neg zero_ne_one]
      exact IsEqualWordOperation.spec_zero C #v[65535, 65535, 65535, 65535] rfl
    · rcases he2sum with hw0 | hw1
      · rw [h1, hw0]
        norm_num
        rw [ovcWitness]
        simp only [if_true, hw0, if_neg zero_ne_one]
        exact IsEqualWordOperation.spec_populate C #v[65535, 65535, 65535, 65535] 1
      · rw [h1, hw1]
        norm_num
        rw [ovcWitness]
        simp only [if_true, hw1]
        exact IsEqualWordOperation.spec_populate_offGate C #v[65535, 65535, 65535, 65535]
          #v[C[0], C[1], 0, 0] #v[65535, 65535, 0, 0] rfl
  · rcases he2sum with hw0 | hw1
    · rw [hw0]
      rcases hbin with h0 | h1
      · rw [ovbWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
        exact IsEqualWordOperation.spec_zero (#v[B[0], B[1], 0, 0] : Word (ZMod p))
          #v[0, 32768, 0, 0] rfl
      · rw [ovbWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
        exact IsEqualWordOperation.spec_populate_offGate
          (#v[B[0], B[1], 0, 0] : Word (ZMod p)) #v[0, 32768, 0, 0]
          B #v[0, 0, 0, 32768] rfl
    · have h1 : ir = 1 := by
        rcases hbin with h0 | h1
        · obtain ⟨-, -, hf⟩ := hpad h0
          rw [hf] at hw1
          simp at hw1
        · exact h1
      rw [hw1, ovbWitness, if_pos h1, if_pos hw1]
      exact IsEqualWordOperation.spec_populate (#v[B[0], B[1], 0, 0] : Word (ZMod p))
        #v[0, 32768, 0, 0] 1
  · rcases he2sum with hw0 | hw1
    · rw [hw0]
      rcases hbin with h0 | h1
      · rw [ovcWitness, if_neg (fun hx => absurd (h0.symm.trans hx) zero_ne_one)]
        exact IsEqualWordOperation.spec_zero (#v[C[0], C[1], 0, 0] : Word (ZMod p))
          #v[65535, 65535, 0, 0] rfl
      · rw [ovcWitness, if_pos h1, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
        exact IsEqualWordOperation.spec_populate_offGate
          (#v[C[0], C[1], 0, 0] : Word (ZMod p)) #v[65535, 65535, 0, 0]
          C #v[65535, 65535, 65535, 65535] rfl
    · have h1 : ir = 1 := by
        rcases hbin with h0 | h1
        · obtain ⟨-, -, hf⟩ := hpad h0
          rw [hf] at hw1
          simp at hw1
        · exact h1
      rw [hw1, ovcWitness, if_pos h1, if_pos hw1]
      exact IsEqualWordOperation.spec_populate (#v[C[0], C[1], 0, 0] : Word (ZMod p))
        #v[65535, 65535, 0, 0] 1
  · exact IsZeroWordOperation.spec_populate (cComp C f) ir
  · rcases hgcneg with hg0 | hg1
    · rw [hg0]
      exact fun hx => absurd hx zero_ne_one
    · rw [hg1, show wCnegWitness ir C f =
          AddOperation.populate (cComp C f) (populateAbsC C f) from by
          rw [wCnegWitness, if_pos hg1]]
      exact AddOperation.spec_populate (cComp_isU64 hcU f) (populateAbsC_isU64 hcU f) 1
  · rcases hgrneg with hg0 | hg1
    · rw [hg0]
      exact fun hx => absurd hx zero_ne_one
    · rw [hg1]
      have h67 := flags67_eq_zero_of_remNeg_mul_eq_one B C ir
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hg1
      have hRCR : populateRemComp B C f = populateRemainder B C f := by
        unfold populateRemComp remCompBits populateRemainder
        rw [if_neg (fun hx => absurd (h67.symm.trans hx) zero_ne_one)]
      rw [hRCR, show wRnegWitness ir B C f =
          AddOperation.populate (populateRemainder B C f) (populateAbsRem B C f) from by
          rw [wRnegWitness, if_pos hg1]]
      exact AddOperation.spec_populate (populateRemainder_isU64 B C f)
        (populateAbsRem_isU64 B C f) 1
  · rcases hltgbool with hg0 | hg1
    · rw [hg0, ltFlagsWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one),
        ltClWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one),
        ltNotEqInvWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one),
        ltBitWitness, if_neg (fun hx => absurd (hg0.symm.trans hx) zero_ne_one)]
      exact LtOperationUnsigned.spec_zero (populateAbsRem B C f) (populateMaxAbsCOr1 C f) rfl
    · rw [hg1, ltClWitness, if_pos hg1, ltFlagsWitness, if_pos hg1,
        ltNotEqInvWitness, if_pos hg1, ltBitWitness, if_pos hg1, ltClWitness, if_pos hg1]
      exact LtOperationUnsigned.spec_populate
  · exact ⟨bMsbCell_bool hbU f, fun hg => by
      obtain ⟨_, hw0⟩ := hirnw_cases hg
      rw [bMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
      exact (U16MSBOperation.spec_populate hbU3 1).2 rfl⟩
  · exact ⟨cMsbCell_bool hcU f, fun hg => by
      obtain ⟨_, hw0⟩ := hirnw_cases hg
      rw [cMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
      exact (U16MSBOperation.spec_populate hcU3 1).2 rfl⟩
  · exact ⟨remMsbCell_bool B C f, fun hg => by
      obtain ⟨_, hw0⟩ := hirnw_cases hg
      rw [remMsbCell, if_neg (fun hx => absurd (hw0.symm.trans hx) zero_ne_one)]
      exact (U16MSBOperation.spec_populate hRb3 1).2 rfl⟩
  · exact ⟨bMsbCell_bool hbU f, fun hg => by
      rw [bMsbCell, if_pos hg]
      exact (U16MSBOperation.spec_populate hbU1 1).2 rfl⟩
  · exact ⟨cMsbCell_bool hcU f, fun hg => by
      rw [cMsbCell, if_pos hg]
      exact (U16MSBOperation.spec_populate hcU1 1).2 rfl⟩
  · exact ⟨remMsbCell_bool B C f, fun hg => by
      rw [remMsbCell, if_pos hg]
      exact (U16MSBOperation.spec_populate hRb1 1).2 rfl⟩
  · exact ⟨quotMsbCell_bool B C f, fun hg => by
      rw [quotMsbCell, if_pos hg]
      exact (U16MSBOperation.spec_populate hQb1 1).2 rfl⟩

end SP1Clean.DivRemChip.CompareComplete
