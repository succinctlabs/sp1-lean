import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Lt
import SP1Clean.Faithful.LtOperationUnsigned
import SP1Clean.Faithful.U16MSBOperation
import SP1Clean.Proofs.Chips.LtChip.Formal

/-! # Whole-chip faithfulness — native Lt row ↔ pinned SP1 Rust AIR

`ltChip_faithful` compares the native Clean circuit with the complete extracted Rust `LtCols`
assertion system and interaction multiset, including padding rows. The explicit row codec preserves
the Rust layout: the CPU/ALU reader blocks form the input prefix, followed by the `is_slt` and
`is_sltu` selectors and the ten `LtOperationSigned` cells.

The assertion proof keeps the generated operation and reader lists folded behind small structural
decomposition lemmas. This avoids the elaboration blow-up caused by unfolding nested
`ProvableStruct` specifications while still checking every Rust assertion. The interaction proof
matches all four buses exactly; its only permutations account for the native composition placing
the two CPU byte checks before the three comparison checks and factoring the destination-register
write after the ALU reader.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[circuit_norm] private theorem ltChip_eval_ltUnsignedColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.LtOperationUnsigned (Expression F)) :
    Eval.eval env cols =
      ({ u16_compare_operation := Eval.eval env cols.u16_compare_operation
         u16_flags := Eval.eval env cols.u16_flags
         not_eq_inv := Eval.eval env cols.not_eq_inv
         comparison_limbs := Eval.eval env cols.comparison_limbs } :
        Extracted.LtOperationUnsigned F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_ltUnsignedInputs
    {F : Type} [FiniteField F] (env : Environment F)
    (input : LtOperationUnsigned.Inputs (Expression F)) :
    Eval.eval env input =
      ({ b := Eval.eval env input.b, cc := Eval.eval env input.cc,
         cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real } :
        LtOperationUnsigned.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem ltChip_eval_u16CompareColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16CompareOperation (Expression F)) :
    Eval.eval env cols =
      ({ bit := Eval.eval env cols.bit } :
        Extracted.U16CompareOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem equality_constraints_exact
    (value : Expression (ZMod p)) (offset : ℕ) :
    ((Gadgets.Equality.main (M := field) (value, 0)).operations offset).constraints =
      [value - 0] := by
  simp [Gadgets.Equality.main, circuit_norm, explicit_provable_type]

omit [Fact (2 ^ 17 < p)] in
private theorem ltChip_u16MSB_assertions_exact
    (env : Environment (ZMod p))
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((U16MSBOperation.main input).operations offset) =
      Extracted.U16MSBOperation.asserts
        (Expression.eval env input.a) (Eval.eval env input.cols)
        (Expression.eval env input.is_real) := by
  simp [nativeAssertZeros, U16MSBOperation.main,
    Gadgets.Equality.main, Extracted.U16MSBOperation.asserts, circuit_norm]
  have heval (value : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) value)[0] =
        Expression.eval env value := rfl
  simp_rw [heval]
  have hinput : Eval.eval env input =
      ({ a := Eval.eval env input.a, cols := Eval.eval env input.cols,
         is_real := Eval.eval env input.is_real } :
        U16MSBOperation.Inputs (ZMod p)) := by
    rw [ProvableStruct.eval_eq_eval]
    rfl
  have hcols : Eval.eval env input.cols =
      ({ msb := Eval.eval env input.cols.msb } :
        Extracted.U16MSBOperation (ZMod p)) := by
    rw [ProvableStruct.eval_eq_eval]
    rfl
  rw [← ProvableStruct.eval_eq_eval, hinput, hcols]
  simp only [eval_sub, Expression.eval, sub_zero, CircuitType.eval_expr]

omit [Fact (2 ^ 17 < p)] in
private theorem ltChip_u16Compare_assertions_exact
    (env : Environment (ZMod p))
    (input : Var U16CompareOperation.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((U16CompareOperation.main input).operations offset) =
      Extracted.U16CompareOperation.asserts
        (Expression.eval env input.a) (Expression.eval env input.b)
        (Eval.eval env input.cols) (Expression.eval env input.is_real) := by
  simp [nativeAssertZeros, U16CompareOperation.main,
    Gadgets.Equality.main, Extracted.U16CompareOperation.asserts, circuit_norm]
  have heval (value : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) value)[0] =
        Expression.eval env value := rfl
  simp_rw [heval]
  have hinput : Eval.eval env input =
      ({ a := Eval.eval env input.a, b := Eval.eval env input.b,
         cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real } :
        U16CompareOperation.Inputs (ZMod p)) := by
    rw [ProvableStruct.eval_eq_eval]
    rfl
  have hcols : Eval.eval env input.cols =
      ({ bit := Eval.eval env input.cols.bit } :
        Extracted.U16CompareOperation (ZMod p)) := by
    rw [ProvableStruct.eval_eq_eval]
    rfl
  rw [← ProvableStruct.eval_eq_eval, hinput, hcols]
  simp only [eval_sub, Expression.eval, sub_zero, CircuitType.eval_expr]

private def ltUnsignedAssertionTail (b cc : Word (ZMod p))
    (cols : Extracted.LtOperationUnsigned (ZMod p)) (isReal : ZMod p) :
    List (ZMod p) :=
  let sum3 := (0 : ZMod p) + cols.u16_flags[3]
  let sum2 := sum3 + cols.u16_flags[2]
  let sum1 := sum2 + cols.u16_flags[1]
  let selectedAll := sum1 + cols.u16_flags[0]
  let flagTotal :=
    cols.u16_flags[0] + cols.u16_flags[1] +
      cols.u16_flags[2] + cols.u16_flags[3]
  let comparison0 :=
    (0 : ZMod p) + b[3] * cols.u16_flags[3] + b[2] * cols.u16_flags[2] +
      b[1] * cols.u16_flags[1] + b[0] * cols.u16_flags[0]
  let comparison1 :=
    (0 : ZMod p) + cc[3] * cols.u16_flags[3] + cc[2] * cols.u16_flags[2] +
      cc[1] * cols.u16_flags[1] + cc[0] * cols.u16_flags[0]
  [ isReal * (isReal - 1),
    cols.u16_flags[0] * (cols.u16_flags[0] - 1),
    cols.u16_flags[1] * (cols.u16_flags[1] - 1),
    cols.u16_flags[2] * (cols.u16_flags[2] - 1),
    cols.u16_flags[3] * (cols.u16_flags[3] - 1),
    flagTotal * (flagTotal - 1),
    (isReal - sum3) * (b[3] - cc[3]),
    (isReal - sum2) * (b[2] - cc[2]),
    (isReal - sum1) * (b[1] - cc[1]),
    (isReal - selectedAll) * (b[0] - cc[0]),
    comparison0 - cols.comparison_limbs[0],
    comparison1 - cols.comparison_limbs[1],
    ((1 : ZMod p) - flagTotal - (1 : ZMod p)) *
      (cols.not_eq_inv *
        (cols.comparison_limbs[0] - cols.comparison_limbs[1]) - isReal) ]

omit [Fact (2 ^ 17 < p)] in
private theorem extracted_ltUnsigned_assertions_decompose
    (b cc : Word (ZMod p)) (cols : Extracted.LtOperationUnsigned (ZMod p))
    (isReal : ZMod p) :
    Extracted.LtOperationUnsigned.asserts b cc cols isReal =
      Extracted.U16CompareOperation.asserts
        cols.comparison_limbs[0] cols.comparison_limbs[1]
        cols.u16_compare_operation isReal ++
      ltUnsignedAssertionTail b cc cols isReal := by
  rw [Extracted.LtOperationUnsigned.asserts]
  simp [ltUnsignedAssertionTail]

private def ltUnsignedConstraintTail
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  let b := input.b
  let cc := input.cc
  let cols := input.cols
  let isReal := input.is_real
  let sum3 := (0 : Expression (ZMod p)) + cols.u16_flags[3]
  let sum2 := sum3 + cols.u16_flags[2]
  let sum1 := sum2 + cols.u16_flags[1]
  let selectedAll := sum1 + cols.u16_flags[0]
  let flagTotal :=
    cols.u16_flags[0] + cols.u16_flags[1] +
      cols.u16_flags[2] + cols.u16_flags[3]
  let comparison0 :=
    (0 : Expression (ZMod p)) +
      b[3] * cols.u16_flags[3] + b[2] * cols.u16_flags[2] +
      b[1] * cols.u16_flags[1] + b[0] * cols.u16_flags[0]
  let comparison1 :=
    (0 : Expression (ZMod p)) +
      cc[3] * cols.u16_flags[3] + cc[2] * cols.u16_flags[2] +
      cc[1] * cols.u16_flags[1] + cc[0] * cols.u16_flags[0]
  [ isReal * (isReal - 1) - 0,
    cols.u16_flags[0] * (cols.u16_flags[0] - 1) - 0,
    cols.u16_flags[1] * (cols.u16_flags[1] - 1) - 0,
    cols.u16_flags[2] * (cols.u16_flags[2] - 1) - 0,
    cols.u16_flags[3] * (cols.u16_flags[3] - 1) - 0,
    flagTotal * (flagTotal - 1) - 0,
    (isReal - sum3) * (b[3] - cc[3]) - 0,
    (isReal - sum2) * (b[2] - cc[2]) - 0,
    (isReal - sum1) * (b[1] - cc[1]) - 0,
    (isReal - selectedAll) * (b[0] - cc[0]) - 0,
    (comparison0 - cols.comparison_limbs[0]) - 0,
    (comparison1 - cols.comparison_limbs[1]) - 0,
    (((1 : Expression (ZMod p)) - flagTotal -
      (1 : Expression (ZMod p))) *
      (cols.not_eq_inv *
        (cols.comparison_limbs[0] - cols.comparison_limbs[1]) - isReal)) - 0 ]

private theorem ltUnsigned_constraints_decompose
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) (offset : ℕ) :
    ((LtOperationUnsigned.main input).operations offset).constraints =
      ((U16CompareOperation.main
        ⟨input.cols.comparison_limbs[0], input.cols.comparison_limbs[1],
          { bit := input.cols.u16_compare_operation.bit },
          input.is_real⟩).operations offset).constraints ++
      ltUnsignedConstraintTail input := by
  simp only [LtOperationUnsigned.main, U16CompareOperation.circuit,
    circuit_norm]
  repeat rw [equality_constraints_exact]
  unfold ltUnsignedConstraintTail
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem ltUnsignedConstraintTail_eval
    (env : Environment (ZMod p))
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) :
    (ltUnsignedConstraintTail input).map (Expression.eval env) =
      ltUnsignedAssertionTail
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols) (Expression.eval env input.is_real) := by
  have hb0 : (Eval.eval env input.b)[0] = Expression.eval env input.b[0] :=
    (ProvableType.getElem_eval_fields env input.b 0 (by decide)).symm
  have hb1 : (Eval.eval env input.b)[1] = Expression.eval env input.b[1] :=
    (ProvableType.getElem_eval_fields env input.b 1 (by decide)).symm
  have hb2 : (Eval.eval env input.b)[2] = Expression.eval env input.b[2] :=
    (ProvableType.getElem_eval_fields env input.b 2 (by decide)).symm
  have hb3 : (Eval.eval env input.b)[3] = Expression.eval env input.b[3] :=
    (ProvableType.getElem_eval_fields env input.b 3 (by decide)).symm
  have hc0 : (Eval.eval env input.cc)[0] = Expression.eval env input.cc[0] :=
    (ProvableType.getElem_eval_fields env input.cc 0 (by decide)).symm
  have hc1 : (Eval.eval env input.cc)[1] = Expression.eval env input.cc[1] :=
    (ProvableType.getElem_eval_fields env input.cc 1 (by decide)).symm
  have hc2 : (Eval.eval env input.cc)[2] = Expression.eval env input.cc[2] :=
    (ProvableType.getElem_eval_fields env input.cc 2 (by decide)).symm
  have hc3 : (Eval.eval env input.cc)[3] = Expression.eval env input.cc[3] :=
    (ProvableType.getElem_eval_fields env input.cc 3 (by decide)).symm
  have hf0 :
      (Eval.eval env input.cols.u16_flags)[0] =
        Expression.eval env input.cols.u16_flags[0] :=
    (ProvableType.getElem_eval_fields env input.cols.u16_flags 0 (by decide)).symm
  have hf1 :
      (Eval.eval env input.cols.u16_flags)[1] =
        Expression.eval env input.cols.u16_flags[1] :=
    (ProvableType.getElem_eval_fields env input.cols.u16_flags 1 (by decide)).symm
  have hf2 :
      (Eval.eval env input.cols.u16_flags)[2] =
        Expression.eval env input.cols.u16_flags[2] :=
    (ProvableType.getElem_eval_fields env input.cols.u16_flags 2 (by decide)).symm
  have hf3 :
      (Eval.eval env input.cols.u16_flags)[3] =
        Expression.eval env input.cols.u16_flags[3] :=
    (ProvableType.getElem_eval_fields env input.cols.u16_flags 3 (by decide)).symm
  have hcl0 :
      (Eval.eval env input.cols.comparison_limbs)[0] =
        Expression.eval env input.cols.comparison_limbs[0] :=
    (ProvableType.getElem_eval_fields env input.cols.comparison_limbs 0 (by decide)).symm
  have hcl1 :
      (Eval.eval env input.cols.comparison_limbs)[1] =
        Expression.eval env input.cols.comparison_limbs[1] :=
    (ProvableType.getElem_eval_fields env input.cols.comparison_limbs 1 (by decide)).symm
  unfold ltUnsignedConstraintTail ltUnsignedAssertionTail
  simp only [List.map_cons, List.map_nil, List.cons.injEq]
  rw [eval_ltUnsignedColumns]
  rw [hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3,
    hf0, hf1, hf2, hf3, hcl0, hcl1]
  simp only [CircuitType.eval_expr, eval_sub, Expression.eval, sub_zero]
  simp

private theorem native_ltUnsigned_assertions_decompose
    (env : Environment (ZMod p))
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((LtOperationUnsigned.main input).operations offset) =
      nativeAssertZeros env
        ((U16CompareOperation.main
          ⟨input.cols.comparison_limbs[0], input.cols.comparison_limbs[1],
            { bit := input.cols.u16_compare_operation.bit },
            input.is_real⟩).operations offset) ++
      ltUnsignedAssertionTail
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols) (Expression.eval env input.is_real) := by
  rw [nativeAssertZeros, ltUnsigned_constraints_decompose, List.map_append,
    ← nativeAssertZeros, ltUnsignedConstraintTail_eval]

private theorem ltChip_ltUnsigned_assertions_exact
    (env : Environment (ZMod p))
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((LtOperationUnsigned.main input).operations offset) =
      Extracted.LtOperationUnsigned.asserts
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols) (Expression.eval env input.is_real) := by
  let cmpInput : Var U16CompareOperation.Inputs (ZMod p) :=
    ⟨input.cols.comparison_limbs[0], input.cols.comparison_limbs[1],
      { bit := input.cols.u16_compare_operation.bit }, input.is_real⟩
  have ha : Expression.eval env cmpInput.a =
      (Eval.eval env input.cols).comparison_limbs[0] := by
    simp only [cmpInput]
    rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env input.cols.comparison_limbs 0 (by decide)
  have hb : Expression.eval env cmpInput.b =
      (Eval.eval env input.cols).comparison_limbs[1] := by
    simp only [cmpInput]
    rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env input.cols.comparison_limbs 1 (by decide)
  have hcols : Eval.eval env cmpInput.cols =
      (Eval.eval env input.cols).u16_compare_operation := by
    simp only [cmpInput, eval_u16CompareColumns]
    rw [eval_ltUnsignedColumns]
    rw [eval_u16CompareColumns]
  have hreal : Expression.eval env cmpInput.is_real =
      Expression.eval env input.is_real := rfl
  rw [native_ltUnsigned_assertions_decompose,
    extracted_ltUnsigned_assertions_decompose,
    ltChip_u16Compare_assertions_exact]
  rw [ha, hb, hcols, hreal]

@[circuit_norm] theorem eval_ltSignedColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.LtOperationSigned (Expression F)) :
    Eval.eval env cols =
      ({ result := Eval.eval env cols.result
         b_msb := Eval.eval env cols.b_msb
         c_msb := Eval.eval env cols.c_msb } :
        Extracted.LtOperationSigned F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_ltSignedInputs
    {F : Type} [FiniteField F] (env : Environment F)
    (input : LtOperationSigned.Inputs (Expression F)) :
    Eval.eval env input =
      ({ b := Eval.eval env input.b, cc := Eval.eval env input.cc,
         cols := Eval.eval env input.cols,
         is_signed := Eval.eval env input.is_signed,
         is_real := Eval.eval env input.is_real } :
        LtOperationSigned.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem ltChip_eval_u16MSBColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_aluOpBPrev
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.ALUTypeReader (Expression F)) :
    (Eval.eval env cols).op_b_memory.prev_value =
      Eval.eval env cols.op_b_memory.prev_value := by
  rw [Readers.ALUTypeReader.eval_cols]
  change (Eval.eval env cols.op_b_memory).prev_value =
    Eval.eval env cols.op_b_memory.prev_value
  rw [Readers.ALUTypeReader.eval_accessCols]

@[circuit_norm] private theorem eval_ltSignedBit
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.LtOperationSigned (Expression F)) :
    (Eval.eval env cols).result.u16_compare_operation.bit =
      Expression.eval env cols.result.u16_compare_operation.bit := by
  rw [eval_ltSignedColumns]
  change (Eval.eval env cols.result).u16_compare_operation.bit =
    Expression.eval env cols.result.u16_compare_operation.bit
  rw [eval_ltUnsignedColumns]
  change (Eval.eval env cols.result.u16_compare_operation).bit =
    Expression.eval env cols.result.u16_compare_operation.bit
  rw [eval_u16CompareColumns]
  simp only [CircuitType.eval_expr]

private theorem vec2_eta {F : Type} (value : Vector F 2) :
    #v[value[0], value[1]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem vec4_eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem vec3_eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem eval_vec4_literal {F : Type} [FiniteField F]
    (env : Environment F) (a b c d : Expression F) :
    Eval.eval env (#v[a, b, c, d] : Vector (Expression F) 4) =
      #v[Expression.eval env a, Expression.eval env b,
        Expression.eval env c, Expression.eval env d] := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env
    (#v[a, b, c, d] : Vector (Expression F) 4) i hi]
  interval_cases i <;> rfl

private theorem ltUnsigned_eta {F : Type}
    (cols : Extracted.LtOperationUnsigned F) :
    (⟨cols.u16_compare_operation,
      #v[cols.u16_flags[0], cols.u16_flags[1],
        cols.u16_flags[2], cols.u16_flags[3]],
      cols.not_eq_inv,
      #v[cols.comparison_limbs[0], cols.comparison_limbs[1]]⟩ :
      Extracted.LtOperationUnsigned F) = cols := by
  cases cols
  simp only
  rw [vec4_eta, vec2_eta]

private theorem ltSigned_eta {F : Type}
    (cols : Extracted.LtOperationSigned F) :
    ({ result :=
        { u16_compare_operation :=
            { bit := cols.result.u16_compare_operation.bit }
          u16_flags :=
            #v[cols.result.u16_flags[0], cols.result.u16_flags[1],
              cols.result.u16_flags[2], cols.result.u16_flags[3]]
          not_eq_inv := cols.result.not_eq_inv
          comparison_limbs :=
            #v[cols.result.comparison_limbs[0],
              cols.result.comparison_limbs[1]] }
       b_msb := { msb := cols.b_msb.msb }
       c_msb := { msb := cols.c_msb.msb } } :
      Extracted.LtOperationSigned F) = cols := by
  cases cols with
  | mk result bMsb cMsb =>
      cases bMsb
      cases cMsb
      rw [Extracted.LtOperationSigned.mk.injEq]
      exact ⟨ltUnsigned_eta result, rfl, rfl⟩

private theorem eval_ltSigned_eta {F : Type} [FiniteField F]
    (env : Environment F)
    (cols : Extracted.LtOperationSigned (Expression F)) :
    ({ result :=
        { u16_compare_operation :=
            { bit := Eval.eval env cols.result.u16_compare_operation.bit }
          u16_flags :=
            #v[(Eval.eval env cols.result.u16_flags)[0],
              (Eval.eval env cols.result.u16_flags)[1],
              (Eval.eval env cols.result.u16_flags)[2],
              (Eval.eval env cols.result.u16_flags)[3]]
          not_eq_inv := Eval.eval env cols.result.not_eq_inv
          comparison_limbs :=
            #v[(Eval.eval env cols.result.comparison_limbs)[0],
              (Eval.eval env cols.result.comparison_limbs)[1]] }
       b_msb := { msb := Eval.eval env cols.b_msb.msb }
       c_msb := { msb := Eval.eval env cols.c_msb.msb } } :
      Extracted.LtOperationSigned F) = Eval.eval env cols := by
  rw [eval_ltSignedColumns, eval_ltUnsignedColumns,
    eval_u16CompareColumns]
  rw [vec4_eta, vec2_eta]
  rw [Extracted.LtOperationSigned.mk.injEq]
  exact ⟨rfl, (eval_u16MSBColumns env cols.b_msb).symm,
    (eval_u16MSBColumns env cols.c_msb).symm⟩

private theorem registerAccess_eta {F : Type}
    (cols : Extracted.RegisterAccessCols F) :
    ({ prev_value :=
        #v[cols.prev_value[0], cols.prev_value[1],
          cols.prev_value[2], cols.prev_value[3]]
       access_timestamp := cols.access_timestamp } :
      Extracted.RegisterAccessCols F) = cols := by
  cases cols
  rw [Extracted.RegisterAccessCols.mk.injEq]
  exact ⟨vec4_eta _, rfl⟩

private theorem aluType_eta {F : Type}
    (cols : Extracted.ALUTypeReader F) :
    ({ op_a := cols.op_a
       op_a_memory :=
        { prev_value :=
            #v[cols.op_a_memory.prev_value[0],
              cols.op_a_memory.prev_value[1],
              cols.op_a_memory.prev_value[2],
              cols.op_a_memory.prev_value[3]]
          access_timestamp := cols.op_a_memory.access_timestamp }
       op_a_0 := cols.op_a_0
       op_b := cols.op_b
       op_b_memory :=
        { prev_value :=
            #v[cols.op_b_memory.prev_value[0],
              cols.op_b_memory.prev_value[1],
              cols.op_b_memory.prev_value[2],
              cols.op_b_memory.prev_value[3]]
          access_timestamp := cols.op_b_memory.access_timestamp }
       op_c :=
        #v[cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3]]
       op_c_memory :=
        { prev_value :=
            #v[cols.op_c_memory.prev_value[0],
              cols.op_c_memory.prev_value[1],
              cols.op_c_memory.prev_value[2],
              cols.op_c_memory.prev_value[3]]
          access_timestamp := cols.op_c_memory.access_timestamp }
       imm_c := cols.imm_c } :
      Extracted.ALUTypeReader F) = cols := by
  cases cols
  simp only
  rw [registerAccess_eta, registerAccess_eta, vec4_eta, registerAccess_eta]

private theorem cpuState_eta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Extracted.CPUState F) = cols := by
  cases cols
  rw [Extracted.CPUState.mk.injEq]
  exact ⟨rfl, rfl, rfl, vec3_eta _⟩

private def ltSignedAssertionTail (cols : Extracted.LtOperationSigned (ZMod p))
    (isSigned isReal : ZMod p) : List (ZMod p) :=
  [ isSigned * (isSigned - 1),
    isReal * (isReal - 1),
    (isReal - 1) * isSigned,
    (isSigned - 1) * cols.b_msb.msb,
    (isSigned - 1) * cols.c_msb.msb ]

omit [Fact (2 ^ 17 < p)] in
private theorem extracted_ltSigned_assertions_decompose
    (b cc : Word (ZMod p)) (cols : Extracted.LtOperationSigned (ZMod p))
    (isSigned isReal : ZMod p) :
    Extracted.LtOperationSigned.asserts b cc cols isSigned isReal =
      Extracted.U16MSBOperation.asserts b[3] cols.b_msb isSigned ++
      Extracted.U16MSBOperation.asserts cc[3] cols.c_msb isSigned ++
      Extracted.LtOperationUnsigned.asserts
        #v[b[0], b[1], b[2],
          b[3] + isSigned * 32768 - 65536 * cols.b_msb.msb]
        #v[cc[0], cc[1], cc[2],
          cc[3] + isSigned * 32768 - 65536 * cols.c_msb.msb]
        cols.result isReal ++
      ltSignedAssertionTail cols isSigned isReal := by
  rw [Extracted.LtOperationSigned.asserts]
  rw [ltUnsigned_eta]
  simp [ltSignedAssertionTail]

private def ltSignedConstraintTail
    (input : Var LtOperationSigned.Inputs (ZMod p)) :
    List (Expression (ZMod p)) :=
  [ input.is_signed * (input.is_signed - 1) - 0,
    input.is_real * (input.is_real - 1) - 0,
    (input.is_real - 1) * input.is_signed - 0,
    (input.is_signed - 1) * input.cols.b_msb.msb - 0,
    (input.is_signed - 1) * input.cols.c_msb.msb - 0 ]

private theorem ltSigned_constraints_decompose
    (input : Var LtOperationSigned.Inputs (ZMod p)) (offset : ℕ) :
    ((LtOperationSigned.main input).operations offset).constraints =
      ((U16MSBOperation.main
        ⟨input.b[3], input.cols.b_msb, input.is_signed⟩).operations offset).constraints ++
      ((U16MSBOperation.main
        ⟨input.cc[3], input.cols.c_msb, input.is_signed⟩).operations offset).constraints ++
      ((LtOperationUnsigned.main
        ⟨#v[input.b[0], input.b[1], input.b[2],
              input.b[3] + input.is_signed * 32768 -
                65536 * input.cols.b_msb.msb],
          #v[input.cc[0], input.cc[1], input.cc[2],
              input.cc[3] + input.is_signed * 32768 -
                65536 * input.cols.c_msb.msb],
          input.cols.result, input.is_real⟩).operations offset).constraints ++
      ltSignedConstraintTail input := by
  simp only [LtOperationSigned.main, U16MSBOperation.circuit,
    LtOperationUnsigned.circuit, circuit_norm]
  repeat rw [equality_constraints_exact]
  unfold ltSignedConstraintTail
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem ltSignedConstraintTail_eval
    (env : Environment (ZMod p))
    (input : Var LtOperationSigned.Inputs (ZMod p)) :
    (ltSignedConstraintTail input).map (Expression.eval env) =
      ltSignedAssertionTail (Eval.eval env input.cols)
        (Expression.eval env input.is_signed)
        (Expression.eval env input.is_real) := by
  unfold ltSignedConstraintTail ltSignedAssertionTail
  simp only [List.map_cons, List.map_nil, List.cons.injEq]
  rw [eval_ltSignedColumns, eval_u16MSBColumns, eval_u16MSBColumns]
  simp only [CircuitType.eval_expr, eval_sub, Expression.eval, sub_zero]
  simp

private theorem native_ltSigned_assertions_decompose
    (env : Environment (ZMod p))
    (input : Var LtOperationSigned.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((LtOperationSigned.main input).operations offset) =
      nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨input.b[3], input.cols.b_msb, input.is_signed⟩).operations offset) ++
      nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨input.cc[3], input.cols.c_msb, input.is_signed⟩).operations offset) ++
      nativeAssertZeros env
        ((LtOperationUnsigned.main
          ⟨#v[input.b[0], input.b[1], input.b[2],
                input.b[3] + input.is_signed * 32768 -
                  65536 * input.cols.b_msb.msb],
            #v[input.cc[0], input.cc[1], input.cc[2],
                input.cc[3] + input.is_signed * 32768 -
                  65536 * input.cols.c_msb.msb],
            input.cols.result, input.is_real⟩).operations offset) ++
      ltSignedAssertionTail (Eval.eval env input.cols)
        (Expression.eval env input.is_signed)
        (Expression.eval env input.is_real) := by
  rw [nativeAssertZeros, ltSigned_constraints_decompose,
    List.map_append, List.map_append, List.map_append,
    ← nativeAssertZeros, ← nativeAssertZeros, ← nativeAssertZeros,
    ltSignedConstraintTail_eval]

/-- Folded exact normalization of the signed-compare assertion fragment.  This is an implementation
lemma for enclosing whole-chip `ChipFaithful` proofs, not an operation-level faithfulness boundary:
it prevents parent proofs from unfolding the deeply nested compare circuit and its generated oracle
at the same time. -/
theorem ltSigned_assertions_exact
    (env : Environment (ZMod p))
    (input : Var LtOperationSigned.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((LtOperationSigned.main input).operations offset) =
      Extracted.LtOperationSigned.asserts
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_signed)
        (Expression.eval env input.is_real) := by
  have hb0 : (Eval.eval env input.b)[0] = Expression.eval env input.b[0] :=
    (ProvableType.getElem_eval_fields env input.b 0 (by decide)).symm
  have hb1 : (Eval.eval env input.b)[1] = Expression.eval env input.b[1] :=
    (ProvableType.getElem_eval_fields env input.b 1 (by decide)).symm
  have hb2 : (Eval.eval env input.b)[2] = Expression.eval env input.b[2] :=
    (ProvableType.getElem_eval_fields env input.b 2 (by decide)).symm
  have hb3 : (Eval.eval env input.b)[3] = Expression.eval env input.b[3] :=
    (ProvableType.getElem_eval_fields env input.b 3 (by decide)).symm
  have hc0 : (Eval.eval env input.cc)[0] = Expression.eval env input.cc[0] :=
    (ProvableType.getElem_eval_fields env input.cc 0 (by decide)).symm
  have hc1 : (Eval.eval env input.cc)[1] = Expression.eval env input.cc[1] :=
    (ProvableType.getElem_eval_fields env input.cc 1 (by decide)).symm
  have hc2 : (Eval.eval env input.cc)[2] = Expression.eval env input.cc[2] :=
    (ProvableType.getElem_eval_fields env input.cc 2 (by decide)).symm
  have hc3 : (Eval.eval env input.cc)[3] = Expression.eval env input.cc[3] :=
    (ProvableType.getElem_eval_fields env input.cc 3 (by decide)).symm
  rw [native_ltSigned_assertions_decompose,
    extracted_ltSigned_assertions_decompose,
    u16msb_assertions_exact, u16msb_assertions_exact,
    ltUnsigned_assertions_exact]
  simp only [eval_u16MSBColumns]
  rw [eval_ltSignedColumns, eval_u16MSBColumns, eval_u16MSBColumns]
  rw [hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
  rw [eval_vec4_literal, eval_vec4_literal]
  simp only [CircuitType.eval_expr, eval_sub, Expression.eval]

/-- Rebuild the shared standalone `LtOperationSigned` block as the byte-identical struct embedded in
the generated Lt oracle namespace. -/
def ltOracleOperation {F : Type} (cols : Extracted.LtOperationSigned F) :
    Extracted.LtOracle.LtOperationSigned F :=
  { result :=
      { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }
        u16_flags := cols.result.u16_flags
        not_eq_inv := cols.result.not_eq_inv
        comparison_limbs := cols.result.comparison_limbs }
    b_msb := { msb := cols.b_msb.msb }
    c_msb := { msb := cols.c_msb.msb } }

/-- Inverse of `ltOracleOperation`. -/
def ltNativeOperation {F : Type} (cols : Extracted.LtOracle.LtOperationSigned F) :
    Extracted.LtOperationSigned F :=
  { result :=
      { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }
        u16_flags := cols.result.u16_flags
        not_eq_inv := cols.result.not_eq_inv
        comparison_limbs := cols.result.comparison_limbs }
    b_msb := { msb := cols.b_msb.msb }
    c_msb := { msb := cols.c_msb.msb } }

/-- Whole-chip row reconfiguration. The reader blocks and the flag columns are already the canonical
generated substrate; the compare block is copied into Rust's chip-private operation row. This is not
an operation-level faithfulness claim. -/
def ltChipReconfigure {F : Type} (cols : LtChip.Columns F) :
    Extracted.LtOracle.LtCols F :=
  { state := cols.state
    adapter := cols.adapter
    is_slt := cols.is_slt
    is_sltu := cols.is_sltu
    lt_operation := ltOracleOperation cols.lt_operation }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def ltChipDeconfigure {F : Type} (cols : Extracted.LtOracle.LtCols F) :
    LtChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    is_slt := cols.is_slt
    is_sltu := cols.is_sltu
    lt_operation := ltNativeOperation cols.lt_operation }

/-- SP1 Rust's complete Lt-chip oracle, viewed from the native Lean row. -/
def ltChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F LtChip.Columns Extracted.LtOracle.LtCols where
  reconfigure := ltChipReconfigure
  deconfigure := ltChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.LtOracle.LtCols.asserts
  interactions := Extracted.LtOracle.LtCols.interactions

/- Namespace bridges between the Lt oracle's embedded chip-private helper copies and the canonical
standalone generated modules. The two bodies are rendered from the same compiler output, so each
bridge is a definitional unfolding, not a mathematical claim. They let every heavy compare-op lemma
below stay stated once against the standalone modules (also consumed by the Branch chip family and
the DivRem oracle bridges). -/

private theorem ltOracle_u16compare_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.LtOracle.U16CompareOperation.asserts a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.asserts a b ⟨bit⟩ is_real := by
  rw [Extracted.LtOracle.U16CompareOperation.asserts,
    Extracted.U16CompareOperation.asserts]

private theorem ltOracle_u16compare_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.LtOracle.U16CompareOperation.interactions a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.interactions a b ⟨bit⟩ is_real := by
  rw [Extracted.LtOracle.U16CompareOperation.interactions,
    Extracted.U16CompareOperation.interactions]

private theorem ltOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LtOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.LtOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem ltOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LtOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.LtOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

private theorem ltOracle_ltUnsigned_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.LtOracle.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.LtOracle.LtOperationUnsigned.asserts,
    Extracted.LtOperationUnsigned.asserts]
  simp only [ltOracle_u16compare_asserts_eq]

private theorem ltOracle_ltUnsigned_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.LtOracle.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.LtOracle.LtOperationUnsigned.interactions,
    Extracted.LtOperationUnsigned.interactions]
  simp only [ltOracle_u16compare_interactions_eq]

private theorem ltOracle_ltSigned_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (bMsb cMsb is_signed is_real : F) :
    Extracted.LtOracle.LtOperationSigned.asserts b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real =
      Extracted.LtOperationSigned.asserts b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real := by
  rw [Extracted.LtOracle.LtOperationSigned.asserts,
    Extracted.LtOperationSigned.asserts]
  simp only [ltOracle_u16msb_asserts_eq, ltOracle_ltUnsigned_asserts_eq]

private theorem ltOracle_ltSigned_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (bMsb cMsb is_signed is_real : F) :
    Extracted.LtOracle.LtOperationSigned.interactions b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real =
      Extracted.LtOperationSigned.interactions b cc
        ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩, ⟨bMsb⟩, ⟨cMsb⟩⟩
        is_signed is_real := by
  rw [Extracted.LtOracle.LtOperationSigned.interactions,
    Extracted.LtOperationSigned.interactions]
  simp only [ltOracle_u16msb_interactions_eq, ltOracle_ltUnsigned_interactions_eq]

def ltChipInput {F : Type} [Add F]
    (cols : LtChip.Columns F) : LtChip.Inputs F :=
  { is_real := cols.is_slt + cols.is_sltu
    state := cols.state
    adapter := cols.adapter }

def ltChipLocals {F : Type} (cols : LtChip.Columns F) : Vector F 12 :=
  Vector.cast (by rfl)
    (#v[cols.is_slt, cols.is_sltu] ++ toElements cols.lt_operation)

def ltChipPhysicalRow {F : Type} [Add F]
    (cols : LtChip.Columns F) : Array F :=
  inputFirstRow (ltChipInput cols) (ltChipLocals cols)

def ltChipOperationOfLocals {F : Type} (locals : Vector F 12) :
    Extracted.LtOperationSigned F :=
  fromElements (Vector.cast (by rfl) (locals.drop 2))

def ltChipColumnsOfInput {F : Type} (input : LtChip.Inputs F)
    (locals : Vector F 12) : LtChip.Columns F :=
  ⟨input.state, input.adapter, locals[0], locals[1],
    ltChipOperationOfLocals locals⟩

private theorem ltChipLocals_zero {F : Type} (cols : LtChip.Columns F) :
    (ltChipLocals cols)[0] = cols.is_slt := by
  simp [ltChipLocals]

private theorem ltChipLocals_one {F : Type} (cols : LtChip.Columns F) :
    (ltChipLocals cols)[1] = cols.is_sltu := by
  simp [ltChipLocals]

private theorem ltChipOperationOfLocals_roundtrip {F : Type}
    (cols : LtChip.Columns F) :
    ltChipOperationOfLocals (ltChipLocals cols) = cols.lt_operation := by
  refine (ProvableType.ext_iff (α := Extracted.LtOperationSigned) _ _).mpr
    (fun i hi => ?_)
  unfold ltChipOperationOfLocals ltChipLocals
  rw [ProvableType.toElements_fromElements, Vector.getElem_cast,
    Vector.getElem_drop, Vector.getElem_cast]
  simp

theorem ltChipColumnsOfInput_roundtrip {F : Type} [Add F]
    (cols : LtChip.Columns F) :
    ltChipColumnsOfInput (ltChipInput cols) (ltChipLocals cols) = cols := by
  unfold ltChipColumnsOfInput ltChipInput
  rw [LtChip.Columns.mk.injEq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact ltChipLocals_zero cols
  constructor
  · exact ltChipLocals_one cols
  · exact ltChipOperationOfLocals_roundtrip cols

omit [Fact (2 ^ 17 < p)] in
private theorem eval_ltChipOperationOfLocals
    (input : LtChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 12)
    (data : ProverData (ZMod p)) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (varFromOffset Extracted.LtOperationSigned (F := ZMod p)
          (size LtChip.Inputs + 2)) =
      ltChipOperationOfLocals locals := by
  refine (ProvableType.ext_iff (α := Extracted.LtOperationSigned) _ _).mpr
    (fun i hi => ?_)
  rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange]
  unfold ltChipOperationOfLocals
  rw [ProvableType.toElements_fromElements, Vector.getElem_cast,
    Vector.getElem_drop]
  have hlocal := eval_local_inputFirstRow input locals data (2 + i) (by
    have hsize : size Extracted.LtOperationSigned = 10 := rfl
    rw [hsize] at hi
    omega)
  simp only [Expression.eval] at hlocal
  simpa only [Nat.add_assoc] using hlocal

theorem eval_ltChipDirectOutput
    (input : LtChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 12)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((LtChip.elaborated (p := p)).output
          (varFromOffset LtChip.Inputs 0) (size LtChip.Inputs)) =
      ltChipColumnsOfInput input locals := by
  rw [LtChip.directOutput_eq]
  rw [← CircuitType.eval_expression, LtChip.eval_columns]
  unfold ltChipColumnsOfInput
  rw [LtChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [LtChip.eval_inputs, LtChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  constructor
  · simpa only [ProvableType.eval_field, Nat.add_zero] using
      (eval_local_inputFirstRow input locals data 0 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 1 (by decide))
  · exact eval_ltChipOperationOfLocals input locals data

def ltChipRowCodec :
    ChipRowCodec LtChip.Inputs LtChip.Columns
      (LtChip.circuit (p := p)) where
  assignment cols data := {
    row := ltChipPhysicalRow cols
    input := ltChipInput cols
    width_eq := by
      rw [ltChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        LtChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (LtChip.circuit (p := p))
        (ltChipInput cols) (ltChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((LtChip.main _).output _) = _
      rw [LtChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_ltChipDirectOutput (p := p) (ltChipInput cols)
        (ltChipLocals cols) data).trans
          (ltChipColumnsOfInput_roundtrip cols) }

theorem ltChip_lookups_empty :
    (⟨LtChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LtChip.circuit_main_eq]
  simp [LtChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    LtOperationSigned.circuit, LtOperationSigned.main,
    LtOperationUnsigned.circuit, LtOperationUnsigned.main,
    U16MSBOperation.circuit, U16MSBOperation.main,
    U16CompareOperation.circuit, U16CompareOperation.main,
    Gadgets.Equality.main, circuit_norm]

private def lt_chip_is_slt (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset }

private def lt_chip_is_sltu (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 1 }

private def lt_chip_is_real (offset : ℕ) : Expression (ZMod p) :=
  lt_chip_is_slt offset + lt_chip_is_sltu offset

private def lt_chip_operation (offset : ℕ) :
    Var Extracted.LtOperationSigned (ZMod p) :=
  varFromOffset Extracted.LtOperationSigned (offset + 2)

private def lt_chip_write_value (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  #v[(lt_chip_operation offset).result.u16_compare_operation.bit, 0, 0, 0]

private def lt_chip_cpu_opcode (offset : ℕ) : Expression (ZMod p) :=
  lt_chip_is_slt offset * 9 + lt_chip_is_sltu offset * 10

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_write_value
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (lt_chip_write_value (p := p) offset) =
      #v[Expression.eval env
            (lt_chip_operation (p := p) offset).result.u16_compare_operation.bit,
        0, 0, 0] := by
  unfold lt_chip_write_value
  rw [eval_vec4_literal]
  rfl

set_option maxHeartbeats 2000000 in
private theorem lt_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var LtChip.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((LtChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state,
                #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((LtOperationSigned.main
              ⟨input.op_b_val, input.op_c_val, lt_chip_operation offset,
                lt_chip_is_slt offset, input.is_real⟩).operations
                  (offset + 12))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
                lt_chip_cpu_opcode offset,
                (lt_chip_write_value offset)[0],
                (lt_chip_write_value offset)[1],
                (lt_chip_write_value offset)[2],
                (lt_chip_write_value offset)[3]⟩).operations (offset + 12))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, lt_chip_write_value offset,
                input.is_real⟩).operations (offset + 12))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
        Expression.eval env (input.is_real - lt_chip_is_real offset) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (lt_chip_is_slt offset * (lt_chip_is_slt offset - 1),
                0)).operations (offset + 12))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (lt_chip_is_sltu offset * (lt_chip_is_sltu offset - 1),
                0)).operations (offset + 12))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (lt_chip_is_real offset * (lt_chip_is_real offset - 1),
                0)).operations (offset + 12))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 12)))) := by
  simp only [nativeAssertZeros, LtChip.main, lt_chip_is_slt,
    lt_chip_is_sltu, lt_chip_is_real, lt_chip_operation,
    lt_chip_write_value, lt_chip_cpu_opcode,
    Readers.CPUState.circuit, LtOperationSigned.circuit,
    Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]
  rw [show offset + 2 + 10 = offset + 12 by omega]
  simp only [List.forall_cons, List.forall_append]

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

omit [Fact (2 ^ 17 < p)] in
private theorem ltCols_asserts_decompose
    (cols : LtChip.Columns (ZMod p)) :
    Extracted.LtOracle.LtCols.asserts (ltChipReconfigure cols) =
      Extracted.LtOperationSigned.asserts
        #v[cols.adapter.op_b_memory.prev_value[0],
          cols.adapter.op_b_memory.prev_value[1],
          cols.adapter.op_b_memory.prev_value[2],
          cols.adapter.op_b_memory.prev_value[3]]
        #v[cols.adapter.op_c_memory.prev_value[0],
          cols.adapter.op_c_memory.prev_value[1],
          cols.adapter.op_c_memory.prev_value[2],
          cols.adapter.op_c_memory.prev_value[3]]
        cols.lt_operation cols.is_slt (cols.is_slt + cols.is_sltu) ++
      Extracted.CPUState.asserts cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_slt + cols.is_sltu) ++
      Extracted.ALUTypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_slt * 9 + cols.is_sltu * 10)
        #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
        cols.adapter (cols.is_slt + cols.is_sltu)
        (cols.is_slt + cols.is_sltu) ++
      [ cols.is_slt * (cols.is_slt - 1),
        cols.is_sltu * (cols.is_sltu - 1),
        (cols.is_slt + cols.is_sltu) *
          (cols.is_slt + cols.is_sltu - 1),
        cols.adapter.op_a_0 ] := by
  rw [Extracted.LtOracle.LtCols.asserts]
  dsimp only [ltChipReconfigure, ltOracleOperation]
  simp only [ltOracle_ltSigned_asserts_eq]
  rw [ltSigned_eta, cpuState_eta, aluType_eta, vec3_eta]
  simp only [zero_add]

set_option maxHeartbeats 200000 in
theorem ltChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var LtChip.Inputs (ZMod p))
    (offset : ℕ) (cols : LtChip.Columns (ZMod p))
    (hbind : BindsChipOutput LtChip.main env input offset cols)
    (hinputReal : Expression.eval env input.is_real =
      Expression.eval env (lt_chip_is_real offset)) :
    List.Forall (· = 0) (ltChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((LtChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LtChip.elaborated (p := p)) hbind
  rw [LtChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval, LtChip.eval_columns] at hbind
  subst cols
  let operation : Var Extracted.LtOperationSigned (ZMod p) :=
    lt_chip_operation offset
  let writeValue : Word (Expression (ZMod p)) :=
    lt_chip_write_value offset
  let stateValue := Eval.eval env input.state
  let adapterValue := Eval.eval env input.adapter
  let rustOperation : Extracted.LtOperationSigned (ZMod p) :=
    Eval.eval env operation
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0],
      adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2],
      adapterValue.op_b_memory.prev_value[3]]
  let rustC : Word (ZMod p) :=
    #v[adapterValue.op_c_memory.prev_value[0],
      adapterValue.op_c_memory.prev_value[1],
      adapterValue.op_c_memory.prev_value[2],
      adapterValue.op_c_memory.prev_value[3]]
  let rustIsSlt := Expression.eval env (lt_chip_is_slt offset)
  let rustIsSltu := Expression.eval env (lt_chip_is_sltu offset)
  let rustIsReal := Expression.eval env (lt_chip_is_real offset)
  let rustCpuOpcode := Expression.eval env (lt_chip_cpu_opcode offset)
  let rustWriteValue : Word (ZMod p) := Eval.eval env writeValue
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let rustState : Extracted.CPUState (ZMod p) := stateValue
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[stateValue.pc[0] + 4, stateValue.pc[1], stateValue.pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions (p := p) env cpuInput offset
    rustState rustNextPc 8 rustIsReal (by
      simp only [cpuInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
  let opInput : Var LtOperationSigned.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, operation,
      lt_chip_is_slt offset, input.is_real⟩
  have hB : Eval.eval env opInput.b = rustB := by
    simp only [opInput, rustB, adapterValue, LtChip.Inputs.op_b_val]
    rw [← eval_aluOpBPrev]
    exact (vec4_eta _).symm
  have hC : Eval.eval env opInput.cc = rustC := by
    simp only [opInput, rustC, adapterValue, LtChip.Inputs.op_c_val]
    rw [← Readers.ALUTypeReader.eval_opCPrev]
    exact (vec4_eta _).symm
  have hOpExact := ltSigned_assertions_exact (p := p) env opInput
    (offset + 12)
  have hOp :
      nativeAssertZeros env ((LtOperationSigned.main opInput).operations
          (offset + 12)) =
        Extracted.LtOperationSigned.asserts rustB rustC rustOperation
          rustIsSlt rustIsReal := by
    rw [hOpExact, hB, hC]
    simp only [opInput, rustOperation, rustIsSlt, rustIsReal]
    rw [hinputReal]
  let rustAdapter : Extracted.ALUTypeReader (ZMod p) := adapterValue
  let aluInput : Var Readers.ALUTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
      lt_chip_cpu_opcode offset,
      writeValue[0], writeValue[1], writeValue[2], writeValue[3]⟩
  have hAluReal :
      (ProvableStruct.eval env aluInput).is_real = rustIsReal := by
    rw [← ProvableStruct.eval_eq_eval, Readers.ALUTypeReader.eval_inputs]
    simpa only [aluInput, rustIsReal, ProvableType.eval_field] using hinputReal
  have hAluTrusted :
      (ProvableStruct.eval env aluInput).is_trusted = rustIsReal := by
    rw [← ProvableStruct.eval_eq_eval, Readers.ALUTypeReader.eval_inputs]
    simpa only [aluInput, rustIsReal, ProvableType.eval_field] using hinputReal
  have hAlu := CanonicalReader.aluTypeAssertions (p := p) env aluInput
    (offset + 12) stateValue.clk_high
    (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) rustCpuOpcode
    rustIsReal rustIsReal
    #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    hAluReal hAluTrusted
    (by
      change ProvableStruct.eval env input.adapter = Eval.eval env input.adapter
      exact (ProvableStruct.eval_eq_eval env input.adapter).symm)
    (by
      simp only [aluInput, rustWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 0 (by decide))
    (by
      simp only [aluInput, rustWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 1 (by decide))
    (by
      simp only [aluInput, rustWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 2 (by decide))
    (by
      simp only [aluInput, rustWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 3 (by decide)) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, writeValue, input.is_real⟩
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 :=
    (Readers.ALUTypeReader.eval_opA0 env input.adapter).symm
  have hInputGate :
      Expression.eval env (input.is_real * (input.is_real - 1)) =
        rustIsReal * (rustIsReal - 1) := by
    simpa only [eval_mul, eval_sub, Expression.eval] using
      congrArg (fun value => value * (value - 1)) hinputReal
  have hLink :
      Expression.eval env (input.is_real - lt_chip_is_real offset) = 0 := by
    simp only [eval_sub, hinputReal, sub_self]
  rw [lt_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, ltChipOracle]
  rw [ltCols_asserts_decompose]
  simp only [List.forall_append, List.forall_cons]
  rw [forall_nil_iff]
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hAluG⟩,
      hS, hU, hSum, hOpA0, _⟩
    have hOpN :
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((LtOperationSigned.main opInput).operations (offset + 12))) := by
      rw [hOp]
      simpa only [rustB, rustC, rustOperation, rustIsSlt, rustIsReal,
        operation, adapterValue, lt_chip_operation, lt_chip_is_slt,
        lt_chip_is_sltu, lt_chip_is_real, eval_add,
        ProvableType.eval_field, Expression.eval] using hOpG
    have hCpuOracle :
        List.Forall (· = 0)
          (Extracted.CPUState.asserts rustState rustNextPc 8 rustIsReal) := by
      simpa only [rustState, rustNextPc, stateValue, rustIsReal,
        lt_chip_is_real, lt_chip_is_slt, lt_chip_is_sltu, eval_add,
        ProvableType.eval_field, Expression.eval] using hCpuG
    have hCpuN := hCpu.mp hCpuOracle
    have hAluOracle :
        List.Forall (· = 0)
          (Extracted.ALUTypeReader.asserts stateValue.clk_high
            (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536)
            #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
            rustCpuOpcode rustWriteValue rustAdapter rustIsReal rustIsReal) := by
      simpa only [stateValue, rustCpuOpcode, rustWriteValue, rustAdapter,
        rustIsReal,
        writeValue, operation, adapterValue, lt_chip_write_value,
        lt_chip_operation, lt_chip_cpu_opcode, lt_chip_is_real,
        lt_chip_is_slt, lt_chip_is_sltu, eval_vec4_literal,
        eval_ltSignedBit, vec3_eta, zero_add,
        eval_add, eval_mul, ProvableType.eval_field,
        Expression.eval] using hAluG
    have hOpA0Rust : rustAdapter.op_a_0 = 0 := by
      simpa only [rustAdapter, adapterValue] using hOpA0
    have hAluPairN := hAlu.mp ⟨hAluOracle, hOpA0Rust⟩
    have hAluN := hAluPairN.1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput
        (offset + 12)).mpr trivial
    have hSN := (CanonicalReader.equalityAssertions env
      (lt_chip_is_slt offset * (lt_chip_is_slt offset - 1))
      0 (offset + 12)).mpr (by
        simpa only [lt_chip_is_slt, eval_mul, eval_sub,
          ProvableType.eval_field, Expression.eval] using hS)
    have hUN := (CanonicalReader.equalityAssertions env
      (lt_chip_is_sltu offset * (lt_chip_is_sltu offset - 1))
      0 (offset + 12)).mpr (by
        simpa only [lt_chip_is_sltu, eval_mul, eval_sub,
          ProvableType.eval_field, Expression.eval] using hU)
    have hSumN := (CanonicalReader.equalityAssertions env
      (lt_chip_is_real offset * (lt_chip_is_real offset - 1))
      0 (offset + 12)).mpr (by
        simpa only [lt_chip_is_real, lt_chip_is_slt, lt_chip_is_sltu,
          eval_mul, eval_sub, eval_add, ProvableType.eval_field,
          Expression.eval] using hSum)
    have hOpA0N := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 12)).mpr (by
        rw [hopEval]
        exact hOpA0)
    have hSumValue : rustIsReal * (rustIsReal - 1) = 0 := by
      simpa only [rustIsReal, lt_chip_is_real, lt_chip_is_slt,
        lt_chip_is_sltu, eval_add, ProvableType.eval_field,
        Expression.eval] using hSum
    exact ⟨hCpuN, hOpN, hAluN, hWriteN,
      hInputGate.trans hSumValue, hLink, hSN, hUN, hSumN, hOpA0N⟩
  · rintro ⟨hCpuN, hOpN, hAluN, _hWriteN, _hInputGateN, _hLinkN,
      hSN, hUN, hSumN, hOpA0N⟩
    have hCpuFolded := hCpu.mpr hCpuN
    have hOpFolded :
        List.Forall (· = 0)
          (Extracted.LtOperationSigned.asserts rustB rustC rustOperation
            rustIsSlt rustIsReal) := by
      rw [← hOp]
      exact hOpN
    have hOpA0 := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 12)).mp hOpA0N
    have hAluPairG := hAlu.mpr
      ⟨hAluN, by
        change (Eval.eval env input.adapter).op_a_0 = 0
        rw [← hopEval]
        exact hOpA0⟩
    have hAluOracle := hAluPairG.1
    have hS := (CanonicalReader.equalityAssertions env
      (lt_chip_is_slt offset * (lt_chip_is_slt offset - 1))
      0 (offset + 12)).mp hSN
    have hU := (CanonicalReader.equalityAssertions env
      (lt_chip_is_sltu offset * (lt_chip_is_sltu offset - 1))
      0 (offset + 12)).mp hUN
    have hSum := (CanonicalReader.equalityAssertions env
      (lt_chip_is_real offset * (lt_chip_is_real offset - 1))
      0 (offset + 12)).mp hSumN
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, trivial⟩
    · simpa only [rustB, rustC, rustOperation, rustIsSlt, rustIsReal,
        operation, adapterValue, lt_chip_operation, lt_chip_is_slt,
        lt_chip_is_sltu, lt_chip_is_real, eval_add,
        ProvableType.eval_field, Expression.eval] using hOpFolded
    · simpa only [rustState, rustNextPc, stateValue, rustIsReal,
        lt_chip_is_real, lt_chip_is_slt, lt_chip_is_sltu, eval_add,
        ProvableType.eval_field, Expression.eval] using hCpuFolded
    · simpa only [stateValue, rustCpuOpcode, rustWriteValue, rustAdapter,
        rustIsReal,
        writeValue, operation, adapterValue, lt_chip_write_value,
        lt_chip_operation, lt_chip_cpu_opcode, lt_chip_is_real,
        lt_chip_is_slt, lt_chip_is_sltu, eval_vec4_literal,
        eval_ltSignedBit, vec3_eta, zero_add,
        eval_add, eval_mul, ProvableType.eval_field,
        Expression.eval] using hAluOracle
    · simpa only [lt_chip_is_slt, eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hS
    · simpa only [lt_chip_is_sltu, eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hU
    · simpa only [lt_chip_is_real, lt_chip_is_slt, lt_chip_is_sltu,
        eval_mul, eval_sub, eval_add, ProvableType.eval_field,
        Expression.eval] using hSum
    · rw [← hopEval]
      exact hOpA0

set_option maxHeartbeats 200000 in
private theorem ltChipRowCodec_inputReal
    (cols : LtChip.Columns (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := ltChipRowCodec.assignment cols data
    Expression.eval assignment.environment
        (⟨LtChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar.is_real =
      Expression.eval assignment.environment
        (lt_chip_is_real
          (⟨LtChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowOffset) := by
  dsimp only
  let assignment := ltChipRowCodec.assignment cols data
  rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
  have hInput :
      Expression.eval
          (Environment.fromArray
            (inputFirstRow (ltChipInput cols) (ltChipLocals cols)) data)
          (varFromOffset LtChip.Inputs 0).is_real =
        (ltChipInput cols).is_real := by
    rw [← LtChip.eval_inputIsReal]
    exact congrArg (fun value => value.is_real)
      (eval_inputFirstRow (ltChipInput cols) (ltChipLocals cols) data)
  have hS := eval_local_inputFirstRow (ltChipInput cols)
    (ltChipLocals cols) data 0 (by decide)
  have hU := eval_local_inputFirstRow (ltChipInput cols)
    (ltChipLocals cols) data 1 (by decide)
  change
    Expression.eval assignment.environment
        (varFromOffset LtChip.Inputs 0).is_real =
      assignment.environment.get (size LtChip.Inputs) +
        assignment.environment.get (size LtChip.Inputs + 1)
  rw [show assignment.environment =
      Environment.fromArray
        (inputFirstRow (ltChipInput cols) (ltChipLocals cols)) data by rfl]
  rw [hInput]
  simp only [ltChipInput]
  simp only [Expression.eval] at hS hU
  rw [ltChipLocals_zero] at hS
  rw [ltChipLocals_one] at hU
  simp only [ltChipInput] at hS hU
  simpa only [Nat.add_zero] using (congrArg₂ (· + ·) hS hU).symm

set_option maxHeartbeats 200000 in
theorem ltChip_constraints_constructive
    (rustCols : Extracted.LtOracle.LtCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := ltChipRowCodec.assignment
      (ltChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (ltChipOracle.assertZeros rustCols) ↔
      (⟨LtChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := ltChipOracle.deconfigure rustCols
  let assignment := ltChipRowCodec.assignment cols data
  have hbind : BindsChipOutput LtChip.main assignment.environment
      (⟨LtChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨LtChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LtChip.circuit_main_eq] at h
    exact h
  have hinputReal :
      Expression.eval assignment.environment
          (⟨LtChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowInputVar.is_real =
        Expression.eval assignment.environment
          (lt_chip_is_real
            (⟨LtChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOffset) :=
    ltChipRowCodec_inputReal (p := p) cols data
  have hlegacy := ltChip_constraints_faithful (p := p)
    assignment.environment
    (⟨LtChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LtChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind hinputReal
  have hassertions :
      List.Forall (· = 0) (ltChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨LtChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, LtChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (LtChip.circuit (p := p))
      assignment.environment ltChip_lookups_empty).symm

omit [Fact (2 ^ 17 < p)] in
private theorem ltCols_interactions_decompose
    (cols : LtChip.Columns (ZMod p)) :
    Extracted.LtOracle.LtCols.interactions (ltChipReconfigure cols) =
      Extracted.LtOperationSigned.interactions
        #v[cols.adapter.op_b_memory.prev_value[0],
          cols.adapter.op_b_memory.prev_value[1],
          cols.adapter.op_b_memory.prev_value[2],
          cols.adapter.op_b_memory.prev_value[3]]
        #v[cols.adapter.op_c_memory.prev_value[0],
          cols.adapter.op_c_memory.prev_value[1],
          cols.adapter.op_c_memory.prev_value[2],
          cols.adapter.op_c_memory.prev_value[3]]
        cols.lt_operation cols.is_slt (cols.is_slt + cols.is_sltu) ++
      Extracted.CPUState.interactions cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_slt + cols.is_sltu) ++
      Extracted.ALUTypeReader.interactions cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_slt * 9 + cols.is_sltu * 10)
        #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
        cols.adapter (cols.is_slt + cols.is_sltu)
        (cols.is_slt + cols.is_sltu) := by
  rw [Extracted.LtOracle.LtCols.interactions]
  dsimp only [ltChipReconfigure, ltOracleOperation]
  simp only [ltOracle_ltSigned_interactions_eq]
  rw [ltSigned_eta, cpuState_eta, aluType_eta, vec3_eta]
  simp only [zero_add, List.append_nil]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_bit
    (env : Environment (ZMod p)) (offset : ℕ) :
    (Eval.eval env (lt_chip_operation (p := p) offset)).result.u16_compare_operation.bit =
      env.get (offset + 2) := by
  simp [lt_chip_operation, explicit_provable_type, circuit_norm,
    Nat.add_assoc]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_comparison_zero
    (env : Environment (ZMod p)) (offset : ℕ) :
    (Eval.eval env (lt_chip_operation (p := p) offset)).result.comparison_limbs[0] =
      env.get (offset + 8) := by
  simp [lt_chip_operation, explicit_provable_type, circuit_norm,
    Nat.add_assoc]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_comparison_one
    (env : Environment (ZMod p)) (offset : ℕ) :
    (Eval.eval env (lt_chip_operation (p := p) offset)).result.comparison_limbs[1] =
      env.get (offset + 9) := by
  simp [lt_chip_operation, explicit_provable_type, circuit_norm,
    Nat.add_assoc]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_b_msb
    (env : Environment (ZMod p)) (offset : ℕ) :
    (Eval.eval env (lt_chip_operation (p := p) offset)).b_msb.msb =
      env.get (offset + 10) := by
  simp [lt_chip_operation, explicit_provable_type, circuit_norm,
    Nat.add_assoc]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_lt_chip_c_msb
    (env : Environment (ZMod p)) (offset : ℕ) :
    (Eval.eval env (lt_chip_operation (p := p) offset)).c_msb.msb =
      env.get (offset + 11) := by
  simp [lt_chip_operation, explicit_provable_type, circuit_norm,
    Nat.add_assoc]

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

set_option maxHeartbeats 200000 in
theorem ltChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var LtChip.Inputs (ZMod p))
    (offset : ℕ) (cols : LtChip.Columns (ZMod p))
    (hbind : BindsChipOutput LtChip.main env input offset cols)
    (hinputReal : Expression.eval env input.is_real =
      Expression.eval env (lt_chip_is_real offset)) :
    List.Perm (nativeAccesses env ((LtChip.main input).operations offset))
      (ltChipOracle.accesses cols) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hsign :
      -signedVal
          (Expression.eval env input.is_real -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            Expression.eval env input.is_real) := by
    rw [(by ring :
      Expression.eval env input.adapter.imm_c -
          Expression.eval env input.is_real =
        -(Expression.eval env input.is_real -
          Expression.eval env input.adapter.imm_c)), signedVal_neg hp2]
  replace hbind := BindsChipOutput.ofElaborated
    (LtChip.elaborated (p := p)) hbind
  rw [LtChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval, LtChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  let rustCols : LtChip.Columns (ZMod p) :=
    { state := Eval.eval env input.state
      adapter := Eval.eval env input.adapter
      is_slt := Expression.eval env (lt_chip_is_slt offset)
      is_sltu := Expression.eval env (lt_chip_is_sltu offset)
      lt_operation := Eval.eval env (lt_chip_operation (p := p) offset) }
  change rustCols = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.LtOracle.LtCols.interactions (ltChipReconfigure rustCols)).map
      Extracted.Interaction.toAccess
  have hReal : Expression.eval env input.is_real =
      env.get offset + env.get (offset + 1) := by
    simpa only [lt_chip_is_real, lt_chip_is_slt, lt_chip_is_sltu,
      eval_add, Expression.eval] using hinputReal
  have hsignReal :
      -signedVal
          (env.get offset + env.get (offset + 1) -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            (env.get offset + env.get (offset + 1))) := by
    simpa only [hReal] using hsign
  have hNegFlags :
      -env.get (offset + 1) + -env.get offset =
        -(env.get offset + env.get (offset + 1)) := by
    ring
  have hDoubleNeg :
      -signedVal (-env.get (offset + 1) + -env.get offset) =
        signedVal (env.get offset + env.get (offset + 1)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((LtChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, LtChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit,
      Readers.RegisterAccessTimestamp.main,
      SP1Clean.LtOperationSigned.circuit,
      SP1Clean.LtOperationSigned.main,
      SP1Clean.U16MSBOperation.circuit,
      SP1Clean.U16MSBOperation.main,
      SP1Clean.LtOperationUnsigned.circuit,
      SP1Clean.LtOperationUnsigned.main,
      SP1Clean.U16CompareOperation.circuit,
      SP1Clean.U16CompareOperation.main,
      Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses, ChipOracle.nativeInteractions, ltChipOracle]
  rw [LtChip.interactionsWith_state_eq, LtChip.interactionsWith_byte_eq,
    LtChip.interactionsWith_memory_eq, LtChip.interactionsWith_program_eq]
  have hStatePull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.stateChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_state env gate msg
  have hStatePush :
      ∀ (mult : Expression (ZMod p))
        (msg : SP1Clean.Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.stateChannel (p := p)).pushedIf mult msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_state env mult msg
  have hBytePull :
      ∀ (gate : Expression (ZMod p)) (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.byteChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val,
             (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val,
             (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.memoryChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val,
             (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val,
             (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val,
             (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_memory env gate msg
  have hMemoryPush :
      ∀ (mult : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.memoryChannel (p := p)).pushedIf mult msg).toRaw) =
          (InteractionKind.Memory, "SP1Memory",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.addr0).val,
             (Expression.eval env msg.addr1).val,
             (Expression.eval env msg.addr2).val,
             (Expression.eval env msg.value[0]).val,
             (Expression.eval env msg.value[1]).val,
             (Expression.eval env msg.value[2]).val,
             (Expression.eval env msg.value[3]).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_memory env mult msg
  have hProgramPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((SP1Clean.Channels.programChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Program, "SP1Program",
            [(Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val,
             (Expression.eval env msg.opcode).val,
             (Expression.eval env msg.op_a).val,
             (Expression.eval env msg.op_b[0]).val,
             (Expression.eval env msg.op_b[1]).val,
             (Expression.eval env msg.op_b[2]).val,
             (Expression.eval env msg.op_b[3]).val,
             (Expression.eval env msg.op_c[0]).val,
             (Expression.eval env msg.op_c[1]).val,
             (Expression.eval env msg.op_c[2]).val,
             (Expression.eval env msg.op_c[3]).val,
             (Expression.eval env msg.op_a_0).val,
             (Expression.eval env msg.imm_b).val,
             (Expression.eval env msg.imm_c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_program env gate msg
  have hS :
      ((LtChip.exposedStateInteractions input).map
          ChannelInteraction.toRaw).map (AbstractInteraction.toAccess env) =
        rustAccesses.filter (fun access =>
          access.1 = InteractionKind.State) := by
    dsimp only [rustAccesses, rustCols]
    simp [ltCols_interactions_decompose,
      LtChip.exposedStateInteractions, hStatePull, hStatePush,
      Extracted.LtOperationSigned.interactions,
      Extracted.U16MSBOperation.interactions,
      Extracted.LtOperationUnsigned.interactions,
      Extracted.U16CompareOperation.interactions,
      Extracted.CPUState.interactions,
      Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
      Expression.eval, hReal]
    simp only [lt_chip_is_slt, lt_chip_is_sltu, Expression.eval,
      hNegFlags, true_and, neg_one_mul]
  have hB :
      List.Perm
        (((LtChip.exposedByteInteractions input offset).map
          ChannelInteraction.toRaw).map (AbstractInteraction.toAccess env))
        (rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Byte)) := by
    dsimp only [rustAccesses, rustCols]
    simp only [LtChip.exposedByteInteractions,
      List.map_cons, List.map_nil, hBytePull]
    simp [ltCols_interactions_decompose,
      Extracted.LtOperationSigned.interactions,
      Extracted.U16MSBOperation.interactions,
      Extracted.LtOperationUnsigned.interactions,
      Extracted.U16CompareOperation.interactions,
      Extracted.CPUState.interactions,
      Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      Opcode.ofNat, ConstraintCoe.coe_eq_val, signedVal_neg hp2, h6,
      LtChip.Inputs.op_b_val, LtChip.Inputs.op_c_val, hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      ProvableType.eval_field, lt_chip_is_slt, lt_chip_is_sltu,
      Expression.eval, eval_sub, hReal, hNegFlags,
      eval_lt_chip_bit, eval_lt_chip_comparison_zero,
      eval_lt_chip_comparison_one, eval_lt_chip_b_msb,
      eval_lt_chip_c_msb]
    rw [hsignReal]
    exact
      (List.perm_append_comm
        (l₁ := [_, _])
        (l₂ := [_, _, _])).append_right [_, _, _, _, _, _]
  have hM :
      List.Perm
        (((((LtChip.exposedMemoryInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult))
        (rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Memory)) := by
    dsimp only [rustAccesses, rustCols]
    simp only [LtChip.exposedMemoryInteractions,
      List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
    simp [ltCols_interactions_decompose,
      Extracted.LtOperationSigned.interactions,
      Extracted.U16MSBOperation.interactions,
      Extracted.LtOperationUnsigned.interactions,
      Extracted.U16CompareOperation.interactions,
      Extracted.CPUState.interactions,
      Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      LookupAccessList.negMult, signedVal_neg hp2, hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      ProvableType.eval_field, lt_chip_is_slt, lt_chip_is_sltu,
      Expression.eval, eval_sub, hReal, hNegFlags,
      eval_lt_chip_bit]
    simp only [signedVal_neg hp2, neg_neg]
    rw [hsignReal]
    exact (List.perm_append_comm
      (l₁ := [_, _, _, _]) (l₂ := [_])).append_left [_]
  have hP :
      (((((LtChip.exposedProgramInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult)) =
        rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Program) := by
    dsimp only [rustAccesses, rustCols]
    simp only [LtChip.exposedProgramInteractions,
      LtChip.exposedOpcode, List.map_cons, List.map_nil,
      hProgramPull]
    simp [ltCols_interactions_decompose,
      Extracted.LtOperationSigned.interactions,
      Extracted.U16MSBOperation.interactions,
      Extracted.LtOperationUnsigned.interactions,
      Extracted.U16CompareOperation.interactions,
      Extracted.CPUState.interactions,
      Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      Opcode.ofNat, ConstraintCoe.coe_eq_val,
      LookupAccessList.negMult, hReal]
    simp only [lt_chip_is_slt, lt_chip_is_sltu, Expression.eval,
      hDoubleNeg]
    simp
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  rw [hS, hP]
  exact ((hB.append_left _).append hM).append_right _

set_option maxHeartbeats 200000 in
theorem ltChip_interactions_constructive
    (rustCols : Extracted.LtOracle.LtCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := ltChipRowCodec.assignment
      (ltChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨LtChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (ltChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := ltChipOracle.deconfigure rustCols
  let assignment := ltChipRowCodec.assignment cols data
  have hbind : BindsChipOutput LtChip.main assignment.environment
      (⟨LtChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨LtChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LtChip.circuit_main_eq] at h
    exact h
  have hlegacy := ltChip_interactions_faithful (p := p)
    assignment.environment
    (⟨LtChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LtChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
    (ltChipRowCodec_inputReal (p := p) cols data)
  rw [nativeAccesses_component_eq_rowOperations (LtChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, LtChip.circuit_main_eq] using hlegacy

theorem ltChip_faithful :
    ChipFaithful (p := p) LtChip.Inputs LtChip.Columns
      Extracted.LtOracle.LtCols LtChip.circuit ltChipRowCodec ltChipOracle where
  constraints := ltChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (ltChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
