import SP1Clean.Faithful.DivRemChip
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.IsEqualWordOperation
import SP1Clean.Faithful.LtOperationUnsigned
import SP1Clean.Faithful.U16MSBOperation

/-!
# Complete whole-chip DivRem faithfulness

This module proves that the native Clean DivRem chip and the complete pinned SP1 v6.4.0
`DivRemCols` AIR have extensionally equivalent row assertions and active interaction multisets.
The proof is deliberately decomposed into folded arithmetic, reader, and bus blocks so verifier-side
normalization never unfolds the complete 246-column specification in a parent proof.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe
open SP1Clean.Channels (byteChannel stateChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private def divRemCpuInput
    (input : Var DivRemChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_real⟩

private def divRemReaderInput
    (input : Var DivRemChip.Inputs (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    Var Readers.RTypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real,
    input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc,
    cols.is_divu * 16 + cols.is_remu * 18 +
      cols.is_div * 15 + cols.is_rem * 17 +
      cols.is_divw * 25 + cols.is_remw * 27 +
      cols.is_divuw * 26 + cols.is_remuw * 28,
    cols.a[0], cols.a[1], cols.a[2], cols.a[3]⟩

private def divRemWriteInput
    (input : Var DivRemChip.Inputs (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    Var Readers.RegisterWrite.Inputs (ZMod p) :=
  ⟨input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    input.adapter.op_a, cols.a, input.is_real⟩

private theorem divRemNativeDecompose
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    nativeAssertZeros env
        ((DivRemChip.main input).operations offset) =
      nativeAssertZeros env
          ((Readers.CPUState.main (divRemCpuInput input)).operations
            (offset + 217)) ++
        nativeAssertZeros env
          ((Readers.RTypeReader.main
            (divRemReaderInput input cols)).operations (offset + 217)) ++
        nativeAssertZeros env
          ((DivRemCompare.main
            (DivRemCompare.Inputs.ofCols cols)).operations
              (offset + 217)) ++
        nativeAssertZeros env
          ((DivRemCore.main cols).operations (offset + 217)) ++
        nativeAssertZeros env
          ((Readers.RegisterWrite.main
            (divRemWriteInput input cols)).operations (offset + 217)) := by
  dsimp only
  simp only [nativeAssertZeros, DivRemChip.main,
    Circuit.operations, Circuit.bind_def,
    Operations.constraints_append, List.map_append,
    DivRemChip.populateRow_output_eq]
  have hpopulateLength :
      Operations.localLength (DivRemChip.populateRow input offset).2 = 217 :=
    DivRemChip.populateRow_localLength_eq input offset
  rw [hpopulateLength]
  simp only [DivRemChip.populateRow,
    Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_witness, Operations.constraints_nil,
    List.map_nil, List.nil_append]
  simp only [DivRemChip.constrainRow, Circuit.operations,
    Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_generalFormalCircuit,
    constraints_toSubcircuit_formalAssertion,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_nil, List.map_append, List.append_nil]
  simp only [Readers.CPUState.circuit_localLength,
    Readers.RTypeReader.circuit_localLength,
    DivRemCompare.circuit_localLength,
    DivRemCore.circuit_localLength, Nat.add_zero]
  simp only [Readers.CPUState.circuit, Readers.RTypeReader.circuit,
    DivRemCompare.circuit, DivRemCore.circuit, Readers.RegisterWrite.circuit,
    divRemCpuInput, divRemReaderInput, divRemWriteInput, List.append_assoc]

private def divRemCompareAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemCompare.Inputs F) : List F :=
  let e2 :=
    cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  Extracted.IsEqualWordOperation.asserts
      #v[cols.op_b_prev_value[0], cols.op_b_prev_value[1],
        cols.op_b_prev_value[2], cols.op_b_prev_value[3]]
      #v[0, 0, 0, 32768]
      cols.is_overflow_b cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.op_c_prev_value[0], cols.op_c_prev_value[1],
        cols.op_c_prev_value[2], cols.op_c_prev_value[3]]
      #v[65535, 65535, 65535, 65535]
      cols.is_overflow_c cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.op_b_prev_value[0], cols.op_b_prev_value[1], 0, 0]
      #v[0, 32768, 0, 0] cols.is_overflow_b e2 ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.op_c_prev_value[0], cols.op_c_prev_value[1], 0, 0]
      #v[65535, 65535, 0, 0] cols.is_overflow_c e2 ++
    Extracted.IsZeroWordOperation.asserts
      cols.c cols.is_c_0 cols.is_real ++
    Extracted.AddOperation.asserts
      cols.c cols.abs_c cols.c_neg_operation cols.abs_c_alu_event ++
    Extracted.AddOperation.asserts
      cols.remainder_comp cols.abs_remainder
      cols.rem_neg_operation cols.abs_rem_alu_event ++
    Extracted.LtOperationUnsigned.asserts
      cols.abs_remainder cols.max_abs_c_or_1
      cols.remainder_lt_operation cols.remainder_check_multiplicity ++
    Extracted.U16MSBOperation.asserts
      cols.op_b_prev_value[3] cols.b_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.op_c_prev_value[3] cols.c_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.remainder[3] cols.rem_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.op_b_prev_value[1] cols.b_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.op_c_prev_value[1] cols.c_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.remainder[1] cols.rem_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.quotient[1] cols.quot_msb e2

private def divRemRustCompareAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) : List F :=
  let e2 :=
    cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  Extracted.IsEqualWordOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[0, 0, 0, 32768]
      cols.is_overflow_b cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.adapter.op_c_memory.prev_value[0],
        cols.adapter.op_c_memory.prev_value[1],
        cols.adapter.op_c_memory.prev_value[2],
        cols.adapter.op_c_memory.prev_value[3]]
      #v[65535, 65535, 65535, 65535]
      cols.is_overflow_c cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1], 0, 0]
      #v[0, 32768, 0, 0] cols.is_overflow_b e2 ++
    Extracted.IsEqualWordOperation.asserts
      #v[cols.adapter.op_c_memory.prev_value[0],
        cols.adapter.op_c_memory.prev_value[1], 0, 0]
      #v[65535, 65535, 0, 0] cols.is_overflow_c e2 ++
    Extracted.IsZeroWordOperation.asserts
      cols.c cols.is_c_0 cols.is_real ++
    Extracted.AddOperation.asserts
      cols.c cols.abs_c
      { value :=
          #v[cols.c_neg_operation.value[0],
            cols.c_neg_operation.value[1],
            cols.c_neg_operation.value[2],
            cols.c_neg_operation.value[3]] }
      cols.abs_c_alu_event ++
    Extracted.AddOperation.asserts
      cols.remainder_comp cols.abs_remainder
      { value :=
          #v[cols.rem_neg_operation.value[0],
            cols.rem_neg_operation.value[1],
            cols.rem_neg_operation.value[2],
            cols.rem_neg_operation.value[3]] }
      cols.abs_rem_alu_event ++
    Extracted.LtOperationUnsigned.asserts
      cols.abs_remainder cols.max_abs_c_or_1
      { u16_compare_operation :=
          { bit := cols.remainder_lt_operation.u16_compare_operation.bit }
        u16_flags :=
          #v[cols.remainder_lt_operation.u16_flags[0],
            cols.remainder_lt_operation.u16_flags[1],
            cols.remainder_lt_operation.u16_flags[2],
            cols.remainder_lt_operation.u16_flags[3]]
        not_eq_inv := cols.remainder_lt_operation.not_eq_inv
        comparison_limbs :=
          #v[cols.remainder_lt_operation.comparison_limbs[0],
            cols.remainder_lt_operation.comparison_limbs[1]] }
      cols.remainder_check_multiplicity ++
    Extracted.U16MSBOperation.asserts
      cols.adapter.op_b_memory.prev_value[3]
      cols.b_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.adapter.op_c_memory.prev_value[3]
      cols.c_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.remainder[3] cols.rem_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.asserts
      cols.adapter.op_b_memory.prev_value[1] cols.b_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.adapter.op_c_memory.prev_value[1] cols.c_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.remainder[1] cols.rem_msb e2 ++
    Extracted.U16MSBOperation.asserts
      cols.quotient[1] cols.quot_msb e2

private theorem divRemCompareNativeDecompose
    (env : Environment (ZMod p))
    (input : Var DivRemCompare.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env
        ((DivRemCompare.main input).operations offset) =
      nativeAssertZeros env
          ((IsEqualWordOperation.main
            ⟨#v[input.op_b_prev_value[0], input.op_b_prev_value[1],
                input.op_b_prev_value[2], input.op_b_prev_value[3]],
              #v[0, 0, 0, 32768],
              input.is_overflow_b, input.is_real_not_word⟩).operations
            offset) ++
        nativeAssertZeros env
          ((IsEqualWordOperation.main
            ⟨#v[input.op_c_prev_value[0], input.op_c_prev_value[1],
                input.op_c_prev_value[2], input.op_c_prev_value[3]],
              #v[65535, 65535, 65535, 65535],
              input.is_overflow_c, input.is_real_not_word⟩).operations
            offset) ++
        nativeAssertZeros env
          ((IsEqualWordOperation.main
            ⟨#v[input.op_b_prev_value[0], input.op_b_prev_value[1], 0, 0],
              #v[0, 32768, 0, 0], input.is_overflow_b,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) ++
        nativeAssertZeros env
          ((IsEqualWordOperation.main
            ⟨#v[input.op_c_prev_value[0], input.op_c_prev_value[1], 0, 0],
              #v[65535, 65535, 0, 0], input.is_overflow_c,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) ++
        nativeAssertZeros env
          ((IsZeroWordOperation.main
            ⟨input.c, input.is_c_0, input.is_real⟩).operations offset) ++
        nativeAssertZeros env
          ((AddOperation.main
            ⟨input.c, input.abs_c, ⟨input.c_neg_operation.value⟩,
              input.abs_c_alu_event⟩).operations offset) ++
        nativeAssertZeros env
          ((AddOperation.main
            ⟨input.remainder_comp, input.abs_remainder,
              ⟨input.rem_neg_operation.value⟩,
              input.abs_rem_alu_event⟩).operations
            offset) ++
        nativeAssertZeros env
          ((LtOperationUnsigned.main
            ⟨input.abs_remainder, input.max_abs_c_or_1,
              input.remainder_lt_operation,
              input.remainder_check_multiplicity⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.op_b_prev_value[3], input.b_msb,
              input.is_real_not_word⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.op_c_prev_value[3], input.c_msb,
              input.is_real_not_word⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.remainder[3], input.rem_msb,
              input.is_real_not_word⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.op_b_prev_value[1], input.b_msb,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.op_c_prev_value[1], input.c_msb,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.remainder[1], input.rem_msb,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) ++
        nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.quotient[1], input.quot_msb,
              input.is_divw + input.is_remw + input.is_divuw +
                input.is_remuw⟩).operations offset) := by
  simp only [nativeAssertZeros, DivRemCompare.main,
    Circuit.operations, Circuit.bind_def, assertion,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_formalAssertion,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_nil,
    List.map_append, List.append_nil]
  simp only [IsEqualWordOperation.circuit_localLength,
    IsZeroWordOperation.circuit_localLength,
    AddOperation.circuit_localLength,
    LtOperationUnsigned.circuit_localLength,
    U16MSBOperation.circuit_localLength, Nat.add_zero]
  simp only [IsEqualWordOperation.circuit,
    IsZeroWordOperation.circuit, AddOperation.circuit,
    LtOperationUnsigned.circuit, U16MSBOperation.circuit,
    List.append_assoc]

private theorem divRemEvalVec4Literal {F : Type} [FiniteField F]
    (env : Environment F) (a b c d : Expression F) :
    Eval.eval env
        (#v[a, b, c, d] : Vector (Expression F) 4) =
      #v[Expression.eval env a, Expression.eval env b,
        Expression.eval env c, Expression.eval env d] := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env
    (#v[a, b, c, d] : Vector (Expression F) 4) i hi]
  interval_cases i <;> rfl

private theorem divRemEvalVec3Literal {F : Type} [FiniteField F]
    (env : Environment F) (a b c : Expression F) :
    Eval.eval env
        (#v[a, b, c] : Vector (Expression F) 3) =
      #v[Expression.eval env a, Expression.eval env b,
        Expression.eval env c] := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env
    (#v[a, b, c] : Vector (Expression F) 3) i hi]
  interval_cases i <;> rfl

private theorem divRemCompareNativeExact
    (env : Environment (ZMod p))
    (input : Var DivRemCompare.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env
        ((DivRemCompare.main input).operations offset) =
      divRemCompareAssertions (Eval.eval env input) := by
  rw [divRemCompareNativeDecompose]
  repeat' rw [isEqualWord_assertions_exact]
  rw [isZeroWord_assertions_exact]
  repeat' rw [add_assertions_exact]
  rw [ltUnsigned_assertions_exact]
  repeat' rw [u16msb_assertions_exact]
  rw [DivRemCompare.eval_inputs]
  repeat' rw [divRemEvalVec4Literal]
  simp only [divRemCompareAssertions,
    ProvableType.eval_field,
    ProvableType.getElem_eval_fields,
    eval_isEqualWordColumns, eval_isZeroWordColumns,
    eval_extractedAddColumns, eval_ltUnsignedColumns,
    eval_u16CompareColumns, eval_u16MSBColumns,
    Expression.eval]

private def divRemLowerMulAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) : List F :=
  Extracted.MulOperation.asserts
    #v[cols.c_times_quotient[0], cols.c_times_quotient[1],
      cols.c_times_quotient[2], cols.c_times_quotient[3]]
    cols.quotient_comp cols.c cols.c_times_quotient_lower
    cols.is_real cols.is_real 0 0 0 0

private def divRemUpperMulAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) : List F :=
  Extracted.MulOperation.asserts
    #v[cols.c_times_quotient[4], cols.c_times_quotient[5],
      cols.c_times_quotient[6], cols.c_times_quotient[7]]
    cols.quotient_comp cols.c cols.c_times_quotient_upper
    cols.is_real_not_word 0 (cols.is_div + cols.is_rem) 0
    (cols.is_divu + cols.is_remu) 0

private def divRemCpuAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (state : Extracted.CPUState F) (isReal : F) : List F :=
  Extracted.CPUState.asserts state
    #v[state.pc[0] + 4, state.pc[1], state.pc[2]]
    8 isReal

private def divRemOpcode {F : Type} [Add F] [Mul F]
    [OfNat F 15] [OfNat F 16] [OfNat F 17] [OfNat F 18]
    [OfNat F 25] [OfNat F 26] [OfNat F 27] [OfNat F 28]
    (cols : DivRemChip.Columns F) : F :=
  cols.is_divu * 16 + cols.is_remu * 18 +
    cols.is_div * 15 + cols.is_rem * 17 +
    cols.is_divw * 25 + cols.is_remw * 27 +
    cols.is_divuw * 26 + cols.is_remuw * 28

private def divRemReaderAssertions {F : Type} [Field F]
    [CoeHead F ℕ] (state : Extracted.CPUState F) (opcode : F)
    (a : Word F) (adapter : Extracted.RTypeReader F)
    (isReal : F) : List F :=
  Extracted.RTypeReader.asserts state.clk_high
    (state.clk_0_16 + state.clk_16_24 * 65536)
    state.pc opcode a adapter isReal isReal

private theorem divRemVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem divRemVec2Eta {F : Type} (value : Vector F 2) :
    #v[value[0], value[1]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem divRemVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem divRemVec16Eta {F : Type} (value : Vector F 16) :
    #v[value[0], value[1], value[2], value[3],
      value[4], value[5], value[6], value[7],
      value[8], value[9], value[10], value[11],
      value[12], value[13], value[14], value[15]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem divRemU16toU8Eta {F : Type}
    (cols : Extracted.U16toU8Operation F) :
    ({ low_bytes :=
        #v[cols.low_bytes[0], cols.low_bytes[1],
          cols.low_bytes[2], cols.low_bytes[3]] } :
      Extracted.U16toU8Operation F) = cols := by
  cases cols
  simp only
  rw [divRemVec4Eta]

private theorem divRemMulEta {F : Type}
    (cols : Extracted.MulOperation F) :
    ({ carry :=
        #v[cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3],
          cols.carry[4], cols.carry[5], cols.carry[6], cols.carry[7],
          cols.carry[8], cols.carry[9], cols.carry[10], cols.carry[11],
          cols.carry[12], cols.carry[13], cols.carry[14], cols.carry[15]]
       product :=
        #v[cols.product[0], cols.product[1], cols.product[2], cols.product[3],
          cols.product[4], cols.product[5], cols.product[6], cols.product[7],
          cols.product[8], cols.product[9], cols.product[10], cols.product[11],
          cols.product[12], cols.product[13], cols.product[14], cols.product[15]]
       b_lower_byte :=
        { low_bytes :=
            #v[cols.b_lower_byte.low_bytes[0],
              cols.b_lower_byte.low_bytes[1],
              cols.b_lower_byte.low_bytes[2],
              cols.b_lower_byte.low_bytes[3]] }
       c_lower_byte :=
        { low_bytes :=
            #v[cols.c_lower_byte.low_bytes[0],
              cols.c_lower_byte.low_bytes[1],
              cols.c_lower_byte.low_bytes[2],
              cols.c_lower_byte.low_bytes[3]] }
       b_msb := cols.b_msb
       c_msb := cols.c_msb
       product_msb := { msb := cols.product_msb.msb }
       b_sign_extend := cols.b_sign_extend
       c_sign_extend := cols.c_sign_extend } :
      Extracted.MulOperation F) = cols := by
  cases cols with
  | mk carry product bLower cLower bMsb cMsb productMsb bSign cSign =>
      cases bLower
      cases cLower
      cases productMsb
      simp only
      rw [divRemVec16Eta, divRemVec16Eta,
        divRemVec4Eta, divRemVec4Eta]

private theorem divRemCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Extracted.CPUState F) = cols := by
  cases cols
  simp only
  rw [divRemVec3Eta]

private theorem divRemRegisterAccessEta {F : Type}
    (cols : Extracted.RegisterAccessCols F) :
    ({ prev_value :=
        #v[cols.prev_value[0], cols.prev_value[1],
          cols.prev_value[2], cols.prev_value[3]]
       access_timestamp := cols.access_timestamp } :
      Extracted.RegisterAccessCols F) = cols := by
  cases cols
  simp only
  rw [divRemVec4Eta]

private theorem divRemRTypeEta {F : Type}
    (cols : Extracted.RTypeReader F) :
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
       op_c := cols.op_c
       op_c_memory :=
        { prev_value :=
            #v[cols.op_c_memory.prev_value[0],
              cols.op_c_memory.prev_value[1],
              cols.op_c_memory.prev_value[2],
              cols.op_c_memory.prev_value[3]]
          access_timestamp := cols.op_c_memory.access_timestamp } } :
      Extracted.RTypeReader F) = cols := by
  cases cols
  simp only
  rw [divRemRegisterAccessEta, divRemRegisterAccessEta,
    divRemRegisterAccessEta]

private theorem divRemAddEta {F : Type}
    (cols : Extracted.AddOperation F) :
    ({ value :=
        #v[cols.value[0], cols.value[1],
          cols.value[2], cols.value[3]] } :
      Extracted.AddOperation F) = cols := by
  cases cols
  simp only
  rw [divRemVec4Eta]

private theorem divRemAddDirectEta {F : Type}
    (cols : Extracted.AddOperation F) :
    ({ value := cols.value } : Extracted.AddOperation F) = cols := by
  cases cols
  rfl

private theorem divRemLtEta {F : Type}
    (cols : Extracted.LtOperationUnsigned F) :
    ({ u16_compare_operation := cols.u16_compare_operation
       u16_flags :=
        #v[cols.u16_flags[0], cols.u16_flags[1],
          cols.u16_flags[2], cols.u16_flags[3]]
       not_eq_inv := cols.not_eq_inv
       comparison_limbs :=
        #v[cols.comparison_limbs[0], cols.comparison_limbs[1]] } :
      Extracted.LtOperationUnsigned F) = cols := by
  cases cols
  simp only
  rw [divRemVec4Eta, divRemVec2Eta]

private theorem divRemLtDirectEta {F : Type}
    (cols : Extracted.LtOperationUnsigned F) :
    ({ u16_compare_operation := cols.u16_compare_operation
       u16_flags := cols.u16_flags
       not_eq_inv := cols.not_eq_inv
       comparison_limbs := cols.comparison_limbs } :
      Extracted.LtOperationUnsigned F) = cols := by
  cases cols
  rfl

/- Small `rfl` projection lemmas that let the giant unfolded oracle bodies be re-expressed over
native row fields by syntactic rewriting. Rewriting with these tiny proven equations keeps both
decompose proofs (and their kernel re-checks) linear in the body size; `dsimp`-reducing the folded
`divRemChipReconfigure` literal through the ~250-cell body instead makes the kernel re-derive every
projection by whnf on the whole term — the standard kernel-size cliff. -/

private theorem rc_state {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).state = cols.state := rfl

private theorem rc_adapter {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).adapter = cols.adapter := rfl

private theorem rc_a {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).a = cols.a := rfl

private theorem rc_b {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b = cols.b := rfl

private theorem rc_c {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c = cols.c := rfl

private theorem rc_quotient {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).quotient = cols.quotient := rfl

private theorem rc_quotient_comp {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).quotient_comp = cols.quotient_comp := rfl

private theorem rc_remainder_comp {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).remainder_comp = cols.remainder_comp := rfl

private theorem rc_remainder {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).remainder = cols.remainder := rfl

private theorem rc_abs_remainder {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).abs_remainder = cols.abs_remainder := rfl

private theorem rc_abs_c {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).abs_c = cols.abs_c := rfl

private theorem rc_max_abs_c_or_1 {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).max_abs_c_or_1 = cols.max_abs_c_or_1 := rfl

private theorem rc_c_times_quotient {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_times_quotient = cols.c_times_quotient := rfl

private theorem rc_carry {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).carry = cols.carry := rfl

private theorem rc_is_div {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_div = cols.is_div := rfl

private theorem rc_is_divu {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_divu = cols.is_divu := rfl

private theorem rc_is_rem {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_rem = cols.is_rem := rfl

private theorem rc_is_remu {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_remu = cols.is_remu := rfl

private theorem rc_is_divw {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_divw = cols.is_divw := rfl

private theorem rc_is_remw {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_remw = cols.is_remw := rfl

private theorem rc_is_divuw {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_divuw = cols.is_divuw := rfl

private theorem rc_is_remuw {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_remuw = cols.is_remuw := rfl

private theorem rc_is_overflow {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_overflow = cols.is_overflow := rfl

private theorem rc_b_neg {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b_neg = cols.b_neg := rfl

private theorem rc_b_neg_not_overflow {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b_neg_not_overflow = cols.b_neg_not_overflow := rfl

private theorem rc_b_not_neg_not_overflow {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b_not_neg_not_overflow = cols.b_not_neg_not_overflow := rfl

private theorem rc_is_real_not_word {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_real_not_word = cols.is_real_not_word := rfl

private theorem rc_rem_neg {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).rem_neg = cols.rem_neg := rfl

private theorem rc_c_neg {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_neg = cols.c_neg := rfl

private theorem rc_abs_c_alu_event {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).abs_c_alu_event = cols.abs_c_alu_event := rfl

private theorem rc_abs_rem_alu_event {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).abs_rem_alu_event = cols.abs_rem_alu_event := rfl

private theorem rc_is_real {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_real = cols.is_real := rfl

private theorem rc_remainder_check_multiplicity {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).remainder_check_multiplicity = cols.remainder_check_multiplicity := rfl

private theorem rc_c_times_quotient_lower {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_times_quotient_lower = divRemOracleMulOperation cols.c_times_quotient_lower := rfl

private theorem rc_c_times_quotient_upper {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_times_quotient_upper = divRemOracleMulOperation cols.c_times_quotient_upper := rfl

private theorem rc_remainder_lt_operation {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).remainder_lt_operation = divRemOracleLtOperation cols.remainder_lt_operation := rfl

private theorem rc_is_c_0 {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_c_0 = divRemOracleIsZeroWord cols.is_c_0 := rfl

private theorem rc_is_overflow_b {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_overflow_b = divRemOracleIsEqualWord cols.is_overflow_b := rfl

private theorem rc_is_overflow_c {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).is_overflow_c = divRemOracleIsEqualWord cols.is_overflow_c := rfl

private theorem rc_c_neg_operation_value {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_neg_operation.value = cols.c_neg_operation.value := rfl

private theorem rc_rem_neg_operation_value {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).rem_neg_operation.value = cols.rem_neg_operation.value := rfl

private theorem rc_b_msb_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b_msb.msb = cols.b_msb.msb := rfl

private theorem rc_rem_msb_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).rem_msb.msb = cols.rem_msb.msb := rfl

private theorem rc_c_msb_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_msb.msb = cols.c_msb.msb := rfl

private theorem rc_quot_msb_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).quot_msb.msb = cols.quot_msb.msb := rfl

private theorem om_carry {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).carry = x.carry := rfl

private theorem om_product {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).product = x.product := rfl

private theorem om_b_msb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).b_msb = x.b_msb := rfl

private theorem om_c_msb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).c_msb = x.c_msb := rfl

private theorem om_b_sign_extend {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).b_sign_extend = x.b_sign_extend := rfl

private theorem om_c_sign_extend {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).c_sign_extend = x.c_sign_extend := rfl

private theorem om_blb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).b_lower_byte.low_bytes = x.b_lower_byte.low_bytes := rfl

private theorem om_clb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).c_lower_byte.low_bytes = x.c_lower_byte.low_bytes := rfl

private theorem om_pmsb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).product_msb.msb = x.product_msb.msb := rfl

private theorem olt_bit {F : Type} (x : Extracted.LtOperationUnsigned F) :
    (divRemOracleLtOperation x).u16_compare_operation.bit = x.u16_compare_operation.bit := rfl

private theorem olt_u16_flags {F : Type} (x : Extracted.LtOperationUnsigned F) :
    (divRemOracleLtOperation x).u16_flags = x.u16_flags := rfl

private theorem olt_not_eq_inv {F : Type} (x : Extracted.LtOperationUnsigned F) :
    (divRemOracleLtOperation x).not_eq_inv = x.not_eq_inv := rfl

private theorem olt_comparison_limbs {F : Type} (x : Extracted.LtOperationUnsigned F) :
    (divRemOracleLtOperation x).comparison_limbs = x.comparison_limbs := rfl

private theorem ozw_l0_inverse {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_0.inverse = x.is_zero_limb_0.inverse := rfl

private theorem ozw_l0_result {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_0.result = x.is_zero_limb_0.result := rfl

private theorem ozw_l1_inverse {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_1.inverse = x.is_zero_limb_1.inverse := rfl

private theorem ozw_l1_result {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_1.result = x.is_zero_limb_1.result := rfl

private theorem ozw_l2_inverse {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_2.inverse = x.is_zero_limb_2.inverse := rfl

private theorem ozw_l2_result {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_2.result = x.is_zero_limb_2.result := rfl

private theorem ozw_l3_inverse {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_3.inverse = x.is_zero_limb_3.inverse := rfl

private theorem ozw_l3_result {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_3.result = x.is_zero_limb_3.result := rfl

private theorem ozw_is_zero_first_half {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_first_half = x.is_zero_first_half := rfl

private theorem ozw_is_zero_second_half {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_second_half = x.is_zero_second_half := rfl

private theorem ozw_result {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).result = x.result := rfl

private theorem oew_diff {F : Type} (x : Extracted.IsEqualWordOperation F) :
    (divRemOracleIsEqualWord x).is_diff_zero = divRemOracleIsZeroWord x.is_diff_zero := rfl


private theorem om_product_msb {F : Type} (x : Extracted.MulOperation F) :
    (divRemOracleMulOperation x).product_msb = ⟨x.product_msb.msb⟩ := rfl

private theorem olt_u16co {F : Type} (x : Extracted.LtOperationUnsigned F) :
    (divRemOracleLtOperation x).u16_compare_operation =
      ⟨x.u16_compare_operation.bit⟩ := rfl

private theorem ozw_limb_0 {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_0 =
      ⟨x.is_zero_limb_0.inverse, x.is_zero_limb_0.result⟩ := rfl

private theorem ozw_limb_1 {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_1 =
      ⟨x.is_zero_limb_1.inverse, x.is_zero_limb_1.result⟩ := rfl

private theorem ozw_limb_2 {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_2 =
      ⟨x.is_zero_limb_2.inverse, x.is_zero_limb_2.result⟩ := rfl

private theorem ozw_limb_3 {F : Type} (x : Extracted.IsZeroWordOperation F) :
    (divRemOracleIsZeroWord x).is_zero_limb_3 =
      ⟨x.is_zero_limb_3.inverse, x.is_zero_limb_3.result⟩ := rfl

private theorem rc_b_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).b_msb = ⟨cols.b_msb.msb⟩ := rfl

private theorem rc_rem_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).rem_msb = ⟨cols.rem_msb.msb⟩ := rfl

private theorem rc_c_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_msb = ⟨cols.c_msb.msb⟩ := rfl

private theorem rc_quot_msb {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).quot_msb = ⟨cols.quot_msb.msb⟩ := rfl

private theorem rc_c_neg_operation {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).c_neg_operation = ⟨cols.c_neg_operation.value⟩ := rfl

private theorem rc_rem_neg_operation {F : Type} (cols : DivRemChip.Columns F) :
    (divRemChipReconfigure cols).rem_neg_operation = ⟨cols.rem_neg_operation.value⟩ := rfl

/- Namespace bridges between the DivRem oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let every heavy
operation lemma stay stated once against the standalone modules (also consumed by the Mul chip). -/

private theorem divRemOracle_u16tou8safe_value_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values low_bytes : Vector F 4) (is_real : F) :
    Extracted.DivRemOracle.U16toU8OperationSafe.value u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.value u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.DivRemOracle.U16toU8OperationSafe.value,
    Extracted.U16toU8OperationSafe.value]

private theorem divRemOracle_u16tou8safe_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values low_bytes : Vector F 4) (is_real : F) :
    Extracted.DivRemOracle.U16toU8OperationSafe.asserts u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.asserts u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.DivRemOracle.U16toU8OperationSafe.asserts,
    Extracted.U16toU8OperationSafe.asserts]

private theorem divRemOracle_u16tou8safe_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values low_bytes : Vector F 4) (is_real : F) :
    Extracted.DivRemOracle.U16toU8OperationSafe.interactions u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.interactions u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.DivRemOracle.U16toU8OperationSafe.interactions,
    Extracted.U16toU8OperationSafe.interactions]

private theorem divRemOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.DivRemOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.DivRemOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem divRemOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.DivRemOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.DivRemOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

private theorem divRemOracle_isZero_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a inverse result is_real : F) :
    Extracted.DivRemOracle.IsZeroOperation.asserts a ⟨inverse, result⟩ is_real =
      Extracted.IsZeroOperation.asserts a ⟨inverse, result⟩ is_real := by
  rw [Extracted.DivRemOracle.IsZeroOperation.asserts,
    Extracted.IsZeroOperation.asserts]

private theorem divRemOracle_isZero_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a inverse result is_real : F) :
    Extracted.DivRemOracle.IsZeroOperation.interactions a ⟨inverse, result⟩ is_real =
      Extracted.IsZeroOperation.interactions a ⟨inverse, result⟩ is_real := by
  rw [Extracted.DivRemOracle.IsZeroOperation.interactions,
    Extracted.IsZeroOperation.interactions]

private theorem divRemOracle_isZeroWord_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a : Word F) (i0 r0 i1 r1 i2 r2 i3 r3 h1 h2 res is_real : F) :
    Extracted.DivRemOracle.IsZeroWordOperation.asserts a
        ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩ is_real =
      Extracted.IsZeroWordOperation.asserts a
        ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩ is_real := by
  rw [Extracted.DivRemOracle.IsZeroWordOperation.asserts,
    Extracted.IsZeroWordOperation.asserts]
  simp only [divRemOracle_isZero_asserts_eq]

private theorem divRemOracle_isZeroWord_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a : Word F) (i0 r0 i1 r1 i2 r2 i3 r3 h1 h2 res is_real : F) :
    Extracted.DivRemOracle.IsZeroWordOperation.interactions a
        ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩ is_real =
      Extracted.IsZeroWordOperation.interactions a
        ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩ is_real := by
  rw [Extracted.DivRemOracle.IsZeroWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions]
  simp only [divRemOracle_isZero_interactions_eq]

private theorem divRemOracle_isEqualWord_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (i0 r0 i1 r1 i2 r2 i3 r3 h1 h2 res is_real : F) :
    Extracted.DivRemOracle.IsEqualWordOperation.asserts a b
        ⟨⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩⟩ is_real =
      Extracted.IsEqualWordOperation.asserts a b
        ⟨⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩⟩ is_real := by
  rw [Extracted.DivRemOracle.IsEqualWordOperation.asserts,
    Extracted.IsEqualWordOperation.asserts]
  simp only [divRemOracle_isZeroWord_asserts_eq]

private theorem divRemOracle_isEqualWord_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (i0 r0 i1 r1 i2 r2 i3 r3 h1 h2 res is_real : F) :
    Extracted.DivRemOracle.IsEqualWordOperation.interactions a b
        ⟨⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩⟩ is_real =
      Extracted.IsEqualWordOperation.interactions a b
        ⟨⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, h1, h2, res⟩⟩ is_real := by
  rw [Extracted.DivRemOracle.IsEqualWordOperation.interactions,
    Extracted.IsEqualWordOperation.interactions]
  simp only [divRemOracle_isZeroWord_interactions_eq]

private theorem divRemOracle_addOperation_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b value : Word F) (is_real : F) :
    Extracted.DivRemOracle.AddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.DivRemOracle.AddOperation.asserts, Extracted.AddOperation.asserts]

private theorem divRemOracle_addOperation_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b value : Word F) (is_real : F) :
    Extracted.DivRemOracle.AddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.DivRemOracle.AddOperation.interactions,
    Extracted.AddOperation.interactions]

private theorem divRemOracle_u16compare_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.DivRemOracle.U16CompareOperation.asserts a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.asserts a b ⟨bit⟩ is_real := by
  rw [Extracted.DivRemOracle.U16CompareOperation.asserts,
    Extracted.U16CompareOperation.asserts]

private theorem divRemOracle_u16compare_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b bit is_real : F) :
    Extracted.DivRemOracle.U16CompareOperation.interactions a b ⟨bit⟩ is_real =
      Extracted.U16CompareOperation.interactions a b ⟨bit⟩ is_real := by
  rw [Extracted.DivRemOracle.U16CompareOperation.interactions,
    Extracted.U16CompareOperation.interactions]

private theorem divRemOracle_ltOperation_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.DivRemOracle.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.asserts b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.DivRemOracle.LtOperationUnsigned.asserts,
    Extracted.LtOperationUnsigned.asserts]
  simp only [divRemOracle_u16compare_asserts_eq]

private theorem divRemOracle_ltOperation_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (bit : F) (u16_flags : Vector F 4) (not_eq_inv : F)
    (comparison_limbs : Vector F 2) (is_real : F) :
    Extracted.DivRemOracle.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real =
      Extracted.LtOperationUnsigned.interactions b cc
        ⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩ is_real := by
  rw [Extracted.DivRemOracle.LtOperationUnsigned.interactions,
    Extracted.LtOperationUnsigned.interactions]
  simp only [divRemOracle_u16compare_interactions_eq]

/-- The DivRem oracle's embedded `MulOperation.asserts` copy agrees with the canonical standalone
module on every arithmetic block. -/
private theorem divRemOracle_mulOperation_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (carry product : Vector F 16) (blb clb : Vector F 4)
    (bmsb cmsb pmsb bse cse : F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.DivRemOracle.MulOperation.asserts a b c
        ⟨carry, product, ⟨blb⟩, ⟨clb⟩, bmsb, cmsb, ⟨pmsb⟩, bse, cse⟩
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.asserts a b c
        ⟨carry, product, ⟨blb⟩, ⟨clb⟩, bmsb, cmsb, ⟨pmsb⟩, bse, cse⟩
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.DivRemOracle.MulOperation.asserts, Extracted.MulOperation.asserts]
  simp only [divRemOracle_u16tou8safe_value_eq, divRemOracle_u16tou8safe_asserts_eq,
    divRemOracle_u16msb_asserts_eq]

/-- Interaction-list half of `divRemOracle_mulOperation_asserts_eq`. -/
private theorem divRemOracle_mulOperation_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (carry product : Vector F 16) (blb clb : Vector F 4)
    (bmsb cmsb pmsb bse cse : F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.DivRemOracle.MulOperation.interactions a b c
        ⟨carry, product, ⟨blb⟩, ⟨clb⟩, bmsb, cmsb, ⟨pmsb⟩, bse, cse⟩
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.interactions a b c
        ⟨carry, product, ⟨blb⟩, ⟨clb⟩, bmsb, cmsb, ⟨pmsb⟩, bse, cse⟩
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.DivRemOracle.MulOperation.interactions,
    Extracted.MulOperation.interactions]
  simp only [divRemOracle_u16tou8safe_value_eq,
    divRemOracle_u16tou8safe_interactions_eq, divRemOracle_u16msb_interactions_eq]


set_option linter.unusedSimpArgs false in
private theorem divRemOracle_isZeroWord_asserts_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a : Word F) (x : Extracted.IsZeroWordOperation F) (is_real : F) :
    Extracted.DivRemOracle.IsZeroWordOperation.asserts a
        (divRemOracleIsZeroWord x) is_real =
      Extracted.IsZeroWordOperation.asserts a x is_real := by
  rw [Extracted.DivRemOracle.IsZeroWordOperation.asserts,
    Extracted.IsZeroWordOperation.asserts]
  simp only [ozw_limb_0, ozw_limb_1, ozw_limb_2, ozw_limb_3,
    ozw_l0_inverse, ozw_l0_result, ozw_l1_inverse, ozw_l1_result,
    ozw_l2_inverse, ozw_l2_result, ozw_l3_inverse, ozw_l3_result,
    ozw_is_zero_first_half, ozw_is_zero_second_half, ozw_result,
    divRemOracle_isZero_asserts_eq]

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_isZeroWord_interactions_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a : Word F) (x : Extracted.IsZeroWordOperation F) (is_real : F) :
    Extracted.DivRemOracle.IsZeroWordOperation.interactions a
        (divRemOracleIsZeroWord x) is_real =
      Extracted.IsZeroWordOperation.interactions a x is_real := by
  rw [Extracted.DivRemOracle.IsZeroWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions]
  simp only [ozw_limb_0, ozw_limb_1, ozw_limb_2, ozw_limb_3,
    ozw_l0_inverse, ozw_l0_result, ozw_l1_inverse, ozw_l1_result,
    ozw_l2_inverse, ozw_l2_result, ozw_l3_inverse, ozw_l3_result,
    divRemOracle_isZero_interactions_eq]

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_isEqualWord_asserts_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (x : Extracted.IsEqualWordOperation F) (is_real : F) :
    Extracted.DivRemOracle.IsEqualWordOperation.asserts a b
        (divRemOracleIsEqualWord x) is_real =
      Extracted.IsEqualWordOperation.asserts a b x is_real := by
  rw [Extracted.DivRemOracle.IsEqualWordOperation.asserts,
    Extracted.IsEqualWordOperation.asserts]
  simp only [oew_diff, ozw_limb_0, ozw_limb_1, ozw_limb_2, ozw_limb_3,
    ozw_l0_inverse, ozw_l0_result, ozw_l1_inverse, ozw_l1_result,
    ozw_l2_inverse, ozw_l2_result, ozw_l3_inverse, ozw_l3_result,
    ozw_is_zero_first_half, ozw_is_zero_second_half, ozw_result,
    divRemOracle_isZeroWord_asserts_eq, divRemOracle_isZeroWord_asserts_eq']

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_isEqualWord_interactions_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (x : Extracted.IsEqualWordOperation F) (is_real : F) :
    Extracted.DivRemOracle.IsEqualWordOperation.interactions a b
        (divRemOracleIsEqualWord x) is_real =
      Extracted.IsEqualWordOperation.interactions a b x is_real := by
  rw [Extracted.DivRemOracle.IsEqualWordOperation.interactions,
    Extracted.IsEqualWordOperation.interactions]
  simp only [oew_diff, ozw_limb_0, ozw_limb_1, ozw_limb_2, ozw_limb_3,
    ozw_l0_inverse, ozw_l0_result, ozw_l1_inverse, ozw_l1_result,
    ozw_l2_inverse, ozw_l2_result, ozw_l3_inverse, ozw_l3_result,
    divRemOracle_isZeroWord_interactions_eq, divRemOracle_isZeroWord_interactions_eq']

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_ltOperation_asserts_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (x : Extracted.LtOperationUnsigned F) (is_real : F) :
    Extracted.DivRemOracle.LtOperationUnsigned.asserts b cc
        (divRemOracleLtOperation x) is_real =
      Extracted.LtOperationUnsigned.asserts b cc x is_real := by
  rw [Extracted.DivRemOracle.LtOperationUnsigned.asserts,
    Extracted.LtOperationUnsigned.asserts]
  simp only [olt_u16co, olt_bit, olt_u16_flags, olt_not_eq_inv,
    olt_comparison_limbs, divRemOracle_u16compare_asserts_eq]

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_ltOperation_interactions_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (x : Extracted.LtOperationUnsigned F) (is_real : F) :
    Extracted.DivRemOracle.LtOperationUnsigned.interactions b cc
        (divRemOracleLtOperation x) is_real =
      Extracted.LtOperationUnsigned.interactions b cc x is_real := by
  rw [Extracted.DivRemOracle.LtOperationUnsigned.interactions,
    Extracted.LtOperationUnsigned.interactions]
  simp only [olt_u16co, olt_bit, olt_u16_flags, olt_not_eq_inv,
    olt_comparison_limbs, divRemOracle_u16compare_interactions_eq]

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_mulOperation_asserts_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (x : Extracted.MulOperation F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.DivRemOracle.MulOperation.asserts a b c (divRemOracleMulOperation x)
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.asserts a b c x
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.DivRemOracle.MulOperation.asserts, Extracted.MulOperation.asserts]
  simp only [om_carry, om_product, om_b_msb, om_c_msb, om_b_sign_extend,
    om_c_sign_extend, om_blb, om_clb, om_pmsb, om_product_msb,
    divRemOracle_u16tou8safe_value_eq, divRemOracle_u16tou8safe_asserts_eq,
    divRemOracle_u16msb_asserts_eq]

set_option linter.unusedSimpArgs false in
private theorem divRemOracle_mulOperation_interactions_eq' {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (x : Extracted.MulOperation F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.DivRemOracle.MulOperation.interactions a b c (divRemOracleMulOperation x)
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.interactions a b c x
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.DivRemOracle.MulOperation.interactions,
    Extracted.MulOperation.interactions]
  simp only [om_carry, om_product, om_b_msb, om_c_msb, om_b_sign_extend,
    om_c_sign_extend, om_blb, om_clb, om_pmsb, om_product_msb,
    divRemOracle_u16tou8safe_value_eq, divRemOracle_u16tou8safe_interactions_eq,
    divRemOracle_u16msb_interactions_eq]

omit [Fact (2 ^ 24 < p)] in
-- The former 64M ceiling was ~3200x over: folding the twenty-way append peel into one
-- `List.append_cancel_left_eq` rewrite drops the measured floor to (10000, 20000].
set_option linter.unusedSimpArgs false in
private theorem divRemRustAssertionsDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    Extracted.DivRemOracle.DivRemCols.asserts (divRemChipReconfigure cols) =
      divRemLowerMulAssertions cols ++
        divRemUpperMulAssertions cols ++
        divRemRustCompareAssertions cols ++
        divRemCpuAssertions cols.state cols.is_real ++
        divRemReaderAssertions cols.state (divRemOpcode cols)
          cols.a cols.adapter cols.is_real ++
        DivRemChip.ownAsserts cols := by
  rw [Extracted.DivRemOracle.DivRemCols.asserts]
  simp only [rc_state,
    rc_adapter,
    rc_a,
    rc_b,
    rc_c,
    rc_quotient,
    rc_quotient_comp,
    rc_remainder_comp,
    rc_remainder,
    rc_abs_remainder,
    rc_abs_c,
    rc_max_abs_c_or_1,
    rc_c_times_quotient,
    rc_carry,
    rc_is_div,
    rc_is_divu,
    rc_is_rem,
    rc_is_remu,
    rc_is_divw,
    rc_is_remw,
    rc_is_divuw,
    rc_is_remuw,
    rc_is_overflow,
    rc_b_neg,
    rc_b_neg_not_overflow,
    rc_b_not_neg_not_overflow,
    rc_is_real_not_word,
    rc_rem_neg,
    rc_c_neg,
    rc_abs_c_alu_event,
    rc_abs_rem_alu_event,
    rc_is_real,
    rc_remainder_check_multiplicity,
    rc_c_times_quotient_lower,
    rc_c_times_quotient_upper,
    rc_remainder_lt_operation,
    rc_is_c_0,
    rc_is_overflow_b,
    rc_is_overflow_c,
    rc_c_neg_operation_value,
    rc_rem_neg_operation_value,
    rc_b_msb_msb,
    rc_rem_msb_msb,
    rc_c_msb_msb,
    rc_quot_msb_msb,
    om_carry,
    om_product,
    om_b_msb,
    om_c_msb,
    om_b_sign_extend,
    om_c_sign_extend,
    om_blb,
    om_clb,
    om_pmsb,
    olt_bit,
    olt_u16_flags,
    olt_not_eq_inv,
    olt_comparison_limbs,
    ozw_l0_inverse,
    ozw_l0_result,
    ozw_l1_inverse,
    ozw_l1_result,
    ozw_l2_inverse,
    ozw_l2_result,
    ozw_l3_inverse,
    ozw_l3_result,
    ozw_is_zero_first_half,
    ozw_is_zero_second_half,
    ozw_result,
    oew_diff]
  simp only [om_product_msb, olt_u16co, ozw_limb_0, ozw_limb_1, ozw_limb_2,
    ozw_limb_3, rc_b_msb, rc_rem_msb, rc_c_msb, rc_quot_msb,
    rc_c_neg_operation, rc_rem_neg_operation]
  simp only [divRemOracle_mulOperation_asserts_eq,
    divRemOracle_mulOperation_asserts_eq',
    divRemOracle_isEqualWord_asserts_eq, divRemOracle_isEqualWord_asserts_eq',
    divRemOracle_isZeroWord_asserts_eq, divRemOracle_isZeroWord_asserts_eq',
    divRemOracle_addOperation_asserts_eq,
    divRemOracle_ltOperation_asserts_eq, divRemOracle_ltOperation_asserts_eq',
    divRemOracle_u16msb_asserts_eq]
  simp only [divRemLowerMulAssertions, divRemUpperMulAssertions,
    divRemRustCompareAssertions, divRemCpuAssertions,
    divRemReaderAssertions, divRemOpcode, DivRemChip.ownAsserts]
  simp only [divRemMulEta, divRemCpuEta, divRemRTypeEta, divRemVec2Eta,
    divRemVec3Eta, divRemVec4Eta, divRemVec16Eta]
  simp only [List.append_assoc]
  simp only [List.append_cancel_left_eq]
  simp only [List.cons.injEq, true_and]
  norm_num

private def divRemLowerMulInput
    (cols : Var DivRemChip.Columns (ZMod p)) :
    Var MulOperation.Inputs (ZMod p) :=
  ⟨cols.quotient_comp, cols.c, cols.c_times_quotient_lower,
    cols.is_real, cols.is_real, 0, 0, 0, 0⟩

private def divRemUpperMulInput
    (cols : Var DivRemChip.Columns (ZMod p)) :
    Var MulOperation.Inputs (ZMod p) :=
  ⟨cols.quotient_comp, cols.c, cols.c_times_quotient_upper,
    cols.is_real_not_word, 0, cols.is_div + cols.is_rem,
    cols.is_divu + cols.is_remu, 0, 0⟩

private theorem divRemConstraintsMapAssert
    {F : Type} [FiniteField F] (es : List (Expression F)) :
    Operations.constraints (es.map Operation.assert) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, Operations.constraints_assert, ih]

private theorem divRemCoreNativeDecompose
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env
        ((DivRemCore.main cols).operations offset) =
      nativeAssertZeros env
          ((MulOperation.main
            (divRemLowerMulInput cols)).operations offset) ++
        nativeAssertZeros env
          ((MulOperation.main
            (divRemUpperMulInput cols)).operations offset) ++
        [Expression.eval env
            (cols.is_real * (cols.c_times_quotient[0] -
              (cols.c_times_quotient_lower.product[0] +
                cols.c_times_quotient_lower.product[1] * 256))),
          Expression.eval env
            (cols.is_real * (cols.c_times_quotient[1] -
              (cols.c_times_quotient_lower.product[2] +
                cols.c_times_quotient_lower.product[3] * 256))),
          Expression.eval env
            (cols.is_real * (cols.c_times_quotient[2] -
              (cols.c_times_quotient_lower.product[4] +
                cols.c_times_quotient_lower.product[5] * 256))),
          Expression.eval env
            (cols.is_real * (cols.c_times_quotient[3] -
              (cols.c_times_quotient_lower.product[6] +
                cols.c_times_quotient_lower.product[7] * 256))),
          Expression.eval env
            ((cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
              (cols.c_times_quotient[4] -
                (cols.c_times_quotient_upper.product[8] +
                  cols.c_times_quotient_upper.product[9] * 256))),
          Expression.eval env
            ((cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
              (cols.c_times_quotient[5] -
                (cols.c_times_quotient_upper.product[10] +
                  cols.c_times_quotient_upper.product[11] * 256))),
          Expression.eval env
            ((cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
              (cols.c_times_quotient[6] -
                (cols.c_times_quotient_upper.product[12] +
                  cols.c_times_quotient_upper.product[13] * 256))),
          Expression.eval env
            ((cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
              (cols.c_times_quotient[7] -
                (cols.c_times_quotient_upper.product[14] +
                  cols.c_times_quotient_upper.product[15] * 256)))] ++
        (DivRemChip.ownAsserts cols).map (Expression.eval env) := by
  simp only [nativeAssertZeros, DivRemCore.main,
    Circuit.operations, Circuit.bind_def, assertion,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Channel.pullIf,
    Operations.localLength, Operations.constraints_append,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_formalAssertion,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_interact, Operations.constraints_nil,
    List.map_append, List.map_nil,
    DivRemChip.assertZeros, divRemLowerMulInput,
    divRemUpperMulInput, Nat.add_zero]
  simp only [MulOperation.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [MulOperation.circuit, Gadgets.Equality.circuit]
  repeat' rw [CanonicalReader.equalityAssertionList]
  rw [divRemConstraintsMapAssert]
  simp only [Expression.eval, sub_zero, List.append_nil,
    List.nil_append, List.cons_append, List.append_assoc]

private theorem divRemLowerForward
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (hRust :
      List.Forall (· = 0)
        (divRemLowerMulAssertions (Eval.eval env cols))) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((MulOperation.main
            (divRemLowerMulInput cols)).operations offset)) ∧
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[0],
          (Eval.eval env cols).c_times_quotient[1],
          (Eval.eval env cols).c_times_quotient[2],
          (Eval.eval env cols).c_times_quotient[3]]
        (Eval.eval env cols).c_times_quotient_lower
        (Eval.eval env cols).is_real 0 0 0 0 := by
  have h := mulOperation_assertions_forward env
    (divRemLowerMulInput cols) offset
    #v[(Eval.eval env cols).c_times_quotient[0],
        (Eval.eval env cols).c_times_quotient[1],
      (Eval.eval env cols).c_times_quotient[2],
      (Eval.eval env cols).c_times_quotient[3]]
    (by
      simp only [divRemLowerMulAssertions] at hRust
      rw [DivRemChip.eval_divRemCols_quotientComp_verifier,
        DivRemChip.eval_divRemCols_c_verifier,
        DivRemChip.eval_divRemCols_mulLower_verifier,
        DivRemChip.eval_divRemCols_isReal_verifier] at hRust
      simpa only [divRemLowerMulInput,
        ProvableStruct.structEvalLiteralProc,
        DivRemChip.eval_divRemCols_ctq_getElem_verifier,
        ProvableType.eval_field, ProvableType.getElem_eval_fields,
        Expression.eval] using hRust)
  refine ⟨h.1, ?_⟩
  have hp := h.2
  simp only [divRemLowerMulInput, Expression.eval] at hp
  rw [DivRemChip.eval_divRemCols_mulLower_verifier,
    DivRemChip.eval_divRemCols_isReal_verifier]
  simpa only [ProvableType.eval_field] using hp

private theorem divRemUpperForward
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (hRust :
      List.Forall (· = 0)
        (divRemUpperMulAssertions (Eval.eval env cols))) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((MulOperation.main
            (divRemUpperMulInput cols)).operations offset)) ∧
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[4],
          (Eval.eval env cols).c_times_quotient[5],
          (Eval.eval env cols).c_times_quotient[6],
          (Eval.eval env cols).c_times_quotient[7]]
        (Eval.eval env cols).c_times_quotient_upper
        0
        ((Eval.eval env cols).is_div + (Eval.eval env cols).is_rem)
        ((Eval.eval env cols).is_divu + (Eval.eval env cols).is_remu)
        0
        0 := by
  have h := mulOperation_assertions_forward env
    (divRemUpperMulInput cols) offset
    #v[(Eval.eval env cols).c_times_quotient[4],
      (Eval.eval env cols).c_times_quotient[5],
      (Eval.eval env cols).c_times_quotient[6],
      (Eval.eval env cols).c_times_quotient[7]]
    (by
      simp only [divRemUpperMulAssertions] at hRust
      rw [DivRemChip.eval_divRemCols_quotientComp_verifier,
        DivRemChip.eval_divRemCols_c_verifier,
        DivRemChip.eval_divRemCols_mulUpper_verifier,
        DivRemChip.eval_divRemCols_isRealNotWord_verifier,
        DivRemChip.eval_divRemCols_isDiv_verifier,
        DivRemChip.eval_divRemCols_isDivu_verifier,
        DivRemChip.eval_divRemCols_isRem_verifier,
        DivRemChip.eval_divRemCols_isRemu_verifier] at hRust
      simpa only [divRemUpperMulInput,
        ProvableStruct.structEvalLiteralProc,
        DivRemChip.eval_divRemCols_ctq_getElem_verifier,
        ProvableType.eval_field, ProvableType.getElem_eval_fields,
        Expression.eval] using hRust)
  refine ⟨h.1, ?_⟩
  have hp := h.2
  simp only [divRemUpperMulInput, Expression.eval] at hp
  rw [DivRemChip.eval_divRemCols_mulUpper_verifier,
    DivRemChip.eval_divRemCols_isDiv_verifier,
    DivRemChip.eval_divRemCols_isDivu_verifier,
    DivRemChip.eval_divRemCols_isRem_verifier,
    DivRemChip.eval_divRemCols_isRemu_verifier]
  simpa only [ProvableType.eval_field] using hp

private def divRemLowerGlue (cols : DivRemChip.Columns (ZMod p)) :
    List (ZMod p) :=
  [cols.is_real * (cols.c_times_quotient[0] -
      (cols.c_times_quotient_lower.product[0] +
        cols.c_times_quotient_lower.product[1] * 256)),
    cols.is_real * (cols.c_times_quotient[1] -
      (cols.c_times_quotient_lower.product[2] +
        cols.c_times_quotient_lower.product[3] * 256)),
    cols.is_real * (cols.c_times_quotient[2] -
      (cols.c_times_quotient_lower.product[4] +
        cols.c_times_quotient_lower.product[5] * 256)),
    cols.is_real * (cols.c_times_quotient[3] -
      (cols.c_times_quotient_lower.product[6] +
        cols.c_times_quotient_lower.product[7] * 256))]

private def divRemUpperGlue (cols : DivRemChip.Columns (ZMod p)) :
    List (ZMod p) :=
  let gate := cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
  [gate * (cols.c_times_quotient[4] -
      (cols.c_times_quotient_upper.product[8] +
        cols.c_times_quotient_upper.product[9] * 256)),
    gate * (cols.c_times_quotient[5] -
      (cols.c_times_quotient_upper.product[10] +
        cols.c_times_quotient_upper.product[11] * 256)),
    gate * (cols.c_times_quotient[6] -
      (cols.c_times_quotient_upper.product[12] +
        cols.c_times_quotient_upper.product[13] * 256)),
    gate * (cols.c_times_quotient[7] -
      (cols.c_times_quotient_upper.product[14] +
        cols.c_times_quotient_upper.product[15] * 256))]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemGatedSelectorIff
    {gate value selected : ZMod p}
    (hgate : gate * (gate - 1) = 0) :
    gate * (value - gate * selected) = 0 ↔
      gate * (value - selected) = 0 := by
  constructor
  · intro h
    linear_combination h + selected * hgate
  · intro h
    linear_combination h - selected * hgate

omit [Fact (2 ^ 24 < p)] in
private theorem divRemLowerPlacementGlue
    (cols : DivRemChip.Columns (ZMod p))
    (hgate : cols.is_real * (cols.is_real - 1) = 0) :
    MulOutputPlacement
        #v[cols.c_times_quotient[0], cols.c_times_quotient[1],
          cols.c_times_quotient[2], cols.c_times_quotient[3]]
        cols.c_times_quotient_lower cols.is_real 0 0 0 0 ↔
      List.Forall (· = 0) (divRemLowerGlue cols) := by
  simp only [MulOutputPlacement, MulOperation.aSelector,
    MulOperation.productVal, divRemLowerGlue, List.Forall,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ,
    add_zero, zero_mul]
  repeat' rw [divRemGatedSelectorIff hgate]
  norm_num

omit [Fact (2 ^ 24 < p)] in
private theorem divRemUpperPlacementGlue
    (cols : DivRemChip.Columns (ZMod p))
    (hgate :
      let gate :=
        cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
      gate * (gate - 1) = 0) :
    MulOutputPlacement
        #v[cols.c_times_quotient[4], cols.c_times_quotient[5],
          cols.c_times_quotient[6], cols.c_times_quotient[7]]
        cols.c_times_quotient_upper 0
        (cols.is_div + cols.is_rem)
        (cols.is_divu + cols.is_remu) 0 0 ↔
      List.Forall (· = 0) (divRemUpperGlue cols) := by
  let gate :=
    cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
  have hgroup :
      (cols.is_div + cols.is_rem) +
          (cols.is_divu + cols.is_remu) = gate := by
    dsimp only [gate]
    ring_nf
  change gate * (gate - 1) = 0 at hgate
  simp only [MulOutputPlacement, MulOperation.aSelector,
    MulOperation.productVal, divRemUpperGlue, List.Forall,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ,
    zero_add, add_zero, zero_mul, hgroup]
  repeat' rw [divRemGatedSelectorIff hgate]
  norm_num
  simp only [gate]

private theorem divRemOwnConstraint
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p))
    (hown :
      List.Forall (· = 0)
        (DivRemChip.ownAsserts (Eval.eval env cols)))
    (expression : Expression (ZMod p))
    (hexpression : expression ∈ DivRemChip.ownAsserts cols) :
    Expression.eval env expression = 0 := by
  apply (List.forall_iff_forall_mem.mp hown)
  rw [← divRemOwnAsserts_eval env cols]
  exact List.mem_map_of_mem (f := Expression.eval env) hexpression

private structure DivRemMulFlagFacts
    (cols : DivRemChip.Columns (ZMod p)) : Prop where
  real : cols.is_real * (cols.is_real - 1) = 0
  realNotWord :
    cols.is_real_not_word * (cols.is_real_not_word - 1) = 0
  div : cols.is_div * (cols.is_div - 1) = 0
  divu : cols.is_divu * (cols.is_divu - 1) = 0
  rem : cols.is_rem * (cols.is_rem - 1) = 0
  remu : cols.is_remu * (cols.is_remu - 1) = 0
  divw : cols.is_divw * (cols.is_divw - 1) = 0
  remw : cols.is_remw * (cols.is_remw - 1) = 0
  divuw : cols.is_divuw * (cols.is_divuw - 1) = 0
  remuw : cols.is_remuw * (cols.is_remuw - 1) = 0
  sum :
    cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem +
      cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1

private theorem divRemMulFlagFacts
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p))
    (hown :
      List.Forall (· = 0)
        (DivRemChip.ownAsserts (Eval.eval env cols))) :
    DivRemMulFlagFacts (Eval.eval env cols) := by
  have hreal := divRemOwnConstraint env cols hown
    (cols.is_real * (cols.is_real - 1))
    (DivRemChip.isReal_gate_mem_ownAsserts cols)
  have hrealNotWord := divRemOwnConstraint env cols hown
    (cols.is_real_not_word * (cols.is_real_not_word - 1))
    (DivRemChip.isRealNotWord_gate_mem_ownAsserts cols)
  have hdiv := divRemOwnConstraint env cols hown
    (cols.is_div * (cols.is_div - 1))
    (DivRemChip.isDiv_gate_mem_ownAsserts cols)
  have hdivu := divRemOwnConstraint env cols hown
    (cols.is_divu * (cols.is_divu - 1))
    (DivRemChip.isDivu_gate_mem_ownAsserts cols)
  have hrem := divRemOwnConstraint env cols hown
    (cols.is_rem * (cols.is_rem - 1))
    (DivRemChip.isRem_gate_mem_ownAsserts cols)
  have hremu := divRemOwnConstraint env cols hown
    (cols.is_remu * (cols.is_remu - 1))
    (DivRemChip.isRemu_gate_mem_ownAsserts cols)
  have hdivw := divRemOwnConstraint env cols hown
    (cols.is_divw * (cols.is_divw - 1))
    (DivRemChip.isDivw_gate_mem_ownAsserts cols)
  have hremw := divRemOwnConstraint env cols hown
    (cols.is_remw * (cols.is_remw - 1))
    (DivRemChip.isRemw_gate_mem_ownAsserts cols)
  have hdivuw := divRemOwnConstraint env cols hown
    (cols.is_divuw * (cols.is_divuw - 1))
    (DivRemChip.isDivuw_gate_mem_ownAsserts cols)
  have hremuw := divRemOwnConstraint env cols hown
    (cols.is_remuw * (cols.is_remuw - 1))
    (DivRemChip.isRemuw_gate_mem_ownAsserts cols)
  have hsumZero := divRemOwnConstraint env cols hown
    (1 - (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem +
      cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw))
    (DivRemChip.flagsSum_mem_ownAsserts cols)
  constructor
  · rw [DivRemChip.eval_divRemCols_isReal_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hreal
  · rw [DivRemChip.eval_divRemCols_isRealNotWord_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hrealNotWord
  · rw [DivRemChip.eval_divRemCols_isDiv_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hdiv
  · rw [DivRemChip.eval_divRemCols_isDivu_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hdivu
  · rw [DivRemChip.eval_divRemCols_isRem_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hrem
  · rw [DivRemChip.eval_divRemCols_isRemu_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hremu
  · rw [DivRemChip.eval_divRemCols_isDivw_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hdivw
  · rw [DivRemChip.eval_divRemCols_isRemw_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hremw
  · rw [DivRemChip.eval_divRemCols_isDivuw_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hdivuw
  · rw [DivRemChip.eval_divRemCols_isRemuw_verifier]
    simpa only [ProvableType.eval_field, eval_mul, eval_sub,
      Expression.eval] using hremuw
  · rw [DivRemChip.eval_divRemCols_isDiv_verifier,
      DivRemChip.eval_divRemCols_isDivu_verifier,
      DivRemChip.eval_divRemCols_isRem_verifier,
      DivRemChip.eval_divRemCols_isRemu_verifier,
      DivRemChip.eval_divRemCols_isDivw_verifier,
      DivRemChip.eval_divRemCols_isRemw_verifier,
      DivRemChip.eval_divRemCols_isDivuw_verifier,
      DivRemChip.eval_divRemCols_isRemuw_verifier]
    simp only [ProvableType.eval_field, eval_sub,
      Expression.eval] at *
    linear_combination -hsumZero

omit [Fact (2 ^ 24 < p)] in
private theorem divRemMulPredOfBool {value : ZMod p}
    (hvalue : value = 0 ∨ value = 1) :
    value * (value - 1) = 0 := by
  rcases hvalue with hvalue | hvalue <;> rw [hvalue] <;> norm_num

private structure DivRemGroupGateFacts
    (cols : DivRemChip.Columns (ZMod p)) : Prop where
  upper :
    let gate := cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
    gate * (gate - 1) = 0
  signed :
    let gate := cols.is_div + cols.is_rem
    gate * (gate - 1) = 0
  unsigned :
    let gate := cols.is_divu + cols.is_remu
    gate * (gate - 1) = 0

private theorem divRemGroupGateFacts
    {cols : DivRemChip.Columns (ZMod p)}
    (hfacts : DivRemMulFlagFacts cols) :
    DivRemGroupGateFacts cols := by
  have bDiv := bool_of_mul_pred hfacts.div
  have bDivu := bool_of_mul_pred hfacts.divu
  have bRem := bool_of_mul_pred hfacts.rem
  have bRemu := bool_of_mul_pred hfacts.remu
  have bDivw := bool_of_mul_pred hfacts.divw
  have bRemw := bool_of_mul_pred hfacts.remw
  have bDivuw := bool_of_mul_pred hfacts.divuw
  have bRemuw := bool_of_mul_pred hfacts.remuw
  have hvals := DivRemChip.flags_val_sum
    bDivu bRemu bDiv bRem bDivw bRemw bDivuw bRemuw hfacts.sum
  have bUpper := DivRemChip.group_binary4
    bDiv bDivu bRem bRemu (by omega)
  have bSigned := DivRemChip.group_binary2 bDiv bRem (by omega)
  have bUnsigned := DivRemChip.group_binary2 bDivu bRemu (by omega)
  exact ⟨divRemMulPredOfBool bUpper,
    divRemMulPredOfBool bSigned,
    divRemMulPredOfBool bUnsigned⟩

private theorem divRemEvalMulOperation
    {F : Type} [FiniteField F]
    (env : Environment F)
    (cols : Extracted.MulOperation (Expression F)) :
    Eval.eval env cols =
      ({ carry := Eval.eval env cols.carry
         product := Eval.eval env cols.product
         b_lower_byte := Eval.eval env cols.b_lower_byte
         c_lower_byte := Eval.eval env cols.c_lower_byte
         b_msb := Eval.eval env cols.b_msb
         c_msb := Eval.eval env cols.c_msb
         product_msb := Eval.eval env cols.product_msb
         b_sign_extend := Eval.eval env cols.b_sign_extend
         c_sign_extend := Eval.eval env cols.c_sign_extend } :
        Extracted.MulOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulLowerProduct
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).c_times_quotient_lower.product[i] =
      Expression.eval env cols.c_times_quotient_lower.product[i] := by
  rw [DivRemChip.eval_divRemCols_mulLower_verifier,
    divRemEvalMulOperation]
  simpa only using
    (ProvableType.getElem_eval_fields env
      cols.c_times_quotient_lower.product i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulUpperProduct
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).c_times_quotient_upper.product[i] =
      Expression.eval env cols.c_times_quotient_upper.product[i] := by
  rw [DivRemChip.eval_divRemCols_mulUpper_verifier,
    divRemEvalMulOperation]
  simpa only using
    (ProvableType.getElem_eval_fields env
      cols.c_times_quotient_upper.product i hi).symm

private def divRemGlueExpressions
    (cols : Var DivRemChip.Columns (ZMod p)) :
    List (Expression (ZMod p)) :=
  [cols.is_real * (cols.c_times_quotient[0] -
      (cols.c_times_quotient_lower.product[0] +
        cols.c_times_quotient_lower.product[1] * 256)),
    cols.is_real * (cols.c_times_quotient[1] -
      (cols.c_times_quotient_lower.product[2] +
        cols.c_times_quotient_lower.product[3] * 256)),
    cols.is_real * (cols.c_times_quotient[2] -
      (cols.c_times_quotient_lower.product[4] +
        cols.c_times_quotient_lower.product[5] * 256)),
    cols.is_real * (cols.c_times_quotient[3] -
      (cols.c_times_quotient_lower.product[6] +
        cols.c_times_quotient_lower.product[7] * 256)),
    (cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
      (cols.c_times_quotient[4] -
        (cols.c_times_quotient_upper.product[8] +
          cols.c_times_quotient_upper.product[9] * 256)),
    (cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
      (cols.c_times_quotient[5] -
        (cols.c_times_quotient_upper.product[10] +
          cols.c_times_quotient_upper.product[11] * 256)),
    (cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
      (cols.c_times_quotient[6] -
        (cols.c_times_quotient_upper.product[12] +
          cols.c_times_quotient_upper.product[13] * 256)),
    (cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu) *
      (cols.c_times_quotient[7] -
        (cols.c_times_quotient_upper.product[14] +
          cols.c_times_quotient_upper.product[15] * 256))]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemGlueExpressionsEval
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    (divRemGlueExpressions cols).map (Expression.eval env) =
      divRemLowerGlue (Eval.eval env cols) ++
        divRemUpperGlue (Eval.eval env cols) := by
  simp only [divRemGlueExpressions, divRemLowerGlue,
    divRemUpperGlue, List.map, eval_sub, Expression.eval]
  rw [DivRemChip.eval_divRemCols_isReal_verifier,
    DivRemChip.eval_divRemCols_isDiv_verifier,
    DivRemChip.eval_divRemCols_isDivu_verifier,
    DivRemChip.eval_divRemCols_isRem_verifier,
    DivRemChip.eval_divRemCols_isRemu_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_ctq_getElem_verifier]
  repeat' rw [divRemEvalMulLowerProduct]
  repeat' rw [divRemEvalMulUpperProduct]
  simp only [ProvableType.eval_field]
  rfl

private theorem divRemCoreForallDecompose
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((DivRemCore.main cols).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((MulOperation.main
              (divRemLowerMulInput cols)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((MulOperation.main
              (divRemUpperMulInput cols)).operations offset)) ∧
        List.Forall (· = 0)
          (divRemLowerGlue (Eval.eval env cols)) ∧
        List.Forall (· = 0)
          (divRemUpperGlue (Eval.eval env cols)) ∧
        List.Forall (· = 0)
          (DivRemChip.ownAsserts (Eval.eval env cols)) := by
  rw [divRemCoreNativeDecompose]
  change List.Forall (· = 0)
      (nativeAssertZeros env
          ((MulOperation.main
            (divRemLowerMulInput cols)).operations offset) ++
        nativeAssertZeros env
          ((MulOperation.main
            (divRemUpperMulInput cols)).operations offset) ++
        (divRemGlueExpressions cols).map (Expression.eval env) ++
        (DivRemChip.ownAsserts cols).map (Expression.eval env)) ↔ _
  rw [divRemGlueExpressionsEval, divRemOwnAsserts_eval]
  simp only [List.forall_append]
  tauto

private theorem divRemLowerBackward
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (hNative :
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((MulOperation.main
            (divRemLowerMulInput cols)).operations offset)))
    (hPlacement :
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[0],
          (Eval.eval env cols).c_times_quotient[1],
          (Eval.eval env cols).c_times_quotient[2],
          (Eval.eval env cols).c_times_quotient[3]]
        (Eval.eval env cols).c_times_quotient_lower
        (Eval.eval env cols).is_real 0 0 0 0)
    (hReal :
      (Eval.eval env cols).is_real *
        ((Eval.eval env cols).is_real - 1) = 0) :
    List.Forall (· = 0)
      (divRemLowerMulAssertions (Eval.eval env cols)) := by
  have hEvalReal :
      Expression.eval env cols.is_real =
        (Eval.eval env cols).is_real := by
    simpa only [ProvableType.eval_field] using
      (DivRemChip.eval_divRemCols_isReal_verifier env cols).symm
  have hPlacement' :
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[0],
          (Eval.eval env cols).c_times_quotient[1],
          (Eval.eval env cols).c_times_quotient[2],
          (Eval.eval env cols).c_times_quotient[3]]
        (Eval.eval env (divRemLowerMulInput cols).cols)
        (Expression.eval env (divRemLowerMulInput cols).is_mul)
        (Expression.eval env (divRemLowerMulInput cols).is_mulh)
        (Expression.eval env (divRemLowerMulInput cols).is_mulhu)
        (Expression.eval env (divRemLowerMulInput cols).is_mulhsu)
        (Expression.eval env (divRemLowerMulInput cols).is_mulw) := by
    simp only [divRemLowerMulInput]
    rw [← DivRemChip.eval_divRemCols_mulLower_verifier, hEvalReal]
    exact hPlacement
  have hReal' :
      Expression.eval env (divRemLowerMulInput cols).is_mul *
        (Expression.eval env (divRemLowerMulInput cols).is_mul - 1) = 0 := by
    simp only [divRemLowerMulInput]
    rw [hEvalReal]
    exact hReal
  have hRust := mulOperation_assertions_backward env
    (divRemLowerMulInput cols) offset
    #v[(Eval.eval env cols).c_times_quotient[0],
      (Eval.eval env cols).c_times_quotient[1],
      (Eval.eval env cols).c_times_quotient[2],
      (Eval.eval env cols).c_times_quotient[3]]
    hNative hPlacement' hReal'
    (by simp only [divRemLowerMulInput, Expression.eval, zero_mul])
    (by simp only [divRemLowerMulInput, Expression.eval, zero_mul])
    (by simp only [divRemLowerMulInput, Expression.eval, zero_mul])
    (by simp only [divRemLowerMulInput, Expression.eval, zero_mul])
    (by
      simpa only [divRemLowerMulInput, Expression.eval, add_zero]
        using hReal')
  simp only [divRemLowerMulAssertions] at *
  rw [DivRemChip.eval_divRemCols_quotientComp_verifier,
    DivRemChip.eval_divRemCols_c_verifier,
    DivRemChip.eval_divRemCols_mulLower_verifier,
    DivRemChip.eval_divRemCols_isReal_verifier]
  simpa only [divRemLowerMulInput,
    DivRemChip.eval_divRemCols_ctq_getElem_verifier,
    ProvableType.eval_field, ProvableType.getElem_eval_fields,
    Expression.eval] using hRust

private theorem divRemUpperBackward
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ)
    (hNative :
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((MulOperation.main
            (divRemUpperMulInput cols)).operations offset)))
    (hPlacement :
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[4],
          (Eval.eval env cols).c_times_quotient[5],
          (Eval.eval env cols).c_times_quotient[6],
          (Eval.eval env cols).c_times_quotient[7]]
        (Eval.eval env cols).c_times_quotient_upper 0
        ((Eval.eval env cols).is_div + (Eval.eval env cols).is_rem)
        ((Eval.eval env cols).is_divu + (Eval.eval env cols).is_remu)
        0 0)
    (hGroups : DivRemGroupGateFacts (Eval.eval env cols)) :
    List.Forall (· = 0)
      (divRemUpperMulAssertions (Eval.eval env cols)) := by
  have hEvalDiv :
      Expression.eval env cols.is_div =
        (Eval.eval env cols).is_div := by
    simpa only [ProvableType.eval_field] using
      (DivRemChip.eval_divRemCols_isDiv_verifier env cols).symm
  have hEvalDivu :
      Expression.eval env cols.is_divu =
        (Eval.eval env cols).is_divu := by
    simpa only [ProvableType.eval_field] using
      (DivRemChip.eval_divRemCols_isDivu_verifier env cols).symm
  have hEvalRem :
      Expression.eval env cols.is_rem =
        (Eval.eval env cols).is_rem := by
    simpa only [ProvableType.eval_field] using
      (DivRemChip.eval_divRemCols_isRem_verifier env cols).symm
  have hEvalRemu :
      Expression.eval env cols.is_remu =
        (Eval.eval env cols).is_remu := by
    simpa only [ProvableType.eval_field] using
      (DivRemChip.eval_divRemCols_isRemu_verifier env cols).symm
  have hPlacement' :
      MulOutputPlacement
        #v[(Eval.eval env cols).c_times_quotient[4],
          (Eval.eval env cols).c_times_quotient[5],
          (Eval.eval env cols).c_times_quotient[6],
          (Eval.eval env cols).c_times_quotient[7]]
        (Eval.eval env (divRemUpperMulInput cols).cols)
        (Expression.eval env (divRemUpperMulInput cols).is_mul)
        (Expression.eval env (divRemUpperMulInput cols).is_mulh)
        (Expression.eval env (divRemUpperMulInput cols).is_mulhu)
        (Expression.eval env (divRemUpperMulInput cols).is_mulhsu)
        (Expression.eval env (divRemUpperMulInput cols).is_mulw) := by
    simp only [divRemUpperMulInput, Expression.eval]
    rw [← DivRemChip.eval_divRemCols_mulUpper_verifier,
      hEvalDiv, hEvalDivu, hEvalRem, hEvalRemu]
    exact hPlacement
  have hSigned :
      Expression.eval env (divRemUpperMulInput cols).is_mulh *
        (Expression.eval env (divRemUpperMulInput cols).is_mulh - 1) = 0 := by
    simp only [divRemUpperMulInput, Expression.eval]
    rw [hEvalDiv, hEvalRem]
    exact hGroups.signed
  have hUnsigned :
      Expression.eval env (divRemUpperMulInput cols).is_mulhu *
        (Expression.eval env (divRemUpperMulInput cols).is_mulhu - 1) = 0 := by
    simp only [divRemUpperMulInput, Expression.eval]
    rw [hEvalDivu, hEvalRemu]
    exact hGroups.unsigned
  have hSum :
      let sum :=
        Expression.eval env (divRemUpperMulInput cols).is_mul +
          Expression.eval env (divRemUpperMulInput cols).is_mulh +
          Expression.eval env (divRemUpperMulInput cols).is_mulhu +
          Expression.eval env (divRemUpperMulInput cols).is_mulhsu +
          Expression.eval env (divRemUpperMulInput cols).is_mulw
      sum * (sum - 1) = 0 := by
    simp only [divRemUpperMulInput, Expression.eval, zero_add, add_zero]
    rw [hEvalDiv, hEvalDivu, hEvalRem, hEvalRemu]
    simpa only [add_assoc, add_left_comm] using hGroups.upper
  have hRust := mulOperation_assertions_backward env
    (divRemUpperMulInput cols) offset
    #v[(Eval.eval env cols).c_times_quotient[4],
      (Eval.eval env cols).c_times_quotient[5],
      (Eval.eval env cols).c_times_quotient[6],
      (Eval.eval env cols).c_times_quotient[7]]
    hNative hPlacement'
    (by simp only [divRemUpperMulInput, Expression.eval, zero_mul])
    hSigned hUnsigned
    (by simp only [divRemUpperMulInput, Expression.eval, zero_mul])
    (by simp only [divRemUpperMulInput, Expression.eval, zero_mul])
    hSum
  simp only [divRemUpperMulAssertions] at *
  rw [DivRemChip.eval_divRemCols_quotientComp_verifier,
    DivRemChip.eval_divRemCols_c_verifier,
    DivRemChip.eval_divRemCols_mulUpper_verifier,
    DivRemChip.eval_divRemCols_isRealNotWord_verifier,
    DivRemChip.eval_divRemCols_isDiv_verifier,
    DivRemChip.eval_divRemCols_isDivu_verifier,
    DivRemChip.eval_divRemCols_isRem_verifier,
    DivRemChip.eval_divRemCols_isRemu_verifier]
  simpa only [divRemUpperMulInput,
    DivRemChip.eval_divRemCols_ctq_getElem_verifier,
    ProvableType.eval_field, ProvableType.getElem_eval_fields,
    Expression.eval] using hRust

private theorem divRemCoreAssertionsExact
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (divRemLowerMulAssertions (Eval.eval env cols) ++
          divRemUpperMulAssertions (Eval.eval env cols) ++
          DivRemChip.ownAsserts (Eval.eval env cols)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((DivRemCore.main cols).operations offset)) := by
  constructor
  · intro hRust
    have hsplit :
        (List.Forall (· = 0)
            (divRemLowerMulAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (divRemUpperMulAssertions (Eval.eval env cols))) ∧
          List.Forall (· = 0)
            (DivRemChip.ownAsserts (Eval.eval env cols)) := by
      simpa only [List.forall_append] using hRust
    obtain ⟨⟨hLowerRust, hUpperRust⟩, hown⟩ := hsplit
    have hfacts := divRemMulFlagFacts env cols hown
    have hgroups := divRemGroupGateFacts hfacts
    have hLower := divRemLowerForward env cols offset hLowerRust
    have hUpper := divRemUpperForward env cols offset hUpperRust
    apply (divRemCoreForallDecompose env cols offset).mpr
    exact ⟨hLower.1, hUpper.1,
      (divRemLowerPlacementGlue
        (Eval.eval env cols) hfacts.real).mp hLower.2,
      (divRemUpperPlacementGlue
        (Eval.eval env cols) hgroups.upper).mp hUpper.2,
      hown⟩
  · intro hNative
    obtain ⟨hLowerNative, hUpperNative, hLowerGlue,
        hUpperGlue, hown⟩ :=
      (divRemCoreForallDecompose env cols offset).mp hNative
    have hfacts := divRemMulFlagFacts env cols hown
    have hgroups := divRemGroupGateFacts hfacts
    have hLowerPlacement :=
      (divRemLowerPlacementGlue
        (Eval.eval env cols) hfacts.real).mpr hLowerGlue
    have hUpperPlacement :=
      (divRemUpperPlacementGlue
        (Eval.eval env cols) hgroups.upper).mpr hUpperGlue
    have hLowerRust := divRemLowerBackward env cols offset
      hLowerNative hLowerPlacement hfacts.real
    have hUpperRust := divRemUpperBackward env cols offset
      hUpperNative hUpperPlacement hgroups
    simp only [List.forall_append]
    exact ⟨⟨hLowerRust, hUpperRust⟩, hown⟩

omit [Fact (2 ^ 24 < p)] in
private theorem divRemRustCompare_eq
    (cols : DivRemChip.Columns (ZMod p)) :
    divRemRustCompareAssertions cols =
      divRemCompareAssertions (DivRemCompare.Inputs.ofCols cols) := by
  simp only [divRemRustCompareAssertions, divRemCompareAssertions,
    DivRemCompare.Inputs.ofCols]
  repeat' rw [divRemVec4Eta]
  rw [divRemVec2Eta]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalCompareOfCols
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    Eval.eval env (DivRemCompare.Inputs.ofCols cols) =
      DivRemCompare.Inputs.ofCols (Eval.eval env cols) := by
  rw [DivRemCompare.eval_inputs,
    DivRemChip.eval_divRemCols_verifier]
  simp [DivRemCompare.Inputs.ofCols,
    ProvableType.eval_field, ProvableType.eval_fields,
    eval_rTypeReader, eval_registerAccessCols,
    eval_u16MSBColumns, eval_isEqualWordColumns,
    eval_isZeroWordColumns, eval_extractedAddColumns,
    eval_ltUnsignedColumns, eval_u16CompareColumns]

private theorem divRemCompareAssertionsExact
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (divRemRustCompareAssertions (Eval.eval env cols)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((DivRemCompare.main
            (DivRemCompare.Inputs.ofCols cols)).operations offset)) := by
  rw [divRemCompareNativeExact, divRemEvalCompareOfCols,
    divRemRustCompare_eq]

private theorem divRemEvalPopulatedState
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (DivRemChip.populatedRowAt input offset)).state =
      Eval.eval env input.state := by
  rw [DivRemChip.eval_divRemCols_state_verifier,
    DivRemChip.populatedRowAt_state_eq]

private theorem divRemEvalPopulatedAdapter
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (DivRemChip.populatedRowAt input offset)).adapter =
      Eval.eval env input.adapter := by
  rw [DivRemChip.eval_divRemCols_adapter_verifier,
    DivRemChip.populatedRowAt_adapter_eq]

private theorem divRemEvalPopulatedIsReal
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    (Eval.eval env (DivRemChip.populatedRowAt input offset)).is_real =
      Expression.eval env input.is_real := by
  rw [DivRemChip.eval_divRemCols_isReal_verifier,
    DivRemChip.populatedRowAt_isReal_eq]
  simp only [ProvableType.eval_field]

private theorem divRemCpuAssertionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
    (divRemCpuAssertions
          (Eval.eval env (DivRemChip.populatedRowAt input offset)).state
          (Eval.eval env (DivRemChip.populatedRowAt input offset)).is_real) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.CPUState.main
            (divRemCpuInput input)).operations (offset + 217))) := by
  let state := Eval.eval env input.state
  let nextPc : Vector (ZMod p) 3 :=
    #v[state.pc[0] + 4, state.pc[1], state.pc[2]]
  let isReal := Expression.eval env input.is_real
  have h := CanonicalReader.cpuStateAssertions (p := p) env
    (divRemCpuInput input) (offset + 217) state nextPc 8 isReal (by
      simp only [divRemCpuInput, isReal,
        ProvableStruct.structEvalLiteralProc])
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simpa only [divRemCpuAssertions, state, nextPc, isReal] using h

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalOpcode
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    divRemOpcode (Eval.eval env cols) =
      Expression.eval env (divRemOpcode cols) := by
  simp only [divRemOpcode]
  rw [DivRemChip.eval_divRemCols_isDiv_verifier,
    DivRemChip.eval_divRemCols_isDivu_verifier,
    DivRemChip.eval_divRemCols_isRem_verifier,
    DivRemChip.eval_divRemCols_isRemu_verifier,
    DivRemChip.eval_divRemCols_isDivw_verifier,
    DivRemChip.eval_divRemCols_isRemw_verifier,
    DivRemChip.eval_divRemCols_isDivuw_verifier,
    DivRemChip.eval_divRemCols_isRemuw_verifier]
  simp only [ProvableType.eval_field, Expression.eval]

private theorem divRemReaderAssertionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    (List.Forall (· = 0)
          (divRemReaderAssertions
            (Eval.eval env cols).state
            (divRemOpcode (Eval.eval env cols))
            (Eval.eval env cols).a
            (Eval.eval env cols).adapter
            (Eval.eval env cols).is_real) ∧
        (Eval.eval env cols).adapter.op_a_0 = 0) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RTypeReader.main
              (divRemReaderInput input cols)).operations
                (offset + 217))) ∧
        (Eval.eval env cols).adapter.op_a_0 = 0) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let state := Eval.eval env input.state
  let adapter := Eval.eval env input.adapter
  let a := Eval.eval env cols.a
  let opcode := Expression.eval env (divRemOpcode cols)
  let isReal := Expression.eval env input.is_real
  have hop :
      Expression.eval env input.adapter.op_a_0 = adapter.op_a_0 := by
    simp only [adapter, eval_rTypeReader,
      eval_registerAccessCols, ProvableType.eval_field]
  have h := CanonicalReader.rTypeAssertions (p := p) env
    (divRemReaderInput input cols) (offset + 217)
    state.clk_high (state.clk_0_16 + state.clk_16_24 * 65536)
    opcode isReal isReal state.pc a adapter
    (by simp only [divRemReaderInput, isReal,
      ProvableStruct.structEvalLiteralProc])
    (by simp only [divRemReaderInput, isReal,
      ProvableStruct.structEvalLiteralProc])
    (by simpa only [divRemReaderInput] using hop)
    (by
      simpa only [divRemReaderInput, a] using
        (ProvableType.getElem_eval_fields env cols.a 0 (by decide)))
    (by
      simpa only [divRemReaderInput, a] using
        (ProvableType.getElem_eval_fields env cols.a 1 (by decide)))
    (by
      simpa only [divRemReaderInput, a] using
        (ProvableType.getElem_eval_fields env cols.a 2 (by decide)))
    (by
      simpa only [divRemReaderInput, a] using
        (ProvableType.getElem_eval_fields env cols.a 3 (by decide)))
    rfl
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalOpcode env cols,
    DivRemChip.eval_divRemCols_a_verifier,
    divRemEvalPopulatedAdapter env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simpa only [divRemReaderAssertions, state, adapter, a, opcode,
    isReal] using h

private theorem divRemOpA0OfOwn
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p))
    (hown :
      List.Forall (· = 0)
        (DivRemChip.ownAsserts (Eval.eval env cols))) :
    (Eval.eval env cols).adapter.op_a_0 = 0 := by
  have hop := divRemOwnConstraint env cols hown cols.adapter.op_a_0
    (DivRemChip.opA0_mem_ownAsserts cols)
  rw [DivRemChip.eval_divRemCols_adapter_verifier,
    eval_rTypeReader]
  change Eval.eval env cols.adapter.op_a_0 = 0
  simpa only [ProvableType.eval_field] using hop

private theorem divRemWholeAssertionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    List.Forall (· = 0)
        (Extracted.DivRemOracle.DivRemCols.asserts
          (divRemChipReconfigure (Eval.eval env cols))) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((DivRemChip.main input).operations offset)) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  rw [divRemRustAssertionsDecompose]
  rw [divRemNativeDecompose]
  constructor
  · intro hRust
    have hsplit :
        List.Forall (· = 0)
            (divRemLowerMulAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (divRemUpperMulAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (divRemRustCompareAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (divRemCpuAssertions (Eval.eval env cols).state
              (Eval.eval env cols).is_real) ∧
          List.Forall (· = 0)
            (divRemReaderAssertions (Eval.eval env cols).state
              (divRemOpcode (Eval.eval env cols))
              (Eval.eval env cols).a (Eval.eval env cols).adapter
              (Eval.eval env cols).is_real) ∧
          List.Forall (· = 0)
            (DivRemChip.ownAsserts (Eval.eval env cols)) := by
      simpa only [cols, List.forall_append, and_assoc] using hRust
    obtain ⟨hLower, hUpper, hCompare, hCpu, hReader, hOwn⟩ := hsplit
    have hopA0 := divRemOpA0OfOwn env cols hOwn
    have hCore :=
      (divRemCoreAssertionsExact env cols (offset + 217)).mp (by
        simpa only [List.forall_append, and_assoc] using And.intro hLower
          (And.intro hUpper hOwn))
    have hCompareNative :=
      (divRemCompareAssertionsExact env cols (offset + 217)).mp hCompare
    have hCpuNative :=
      (divRemCpuAssertionsExact env input offset).mp hCpu
    have hReaderNative :=
      ((divRemReaderAssertionsExact env input offset).mp
        ⟨hReader, hopA0⟩).1
    have hWriteNative :=
      (CanonicalReader.registerWriteAssertions env
        (divRemWriteInput input cols) (offset + 217)).mpr trivial
    simpa only [cols, List.forall_append, and_assoc] using And.intro hCpuNative
      (And.intro hReaderNative
        (And.intro hCompareNative
          (And.intro hCore hWriteNative)))
  · intro hNative
    have hsplit :
        List.Forall (· = 0)
            (nativeAssertZeros env
              ((Readers.CPUState.main
                (divRemCpuInput input)).operations (offset + 217))) ∧
          List.Forall (· = 0)
            (nativeAssertZeros env
              ((Readers.RTypeReader.main
                (divRemReaderInput input cols)).operations
                  (offset + 217))) ∧
          List.Forall (· = 0)
            (nativeAssertZeros env
              ((DivRemCompare.main
                (DivRemCompare.Inputs.ofCols cols)).operations
                  (offset + 217))) ∧
          List.Forall (· = 0)
            (nativeAssertZeros env
              ((DivRemCore.main cols).operations (offset + 217))) ∧
          List.Forall (· = 0)
            (nativeAssertZeros env
              ((Readers.RegisterWrite.main
                (divRemWriteInput input cols)).operations
                  (offset + 217))) := by
      simpa only [cols, List.forall_append, and_assoc] using hNative
    obtain ⟨hCpu, hReader, hCompare, hCore, _hWrite⟩ := hsplit
    have hCoreRust :=
      (divRemCoreAssertionsExact env cols (offset + 217)).mpr hCore
    have hCoreSplit :
        List.Forall (· = 0)
            (divRemLowerMulAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (divRemUpperMulAssertions (Eval.eval env cols)) ∧
          List.Forall (· = 0)
            (DivRemChip.ownAsserts (Eval.eval env cols)) := by
      simpa only [List.forall_append, and_assoc] using hCoreRust
    obtain ⟨hLower, hUpper, hOwn⟩ := hCoreSplit
    have hopA0 := divRemOpA0OfOwn env cols hOwn
    have hReaderRust :=
      ((divRemReaderAssertionsExact env input offset).mpr
        ⟨hReader, hopA0⟩).1
    have hCompareRust :=
      (divRemCompareAssertionsExact env cols (offset + 217)).mpr hCompare
    have hCpuRust :=
      (divRemCpuAssertionsExact env input offset).mpr hCpu
    simpa only [cols, List.forall_append, and_assoc] using And.intro hLower
      (And.intro hUpper
        (And.intro hCompareRust
          (And.intro hCpuRust
            (And.intro hReaderRust hOwn))))

private theorem divRemConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : DivRemChip.Columns (ZMod p))
    (hbind : BindsChipOutput DivRemChip.main env input offset cols) :
    List.Forall (· = 0) (divRemChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((DivRemChip.main input).operations offset)) := by
  replace hbind :=
    BindsChipOutput.ofElaborated (DivRemChip.elaborated (p := p)) hbind
  rw [← DivRemChip.elaborated.output_eq,
    DivRemChip.main_output_eq_populateRow,
    DivRemChip.populateRow_output_eq] at hbind
  subst cols
  simp only [divRemChipOracle, ChipOracle.nativeAssertZeros]
  rw [← ProvableStruct.eval_eq_eval]
  exact divRemWholeAssertionsExact env input offset

private def divRemLowerMulInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) :
    List (Extracted.Interaction F) :=
  Extracted.MulOperation.interactions
    #v[cols.c_times_quotient[0], cols.c_times_quotient[1],
      cols.c_times_quotient[2], cols.c_times_quotient[3]]
    cols.quotient_comp cols.c cols.c_times_quotient_lower
    cols.is_real cols.is_real 0 0 0 0

private def divRemUpperMulInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) :
    List (Extracted.Interaction F) :=
  Extracted.MulOperation.interactions
    #v[cols.c_times_quotient[4], cols.c_times_quotient[5],
      cols.c_times_quotient[6], cols.c_times_quotient[7]]
    cols.quotient_comp cols.c cols.c_times_quotient_upper
    cols.is_real_not_word 0 (cols.is_div + cols.is_rem) 0
    (cols.is_divu + cols.is_remu) 0

private def divRemCompareInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemCompare.Inputs F) :
    List (Extracted.Interaction F) :=
  let wordGate :=
    cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  Extracted.IsEqualWordOperation.interactions
      cols.op_b_prev_value #v[0, 0, 0, 32768]
      cols.is_overflow_b cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.interactions
      cols.op_c_prev_value #v[65535, 65535, 65535, 65535]
      cols.is_overflow_c cols.is_real_not_word ++
    Extracted.IsEqualWordOperation.interactions
      #v[cols.op_b_prev_value[0], cols.op_b_prev_value[1], 0, 0]
      #v[0, 32768, 0, 0] cols.is_overflow_b wordGate ++
    Extracted.IsEqualWordOperation.interactions
      #v[cols.op_c_prev_value[0], cols.op_c_prev_value[1], 0, 0]
      #v[65535, 65535, 0, 0] cols.is_overflow_c wordGate ++
    Extracted.IsZeroWordOperation.interactions
      cols.c cols.is_c_0 cols.is_real ++
    Extracted.AddOperation.interactions
      cols.c cols.abs_c cols.c_neg_operation cols.abs_c_alu_event ++
    Extracted.AddOperation.interactions
      cols.remainder_comp cols.abs_remainder
      cols.rem_neg_operation cols.abs_rem_alu_event ++
    Extracted.LtOperationUnsigned.interactions
      cols.abs_remainder cols.max_abs_c_or_1
      cols.remainder_lt_operation cols.remainder_check_multiplicity ++
    Extracted.U16MSBOperation.interactions
      cols.op_b_prev_value[3] cols.b_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.interactions
      cols.op_c_prev_value[3] cols.c_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.interactions
      cols.remainder[3] cols.rem_msb cols.is_real_not_word ++
    Extracted.U16MSBOperation.interactions
      cols.op_b_prev_value[1] cols.b_msb wordGate ++
    Extracted.U16MSBOperation.interactions
      cols.op_c_prev_value[1] cols.c_msb wordGate ++
    Extracted.U16MSBOperation.interactions
      cols.remainder[1] cols.rem_msb wordGate ++
    Extracted.U16MSBOperation.interactions
      cols.quotient[1] cols.quot_msb wordGate

private def divRemCpuInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (state : Extracted.CPUState F) (isReal : F) :
    List (Extracted.Interaction F) :=
  Extracted.CPUState.interactions state
    #v[state.pc[0] + 4, state.pc[1], state.pc[2]] 8 isReal

private def divRemReaderInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (state : Extracted.CPUState F) (opcode : F)
    (a : Word F) (adapter : Extracted.RTypeReader F)
    (isReal : F) : List (Extracted.Interaction F) :=
  Extracted.RTypeReader.interactions state.clk_high
    (state.clk_0_16 + state.clk_16_24 * 65536)
    state.pc opcode a adapter isReal isReal

private def divRemDirectInteractions {F : Type} [Field F]
    [CoeHead F ℕ] (cols : DivRemChip.Columns F) :
    List (Extracted.Interaction F) :=
  let rn := cols.rem_neg * 65535
  let e123 :=
    cols.c_times_quotient[0] + cols.remainder_comp[0] -
      cols.carry[0] * 65536
  let e127 :=
    cols.c_times_quotient[1] + cols.remainder_comp[1] -
      cols.carry[1] * 65536 + cols.carry[0]
  let e131 :=
    cols.c_times_quotient[2] + cols.remainder_comp[2] -
      cols.carry[2] * 65536 + cols.carry[1]
  let e135 :=
    cols.c_times_quotient[3] + cols.remainder_comp[3] -
      cols.carry[3] * 65536 + cols.carry[2]
  let e139 :=
    cols.c_times_quotient[4] + rn -
      cols.carry[4] * 65536 + cols.carry[3]
  let e143 :=
    cols.c_times_quotient[5] + rn -
      cols.carry[5] * 65536 + cols.carry[4]
  let e147 :=
    cols.c_times_quotient[6] + rn -
      cols.carry[6] * 65536 + cols.carry[5]
  let e151 :=
    cols.c_times_quotient[7] + rn -
      cols.carry[7] * 65536 + cols.carry[6]
  [ ⟨.send, .byte 6 e123 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e127 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e131 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e135 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e139 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e143 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e147 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 e151 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_c[0] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_c[1] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_c[2] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_c[3] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_remainder[0] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_remainder[1] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_remainder[2] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.abs_remainder[3] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.quotient[0] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.quotient[1] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.quotient[2] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.quotient[3] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.remainder[0] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.remainder[1] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.remainder[2] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.remainder[3] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[0] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[1] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[2] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[3] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[4] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[5] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[6] 16 0, cols.is_real⟩,
    ⟨.send, .byte 6 cols.c_times_quotient[7] 16 0, cols.is_real⟩ ]

omit [Fact (2 ^ 24 < p)] in
set_option linter.unusedSimpArgs false in
private theorem divRemRustInteractionsDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    Extracted.DivRemOracle.DivRemCols.interactions (divRemChipReconfigure cols) =
      divRemLowerMulInteractions cols ++
        divRemUpperMulInteractions cols ++
        divRemCompareInteractions (DivRemCompare.Inputs.ofCols cols) ++
        divRemCpuInteractions cols.state cols.is_real ++
        divRemReaderInteractions cols.state (divRemOpcode cols)
          cols.a cols.adapter cols.is_real ++
        divRemDirectInteractions cols := by
  rw [Extracted.DivRemOracle.DivRemCols.interactions]
  simp only [rc_state,
    rc_adapter,
    rc_a,
    rc_b,
    rc_c,
    rc_quotient,
    rc_quotient_comp,
    rc_remainder_comp,
    rc_remainder,
    rc_abs_remainder,
    rc_abs_c,
    rc_max_abs_c_or_1,
    rc_c_times_quotient,
    rc_carry,
    rc_is_div,
    rc_is_divu,
    rc_is_rem,
    rc_is_remu,
    rc_is_divw,
    rc_is_remw,
    rc_is_divuw,
    rc_is_remuw,
    rc_is_overflow,
    rc_b_neg,
    rc_b_neg_not_overflow,
    rc_b_not_neg_not_overflow,
    rc_is_real_not_word,
    rc_rem_neg,
    rc_c_neg,
    rc_abs_c_alu_event,
    rc_abs_rem_alu_event,
    rc_is_real,
    rc_remainder_check_multiplicity,
    rc_c_times_quotient_lower,
    rc_c_times_quotient_upper,
    rc_remainder_lt_operation,
    rc_is_c_0,
    rc_is_overflow_b,
    rc_is_overflow_c,
    rc_c_neg_operation_value,
    rc_rem_neg_operation_value,
    rc_b_msb_msb,
    rc_rem_msb_msb,
    rc_c_msb_msb,
    rc_quot_msb_msb,
    om_carry,
    om_product,
    om_b_msb,
    om_c_msb,
    om_b_sign_extend,
    om_c_sign_extend,
    om_blb,
    om_clb,
    om_pmsb,
    olt_bit,
    olt_u16_flags,
    olt_not_eq_inv,
    olt_comparison_limbs,
    ozw_l0_inverse,
    ozw_l0_result,
    ozw_l1_inverse,
    ozw_l1_result,
    ozw_l2_inverse,
    ozw_l2_result,
    ozw_l3_inverse,
    ozw_l3_result,
    ozw_is_zero_first_half,
    ozw_is_zero_second_half,
    ozw_result,
    oew_diff]
  simp only [om_product_msb, olt_u16co, ozw_limb_0, ozw_limb_1, ozw_limb_2,
    ozw_limb_3, rc_b_msb, rc_rem_msb, rc_c_msb, rc_quot_msb,
    rc_c_neg_operation, rc_rem_neg_operation]
  simp only [divRemOracle_mulOperation_interactions_eq,
    divRemOracle_mulOperation_interactions_eq',
    divRemOracle_isEqualWord_interactions_eq,
    divRemOracle_isEqualWord_interactions_eq',
    divRemOracle_isZeroWord_interactions_eq,
    divRemOracle_isZeroWord_interactions_eq',
    divRemOracle_addOperation_interactions_eq,
    divRemOracle_ltOperation_interactions_eq,
    divRemOracle_ltOperation_interactions_eq',
    divRemOracle_u16msb_interactions_eq]
  simp only [divRemLowerMulInteractions, divRemUpperMulInteractions,
    divRemCompareInteractions, divRemCpuInteractions,
    divRemReaderInteractions, divRemOpcode, divRemDirectInteractions,
    DivRemCompare.Inputs.ofCols]
  simp only [divRemMulEta, divRemCpuEta, divRemRTypeEta, divRemVec2Eta,
    divRemVec3Eta, divRemVec4Eta, divRemVec16Eta]
  simp only [List.append_assoc]
  congr 1

omit [Fact (2 ^ 24 < p)] in
open Classical in
private theorem divRemFilterByte
    (ops : Operations (ZMod p)) :
    (Operations.interactions ops).filter
        (fun interaction => interaction.channel = byteChannel.toRaw) =
      Operations.interactionsWith byteChannel.toRaw ops := rfl

private theorem divRemNativeByteDecompose
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    ((DivRemChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      ((Readers.CPUState.main
        (divRemCpuInput input)).operations
          (offset + 217)).interactionsWith byteChannel.toRaw ++
        ((Readers.RTypeReader.main
          (divRemReaderInput input cols)).operations
            (offset + 217)).interactionsWith byteChannel.toRaw ++
        ((DivRemCompare.main
          (DivRemCompare.Inputs.ofCols cols)).operations
            (offset + 217)).interactionsWith byteChannel.toRaw ++
        ((DivRemCore.main cols).operations
            (offset + 217)).interactionsWith byteChannel.toRaw := by
  dsimp only
  simp only [DivRemChip.main, Circuit.operations, Circuit.bind_def,
    Operations.interactionsWith_append,
    DivRemChip.populateRow_output_eq]
  have hpopulateLength :
      Operations.localLength (DivRemChip.populateRow input offset).2 = 217 :=
    DivRemChip.populateRow_localLength_eq input offset
  rw [hpopulateLength]
  simp only [DivRemChip.populateRow,
    Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness_provable, witnessIR,
    Operations.localLength, Operations.interactionsWith_append,
    Operations.interactionsWith_witness,
    Operations.interactionsWith_nil, List.nil_append]
  simp only [DivRemChip.constrainRow, Circuit.operations,
    Circuit.bind_def, Circuit.pure_def,
    subcircuitWithAssertion, assertion,
    Operations.localLength, Operations.interactionsWith_append,
    Operations.interactionsWith_subcircuit,
    GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    Operations.interactionsWith_nil, List.append_nil]
  simp only [Readers.CPUState.circuit_localLength,
    Readers.RTypeReader.circuit_localLength,
    DivRemCompare.circuit_localLength,
    DivRemCore.circuit_localLength, Nat.add_zero]
  simp only [Readers.CPUState.circuit, Readers.RTypeReader.circuit,
    DivRemCompare.circuit, DivRemCore.circuit,
    Readers.RegisterWrite.circuit,
    divRemCpuInput, divRemReaderInput, List.append_assoc]
  repeat' rw [divRemFilterByte]
  have hwrite :
      ((Readers.RegisterWrite.main
        { clk_high := input.state.clk_high
          clk_low :=
            input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4
          op_a := input.adapter.op_a
          value := (DivRemChip.populatedRowAt input offset).a
          is_real := input.is_real }).operations
            (offset + 217)).interactionsWith byteChannel.toRaw = [] := by
    simp [Readers.RegisterWrite.main, Operations.interactionsWith,
      circuit_norm]
  rw [hwrite]
  simp only [List.append_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemIsEqualInteractionsExact
    (env : Environment (ZMod p))
    (input : Var IsEqualWordOperation.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.IsEqualWordOperation.interactions
        (Eval.eval env input.a) (Eval.eval env input.b)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real)).map
          Extracted.Interaction.toAccess =
      (((IsEqualWordOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) :=
  isEqualWord_interactions_faithful_syntactic env input offset
    (Eval.eval env input.a) (Eval.eval env input.b)
    (Expression.eval env input.is_real) (Eval.eval env input.cols)

omit [Fact (2 ^ 24 < p)] in
private theorem divRemIsZeroWordInteractionsExact
    (env : Environment (ZMod p))
    (input : Var IsZeroWordOperation.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.IsZeroWordOperation.interactions
        (Eval.eval env input.a) (Eval.eval env input.cols)
        (Expression.eval env input.is_real)).map
          Extracted.Interaction.toAccess =
      (((IsZeroWordOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) :=
  isZeroWord_interactions_faithful_syntactic env input offset
    (Eval.eval env input.a) (Expression.eval env input.is_real)
    (Eval.eval env input.cols)

private theorem divRemAddInteractionsExact
    (env : Environment (ZMod p))
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.AddOperation.interactions
        (Eval.eval env input.a) (Eval.eval env input.b)
        ⟨Eval.eval env input.cols.value⟩
        (Expression.eval env input.is_real)).map
          Extracted.Interaction.toAccess =
      (((AddOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  let value := Eval.eval env input.cols.value
  have h := add_interactions_faithful_syntactic env input offset
    value (Expression.eval env input.is_real) rfl
    (by
      exact ProvableType.getElem_eval_fields env
        input.cols.value 0 (by decide))
    (by
      exact ProvableType.getElem_eval_fields env
        input.cols.value 1 (by decide))
    (by
      exact ProvableType.getElem_eval_fields env
        input.cols.value 2 (by decide))
    (by
      exact ProvableType.getElem_eval_fields env
        input.cols.value 3 (by decide))
  simpa only [Extracted.AddOperation.interactions, value] using h

private theorem divRemLtInteractionsExact
    (env : Environment (ZMod p))
    (input : Var LtOperationUnsigned.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.LtOperationUnsigned.interactions
        (Eval.eval env input.b) (Eval.eval env input.cc)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real)).map
          Extracted.Interaction.toAccess =
      (((LtOperationUnsigned.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  apply ltUnsigned_interactions_faithful_syntactic env input offset
  · rfl
  · rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 0 (by decide)
  · rw [eval_ltUnsignedColumns]
    exact ProvableType.getElem_eval_fields env
      input.cols.comparison_limbs 1 (by decide)
  · simp only [eval_ltUnsignedColumns, eval_u16CompareColumns,
      ProvableType.eval_field]

private theorem divRemU16MSBInteractionsExact
    (env : Environment (ZMod p))
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.U16MSBOperation.interactions
        (Expression.eval env input.a) (Eval.eval env input.cols)
        (Expression.eval env input.is_real)).map
          Extracted.Interaction.toAccess =
      (((U16MSBOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  apply u16msb_interactions_faithful_syntactic env input offset
  · rfl
  · rfl
  · simp only [eval_u16MSBColumns, ProvableType.eval_field]

private theorem divRemCompareInteractionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemCompare.Inputs (ZMod p)) (offset : ℕ) :
    (divRemCompareInteractions (Eval.eval env input)).map
        Extracted.Interaction.toAccess =
      (((DivRemCompare.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  simp only [DivRemCompare.main, Circuit.operations,
    Circuit.bind_def, assertion,
    Operations.localLength, Operations.interactionsWith_append,
    Operations.interactionsWith_subcircuit,
    FormalAssertion.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_localLength,
    Operations.interactionsWith_nil,
    List.map_append, List.append_nil]
  simp only [IsEqualWordOperation.circuit_localLength,
    IsZeroWordOperation.circuit_localLength,
    AddOperation.circuit_localLength,
    LtOperationUnsigned.circuit_localLength,
    U16MSBOperation.circuit_localLength, Nat.add_zero]
  simp only [IsEqualWordOperation.circuit,
    IsZeroWordOperation.circuit, AddOperation.circuit,
    LtOperationUnsigned.circuit, U16MSBOperation.circuit]
  repeat' rw [divRemFilterByte]
  repeat' rw [← divRemIsEqualInteractionsExact]
  rw [← divRemIsZeroWordInteractionsExact]
  repeat' rw [← divRemAddInteractionsExact]
  rw [← divRemLtInteractionsExact]
  repeat' rw [← divRemU16MSBInteractionsExact]
  rw [DivRemCompare.eval_inputs]
  simp only [divRemCompareInteractions,
    ProvableType.eval_field,
    ProvableType.getElem_eval_fields,
    eval_isEqualWordColumns, eval_isZeroWordColumns,
    eval_extractedAddColumns, eval_ltUnsignedColumns,
    eval_u16CompareColumns, eval_u16MSBColumns,
    Expression.eval]
  simp only [Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions,
    List.map_nil, List.nil_append, List.map_append, List.append_assoc]

private theorem divRemCpuByteInteractionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    (((Readers.CPUState.main
      (divRemCpuInput input)).operations
        (offset + 217)).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env) =
      ((divRemCpuInteractions
        (Eval.eval env cols).state
        (Eval.eval env cols).is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Byte) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let state := Eval.eval env input.state
  let nextPc : Vector (ZMod p) 3 :=
    #v[state.pc[0] + 4, state.pc[1], state.pc[2]]
  let isReal := Expression.eval env input.is_real
  have h := cpustate_byte_interactions_faithful_syntactic env
    (divRemCpuInput input) (offset + 217)
    state nextPc 8 isReal
    (by simp only [divRemCpuInput, isReal])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.eval_field])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.eval_field])
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simpa only [divRemCpuInteractions, state, nextPc, isReal] using h

private theorem divRemReaderByteInteractionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    (((Readers.RTypeReader.main
      (divRemReaderInput input cols)).operations
        (offset + 217)).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env) =
      ((divRemReaderInteractions
        (Eval.eval env cols).state
        (divRemOpcode (Eval.eval env cols))
        (Eval.eval env cols).a
        (Eval.eval env cols).adapter
        (Eval.eval env cols).is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Byte) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let state := Eval.eval env input.state
  let adapter := Eval.eval env input.adapter
  let a := Eval.eval env cols.a
  let opcode := Expression.eval env (divRemOpcode cols)
  let isReal := Expression.eval env input.is_real
  have h := rtypereader_byte_interactions_faithful_syntactic env
    (divRemReaderInput input cols) (offset + 217)
    state.clk_high (state.clk_0_16 + state.clk_16_24 * 65536)
    state.pc opcode a adapter isReal isReal
    (by simp only [divRemReaderInput, isReal])
    (by
      simp only [divRemReaderInput, state, eval_cpuState,
        ProvableType.eval_field, Expression.eval])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, eval_registerAccessTimestamp,
        ProvableType.eval_field])
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalOpcode env cols,
    DivRemChip.eval_divRemCols_a_verifier,
    divRemEvalPopulatedAdapter env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simpa only [divRemReaderInteractions, state, adapter, a, opcode,
    isReal] using h

private theorem divRemCoreByteDecompose
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    (((DivRemCore.main cols).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) =
      (((MulOperation.main
        (divRemLowerMulInput cols)).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env) ++
        (((MulOperation.main
          (divRemUpperMulInput cols)).operations offset).interactionsWith
            byteChannel.toRaw).map (AbstractInteraction.toAccess env) ++
        (divRemDirectInteractions (Eval.eval env cols)).map
          Extracted.Interaction.toAccess := by
  simp only [DivRemCore.main, Circuit.operations, Circuit.bind_def,
    assertion, HasAssertEq.assert_eq, Expression.assertEquals,
    Channel.pullIf, Operations.localLength,
    Operations.interactionsWith_append,
    Operations.interactionsWith_subcircuit,
    FormalAssertion.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_localLength,
    Operations.interactionsWith_interact,
    Operations.interactionsWith_nil,
    List.map_append, List.append_nil]
  simp only [MulOperation.circuit_localLength,
    Gadgets.Equality.localLength_eq, Nat.add_zero]
  simp only [
    MulOperation.circuit, Gadgets.Equality.circuit,
    divRemLowerMulInput, divRemUpperMulInput]
  repeat' rw [divRemFilterByte]
  have heq (n : ℕ)
      (inp : Expression (ZMod p) × Expression (ZMod p)) :
      ((@Gadgets.Equality.main (ZMod p) inferInstance field
        inferInstance inp).operations n).interactionsWith
          byteChannel.toRaw = [] := by
    simp [Gadgets.Equality.main, Operations.interactionsWith,
      circuit_norm]
  repeat' rw [heq]
  have hown :
      ((DivRemChip.assertZeros
        (DivRemChip.ownAsserts cols)).operations offset).interactionsWith
          byteChannel.toRaw = [] := by
    simp only [DivRemChip.assertZeros, Circuit.operations, circuit_norm]
  rw [hown]
  simp only [List.map_nil, List.nil_append, circuit_norm]
  simp only [divRemDirectInteractions,
    List.map_cons, List.map_nil,
    Extracted.Interaction.toAccess_byte,
    toAccess_pullIf_byte,
    Expression.eval]
  rw [← ProvableStruct.eval_eq_eval env cols]
  rw [DivRemChip.eval_divRemCols_isReal_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_ctq_getElem_verifier]
  rw [DivRemChip.eval_divRemCols_remNeg_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_remainderComp_getElem_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_carry_getElem_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_absC_getElem_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_absRemainder_getElem_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_quotient_getElem_verifier]
  repeat' rw [DivRemChip.eval_divRemCols_remainder_getElem_verifier]
  simp only [ProvableType.eval_field, eval_sub,
    Expression.eval, neg_one_mul]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalU16toU8
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16toU8Operation (Expression F)) :
    Eval.eval env cols =
      ({ low_bytes := Eval.eval env cols.low_bytes } :
        Extracted.U16toU8Operation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulProduct
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).product[i] =
      Expression.eval env cols.product[i] := by
  rw [divRemEvalMulOperation]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.product i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulCarry
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).carry[i] =
      Expression.eval env cols.carry[i] := by
  rw [divRemEvalMulOperation]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.carry i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulBLower
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).b_lower_byte.low_bytes[i] =
      Expression.eval env cols.b_lower_byte.low_bytes[i] := by
  rw [divRemEvalMulOperation,
    divRemEvalU16toU8 env cols.b_lower_byte]
  simpa only using
    (ProvableType.getElem_eval_fields env
      cols.b_lower_byte.low_bytes i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulCLower
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).c_lower_byte.low_bytes[i] =
      Expression.eval env cols.c_lower_byte.low_bytes[i] := by
  rw [divRemEvalMulOperation,
    divRemEvalU16toU8 env cols.c_lower_byte]
  simpa only using
    (ProvableType.getElem_eval_fields env
      cols.c_lower_byte.low_bytes i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulBMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F)) :
    (Eval.eval env cols).b_msb =
      Expression.eval env cols.b_msb := by
  rw [divRemEvalMulOperation]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulCMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F)) :
    (Eval.eval env cols).c_msb =
      Expression.eval env cols.c_msb := by
  rw [divRemEvalMulOperation]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemEvalMulProductMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MulOperation (Expression F)) :
    (Eval.eval env cols).product_msb.msb =
      Expression.eval env cols.product_msb.msb := by
  rw [divRemEvalMulOperation, eval_u16MSBColumns]
  simp only [ProvableType.eval_field]

private theorem divRemMulInteractionsExact
    (env : Environment (ZMod p))
    (input : Var MulOperation.Inputs (ZMod p)) (offset : ℕ)
    (a : Word (ZMod p))
    (isMul isMulh isMulhu isMulhsu : ZMod p)
    (ha :
      Expression.eval env
          (input.cols.product[2] + input.cols.product[3] * 256) =
        a[1]) :
    (Extracted.MulOperation.interactions a
        (Eval.eval env input.b) (Eval.eval env input.c)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real)
        isMul isMulh (Expression.eval env input.is_mulw)
        isMulhu isMulhsu).map
          Extracted.Interaction.toAccess =
      (((MulOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have hb (i : ℕ) (hi : i < 4) :
      Expression.eval env input.b[i] = (Eval.eval env input.b)[i] :=
    (ProvableType.getElem_eval_fields env input.b i hi)
  have hc (i : ℕ) (hi : i < 4) :
      Expression.eval env input.c[i] = (Eval.eval env input.c)[i] :=
    (ProvableType.getElem_eval_fields env input.c i hi)
  have hbl (i : ℕ) (hi : i < 4) :
      Expression.eval env input.cols.b_lower_byte.low_bytes[i] =
        (Eval.eval env input.cols).b_lower_byte.low_bytes[i] :=
    (divRemEvalMulBLower env input.cols i hi).symm
  have hcl (i : ℕ) (hi : i < 4) :
      Expression.eval env input.cols.c_lower_byte.low_bytes[i] =
        (Eval.eval env input.cols).c_lower_byte.low_bytes[i] :=
    (divRemEvalMulCLower env input.cols i hi).symm
  have hcarry (i : ℕ) (hi : i < 16) :
      Expression.eval env input.cols.carry[i] =
        (Eval.eval env input.cols).carry[i] :=
    (divRemEvalMulCarry env input.cols i hi).symm
  have hproduct (i : ℕ) (hi : i < 16) :
      Expression.eval env input.cols.product[i] =
        (Eval.eval env input.cols).product[i] :=
    (divRemEvalMulProduct env input.cols i hi).symm
  have hExact := mulOperation_interactions_exact
    (p := p) env input offset a
    (Eval.eval env input.b) (Eval.eval env input.c)
    (Eval.eval env input.cols)
    (Expression.eval env input.is_real)
    (Expression.eval env input.is_mulw)
    rfl rfl
    (hb 0 (by decide)) (hb 1 (by decide))
    (hb 2 (by decide)) (hb 3 (by decide))
    (hc 0 (by decide)) (hc 1 (by decide))
    (hc 2 (by decide)) (hc 3 (by decide)) ha
    (hbl 0 (by decide)) (hbl 1 (by decide))
    (hbl 2 (by decide)) (hbl 3 (by decide))
    (hcl 0 (by decide)) (hcl 1 (by decide))
    (hcl 2 (by decide)) (hcl 3 (by decide))
    (divRemEvalMulBMsb env input.cols).symm
    (divRemEvalMulCMsb env input.cols).symm
    (divRemEvalMulProductMsb env input.cols).symm
    (hcarry 0 (by decide)) (hcarry 1 (by decide))
    (hcarry 2 (by decide)) (hcarry 3 (by decide))
    (hcarry 4 (by decide)) (hcarry 5 (by decide))
    (hcarry 6 (by decide)) (hcarry 7 (by decide))
    (hcarry 8 (by decide)) (hcarry 9 (by decide))
    (hcarry 10 (by decide)) (hcarry 11 (by decide))
    (hcarry 12 (by decide)) (hcarry 13 (by decide))
    (hcarry 14 (by decide)) (hcarry 15 (by decide))
    (hproduct 0 (by decide)) (hproduct 1 (by decide))
    (hproduct 2 (by decide)) (hproduct 3 (by decide))
    (hproduct 4 (by decide)) (hproduct 5 (by decide))
    (hproduct 6 (by decide)) (hproduct 7 (by decide))
    (hproduct 8 (by decide)) (hproduct 9 (by decide))
    (hproduct 10 (by decide)) (hproduct 11 (by decide))
    (hproduct 12 (by decide)) (hproduct 13 (by decide))
    (hproduct 14 (by decide)) (hproduct 15 (by decide))
  simpa only [Extracted.MulOperation.interactions] using hExact

private theorem divRemLowerMulInteractionsActive
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    LookupAccessList.active
        ((divRemLowerMulInteractions (Eval.eval env cols)).map
          Extracted.Interaction.toAccess) =
      LookupAccessList.active
        ((((MulOperation.main
          (divRemLowerMulInput cols)).operations offset).interactionsWith
            byteChannel.toRaw).map (AbstractInteraction.toAccess env)) := by
  let row := Eval.eval env cols
  let input := divRemLowerMulInput cols
  let a : Word (ZMod p) :=
    #v[row.c_times_quotient[0], row.c_times_quotient[1],
      row.c_times_quotient[2], row.c_times_quotient[3]]
  apply mulOperation_interactions_active env input offset
    a row.quotient_comp row.c row.c_times_quotient_lower
    row.is_real row.is_real 0 0 0 0
  · exact Or.inl rfl
  · simp
  · dsimp only [input, divRemLowerMulInput]
    simp only [Expression.eval]
    rw [← divRemEvalMulLowerProduct env cols 2 (by decide),
      ← divRemEvalMulLowerProduct env cols 3 (by decide)]
  · intro a' ha'
    have h := divRemMulInteractionsExact env input offset a'
      row.is_real 0 0 0 ha'
    simp only [input, divRemLowerMulInput, Expression.eval] at h
    rw [← DivRemChip.eval_divRemCols_quotientComp_verifier env cols,
      ← DivRemChip.eval_divRemCols_c_verifier env cols,
      ← DivRemChip.eval_divRemCols_mulLower_verifier env cols,
      ← ProvableType.eval_field env cols.is_real,
      ← DivRemChip.eval_divRemCols_isReal_verifier env cols] at h
    simpa only [divRemLowerMulInteractions, input,
      divRemLowerMulInput, row, Expression.eval] using h

private theorem divRemUpperMulInteractionsActive
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) (offset : ℕ) :
    LookupAccessList.active
        ((divRemUpperMulInteractions (Eval.eval env cols)).map
          Extracted.Interaction.toAccess) =
      LookupAccessList.active
        ((((MulOperation.main
          (divRemUpperMulInput cols)).operations offset).interactionsWith
            byteChannel.toRaw).map (AbstractInteraction.toAccess env)) := by
  let row := Eval.eval env cols
  let input := divRemUpperMulInput cols
  let a : Word (ZMod p) :=
    #v[row.c_times_quotient[4], row.c_times_quotient[5],
      row.c_times_quotient[6], row.c_times_quotient[7]]
  apply mulOperation_interactions_active env input offset
    a row.quotient_comp row.c row.c_times_quotient_upper
    row.is_real_not_word 0 (row.is_div + row.is_rem) 0
      (row.is_divu + row.is_remu) 0
  · exact Or.inl rfl
  · simp
  · dsimp only [input, divRemUpperMulInput]
    simp only [Expression.eval]
    rw [← divRemEvalMulUpperProduct env cols 2 (by decide),
      ← divRemEvalMulUpperProduct env cols 3 (by decide)]
  · intro a' ha'
    have h := divRemMulInteractionsExact env input offset a'
      0 (row.is_div + row.is_rem)
      (row.is_divu + row.is_remu) 0 ha'
    simp only [input, divRemUpperMulInput, Expression.eval] at h
    rw [← DivRemChip.eval_divRemCols_quotientComp_verifier env cols,
      ← DivRemChip.eval_divRemCols_c_verifier env cols,
      ← DivRemChip.eval_divRemCols_mulUpper_verifier env cols,
      ← ProvableType.eval_field env cols.is_real_not_word,
      ← DivRemChip.eval_divRemCols_isRealNotWord_verifier env cols] at h
    simpa only [divRemUpperMulInteractions, input,
      divRemUpperMulInput, row, Expression.eval] using h

omit [Fact (2 ^ 24 < p)] in
private theorem divRemMulAccessesAllByte
    (a b c : Word (ZMod p))
    (cols : Extracted.MulOperation (ZMod p))
    (isReal isMul isMulh isMulw isMulhu isMulhsu : ZMod p) :
    (((Extracted.MulOperation.interactions a b c cols
      isReal isMul isMulh isMulw isMulhu isMulhsu).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Byte)) =
      (Extracted.MulOperation.interactions a b c cols
        isReal isMul isMulh isMulw isMulhu isMulhsu).map
          Extracted.Interaction.toAccess := by
  simp [Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemCompareAccessesAllByte
    (cols : DivRemCompare.Inputs (ZMod p)) :
    (((divRemCompareInteractions cols).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) =
      (divRemCompareInteractions cols).map
        Extracted.Interaction.toAccess := by
  simp [divRemCompareInteractions,
    Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions,
    Extracted.AddOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.Interaction.toAccess]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemDirectAccessesAllByte
    (cols : DivRemChip.Columns (ZMod p)) :
    (((divRemDirectInteractions cols).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) =
      (divRemDirectInteractions cols).map
        Extracted.Interaction.toAccess := by
  simp [divRemDirectInteractions, Extracted.Interaction.toAccess]

omit [Fact (2 ^ 24 < p)] in
private theorem divRemRustByteDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    ((Extracted.DivRemOracle.DivRemCols.interactions (divRemChipReconfigure cols)).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte) =
      (divRemLowerMulInteractions cols).map
          Extracted.Interaction.toAccess ++
        (divRemUpperMulInteractions cols).map
          Extracted.Interaction.toAccess ++
        (divRemCompareInteractions
          (DivRemCompare.Inputs.ofCols cols)).map
            Extracted.Interaction.toAccess ++
        ((divRemCpuInteractions cols.state cols.is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Byte) ++
        ((divRemReaderInteractions cols.state (divRemOpcode cols)
          cols.a cols.adapter cols.is_real).map
            Extracted.Interaction.toAccess).filter
              (fun access => access.1 = InteractionKind.Byte) ++
        (divRemDirectInteractions cols).map
          Extracted.Interaction.toAccess := by
  rw [divRemRustInteractionsDecompose]
  simp only [List.map_append, List.filter_append]
  simp only [divRemLowerMulInteractions, divRemUpperMulInteractions]
  rw [divRemMulAccessesAllByte, divRemMulAccessesAllByte,
    divRemCompareAccessesAllByte, divRemDirectAccessesAllByte]

private theorem divRemByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    List.Perm
      (LookupAccessList.active
        ((((DivRemChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map (AbstractInteraction.toAccess env)))
      (LookupAccessList.active
        (((Extracted.DivRemOracle.DivRemCols.interactions
          (divRemChipReconfigure (Eval.eval env cols))).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Byte))) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let row := Eval.eval env cols
  have hNative := congrArg
    (List.map (AbstractInteraction.toAccess env))
    (divRemNativeByteDecompose input offset)
  simp only [List.map_append] at hNative
  rw [divRemCoreByteDecompose env cols (offset + 217)] at hNative
  have hCpu := divRemCpuByteInteractionsExact env input offset
  have hReader := divRemReaderByteInteractionsExact env input offset
  have hCompare := divRemCompareInteractionsExact env
    (DivRemCompare.Inputs.ofCols cols) (offset + 217)
  rw [divRemEvalCompareOfCols env cols] at hCompare
  have hLower := divRemLowerMulInteractionsActive env cols (offset + 217)
  have hUpper := divRemUpperMulInteractionsActive env cols (offset + 217)
  rw [hNative, divRemRustByteDecompose]
  rw [hCpu, hReader, ← hCompare]
  simp only [LookupAccessList.active, List.filter_append] at hLower hUpper ⊢
  rw [← hLower, ← hUpper]
  let lower :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      ((divRemLowerMulInteractions row).map
        Extracted.Interaction.toAccess)
  let upper :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      ((divRemUpperMulInteractions row).map
        Extracted.Interaction.toAccess)
  let compare :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      ((divRemCompareInteractions
        (DivRemCompare.Inputs.ofCols row)).map
          Extracted.Interaction.toAccess)
  let cpu :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      (((divRemCpuInteractions row.state row.is_real).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Byte))
  let reader :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      (((divRemReaderInteractions row.state (divRemOpcode row)
        row.a row.adapter row.is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Byte))
  let direct :=
    List.filter (fun access => LookupAccessList.multOf access ≠ 0)
      ((divRemDirectInteractions row).map
        Extracted.Interaction.toAccess)
  have hRotate :
      List.Perm
        ((cpu ++ reader) ++ compare ++ (lower ++ upper))
        ((lower ++ upper) ++ compare ++ (cpu ++ reader)) := by
    have hOuter :
        List.Perm
          ((cpu ++ reader) ++ compare ++ (lower ++ upper))
          ((compare ++ (lower ++ upper)) ++ (cpu ++ reader)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := cpu ++ reader)
          (l₂ := compare ++ (lower ++ upper)))
    have hInner :
        List.Perm
          ((compare ++ (lower ++ upper)) ++ (cpu ++ reader))
          (((lower ++ upper) ++ compare) ++ (cpu ++ reader)) :=
      (List.perm_append_comm (l₁ := compare)
        (l₂ := lower ++ upper)).append_right (cpu ++ reader)
    exact hOuter.trans hInner
  simpa only [cols, row, lower, upper, compare, cpu, reader, direct,
    List.append_assoc] using hRotate.append_right direct

private theorem divRemRustStateDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    ((Extracted.DivRemOracle.DivRemCols.interactions (divRemChipReconfigure cols)).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.State) =
      ((divRemCpuInteractions cols.state cols.is_real).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.State) := by
  rw [divRemRustInteractionsDecompose]
  simp [divRemLowerMulInteractions, divRemUpperMulInteractions,
    divRemCompareInteractions, divRemReaderInteractions,
    divRemDirectInteractions,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions,
    Extracted.AddOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess]

private theorem divRemStateInteractionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    ((((DivRemChip.main input).operations offset).interactionsWith
      stateChannel.toRaw).map (AbstractInteraction.toAccess env)) =
      ((Extracted.DivRemOracle.DivRemCols.interactions
          (divRemChipReconfigure (Eval.eval env cols))).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.State) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let state := Eval.eval env input.state
  let nextPc : Vector (ZMod p) 3 :=
    #v[state.pc[0] + 4, state.pc[1], state.pc[2]]
  let isReal := Expression.eval env input.is_real
  have hCpu := cpustate_state_interactions_faithful_syntactic env
    (divRemCpuInput input) state nextPc 8 isReal
    (by simp only [divRemCpuInput, isReal])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.eval_field])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.eval_field])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.eval_field])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by
      simp only [divRemCpuInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by
      simp only [divRemCpuInput, state, nextPc,
        Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero,
        eval_cpuState, ProvableType.getElem_eval_fields,
        Expression.eval])
    (by
      simp only [divRemCpuInput, state, nextPc,
        Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        eval_cpuState, ProvableType.getElem_eval_fields])
    (by
      simp only [divRemCpuInput, state, nextPc,
        Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        eval_cpuState, ProvableType.getElem_eval_fields])
    (by simp only [divRemCpuInput, Expression.eval])
  rw [DivRemChip.interactionsWith_state_eq]
  rw [divRemRustStateDecompose]
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simpa only [divRemCpuInteractions, divRemCpuInput,
    state, nextPc, isReal] using hCpu

private theorem divRemRustProgramDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    ((Extracted.DivRemOracle.DivRemCols.interactions (divRemChipReconfigure cols)).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program) =
      ((divRemReaderInteractions cols.state (divRemOpcode cols)
        cols.a cols.adapter cols.is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Program) := by
  rw [divRemRustInteractionsDecompose]
  simp [divRemLowerMulInteractions, divRemUpperMulInteractions,
    divRemCompareInteractions, divRemCpuInteractions,
    divRemDirectInteractions,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions,
    Extracted.AddOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.Interaction.toAccess]

private theorem divRemProgramInteractionsExact
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    (((((DivRemChip.main input).operations offset).interactionsWith
      programChannel.toRaw).map
        (AbstractInteraction.toAccess env)).map
          LookupAccessList.negMult) =
      ((Extracted.DivRemOracle.DivRemCols.interactions
          (divRemChipReconfigure (Eval.eval env cols))).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Program) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  let state := Eval.eval env input.state
  let adapter := Eval.eval env input.adapter
  let a := Eval.eval env cols.a
  let opcode := Expression.eval env (divRemOpcode cols)
  let isReal := Expression.eval env input.is_real
  have hReader := rtypereader_program_interactions_faithful_syntactic
    env (divRemReaderInput input cols) (offset + 217)
    state.clk_high (state.clk_0_16 + state.clk_16_24 * 65536)
    state.pc opcode a adapter isReal isReal
    (by simp only [divRemReaderInput, isReal])
    (by
      simp only [divRemReaderInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by
      simp only [divRemReaderInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by
      simp only [divRemReaderInput, state, eval_cpuState,
        ProvableType.getElem_eval_fields])
    (by simp only [divRemReaderInput, opcode, divRemOpcode])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, ProvableType.eval_field])
    (by
      simp only [divRemReaderInput, adapter, eval_rTypeReader,
        eval_registerAccessCols, ProvableType.eval_field])
  have hMainReader :
      ((DivRemChip.main input).operations offset).interactionsWith
          programChannel.toRaw =
        ((Readers.RTypeReader.main
          (divRemReaderInput input cols)).operations
            (offset + 217)).interactionsWith programChannel.toRaw := by
    rw [DivRemChip.interactionsWith_program_eq]
    have h := Soundness.rTypeReader_programInteractions
      (divRemReaderInput input cols) (offset + 217)
    simp only [Readers.RTypeReader.circuit] at h
    rw [h]
    rfl
  rw [hMainReader]
  rw [hReader]
  rw [LookupAccessList.map_negMult_negMult]
  rw [divRemRustProgramDecompose]
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalOpcode env cols,
    DivRemChip.eval_divRemCols_a_verifier,
    divRemEvalPopulatedAdapter env input offset,
    divRemEvalPopulatedIsReal env input offset]
  rfl

private theorem divRemRustMemoryDecompose
    (cols : DivRemChip.Columns (ZMod p)) :
    ((Extracted.DivRemOracle.DivRemCols.interactions (divRemChipReconfigure cols)).map
      Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Memory) =
      ((divRemReaderInteractions cols.state (divRemOpcode cols)
        cols.a cols.adapter cols.is_real).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Memory) := by
  rw [divRemRustInteractionsDecompose]
  simp [divRemLowerMulInteractions, divRemUpperMulInteractions,
    divRemCompareInteractions, divRemCpuInteractions,
    divRemDirectInteractions,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.IsEqualWordOperation.interactions,
    Extracted.IsZeroWordOperation.interactions,
    Extracted.IsZeroOperation.interactions,
    Extracted.AddOperation.interactions,
    Extracted.LtOperationUnsigned.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.Interaction.toAccess]

private theorem divRemMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := DivRemChip.populatedRowAt input offset
    List.Perm
      (((((DivRemChip.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)
      (((Extracted.DivRemOracle.DivRemCols.interactions
          (divRemChipReconfigure (Eval.eval env cols))).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Memory)) := by
  dsimp only
  let cols := DivRemChip.populatedRowAt input offset
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            ((memoryChannel.pulledIf gate msg).toRaw) =
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
            ((memoryChannel.pushedIf mult msg).toRaw) =
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
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  rw [DivRemChip.interactionsWith_memory_eq]
  simp only [DivRemChip.exposedMemoryInteractions, List.map_cons,
    List.map_nil, hMemoryPull, hMemoryPush]
  rw [divRemRustMemoryDecompose]
  rw [divRemEvalPopulatedState env input offset,
    divRemEvalOpcode env cols,
    DivRemChip.eval_divRemCols_a_verifier,
    divRemEvalPopulatedAdapter env input offset,
    divRemEvalPopulatedIsReal env input offset]
  simp [divRemReaderInteractions,
    Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    LookupAccessList.negMult, signedVal_neg hp2,
    eval_cpuState, eval_rTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ProvableType.eval_field, ProvableType.getElem_eval_fields,
    Expression.eval]
  exact List.perm_append_comm (l₁ := [_, _, _, _]) (l₂ := [_])

private theorem divRemUnexpectedInteractions
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions ((DivRemChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((DivRemChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (DivRemChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [DivRemChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

private theorem divRemInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : DivRemChip.Columns (ZMod p))
    (hbind : BindsChipOutput DivRemChip.main env input offset cols) :
    List.Perm
      (LookupAccessList.active
        (nativeAccesses env ((DivRemChip.main input).operations offset)))
      (LookupAccessList.active (divRemChipOracle.accesses cols)) := by
  replace hbind :=
    BindsChipOutput.ofElaborated (DivRemChip.elaborated (p := p)) hbind
  rw [← DivRemChip.elaborated.output_eq,
    DivRemChip.main_output_eq_populateRow,
    DivRemChip.populateRow_output_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval] at hbind
  subst cols
  let rustAccesses :=
    (Extracted.DivRemOracle.DivRemCols.interactions
      (divRemChipReconfigure
        (Eval.eval env (DivRemChip.populatedRowAt input offset)))).map
        Extracted.Interaction.toAccess
  have hState := divRemStateInteractionsExact env input offset
  have hByte := divRemByteInteractionsFaithful env input offset
  have hMemory := divRemMemoryInteractionsFaithful env input offset
  have hProgram := divRemProgramInteractionsExact env input offset
  have hStateActive :
      List.Perm
        (LookupAccessList.active
          ((((DivRemChip.main input).operations offset).interactionsWith
            stateChannel.toRaw).map (AbstractInteraction.toAccess env)))
        ((LookupAccessList.active rustAccesses).filter
          (fun access => access.1 = InteractionKind.State)) := by
    have h := congrArg LookupAccessList.active hState
    rw [LookupAccessList.active_filter] at h
    exact List.Perm.of_eq h
  have hByteActive := hByte
  dsimp only at hByteActive
  rw [LookupAccessList.active_filter] at hByteActive
  have hMemoryActive :=
    LookupAccessList.active_perm hMemory
  rw [LookupAccessList.active_filter] at hMemoryActive
  have hProgramActive :
      List.Perm
        (LookupAccessList.active
          (((((DivRemChip.main input).operations offset).interactionsWith
            programChannel.toRaw).map
              (AbstractInteraction.toAccess env)).map
                LookupAccessList.negMult))
        ((LookupAccessList.active rustAccesses).filter
          (fun access => access.1 = InteractionKind.Program)) := by
    have h := congrArg LookupAccessList.active hProgram
    rw [LookupAccessList.active_filter] at h
    exact List.Perm.of_eq h
  simp only [nativeAccesses]
  rw [divRemUnexpectedInteractions]
  simp only [List.map_nil, List.append_nil]
  simp only [divRemChipOracle, ChipOracle.accesses,
    ChipOracle.nativeInteractions]
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind_of_exit_nil
      (LookupAccessList.active rustAccesses)
      (Extracted.active_map_toAccess_exit_filter _)).symm
  simp only [LookupAccessList.active] at hStateActive
  simp only [LookupAccessList.active] at hByteActive
  simp only [LookupAccessList.active] at hMemoryActive
  simp only [LookupAccessList.active] at hProgramActive
  simp only [LookupAccessList.active, List.filter_append]
  exact ((hStateActive.append hByteActive).append hMemoryActive).append
    hProgramActive

theorem divRemChip_constraints_constructive
    (rustCols : Extracted.DivRemOracle.DivRemCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := divRemChipRowCodec.assignment
      (divRemChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols) ↔
      (⟨DivRemChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := divRemChipOracle.deconfigure rustCols
  let assignment := divRemChipRowCodec.assignment cols data
  have hbind : BindsChipOutput DivRemChip.main assignment.environment
      (⟨DivRemChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨DivRemChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [DivRemChip.circuit_main_eq] at h
    exact h
  have hfaithful := divRemConstraintsFaithful
    assignment.environment
    (⟨DivRemChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨DivRemChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨DivRemChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      DivRemChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (DivRemChip.circuit (p := p))
      assignment.environment divRemChip_lookups_empty).symm

theorem divRemChip_interactions_constructive
    (rustCols : Extracted.DivRemOracle.DivRemCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := divRemChipRowCodec.assignment
      (divRemChipOracle.deconfigure rustCols) data
    List.Perm
      (LookupAccessList.active
        (nativeAccesses assignment.environment
          (⟨DivRemChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).operations))
      (LookupAccessList.active
        (divRemChipOracle.rustAccesses rustCols)) := by
  dsimp only
  let cols := divRemChipOracle.deconfigure rustCols
  let assignment := divRemChipRowCodec.assignment cols data
  have hbind : BindsChipOutput DivRemChip.main assignment.environment
      (⟨DivRemChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨DivRemChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [DivRemChip.circuit_main_eq] at h
    exact h
  have hfaithful := divRemInteractionsFaithful
    assignment.environment
    (⟨DivRemChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨DivRemChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (DivRemChip.circuit (p := p)) assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    DivRemChip.circuit_main_eq] using hfaithful

theorem divRemChip_faithful :
    ChipFaithful (p := p) DivRemChip.Inputs DivRemChip.Columns
      Extracted.DivRemOracle.DivRemCols DivRemChip.circuit divRemChipRowCodec
        divRemChipOracle where
  constraints := divRemChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    divRemChip_interactions_constructive rustCols data

end SP1Clean.Faithful
