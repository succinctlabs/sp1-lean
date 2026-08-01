import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Bitwise
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ALUTypeReader
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import SP1Clean.Model.InteractionRecovery

/-! # Whole-chip faithfulness — native Bitwise row ↔ pinned SP1 Rust AIR

`bitwiseChip_faithful` compares every native assertion and emitted bus interaction with the
complete extracted Rust `BitwiseCols` oracle, including padding rows. The row codec is explicit:
the Rust reader blocks form the native input prefix, followed by the three opcode flags and the
sixteen `BitwiseU16Operation` cells in Rust column order.

Rust keeps the byte opcode as a field expression. The extracted oracle and native byte channel do
the same; validity of that opcode is a byte-table fact rather than a lossy extraction-time enum
decode.

Heartbeat budget: eight of the eleven declared ceilings here were 25–200× over and
were measured away (floors ≤40000). The three survivors are real:
`toElements_bitwiseChipOperationOfLocals` fails at 800000, while
`bitwise_chip_constraints_decompose` and `bitwiseChip_interactions_faithful` fail at
150000 and 100000 respectively. Each is kept at roughly twice its measured floor.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Whole-chip row reconfiguration. The reader blocks are already the canonical generated substrate,
so only the native composed-u16-bitwise block (two low-byte decompositions + eight result bytes) is
copied into Rust's chip-private operation row. This is not an operation-level faithfulness claim. -/
def bitwiseChipReconfigure {F : Type} (cols : BitwiseChip.Columns F) :
    Extracted.BitwiseOracle.BitwiseCols F :=
  { state := cols.state
    adapter := cols.adapter
    bitwise_operation :=
      { b_low_bytes := { low_bytes := cols.bitwise_operation.b_low_bytes.low_bytes }
        c_low_bytes := { low_bytes := cols.bitwise_operation.c_low_bytes.low_bytes }
        bitwise_operation := { result := cols.bitwise_operation.bitwise_operation.result } }
    is_xor := cols.is_xor
    is_or := cols.is_or
    is_and := cols.is_and }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def bitwiseChipDeconfigure {F : Type} (cols : Extracted.BitwiseOracle.BitwiseCols F) :
    BitwiseChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    bitwise_operation :=
      { b_low_bytes := { low_bytes := cols.bitwise_operation.b_low_bytes.low_bytes }
        c_low_bytes := { low_bytes := cols.bitwise_operation.c_low_bytes.low_bytes }
        bitwise_operation := { result := cols.bitwise_operation.bitwise_operation.result } }
    is_xor := cols.is_xor
    is_or := cols.is_or
    is_and := cols.is_and }

/-- SP1 Rust's complete Bitwise-chip oracle, viewed from the native Lean row. -/
def bitwiseChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F BitwiseChip.Columns Extracted.BitwiseOracle.BitwiseCols where
  reconfigure := bitwiseChipReconfigure
  deconfigure := bitwiseChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.BitwiseOracle.BitwiseCols.asserts
  interactions := Extracted.BitwiseOracle.BitwiseCols.interactions

def bitwiseChipInput {F : Type} [Add F]
    (cols : BitwiseChip.Columns F) : BitwiseChip.Inputs F :=
  { is_real := cols.is_xor + cols.is_or + cols.is_and
    state := cols.state
    adapter := cols.adapter }

def bitwiseChipLocals {F : Type} (cols : BitwiseChip.Columns F) : Vector F 19 :=
  #v[
    cols.is_xor, cols.is_or, cols.is_and,
    cols.bitwise_operation.b_low_bytes.low_bytes[0],
    cols.bitwise_operation.b_low_bytes.low_bytes[1],
    cols.bitwise_operation.b_low_bytes.low_bytes[2],
    cols.bitwise_operation.b_low_bytes.low_bytes[3],
    cols.bitwise_operation.c_low_bytes.low_bytes[0],
    cols.bitwise_operation.c_low_bytes.low_bytes[1],
    cols.bitwise_operation.c_low_bytes.low_bytes[2],
    cols.bitwise_operation.c_low_bytes.low_bytes[3],
    cols.bitwise_operation.bitwise_operation.result[0],
    cols.bitwise_operation.bitwise_operation.result[1],
    cols.bitwise_operation.bitwise_operation.result[2],
    cols.bitwise_operation.bitwise_operation.result[3],
    cols.bitwise_operation.bitwise_operation.result[4],
    cols.bitwise_operation.bitwise_operation.result[5],
    cols.bitwise_operation.bitwise_operation.result[6],
    cols.bitwise_operation.bitwise_operation.result[7]]

private theorem bitwiseChipLocals_zero {F : Type} (cols : BitwiseChip.Columns F) :
    (bitwiseChipLocals cols)[0] = cols.is_xor := by
  rfl

private theorem bitwiseChipLocals_one {F : Type} (cols : BitwiseChip.Columns F) :
    (bitwiseChipLocals cols)[1] = cols.is_or := by
  rfl

private theorem bitwiseChipLocals_two {F : Type} (cols : BitwiseChip.Columns F) :
    (bitwiseChipLocals cols)[2] = cols.is_and := by
  rfl

def bitwiseChipPhysicalRow {F : Type} [Add F]
    (cols : BitwiseChip.Columns F) : Array F :=
  inputFirstRow (bitwiseChipInput cols) (bitwiseChipLocals cols)

def bitwiseChipOperationOfLocals {F : Type} (locals : Vector F 19) :
    BitwiseU16Operation.Columns F :=
  ⟨⟨#v[locals[3], locals[4], locals[5], locals[6]]⟩,
    ⟨#v[locals[7], locals[8], locals[9], locals[10]]⟩,
    ⟨#v[locals[11], locals[12], locals[13], locals[14],
        locals[15], locals[16], locals[17], locals[18]]⟩⟩

def bitwiseChipColumnsOfInput {F : Type} (input : BitwiseChip.Inputs F)
    (locals : Vector F 19) : BitwiseChip.Columns F :=
  ⟨input.state, input.adapter, bitwiseChipOperationOfLocals locals,
    locals[0], locals[1], locals[2]⟩

set_option maxHeartbeats 2000000 in
private theorem toElements_bitwiseChipOperationOfLocals {F : Type}
    (locals : Vector F 19) :
    toElements (bitwiseChipOperationOfLocals locals) =
      #v[locals[3], locals[4], locals[5], locals[6],
        locals[7], locals[8], locals[9], locals[10],
        locals[11], locals[12], locals[13], locals[14],
        locals[15], locals[16], locals[17], locals[18]] := by
  rfl

private theorem getElem_toElements_bitwiseChipOperationOfLocals {F : Type}
    (locals : Vector F 19) (i : ℕ)
    (hi : i < size BitwiseU16Operation.Columns) :
    (toElements (bitwiseChipOperationOfLocals locals))[i] =
      locals[3 + i]'(by
        have hsize : size BitwiseU16Operation.Columns = 16 := rfl
        rw [hsize] at hi
        omega) := by
  rw [toElements_bitwiseChipOperationOfLocals]
  have hsize : size BitwiseU16Operation.Columns = 16 := rfl
  rw [hsize] at hi
  interval_cases i <;> rfl

private theorem vec4_eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem vec8_eta {F : Type} (value : Vector F 8) :
    #v[value[0], value[1], value[2], value[3], value[4], value[5], value[6], value[7]]
      = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem bitwiseU16_eta {F : Type}
    (cols : BitwiseU16Operation.Columns F) :
    (⟨⟨#v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1],
          cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]]⟩,
      ⟨#v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1],
          cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]]⟩,
      ⟨#v[cols.bitwise_operation.result[0], cols.bitwise_operation.result[1],
          cols.bitwise_operation.result[2], cols.bitwise_operation.result[3],
          cols.bitwise_operation.result[4], cols.bitwise_operation.result[5],
          cols.bitwise_operation.result[6], cols.bitwise_operation.result[7]]⟩⟩ :
      BitwiseU16Operation.Columns F) = cols := by
  cases cols with
  | mk bLow cLow bitwise =>
      cases bLow with
      | mk bBytes =>
          cases cLow with
          | mk cBytes =>
              cases bitwise with
              | mk result =>
                  simp only
                  rw [vec4_eta, vec4_eta, vec8_eta]

omit [Fact (2 ^ 17 < p)] in
private theorem extractedBitwiseU16Value_eq
    (b c : Word (ZMod p)) (cols : Extracted.BitwiseOracle.BitwiseU16Operation (ZMod p))
    (opcode isReal : ZMod p) :
    Extracted.BitwiseOracle.BitwiseU16Operation.value b c cols opcode isReal =
      #v[cols.bitwise_operation.result[0] +
            cols.bitwise_operation.result[1] * 256,
        cols.bitwise_operation.result[2] +
            cols.bitwise_operation.result[3] * 256,
        cols.bitwise_operation.result[4] +
            cols.bitwise_operation.result[5] * 256,
        cols.bitwise_operation.result[6] +
            cols.bitwise_operation.result[7] * 256] := by
  rw [Extracted.BitwiseOracle.BitwiseU16Operation.value]

theorem bitwiseChipColumnsOfInput_roundtrip {F : Type} [Add F]
    (cols : BitwiseChip.Columns F) :
    bitwiseChipColumnsOfInput (bitwiseChipInput cols) (bitwiseChipLocals cols) = cols := by
  cases cols with
  | mk state adapter operation isXor isOr isAnd =>
      cases operation with
      | mk bLow cLow bitwise =>
          cases bLow with
          | mk bBytes =>
              cases cLow with
              | mk cBytes =>
                  cases bitwise with
                  | mk result =>
                      change
                        (⟨state, adapter,
                          ⟨⟨#v[bBytes[0], bBytes[1], bBytes[2], bBytes[3]]⟩,
                            ⟨#v[cBytes[0], cBytes[1], cBytes[2], cBytes[3]]⟩,
                            ⟨#v[result[0], result[1], result[2], result[3],
                                result[4], result[5], result[6], result[7]]⟩⟩,
                          isXor, isOr, isAnd⟩ : BitwiseChip.Columns F) =
                            ⟨state, adapter, ⟨⟨bBytes⟩, ⟨cBytes⟩, ⟨result⟩⟩,
                              isXor, isOr, isAnd⟩
                      rw [vec4_eta, vec4_eta, vec8_eta]

@[circuit_norm] theorem eval_extractedU16toU8Operation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.U16toU8Operation (Expression F)) :
    Eval.eval env cols =
      ({ low_bytes := Eval.eval env cols.low_bytes } :
        Extracted.U16toU8Operation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_bitwiseOperationColumns {F : Type} [FiniteField F]
    (env : Environment F) (cols : BitwiseOperation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ result := Eval.eval env cols.result } : BitwiseOperation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_bitwiseU16OperationColumns {F : Type} [FiniteField F]
    (env : Environment F) (cols : BitwiseU16Operation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ b_low_bytes := Eval.eval env cols.b_low_bytes
         c_low_bytes := Eval.eval env cols.c_low_bytes
         bitwise_operation := Eval.eval env cols.bitwise_operation } :
        BitwiseU16Operation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_bitwiseU16Inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : BitwiseU16Operation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ b := Eval.eval env input.b, c := Eval.eval env input.c,
         cols := Eval.eval env input.cols, opcode := Eval.eval env input.opcode,
         is_real := Eval.eval env input.is_real } :
        BitwiseU16Operation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_bitwiseChipDirectOutput
    (input : BitwiseChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 19)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((BitwiseChip.elaborated (p := p)).output
          (varFromOffset BitwiseChip.Inputs 0) (size BitwiseChip.Inputs)) =
      bitwiseChipColumnsOfInput input locals := by
  rw [BitwiseChip.directOutput_eq]
  rw [← CircuitType.eval_expression, BitwiseChip.eval_columns]
  unfold bitwiseChipColumnsOfInput
  rw [BitwiseChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [BitwiseChip.eval_inputs, BitwiseChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  constructor
  · refine (ProvableType.ext_iff (α := BitwiseU16Operation.Columns) _ _).mpr
      (fun i hi => ?_)
    rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements,
      Vector.getElem_mapRange,
      getElem_toElements_bitwiseChipOperationOfLocals locals i hi]
    have hlocal := eval_local_inputFirstRow input locals data (3 + i) (by
      have hsize : size BitwiseU16Operation.Columns = 16 := rfl
      rw [hsize] at hi
      omega)
    simp only [Expression.eval] at hlocal
    simpa only [Nat.add_assoc] using hlocal
  constructor
  · simpa only [ProvableType.eval_field, Nat.add_zero] using
      (eval_local_inputFirstRow input locals data 0 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 1 (by decide))
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 2 (by decide))

def bitwiseChipRowCodec :
    ChipRowCodec BitwiseChip.Inputs BitwiseChip.Columns
      (BitwiseChip.circuit (p := p)) where
  assignment cols data := {
    row := bitwiseChipPhysicalRow cols
    input := bitwiseChipInput cols
    width_eq := by
      rw [bitwiseChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        BitwiseChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (BitwiseChip.circuit (p := p))
      (bitwiseChipInput cols) (bitwiseChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((BitwiseChip.main _).output _) = _
      rw [BitwiseChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_bitwiseChipDirectOutput (p := p) (bitwiseChipInput cols)
        (bitwiseChipLocals cols) data).trans
          (bitwiseChipColumnsOfInput_roundtrip cols) }

theorem bitwiseChip_lookups_empty :
    (⟨BitwiseChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    BitwiseChip.circuit_main_eq]
  simp [BitwiseChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    BitwiseU16Operation.circuit, BitwiseU16Operation.main,
    BitwiseOperation.circuit, BitwiseOperation.main,
    Gadgets.Equality.main, circuit_norm]

private def bitwise_chip_is_xor (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset }

private def bitwise_chip_is_or (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 1 }

private def bitwise_chip_is_and (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 2 }

private def bitwise_chip_is_real (offset : ℕ) : Expression (ZMod p) :=
  bitwise_chip_is_xor offset + bitwise_chip_is_or offset + bitwise_chip_is_and offset

private def bitwise_chip_byte_opcode (offset : ℕ) : Expression (ZMod p) :=
  bitwise_chip_is_xor offset * 2 + bitwise_chip_is_or offset * 1 +
    bitwise_chip_is_and offset * 0

private def bitwise_chip_cpu_opcode (offset : ℕ) : Expression (ZMod p) :=
  bitwise_chip_is_xor offset * 3 + bitwise_chip_is_or offset * 4 +
    bitwise_chip_is_and offset * 5

private def bitwise_chip_operation (offset : ℕ) :
    Var BitwiseU16Operation.Columns (ZMod p) :=
  varFromOffset BitwiseU16Operation.Columns (offset + 3)

private def bitwise_chip_result (offset : ℕ) : Vector (Expression (ZMod p)) 8 :=
  (bitwise_chip_operation offset).bitwise_operation.result

private def bitwise_chip_write_value (offset : ℕ) : Word (Expression (ZMod p)) :=
  let result := bitwise_chip_result offset
  #v[result[0] + result[1] * 256, result[2] + result[3] * 256,
    result[4] + result[5] * 256, result[6] + result[7] * 256]

omit [Fact (2 ^ 17 < p)] in
private theorem extractedBitwiseU16AssertionList
    (b c : Word (ZMod p)) (cols : Extracted.BitwiseOracle.BitwiseU16Operation (ZMod p))
    (opcode isReal : ZMod p) :
    Extracted.BitwiseOracle.BitwiseU16Operation.asserts b c cols opcode isReal =
      [isReal * (isReal - 1)] := by
  simp only [Extracted.BitwiseOracle.BitwiseU16Operation.asserts,
    Extracted.BitwiseOracle.U16toU8OperationUnsafe.asserts,
    Extracted.BitwiseOracle.BitwiseOperation.asserts, List.nil_append]

private theorem nativeBitwiseU16AssertionList
    (env : Environment (ZMod p)) (input : Var BitwiseU16Operation.Inputs (ZMod p))
    (offset : ℕ) :
    nativeAssertZeros env ((BitwiseU16Operation.main input).operations offset) =
      [ Expression.eval env (input.is_real * (input.is_real - 1)),
        Expression.eval env (input.is_real * (input.is_real - 1)) ] := by
  simp [nativeAssertZeros, BitwiseU16Operation.main,
    BitwiseOperation.circuit, BitwiseOperation.main,
    Gadgets.Equality.main, circuit_norm]
  have heval (value : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) value)[0] =
        Expression.eval env value := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval, sub_zero]
  have hrealEval :
      (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
    have h := congrArg (fun value => value.is_real)
      (ProvableStruct.eval_eq_eval env input)
    rw [eval_bitwiseU16Inputs] at h
    symm
    simpa only [ProvableType.eval_field] using h
  rw [hrealEval]

private theorem bitwiseU16Assertions
    (env : Environment (ZMod p)) (input : Var BitwiseU16Operation.Inputs (ZMod p))
    (offset : ℕ) (b c : Word (ZMod p))
    (cols : Extracted.BitwiseOracle.BitwiseU16Operation (ZMod p)) (opcode isReal : ZMod p)
    (hreal : Expression.eval env input.is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.BitwiseOracle.BitwiseU16Operation.asserts b c cols opcode isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((BitwiseU16Operation.main input).operations offset)) := by
  rw [extractedBitwiseU16AssertionList, nativeBitwiseU16AssertionList]
  simp only [List.Forall, eval_sub, Expression.eval, hreal]
  tauto

set_option maxHeartbeats 400000 in
private theorem bitwise_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var BitwiseChip.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((BitwiseChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((BitwiseU16Operation.main
              ⟨input.op_b_val, input.op_c_val, bitwise_chip_operation offset,
                bitwise_chip_byte_opcode offset, input.is_real⟩).operations
                  (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
                bitwise_chip_cpu_opcode offset,
                (bitwise_chip_write_value offset)[0],
                (bitwise_chip_write_value offset)[1],
                (bitwise_chip_write_value offset)[2],
                (bitwise_chip_write_value offset)[3]⟩).operations (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, bitwise_chip_write_value offset,
                input.is_real⟩).operations (offset + 19))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
        Expression.eval env
          (input.is_real - bitwise_chip_is_real offset) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (bitwise_chip_is_xor offset * (bitwise_chip_is_xor offset - 1),
                0)).operations (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (bitwise_chip_is_or offset * (bitwise_chip_is_or offset - 1),
                0)).operations (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (bitwise_chip_is_and offset * (bitwise_chip_is_and offset - 1),
                0)).operations (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (bitwise_chip_is_real offset * (bitwise_chip_is_real offset - 1),
                0)).operations (offset + 19))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 19)))) := by
  simp only [nativeAssertZeros, BitwiseChip.main, bitwise_chip_is_xor,
    bitwise_chip_is_or, bitwise_chip_is_and, bitwise_chip_is_real,
    bitwise_chip_byte_opcode, bitwise_chip_cpu_opcode, bitwise_chip_operation,
    bitwise_chip_result, bitwise_chip_write_value,
    Readers.CPUState.circuit, BitwiseU16Operation.circuit,
    Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]
  rw [show offset + 3 + 16 = offset + 19 by omega]
  simp only [List.forall_cons, List.forall_append]

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

theorem bitwiseChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var BitwiseChip.Inputs (ZMod p))
    (offset : ℕ) (cols : BitwiseChip.Columns (ZMod p))
    (hbind : BindsChipOutput BitwiseChip.main env input offset cols)
    (hinputReal : Expression.eval env input.is_real =
      Expression.eval env (bitwise_chip_is_real offset)) :
    List.Forall (· = 0) (bitwiseChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((BitwiseChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (BitwiseChip.elaborated (p := p)) hbind
  rw [BitwiseChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc,
    eval_bitwiseU16OperationColumns, eval_extractedU16toU8Operation,
    eval_bitwiseOperationColumns] at hbind
  subst cols
  let operation : Var BitwiseU16Operation.Columns (ZMod p) :=
    bitwise_chip_operation offset
  let result : Vector (Expression (ZMod p)) 8 := bitwise_chip_result offset
  let writeValue : Word (Expression (ZMod p)) := bitwise_chip_write_value offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let rustOperation : Extracted.BitwiseOracle.BitwiseU16Operation (ZMod p) :=
    { b_low_bytes :=
        { low_bytes :=
            #v[(Eval.eval env operation.b_low_bytes.low_bytes)[0],
              (Eval.eval env operation.b_low_bytes.low_bytes)[1],
              (Eval.eval env operation.b_low_bytes.low_bytes)[2],
              (Eval.eval env operation.b_low_bytes.low_bytes)[3]] }
      c_low_bytes :=
        { low_bytes :=
            #v[(Eval.eval env operation.c_low_bytes.low_bytes)[0],
              (Eval.eval env operation.c_low_bytes.low_bytes)[1],
              (Eval.eval env operation.c_low_bytes.low_bytes)[2],
              (Eval.eval env operation.c_low_bytes.low_bytes)[3]] }
      bitwise_operation :=
        { result :=
            #v[(Eval.eval env operation.bitwise_operation.result)[0],
              (Eval.eval env operation.bitwise_operation.result)[1],
              (Eval.eval env operation.bitwise_operation.result)[2],
              (Eval.eval env operation.bitwise_operation.result)[3],
              (Eval.eval env operation.bitwise_operation.result)[4],
              (Eval.eval env operation.bitwise_operation.result)[5],
              (Eval.eval env operation.bitwise_operation.result)[6],
              (Eval.eval env operation.bitwise_operation.result)[7]] } }
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
  let rustC : Word (ZMod p) :=
    #v[adapterValue.op_c_memory.prev_value[0], adapterValue.op_c_memory.prev_value[1],
      adapterValue.op_c_memory.prev_value[2], adapterValue.op_c_memory.prev_value[3]]
  let rustIsReal := Expression.eval env (bitwise_chip_is_real offset)
  let rustByteOpcode := Expression.eval env (bitwise_chip_byte_opcode offset)
  let rustCpuOpcode := Expression.eval env (bitwise_chip_cpu_opcode offset)
  let rustWriteValue : Word (ZMod p) :=
    Extracted.BitwiseOracle.BitwiseU16Operation.value
      rustB rustC rustOperation rustByteOpcode rustIsReal
  have hWriteValue : rustWriteValue = Eval.eval env writeValue := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp only [rustWriteValue, extractedBitwiseU16Value_eq, rustOperation,
        writeValue, bitwise_chip_write_value, bitwise_chip_result, operation,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, ← ProvableType.getElem_eval_fields,
        Expression.eval]
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let rustState : Extracted.CPUState (ZMod p) :=
    { clk_high := stateValue.clk_high
      clk_16_24 := stateValue.clk_16_24
      clk_0_16 := stateValue.clk_0_16
      pc := #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]] }
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[stateValue.pc[0] + 4, stateValue.pc[1], stateValue.pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions (p := p) env cpuInput offset
    rustState rustNextPc 8 rustIsReal (by
      simp only [cpuInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
  let opInput : Var BitwiseU16Operation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, operation,
      bitwise_chip_byte_opcode offset, input.is_real⟩
  have hOp := bitwiseU16Assertions (p := p) env opInput (offset + 19)
    rustB rustC rustOperation rustByteOpcode rustIsReal (by
      simp only [opInput, rustIsReal]
      exact hinputReal)
  let rustAdapter : Extracted.ALUTypeReader (ZMod p) := adapterValue
  let aluInput : Var Readers.ALUTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
      bitwise_chip_cpu_opcode offset,
      writeValue[0], writeValue[1], writeValue[2], writeValue[3]⟩
  have hAlu := CanonicalReader.aluTypeAssertions (p := p) env aluInput
    (offset + 19) stateValue.clk_high
    (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) rustCpuOpcode
    rustIsReal rustIsReal
    #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    (by
      simp only [aluInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
    (by
      simp only [aluInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
      exact hinputReal)
    (by simp only [aluInput, rustAdapter, adapterValue])
    (by
      simp only [aluInput]
      rw [hWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 0 (by decide))
    (by
      simp only [aluInput]
      rw [hWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 1 (by decide))
    (by
      simp only [aluInput]
      rw [hWriteValue]
      exact ProvableType.getElem_eval_fields env writeValue 2 (by decide))
    (by
      simp only [aluInput]
      rw [hWriteValue]
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
      Expression.eval env (input.is_real - bitwise_chip_is_real offset) = 0 := by
    simp only [eval_sub, hinputReal, sub_self]
  rw [bitwise_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, bitwiseChipOracle, bitwiseChipReconfigure]
  simp only [Extracted.BitwiseOracle.BitwiseCols.asserts, List.forall_append,
    List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustB, rustC, rustOperation, operation, rustByteOpcode, rustIsReal,
    opInput, adapterValue, bitwise_chip_operation] at hOp
  dsimp [rustState, rustNextPc, stateValue, rustIsReal, cpuInput] at hCpu
  dsimp [stateValue, rustWriteValue, rustAdapter, adapterValue, rustCpuOpcode,
    rustIsReal, rustByteOpcode, rustB, rustC, rustOperation, operation,
    aluInput, writeValue, result, bitwise_chip_write_value,
    bitwise_chip_result, bitwise_chip_operation] at hAlu
  simp_rw [← ProvableStruct.eval_eq_eval] at hOp hCpu hAlu
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hAluG⟩,
      hX, hO, hA, hSum, hOpA0, _⟩
    have hOpN := hOp.mp (by
      simpa only [bitwise_chip_byte_opcode,
        bitwise_chip_is_real, bitwise_chip_is_xor, bitwise_chip_is_or,
        bitwise_chip_is_and,
        eval_add, eval_mul, Expression.eval] using hOpG)
    have hCpuN := hCpu.mp hCpuG
    have hAluN := (hAlu.mp
      ⟨(by
        simpa only [vec4_eta, bitwise_chip_cpu_opcode,
          bitwise_chip_byte_opcode, bitwise_chip_is_real,
          bitwise_chip_is_xor, bitwise_chip_is_or, bitwise_chip_is_and,
          eval_add, eval_mul, Expression.eval] using hAluG),
        hOpA0⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 19)).mpr trivial
    have hXN := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_xor offset * (bitwise_chip_is_xor offset - 1))
      0 (offset + 19)).mpr (by
        simpa only [bitwise_chip_is_xor, eval_mul, eval_sub,
          Expression.eval] using hX)
    have hON := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_or offset * (bitwise_chip_is_or offset - 1))
      0 (offset + 19)).mpr (by
        simpa only [bitwise_chip_is_or, eval_mul, eval_sub,
          Expression.eval] using hO)
    have hAN := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_and offset * (bitwise_chip_is_and offset - 1))
      0 (offset + 19)).mpr (by
        simpa only [bitwise_chip_is_and, eval_mul, eval_sub,
          Expression.eval] using hA)
    have hSumN := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_real offset * (bitwise_chip_is_real offset - 1))
      0 (offset + 19)).mpr (by
        simpa only [bitwise_chip_is_real, bitwise_chip_is_xor,
          bitwise_chip_is_or, bitwise_chip_is_and, eval_mul, eval_sub,
          eval_add, Expression.eval] using hSum)
    have hOpA0N := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 19)).mpr (by
        rw [hopEval]
        exact hOpA0)
    exact ⟨hCpuN, hOpN, hAluN, hWriteN,
      hInputGate.trans hSum, hLink, hXN, hON, hAN, hSumN, hOpA0N⟩
  · rintro ⟨hCpuN, hOpN, hAluN, _hWriteN, _hInputGateN, _hLinkN,
      hXN, hON, hAN, hSumN, hOpA0N⟩
    have hCpuG := hCpu.mpr hCpuN
    have hOpG' := hOp.mpr hOpN
    have hOpG := by
      simpa only [bitwise_chip_byte_opcode,
        bitwise_chip_is_real, bitwise_chip_is_xor, bitwise_chip_is_or,
        bitwise_chip_is_and,
        eval_add, eval_mul, Expression.eval] using hOpG'
    have hOpA0 := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 19)).mp hOpA0N
    have hAluG' := (hAlu.mpr
      ⟨hAluN, by rw [← hopEval]; exact hOpA0⟩).1
    have hX := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_xor offset * (bitwise_chip_is_xor offset - 1))
      0 (offset + 19)).mp hXN
    have hO := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_or offset * (bitwise_chip_is_or offset - 1))
      0 (offset + 19)).mp hON
    have hA := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_and offset * (bitwise_chip_is_and offset - 1))
      0 (offset + 19)).mp hAN
    have hSum := (CanonicalReader.equalityAssertions env
      (bitwise_chip_is_real offset * (bitwise_chip_is_real offset - 1))
      0 (offset + 19)).mp hSumN
    refine ⟨⟨⟨hOpG, hCpuG⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simpa only [vec4_eta, bitwise_chip_cpu_opcode,
        bitwise_chip_byte_opcode, bitwise_chip_is_real,
        bitwise_chip_is_xor, bitwise_chip_is_or, bitwise_chip_is_and,
        eval_add, eval_mul, Expression.eval] using hAluG'
    · simpa only [bitwise_chip_is_xor, eval_mul, eval_sub,
        Expression.eval] using hX
    · simpa only [bitwise_chip_is_or, eval_mul, eval_sub,
        Expression.eval] using hO
    · simpa only [bitwise_chip_is_and, eval_mul, eval_sub,
        Expression.eval] using hA
    · simpa only [bitwise_chip_is_real, bitwise_chip_is_xor,
        bitwise_chip_is_or, bitwise_chip_is_and, eval_mul, eval_sub,
        eval_add, Expression.eval] using hSum
    · rw [← hopEval]
      exact hOpA0

private theorem bitwiseChipRowCodec_inputReal
    (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := bitwiseChipRowCodec.assignment cols data
    Expression.eval assignment.environment
        (⟨BitwiseChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar.is_real =
      Expression.eval assignment.environment
        (bitwise_chip_is_real
          (⟨BitwiseChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowOffset) := by
  dsimp only
  let assignment := bitwiseChipRowCodec.assignment cols data
  rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
  have hInput :
      Expression.eval
          (Environment.fromArray
            (inputFirstRow (bitwiseChipInput cols) (bitwiseChipLocals cols)) data)
          (varFromOffset BitwiseChip.Inputs 0).is_real =
        (bitwiseChipInput cols).is_real := by
    rw [← BitwiseChip.eval_inputIsReal]
    exact congrArg (fun value => value.is_real)
      (eval_inputFirstRow (bitwiseChipInput cols) (bitwiseChipLocals cols) data)
  have hX := eval_local_inputFirstRow (bitwiseChipInput cols)
    (bitwiseChipLocals cols) data 0 (by decide)
  have hO := eval_local_inputFirstRow (bitwiseChipInput cols)
    (bitwiseChipLocals cols) data 1 (by decide)
  have hA := eval_local_inputFirstRow (bitwiseChipInput cols)
    (bitwiseChipLocals cols) data 2 (by decide)
  change
    Expression.eval assignment.environment
        (varFromOffset BitwiseChip.Inputs 0).is_real =
      assignment.environment.get (size BitwiseChip.Inputs) +
        assignment.environment.get (size BitwiseChip.Inputs + 1) +
        assignment.environment.get (size BitwiseChip.Inputs + 2)
  rw [show assignment.environment =
      Environment.fromArray
        (inputFirstRow (bitwiseChipInput cols) (bitwiseChipLocals cols)) data by rfl]
  rw [hInput]
  simp only [bitwiseChipInput]
  simp only [Expression.eval] at hX hO hA
  rw [bitwiseChipLocals_zero] at hX
  rw [bitwiseChipLocals_one] at hO
  rw [bitwiseChipLocals_two] at hA
  simp only [bitwiseChipInput] at hX hO hA
  simpa only [Nat.add_zero] using (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) hX hO) hA).symm

theorem bitwiseChip_constraints_constructive
    (rustCols : Extracted.BitwiseOracle.BitwiseCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := bitwiseChipRowCodec.assignment
      (bitwiseChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols) ↔
      (⟨BitwiseChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := bitwiseChipOracle.deconfigure rustCols
  let assignment := bitwiseChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BitwiseChip.main assignment.environment
      (⟨BitwiseChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨BitwiseChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BitwiseChip.circuit_main_eq] at h
    exact h
  have hinputReal :
      Expression.eval assignment.environment
          (⟨BitwiseChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowInputVar.is_real =
        Expression.eval assignment.environment
          (bitwise_chip_is_real
            (⟨BitwiseChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOffset) :=
    bitwiseChipRowCodec_inputReal (p := p) cols data
  have hlegacy := bitwiseChip_constraints_faithful (p := p)
    assignment.environment
    (⟨BitwiseChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨BitwiseChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind hinputReal
  have hassertions :
      List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨BitwiseChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, BitwiseChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (BitwiseChip.circuit (p := p))
      assignment.environment bitwiseChip_lookups_empty).symm

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

set_option maxHeartbeats 400000 in
theorem bitwiseChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var BitwiseChip.Inputs (ZMod p))
    (offset : ℕ) (cols : BitwiseChip.Columns (ZMod p))
    (hbind : BindsChipOutput BitwiseChip.main env input offset cols)
    (hinputReal : Expression.eval env input.is_real =
      Expression.eval env (bitwise_chip_is_real offset)) :
    List.Perm (nativeAccesses env ((BitwiseChip.main input).operations offset))
      (bitwiseChipOracle.accesses cols) := by
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
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
  replace hbind := BindsChipOutput.ofElaborated (BitwiseChip.elaborated (p := p)) hbind
  rw [BitwiseChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_bitwiseU16OperationColumns,
    eval_extractedU16toU8Operation, eval_bitwiseOperationColumns] at hbind
  let rustCols : BitwiseChip.Columns (ZMod p) :=
    { state := Eval.eval env input.state
      adapter := Eval.eval env input.adapter
      bitwise_operation :=
        { b_low_bytes :=
            { low_bytes := Eval.eval env
                (bitwise_chip_operation
                  (p := p) offset).b_low_bytes.low_bytes }
          c_low_bytes :=
            { low_bytes := Eval.eval env
                (bitwise_chip_operation
                  (p := p) offset).c_low_bytes.low_bytes }
          bitwise_operation :=
            { result := Eval.eval env
                (bitwise_chip_operation
                  (p := p) offset).bitwise_operation.result } }
      is_xor := Expression.eval env (var ⟨offset⟩)
      is_or := Expression.eval env (var ⟨offset + 1⟩)
      is_and := Expression.eval env (var ⟨offset + 2⟩) }
  change rustCols = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.BitwiseOracle.BitwiseCols.interactions (bitwiseChipReconfigure rustCols)).map
      Extracted.Interaction.toAccess
  have hReal : Expression.eval env input.is_real =
      env.get offset + env.get (offset + 1) + env.get (offset + 2) := by
    simpa only [bitwise_chip_is_real, bitwise_chip_is_xor,
      bitwise_chip_is_or, bitwise_chip_is_and, eval_add,
      Expression.eval] using hinputReal
  have hsignReal :
      -signedVal
          (env.get offset + env.get (offset + 1) + env.get (offset + 2) -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            (env.get offset + env.get (offset + 1) + env.get (offset + 2))) := by
    simpa only [hReal] using hsign
  have hNegFlags :
      -env.get (offset + 2) + (-env.get (offset + 1) + -env.get offset) =
        -(env.get offset + env.get (offset + 1) + env.get (offset + 2)) := by
    ring
  have hDoubleNeg :
      -signedVal
          (-env.get (offset + 2) + (-env.get (offset + 1) + -env.get offset)) =
        signedVal
          (env.get offset + env.get (offset + 1) + env.get (offset + 2)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  have hBLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).b_low_bytes.low_bytes =
        #v[env.get (offset + 3), env.get (offset + 4),
          env.get (offset + 5), env.get (offset + 6)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  have hCLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).c_low_bytes.low_bytes =
        #v[env.get (offset + 7), env.get (offset + 8),
          env.get (offset + 9), env.get (offset + 10)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  have hResultLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).bitwise_operation.result =
        #v[env.get (offset + 11), env.get (offset + 12),
          env.get (offset + 13), env.get (offset + 14),
          env.get (offset + 15), env.get (offset + 16),
          env.get (offset + 17), env.get (offset + 18)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((BitwiseChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, BitwiseChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      SP1Clean.BitwiseU16Operation.circuit, SP1Clean.BitwiseU16Operation.main,
      SP1Clean.BitwiseOperation.circuit, SP1Clean.BitwiseOperation.main,
      Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses, ChipOracle.nativeInteractions, bitwiseChipOracle]
  rw [BitwiseChip.interactionsWith_state_eq, BitwiseChip.interactionsWith_byte_eq,
    BitwiseChip.interactionsWith_memory_eq, BitwiseChip.interactionsWith_program_eq]
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
      ((BitwiseChip.exposedStateInteractions input).map
          ChannelInteraction.toRaw).map (AbstractInteraction.toAccess env) =
        rustAccesses.filter (fun access =>
          access.1 = InteractionKind.State) := by
    dsimp only [rustAccesses, rustCols, bitwiseChipReconfigure]
    simp [BitwiseChip.exposedStateInteractions, hStatePull, hStatePush,
      Extracted.BitwiseOracle.BitwiseCols.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.interactions,
      Extracted.BitwiseOracle.U16toU8OperationUnsafe.interactions,
      Extracted.BitwiseOracle.BitwiseOperation.interactions,
      Extracted.CPUState.interactions, Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
      Expression.eval, hReal, hNegFlags]
    simp only [true_and, neg_one_mul]
  have hB :
      List.Perm
        (((BitwiseChip.exposedByteInteractions input offset).map
          ChannelInteraction.toRaw).map (AbstractInteraction.toAccess env))
        (rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Byte)) := by
    dsimp only [rustAccesses, rustCols, bitwiseChipReconfigure]
    simp only [BitwiseChip.exposedByteInteractions,
      BitwiseChip.exposedByteOpcode, BitwiseChip.exposedBBytes,
      BitwiseChip.exposedCBytes, BitwiseChip.exposedResultBytes,
      List.map_cons, List.map_nil, hBytePull]
    simp [Extracted.BitwiseOracle.BitwiseCols.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.interactions,
      Extracted.BitwiseOracle.U16toU8OperationUnsafe.interactions,
      Extracted.BitwiseOracle.U16toU8OperationUnsafe.value,
      Extracted.BitwiseOracle.BitwiseOperation.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.value,
      Extracted.CPUState.interactions, Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      Opcode.ofNat, ConstraintCoe.coe_eq_val, signedVal_neg hp2, h6,
      BitwiseChip.Inputs.op_b_val, BitwiseChip.Inputs.op_c_val,
      hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, eval_extractedU16toU8Operation,
      eval_bitwiseOperationColumns, ← ProvableType.getElem_eval_fields,
      eval_sub, ProvableType.eval_field,
      Expression.eval, hReal, hNegFlags, hBLocals, hCLocals,
      hResultLocals]
    simp only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hsignReal]
    exact
      (List.perm_append_comm
        (l₁ := [_, _])
        (l₂ := [_, _, _, _, _, _, _, _])).append_right
          [_, _, _, _, _, _]
  have hM :
      List.Perm
        (((((BitwiseChip.exposedMemoryInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult))
        (rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Memory)) := by
    dsimp only [rustAccesses, rustCols, bitwiseChipReconfigure]
    simp only [BitwiseChip.exposedMemoryInteractions,
      List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
    simp [Extracted.BitwiseOracle.BitwiseCols.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.interactions,
      Extracted.BitwiseOracle.U16toU8OperationUnsafe.interactions,
      Extracted.BitwiseOracle.BitwiseOperation.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.value,
      Extracted.CPUState.interactions, Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      LookupAccessList.negMult, signedVal_neg hp2,
      hReal]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, eval_bitwiseOperationColumns,
      ← ProvableType.getElem_eval_fields, eval_sub,
      ProvableType.eval_field, hReal, hNegFlags, hResultLocals]
    simp only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [signedVal_neg hp2, neg_neg]
    rw [hsignReal]
    exact (List.perm_append_comm
      (l₁ := [_, _, _, _]) (l₂ := [_])).append_left [_]
  have hP :
      (((((BitwiseChip.exposedProgramInteractions input offset).map
          ChannelInteraction.toRaw).map
            (AbstractInteraction.toAccess env)).map
              LookupAccessList.negMult)) =
        rustAccesses.filter (fun access =>
          access.1 = InteractionKind.Program) := by
    dsimp only [rustAccesses, rustCols, bitwiseChipReconfigure]
    simp only [BitwiseChip.exposedProgramInteractions,
      BitwiseChip.exposedOpcode, List.map_cons, List.map_nil,
      hProgramPull]
    simp [Extracted.BitwiseOracle.BitwiseCols.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.interactions,
      Extracted.BitwiseOracle.U16toU8OperationUnsafe.interactions,
      Extracted.BitwiseOracle.BitwiseOperation.interactions,
      Extracted.BitwiseOracle.BitwiseU16Operation.value,
      Extracted.CPUState.interactions, Extracted.ALUTypeReader.interactions,
      Extracted.Interaction.toAccess, Extracted.Dir.sign,
      Expression.eval, ProvableType.eval_field,
      eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, ← ProvableType.getElem_eval_fields,
      Opcode.ofNat, ConstraintCoe.coe_eq_val,
      LookupAccessList.negMult, hReal]
    simp only [hDoubleNeg]
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  rw [hS, hP]
  exact ((hB.append_left _).append hM).append_right _

theorem bitwiseChip_interactions_constructive
    (rustCols : Extracted.BitwiseOracle.BitwiseCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := bitwiseChipRowCodec.assignment
      (bitwiseChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨BitwiseChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (bitwiseChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := bitwiseChipOracle.deconfigure rustCols
  let assignment := bitwiseChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BitwiseChip.main assignment.environment
      (⟨BitwiseChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowInputVar
      (⟨BitwiseChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BitwiseChip.circuit_main_eq] at h
    exact h
  have hlegacy := bitwiseChip_interactions_faithful (p := p)
    assignment.environment
    (⟨BitwiseChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨BitwiseChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
    (bitwiseChipRowCodec_inputReal (p := p) cols data)
  rw [nativeAccesses_component_eq_rowOperations (BitwiseChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, BitwiseChip.circuit_main_eq] using hlegacy

theorem bitwiseChip_faithful :
    ChipFaithful (p := p) BitwiseChip.Inputs BitwiseChip.Columns
      Extracted.BitwiseOracle.BitwiseCols BitwiseChip.circuit bitwiseChipRowCodec
      bitwiseChipOracle where
  constraints := bitwiseChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (bitwiseChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
