import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Bitwise
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ALUTypeReader
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import ToClean.Circuit.InteractionRecovery

/-! # Whole-chip Bitwise faithfulness

The native row and pinned Rust oracle agree on all assertions and interaction occurrences,
including padding. Reader columns and selectors form the input prefix; the sixteen byte
columns form the witness suffix. Activity is the selector sum on both sides.

The codec uses `toElements`/`fromElements` so its proofs preserve folded operation columns.
Rust byte opcodes remain field expressions whose validity is established by the byte table.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open SP1Clean.Circuits.Types
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

/-- Reader columns and committed selectors recovered from a completed native row. -/
def bitwiseChipInput {F : Type}
    (cols : BitwiseChip.Columns F) : BitwiseChip.Inputs F :=
  { state := cols.state
    adapter := cols.adapter
    isXor := cols.is_xor
    isOr := cols.is_or
    isAnd := cols.is_and }

/-- The sixteen witnessed byte cells in Clean's native flattening order. -/
def bitwiseChipLocals {F : Type} (cols : BitwiseChip.Columns F) : Vector F 16 :=
  toElements cols.bitwise_operation

/-- A physical Clean row: typed inputs followed by its byte witnesses. -/
def bitwiseChipPhysicalRow {F : Type}
    (cols : BitwiseChip.Columns F) : Array F :=
  inputFirstRow (bitwiseChipInput cols) (bitwiseChipLocals cols)

/-- The byte operation occupies the entire sixteen-cell witness suffix. -/
def bitwiseChipOperationOfLocals {F : Type} (locals : Vector F 16) :
    BitwiseU16Operation.Columns F :=
  fromElements locals

/-- Reassemble completed columns from reader inputs, selectors and byte witnesses. -/
def bitwiseChipColumnsOfInput {F : Type} (input : BitwiseChip.Inputs F)
    (locals : Vector F 16) : BitwiseChip.Columns F :=
  ⟨input.state, input.adapter, bitwiseChipOperationOfLocals locals,
    input.isXor, input.isOr, input.isAnd⟩

private theorem bitwiseChipOperationOfLocals_roundtrip {F : Type}
    (cols : BitwiseChip.Columns F) :
    bitwiseChipOperationOfLocals (bitwiseChipLocals cols) = cols.bitwise_operation := by
  simp only [bitwiseChipOperationOfLocals, bitwiseChipLocals, ProvableType.fromElements_toElements]

private theorem vec4_eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

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

theorem bitwiseChipColumnsOfInput_roundtrip {F : Type}
    (cols : BitwiseChip.Columns F) :
    bitwiseChipColumnsOfInput (bitwiseChipInput cols) (bitwiseChipLocals cols) = cols := by
  unfold bitwiseChipColumnsOfInput bitwiseChipInput
  rw [BitwiseChip.Columns.mk.injEq]
  exact ⟨rfl, rfl, bitwiseChipOperationOfLocals_roundtrip cols,
    rfl, rfl, rfl⟩

@[circuit_norm] theorem eval_extractedU16toU8Operation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Circuits.Types.U16toU8Operation (Expression F)) :
    Eval.eval env cols =
      ({ low_bytes := Eval.eval env cols.low_bytes } :
        Circuits.Types.U16toU8Operation F) := by
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
    (input : BitwiseChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 16)
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
  refine ⟨hinputEval.1, hinputEval.2.1, ?_, hinputEval.2.2.1,
    hinputEval.2.2.2.1, hinputEval.2.2.2.2⟩
  refine (ProvableType.ext_iff (α := BitwiseU16Operation.Columns) _ _).mpr (fun i hi => ?_)
  rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange]
  simp only [bitwiseChipOperationOfLocals, ProvableType.toElements_fromElements]
  have hlocal := eval_local_inputFirstRow input locals data i hi
  simpa only [Expression.eval] using hlocal


/-- Construct any native Bitwise row as a physical input/witness assignment. -/
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

private def bitwise_chip_operation (offset : ℕ) :
    Var BitwiseU16Operation.Columns (ZMod p) :=
  varFromOffset BitwiseU16Operation.Columns offset

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
                BitwiseChip.exposedByteOpcode input, input.is_real⟩).operations
                  (offset + 16))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
                BitwiseChip.exposedOpcode input,
                (bitwise_chip_write_value offset)[0],
                (bitwise_chip_write_value offset)[1],
                (bitwise_chip_write_value offset)[2],
                (bitwise_chip_write_value offset)[3]⟩).operations (offset + 16))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, bitwise_chip_write_value offset,
                input.is_real⟩).operations (offset + 16))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.isXor * (input.isXor - 1),
                0)).operations (offset + 16))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.isOr * (input.isOr - 1),
                0)).operations (offset + 16))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.isAnd * (input.isAnd - 1),
                0)).operations (offset + 16))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 16)))) := by
  simp only [nativeAssertZeros, BitwiseChip.main, BitwiseChip.Inputs.is_real,
    BitwiseChip.exposedByteOpcode, BitwiseChip.exposedOpcode, bitwise_chip_operation,
    bitwise_chip_result, bitwise_chip_write_value,
    Readers.CPUState.circuit, BitwiseU16Operation.circuit,
    Readers.ALUTypeReader.circuit, Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append, List.forall_cons]

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

theorem bitwiseChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var BitwiseChip.Inputs (ZMod p))
    (offset : ℕ) (cols : BitwiseChip.Columns (ZMod p))
    (hbind : BindsChipOutput BitwiseChip.main env input offset cols) :
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
  let rustIsReal := Expression.eval env (input.is_real)
  let rustByteOpcode := Expression.eval env (BitwiseChip.exposedByteOpcode input)
  let rustCpuOpcode := Expression.eval env (BitwiseChip.exposedOpcode input)
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
  let rustState : Circuits.Types.CPUState (ZMod p) :=
    { clk_high := stateValue.clk_high
      clk_16_24 := stateValue.clk_16_24
      clk_0_16 := stateValue.clk_0_16
      pc := #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]] }
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[stateValue.pc[0] + 4, stateValue.pc[1], stateValue.pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions (p := p) env cpuInput offset
    rustState rustNextPc 8 rustIsReal (by
      simp only [cpuInput, rustIsReal, ProvableStruct.structEvalLiteralProc])
  let opInput : Var BitwiseU16Operation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, operation,
      BitwiseChip.exposedByteOpcode input, input.is_real⟩
  have hOp := bitwiseU16Assertions (p := p) env opInput (offset + 16)
    rustB rustC rustOperation rustByteOpcode rustIsReal (by
      simp only [opInput, rustIsReal])
  let rustAdapter : Circuits.Types.ALUTypeReader (ZMod p) := adapterValue
  let aluInput : Var Readers.ALUTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
      BitwiseChip.exposedOpcode input,
      writeValue[0], writeValue[1], writeValue[2], writeValue[3]⟩
  have hAlu := CanonicalReader.aluTypeAssertions (p := p) env aluInput
    (offset + 16) stateValue.clk_high
    (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) rustCpuOpcode
    rustIsReal rustIsReal
    #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    (by
      simp only [aluInput, rustIsReal, ProvableStruct.structEvalLiteralProc])
    (by
      simp only [aluInput, rustIsReal, ProvableStruct.structEvalLiteralProc])
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
      simpa only [BitwiseChip.exposedByteOpcode,
        BitwiseChip.Inputs.is_real, eval_add, eval_mul, Expression.eval] using hOpG)
    have hCpuN := hCpu.mp hCpuG
    have hAluN := (hAlu.mp
      ⟨(by
        simpa only [vec4_eta, BitwiseChip.exposedOpcode,
          BitwiseChip.exposedByteOpcode, BitwiseChip.Inputs.is_real,
          eval_add, eval_mul, Expression.eval] using hAluG),
        hOpA0⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 16)).mpr trivial
    have hXN := (CanonicalReader.equalityAssertions env
      (input.isXor * (input.isXor - 1))
      0 (offset + 16)).mpr (by
        simpa only [eval_mul, eval_sub,
          Expression.eval] using hX)
    have hON := (CanonicalReader.equalityAssertions env
      (input.isOr * (input.isOr - 1))
      0 (offset + 16)).mpr (by
        simpa only [eval_mul, eval_sub,
          Expression.eval] using hO)
    have hAN := (CanonicalReader.equalityAssertions env
      (input.isAnd * (input.isAnd - 1))
      0 (offset + 16)).mpr (by
        simpa only [eval_mul, eval_sub,
          Expression.eval] using hA)
    have hSumN : Expression.eval env (input.is_real * (input.is_real - 1)) = 0 := by
      simpa only [BitwiseChip.Inputs.is_real, eval_sub, Expression.eval] using hSum
    have hOpA0N := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 16)).mpr (by
        rw [hopEval]
        exact hOpA0)
    exact ⟨hCpuN, hOpN, hAluN, hWriteN,
      hXN, hON, hAN, hSumN, hOpA0N⟩
  · rintro ⟨hCpuN, hOpN, hAluN, _hWriteN, hXN, hON, hAN, hSumN, hOpA0N⟩
    have hCpuG := hCpu.mpr hCpuN
    have hOpG' := hOp.mpr hOpN
    have hOpG := by
      simpa only [BitwiseChip.exposedByteOpcode,
        BitwiseChip.Inputs.is_real, eval_add, eval_mul, Expression.eval] using hOpG'
    have hOpA0 := (CanonicalReader.equalityAssertions env
      input.adapter.op_a_0 0 (offset + 16)).mp hOpA0N
    have hAluG' := (hAlu.mpr
      ⟨hAluN, by rw [← hopEval]; exact hOpA0⟩).1
    have hX := (CanonicalReader.equalityAssertions env
      (input.isXor * (input.isXor - 1))
      0 (offset + 16)).mp hXN
    have hO := (CanonicalReader.equalityAssertions env
      (input.isOr * (input.isOr - 1))
      0 (offset + 16)).mp hON
    have hA := (CanonicalReader.equalityAssertions env
      (input.isAnd * (input.isAnd - 1))
      0 (offset + 16)).mp hAN
    have hSum := hSumN
    refine ⟨⟨⟨hOpG, hCpuG⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simpa only [vec4_eta, BitwiseChip.exposedOpcode,
        BitwiseChip.exposedByteOpcode, BitwiseChip.Inputs.is_real,
        eval_add, eval_mul, Expression.eval] using hAluG'
    · simpa only [eval_mul, eval_sub,
        Expression.eval] using hX
    · simpa only [eval_mul, eval_sub,
        Expression.eval] using hO
    · simpa only [eval_mul, eval_sub,
        Expression.eval] using hA
    · simpa only [BitwiseChip.Inputs.is_real, eval_mul, eval_sub,
        eval_add, Expression.eval] using hSum
    · rw [← hopEval]
      exact hOpA0

theorem bitwiseChip_constraints_constructive
    (rustCols : Extracted.BitwiseOracle.BitwiseCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := bitwiseChipRowCodec.assignment
      (bitwiseChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols) ↔
      ({ circuit := BitwiseChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := bitwiseChipOracle.deconfigure rustCols
  let assignment := bitwiseChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BitwiseChip.main assignment.environment
      ({ circuit := BitwiseChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowInputVar
      ({ circuit := BitwiseChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BitwiseChip.circuit_main_eq] at h
    exact h
  have hlegacy := bitwiseChip_constraints_faithful (p := p)
    assignment.environment
    ({ circuit := BitwiseChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowInputVar
    ({ circuit := BitwiseChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            ({ circuit := BitwiseChip.circuit (p := p) } :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, BitwiseChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (BitwiseChip.circuit (p := p))
      assignment.environment BitwiseChip.lookups_empty).symm

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

omit [Fact (2 ^ 17 < p)] in
/-- The Bitwise oracle emits no raw interaction, so its access list carries none of the four kinds
outside SP1's instruction buses. Stated over an opaque row and proved once: inline inside
`bitwiseChip_interactions_faithful` the same `simp` has the whole chip in scope and exceeds the
elaboration budget. -/
private theorem bitwiseNoRawInteractions (cols : Extracted.BitwiseOracle.BitwiseCols (ZMod p)) :
    ∀ i ∈ Extracted.BitwiseOracle.BitwiseCols.interactions cols,
      ¬ Extracted.Interaction.IsRaw i := by
  simp [Extracted.ALUTypeReader.interactions, Extracted.BitwiseOracle.BitwiseCols.interactions, Extracted.BitwiseOracle.BitwiseOperation.interactions, Extracted.BitwiseOracle.BitwiseU16Operation.interactions, Extracted.BitwiseOracle.U16toU8OperationUnsafe.interactions, Extracted.CPUState.interactions,
    Extracted.Interaction.IsRaw]

/-- The native Bitwise chip emits on the four SP1 buses only: its channel set is the bundle's
declared one. Stated over an opaque input so the main anchor does not re-walk `main`. -/
private theorem unexpectedInteractionsEmpty
    (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions ((BitwiseChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈ ((BitwiseChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown := (BitwiseChip.circuit (p := p)).channels_subset input offset hchannel
  simp only [BitwiseChip.circuit, FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def, circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem bitwiseChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var BitwiseChip.Inputs (ZMod p))
    (offset : ℕ) (cols : BitwiseChip.Columns (ZMod p))
    (hbind : BindsChipOutput BitwiseChip.main env input offset cols) :
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
      is_xor := Expression.eval env input.isXor
      is_or := Expression.eval env input.isOr
      is_and := Expression.eval env input.isAnd }
  change rustCols = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.BitwiseOracle.BitwiseCols.interactions (bitwiseChipReconfigure rustCols)).map
      Extracted.Interaction.toAccess
  have hReal : Expression.eval env input.is_real =
      Expression.eval env input.isXor + Expression.eval env input.isOr + Expression.eval env input.isAnd := by
    simp only [Expression.eval]
  have hsignReal :
      -signedVal
          (Expression.eval env input.isXor + Expression.eval env input.isOr + Expression.eval env input.isAnd -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            (Expression.eval env input.isXor + Expression.eval env input.isOr + Expression.eval env input.isAnd)) := by
    simpa only [hReal] using hsign
  have hNegFlags :
      -Expression.eval env input.isAnd + (-Expression.eval env input.isOr + -Expression.eval env input.isXor) =
        -(Expression.eval env input.isXor + Expression.eval env input.isOr + Expression.eval env input.isAnd) := by
    ring
  have hDoubleNeg :
      -signedVal
          (-Expression.eval env input.isAnd + (-Expression.eval env input.isOr + -Expression.eval env input.isXor)) =
        signedVal
          (Expression.eval env input.isXor + Expression.eval env input.isOr + Expression.eval env input.isAnd) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  have hBLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).b_low_bytes.low_bytes =
        #v[env.get (offset), env.get (offset + 1),
          env.get (offset + 2), env.get (offset + 3)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  have hCLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).c_low_bytes.low_bytes =
        #v[env.get (offset + 4), env.get (offset + 5),
          env.get (offset + 6), env.get (offset + 7)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  have hResultLocals :
      Eval.eval env
          (bitwise_chip_operation (p := p) offset).bitwise_operation.result =
        #v[env.get (offset + 8), env.get (offset + 9),
          env.get (offset + 10), env.get (offset + 11),
          env.get (offset + 12), env.get (offset + 13),
          env.get (offset + 14), env.get (offset + 15)] := by
    simp [bitwise_chip_operation, explicit_provable_type, circuit_norm,
      Nat.add_assoc]
  simp only [nativeAccesses]
  rw [unexpectedInteractionsEmpty]
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
      Expression.eval, hNegFlags]
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
      BitwiseChip.Inputs.op_b_val, BitwiseChip.Inputs.op_c_val]
    simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
      eval_aluTypeReader, eval_registerAccessCols,
      eval_registerAccessTimestamp, eval_extractedU16toU8Operation,
      eval_bitwiseOperationColumns, ← ProvableType.getElem_eval_fields,
      eval_sub, ProvableType.eval_field,
      Expression.eval, hNegFlags, hBLocals, hCLocals,
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
      LookupAccessList.negMult, signedVal_neg hp2]
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
      (((((BitwiseChip.exposedProgramInteractions input).map
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
      LookupAccessList.negMult]
    simp only [hDoubleNeg]
  refine List.Perm.trans ?_
    (Extracted.perm_filter_by_kind_of_no_raw _ (bitwiseNoRawInteractions _)).symm
  rw [hS, hP]
  exact ((hB.append_left _).append hM).append_right _

theorem bitwiseChip_interactions_constructive
    (rustCols : Extracted.BitwiseOracle.BitwiseCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := bitwiseChipRowCodec.assignment
      (bitwiseChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        ({ circuit := BitwiseChip.circuit (p := p) } :
          Air.Flat.Component (ZMod p)).operations)
      (bitwiseChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := bitwiseChipOracle.deconfigure rustCols
  let assignment := bitwiseChipRowCodec.assignment cols data
  have hbind : BindsChipOutput BitwiseChip.main assignment.environment
      ({ circuit := BitwiseChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowInputVar
      ({ circuit := BitwiseChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [BitwiseChip.circuit_main_eq] at h
    exact h
  have hlegacy := bitwiseChip_interactions_faithful (p := p)
    assignment.environment
    ({ circuit := BitwiseChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowInputVar
    ({ circuit := BitwiseChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
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
