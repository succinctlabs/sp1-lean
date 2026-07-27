import SP1Clean.Faithful.ChipOracle
import SP1Clean.Faithful.SubwChipAnchors
import SP1Clean.Proofs.Chips.SubwChip.Formal

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def subwChipOracle :
    ChipOracle (ZMod p) Extracted.SubwCols Extracted.SubwCols :=
  ChipOracle.identity Extracted.SubwCols.asserts Extracted.SubwCols.interactions

def subwChipInput {F : Type} (cols : Extracted.SubwCols F) : SubwChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

def subwChipLocals {F : Type} (cols : Extracted.SubwCols F) : Vector F 3 :=
  #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
    cols.subw_operation.msb.msb]

def subwChipPhysicalRow {F : Type} (cols : Extracted.SubwCols F) : Array F :=
  inputFirstRow (subwChipInput cols) (subwChipLocals cols)

def subwChipColumnsOfInput {F : Type} (input : SubwChip.Inputs F)
    (locals : Vector F 3) : Extracted.SubwCols F :=
  ⟨input.state, input.adapter, ⟨#v[locals[0], locals[1]], ⟨locals[2]⟩⟩,
    input.is_real⟩

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

theorem subwChipColumnsOfInput_roundtrip {F : Type} (cols : Extracted.SubwCols F) :
    subwChipColumnsOfInput (subwChipInput cols) (subwChipLocals cols) = cols := by
  cases cols with
  | mk state adapter operation isReal =>
      cases operation with
      | mk value msb =>
          cases msb with
          | mk msbValue =>
              change
                (⟨state, adapter, ⟨#v[value[0], value[1]], ⟨msbValue⟩⟩,
                    isReal⟩ : Extracted.SubwCols F) =
                  ⟨state, adapter, ⟨value, ⟨msbValue⟩⟩, isReal⟩
              rw [vec2_eta]

@[circuit_norm] theorem eval_extractedU16MSBOperation_subw {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } : Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_extractedSubwOperation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.SubwOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value, msb := Eval.eval env cols.msb } :
        Extracted.SubwOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_extractedSubwOperation_value {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.SubwOperation (Expression F)) :
    (Eval.eval env cols).value = Eval.eval env cols.value := by
  rw [eval_extractedSubwOperation]

@[circuit_norm] theorem eval_extractedSubwOperation_msb {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.SubwOperation (Expression F)) :
    (Eval.eval env cols).msb.msb = Eval.eval env cols.msb.msb := by
  rw [eval_extractedSubwOperation, eval_extractedU16MSBOperation_subw]

@[circuit_norm] theorem eval_subwOperationInputs {F : Type} [FiniteField F]
    (env : Environment F) (input : SubwOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a, b := Eval.eval env input.b,
         cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real } :
        SubwOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_subwChipDirectOutput
    (input : SubwChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 3)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((SubwChip.elaborated (p := p)).output
          (varFromOffset SubwChip.Inputs 0) (size SubwChip.Inputs)) =
      subwChipColumnsOfInput input locals := by
  rw [SubwChip.directOutput_eq]
  rw [← CircuitType.eval_expression, SubwChip.eval_columns]
  unfold subwChipColumnsOfInput
  rw [Extracted.SubwCols.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [SubwChip.eval_inputs, SubwChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  constructor
  · rw [Extracted.SubwOperation.mk.injEq]
    constructor
    · rw [eval_extractedSubwOperation_value]
      ext i hi
      interval_cases i
      · rw [← ProvableType.getElem_eval_fields
          (Environment.fromArray (inputFirstRow input locals) data)
          (Vector.mapRange 2 fun i => var { index := size SubwChip.Inputs + i })
          0 (by decide), Vector.getElem_mapRange]
        exact eval_local_inputFirstRow input locals data 0 (by decide)
      · rw [← ProvableType.getElem_eval_fields
          (Environment.fromArray (inputFirstRow input locals) data)
          (Vector.mapRange 2 fun i => var { index := size SubwChip.Inputs + i })
          1 (by decide), Vector.getElem_mapRange]
        exact eval_local_inputFirstRow input locals data 1 (by decide)
    · rw [Extracted.U16MSBOperation.mk.injEq]
      simpa only [eval_extractedSubwOperation, eval_extractedU16MSBOperation_subw,
        ProvableType.eval_field] using
          (eval_local_inputFirstRow input locals data 2 (by decide))
  · exact hinputEval.1

def subwChipRowCodec : ChipRowCodec SubwChip.Inputs Extracted.SubwCols
    (SubwChip.circuit (p := p)) where
  assignment cols data := {
    row := subwChipPhysicalRow cols
    input := subwChipInput cols
    width_eq := by
      rw [subwChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        SubwChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (SubwChip.circuit (p := p)) (subwChipInput cols)
        (subwChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((SubwChip.main _).output _) = _
      rw [SubwChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_subwChipDirectOutput (p := p) (subwChipInput cols)
        (subwChipLocals cols) data).trans (subwChipColumnsOfInput_roundtrip cols) }

theorem subwChip_lookups_empty :
    (⟨SubwChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    SubwChip.circuit_main_eq]
  simp [SubwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SubwOperation.circuit, SubwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.main, circuit_norm]

set_option maxHeartbeats 1000000 in
private theorem subwOperationAssertions
    (env : Environment (ZMod p)) (input : Var SubwOperation.Inputs (ZMod p))
    (offset : ℕ) (a b : Word (ZMod p)) (cols : Extracted.SubwOperation (ZMod p))
    (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hcols : ProvableStruct.eval env input.cols = cols)
    (hreal : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0) (Extracted.SubwOperation.asserts a b cols isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubwOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, SubwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Extracted.SubwOperation.asserts,
    Extracted.U16MSBOperation.asserts, Gadgets.Equality.main, circuit_norm]
  have ha0 : Expression.eval env input.a[0] = a[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) ha
  have ha1 : Expression.eval env input.a[1] = a[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) ha
  have hb0 : Expression.eval env input.b[0] = b[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) hb
  have hb1 : Expression.eval env input.b[1] = b[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) hb
  have hvalue := congrArg (fun x => x.value) hcols
  have hv0 : Expression.eval env input.cols.value[0] = cols.value[0] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[0]) hvalue
  have hv1 : Expression.eval env input.cols.value[1] = cols.value[1] := by
    rw [ProvableType.getElem_eval_fields]
    exact congrArg (fun x => x[1]) hvalue
  have hmsb : Expression.eval env input.cols.msb.msb = cols.msb.msb := by
    have h := congrArg (fun x => x.msb.msb) hcols
    rw [← ProvableStruct.eval_eq_eval, eval_extractedSubwOperation,
      eval_extractedU16MSBOperation_subw] at h
    simpa only [ProvableType.eval_field] using h
  have hr : Expression.eval env input.is_real = isReal := by
    have h := hreal
    rw [← ProvableStruct.eval_eq_eval, eval_subwOperationInputs] at h
    simpa only [ProvableType.eval_field] using h
  have heval (x : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) x)[0] = Expression.eval env x := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval]
  rw [ha0, ha1, hb0, hb1, hv0, hv1, hmsb, hr, hreal]
  simp

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private def subw_chip_value (offset : ℕ) : Vector (Expression (ZMod p)) 2 :=
  Vector.mapRange 2 fun i => var { index := offset + i }

private def subw_chip_msb (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 2 }

set_option maxHeartbeats 1000000 in
private theorem subw_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0) (nativeAssertZeros env ((SubwChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((SubwOperation.main
              ⟨input.op_b_val, input.op_c_val,
                ⟨subw_chip_value offset, ⟨subw_chip_msb offset⟩⟩,
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
                (subw_chip_value offset)[0], (subw_chip_value offset)[1],
                subw_chip_msb offset * 65535, subw_chip_msb offset * 65535⟩).operations
                  (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a,
                #v[(subw_chip_value offset)[0], (subw_chip_value offset)[1],
                  subw_chip_msb offset * 65535, subw_chip_msb offset * 65535],
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field) (input.adapter.op_a_0, 0)).operations
              (offset + 3))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0) := by
  simp only [nativeAssertZeros, SubwChip.main, subw_chip_value, subw_chip_msb,
    Readers.CPUState.circuit, SubwOperation.circuit, Readers.RTypeReader.circuit,
    Readers.RegisterWrite.circuit, circuit_norm, List.map_append, List.forall_append]

set_option maxHeartbeats 4000000 in
theorem subwChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.SubwCols (ZMod p))
    (hbind : BindsChipOutput SubwChip.main env input offset cols) :
    List.Forall (· = 0) (subwChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((SubwChip.main input).operations offset)) := by
  let value : Vector (Expression (ZMod p)) 2 := subw_chip_value offset
  let msb : Expression (ZMod p) := subw_chip_msb offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let rustValue : Vector (ZMod p) 2 :=
    #v[(Eval.eval env value)[0], (Eval.eval env value)[1]]
  let rustMsb : ZMod p := Eval.eval env msb
  let rustOperation : Extracted.SubwOperation (ZMod p) :=
    { value := rustValue, msb := { msb := rustMsb } }
  let rustA : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_c_memory.prev_value[0], adapterValue.op_c_memory.prev_value[1],
      adapterValue.op_c_memory.prev_value[2], adapterValue.op_c_memory.prev_value[3]]
  let rustWriteValue : Word (ZMod p) :=
    #v[rustValue[0], rustValue[1], rustMsb * 65535, rustMsb * 65535]
  let isReal := Expression.eval env input.is_real
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
    rustState rustNextPc 8 isReal (by
      simp only [cpuInput, isReal, ProvableStruct.structEvalLiteralProc])
  let opInput : Var SubwOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb⟩⟩, input.is_real⟩
  have ha : (ProvableStruct.eval env opInput).a = rustA := by
    simp only [opInput, rustA, adapterValue, SubwChip.Inputs.op_b_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_b_memory =
        Eval.eval env input.adapter.op_b_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_b_memory).prev_value =
        Eval.eval env input.adapter.op_b_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hb : (ProvableStruct.eval env opInput).b = rustB := by
    simp only [opInput, rustB, adapterValue, SubwChip.Inputs.op_c_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_c_memory =
        Eval.eval env input.adapter.op_c_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_c_memory).prev_value =
        Eval.eval env input.adapter.op_c_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hOpCols : ProvableStruct.eval env opInput.cols = rustOperation := by
    simp only [opInput, rustOperation, rustValue, rustMsb,
      ProvableStruct.structEvalLiteralProc]
    rw [Extracted.SubwOperation.mk.injEq]
    constructor
    · ext i hi
      interval_cases i
      · rfl
      · rfl
    · rw [Extracted.U16MSBOperation.mk.injEq]
      rw [eval_extractedU16MSBOperation_subw]
  have hOp := subwOperationAssertions (p := p) env opInput (offset + 3)
    rustA rustB rustOperation isReal ha hb hOpCols (by
      simp only [opInput, isReal, ProvableStruct.structEvalLiteralProc])
  let rustAdapter : Extracted.RTypeReader (ZMod p) := adapterValue
  let rTypeInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 20,
      value[0], value[1], msb * 65535, msb * 65535⟩
  have hopAdapter : Expression.eval env input.adapter.op_a_0 = rustAdapter.op_a_0 := by
    calc
      _ = (Eval.eval env input.adapter).op_a_0 :=
        (Readers.RTypeReader.eval_opA0 env input.adapter).symm
      _ = (ProvableStruct.eval env input.adapter).op_a_0 :=
        congrArg (fun x => x.op_a_0) (ProvableStruct.eval_eq_eval env input.adapter)
      _ = _ := rfl
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 :=
    (Readers.RTypeReader.eval_opA0 env input.adapter).symm
  have hRType := CanonicalReader.rTypeAssertions (p := p) env rTypeInput (offset + 3)
    stateValue.clk_high (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) 20
    isReal isReal #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    (by simp only [rTypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [rTypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    hopAdapter
    (by simpa only [rTypeInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by simpa only [rTypeInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by simp only [rTypeInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ])
    (by simp only [rTypeInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a,
      #v[value[0], value[1], msb * 65535, msb * 65535], input.is_real⟩
  replace hbind := BindsChipOutput.ofElaborated (SubwChip.elaborated (p := p)) hbind
  rw [SubwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedSubwOperation,
    eval_extractedU16MSBOperation_subw] at hbind
  subst cols
  rw [subw_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, subwChipOracle,
    ChipOracle.identity, id_eq]
  simp only [Extracted.SubwCols.asserts, List.forall_append, List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustA, rustB, rustValue, rustMsb, rustOperation, adapterValue,
    isReal, opInput, value, msb, subw_chip_value, subw_chip_msb] at hOp
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  dsimp [stateValue, rustWriteValue, rustValue, rustMsb, rustAdapter,
    adapterValue, isReal, rTypeInput, value, msb, subw_chip_value,
    subw_chip_msb] at hRType
  simp_rw [← ProvableStruct.eval_eq_eval] at hOp hCpu hRType
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hRTypeG⟩, hGate, hOpA0, _⟩
    have hOpN := hOp.mp hOpG
    have hCpuN := hCpu.mp hCpuG
    have hRTypeN := (hRType.mp
      ⟨(by simpa only [vec4_eta] using hRTypeG), hOpA0⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 3)).mpr trivial
    have hEqSem : Expression.eval env input.adapter.op_a_0 =
        Expression.eval env (0 : Expression (ZMod p)) := by
      rw [hopEval, hOpA0]
      rfl
    have hEqN :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0
        (offset + 3)).mpr hEqSem
    have hGateN : Expression.eval env (input.is_real * (input.is_real - 1)) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGate
    exact ⟨hCpuN, hOpN, hRTypeN, hWriteN, hEqN, hGateN⟩
  · rintro ⟨hCpuN, hOpN, hRTypeN, _hWriteN, hEqN, hGateN⟩
    have hCpuG := hCpu.mpr hCpuN
    have hOpG := hOp.mpr hOpN
    have hEqSem :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0
        (offset + 3)).mp hEqN
    have hOpA0 : (Eval.eval env input.adapter).op_a_0 = 0 := by
      rw [← hopEval]
      simpa only [Expression.eval] using hEqSem
    have hRTypeG := (hRType.mpr ⟨hRTypeN, hOpA0⟩).1
    have hGate : Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGateN
    refine ⟨⟨⟨hOpG, hCpuG⟩, ?_⟩, hGate, hOpA0, trivial⟩
    simpa only [vec4_eta] using hRTypeG

set_option maxHeartbeats 2000000 in
theorem subwChip_constraints_constructive
    (rustCols : Extracted.SubwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subwChipRowCodec.assignment
      (subwChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (subwChipOracle.assertZeros rustCols) ↔
      (⟨SubwChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := subwChipOracle.deconfigure rustCols
  let assignment := subwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubwChip.main assignment.environment
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubwChip.circuit_main_eq] at h
    exact h
  have hlegacy := subwChip_constraints_faithful (p := p) assignment.environment
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (subwChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨SubwChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, SubwChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (SubwChip.circuit (p := p))
      assignment.environment subwChip_lookups_empty).symm

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

set_option maxHeartbeats 2000000 in
theorem subwChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.SubwCols (ZMod p))
    (hbind : BindsChipOutput SubwChip.main env input offset cols) :
    List.Perm (nativeAccesses env ((SubwChip.main input).operations offset))
      (subwChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated (SubwChip.elaborated (p := p)) hbind
  rw [SubwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedSubwOperation,
    eval_extractedU16MSBOperation_subw] at hbind
  subst cols
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((SubwChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, SubwChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.RTypeReader.circuit, Readers.RTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      SubwOperation.circuit, SubwOperation.main,
      U16MSBOperation.circuit, U16MSBOperation.main, Gadgets.Equality.main,
      FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses, ChipOracle.nativeInteractions,
    subwChipOracle, ChipOracle.identity, id_eq]
  apply subwcols_interactions_faithful_syntactic
  all_goals
    simp only [eval_cpuState, Readers.RTypeReader.eval_cols,
      eval_registerAccessCols, eval_registerAccessTimestamp,
      ProvableType.eval_field,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mapRange,
      Expression.eval, Nat.add_zero]

set_option maxHeartbeats 2000000 in
theorem subwChip_interactions_constructive
    (rustCols : Extracted.SubwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := subwChipRowCodec.assignment
      (subwChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨SubwChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (subwChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := subwChipOracle.deconfigure rustCols
  let assignment := subwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput SubwChip.main assignment.environment
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [SubwChip.circuit_main_eq] at h
    exact h
  have hlegacy := subwChip_interactions_faithful (p := p) assignment.environment
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨SubwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations (SubwChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, SubwChip.circuit_main_eq] using hlegacy

theorem subwChip_faithful :
    ChipFaithful (p := p) SubwChip.Inputs Extracted.SubwCols Extracted.SubwCols
      SubwChip.circuit subwChipRowCodec subwChipOracle where
  constraints := subwChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (subwChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
