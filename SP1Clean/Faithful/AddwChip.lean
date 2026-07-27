import SP1Clean.Faithful.ChipOracle
import SP1Clean.Faithful.AddwChipAnchors
import SP1Clean.Proofs.Chips.AddwChip.Formal

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def addwChipOracle :
    ChipOracle (ZMod p) Extracted.AddwCols Extracted.AddwCols :=
  ChipOracle.identity Extracted.AddwCols.asserts Extracted.AddwCols.interactions

def addwChipInput {F : Type} (cols : Extracted.AddwCols F) : AddwChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

def addwChipLocals {F : Type} (cols : Extracted.AddwCols F) : Vector F 3 :=
  #v[cols.addw_operation.value[0], cols.addw_operation.value[1],
    cols.addw_operation.msb.msb]

def addwChipPhysicalRow {F : Type} (cols : Extracted.AddwCols F) : Array F :=
  inputFirstRow (addwChipInput cols) (addwChipLocals cols)

def addwChipColumnsOfInput {F : Type} (input : AddwChip.Inputs F)
    (locals : Vector F 3) : Extracted.AddwCols F :=
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

theorem addwChipColumnsOfInput_roundtrip {F : Type} (cols : Extracted.AddwCols F) :
    addwChipColumnsOfInput (addwChipInput cols) (addwChipLocals cols) = cols := by
  cases cols with
  | mk state adapter operation isReal =>
      cases operation with
      | mk value msb =>
          cases msb with
          | mk msbValue =>
              change
                (⟨state, adapter, ⟨#v[value[0], value[1]], ⟨msbValue⟩⟩,
                    isReal⟩ : Extracted.AddwCols F) =
                  ⟨state, adapter, ⟨value, ⟨msbValue⟩⟩, isReal⟩
              rw [vec2_eta]

@[circuit_norm] theorem eval_extractedU16MSBOperation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } : Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_extractedAddwOperation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.AddwOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value, msb := Eval.eval env cols.msb } :
        Extracted.AddwOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_extractedAddwOperation_value {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.AddwOperation (Expression F)) :
    (Eval.eval env cols).value = Eval.eval env cols.value := by
  rw [eval_extractedAddwOperation]

@[circuit_norm] theorem eval_extractedAddwOperation_msb {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.AddwOperation (Expression F)) :
    (Eval.eval env cols).msb.msb = Eval.eval env cols.msb.msb := by
  rw [eval_extractedAddwOperation, eval_extractedU16MSBOperation]

@[circuit_norm] theorem eval_addwOperationInputs {F : Type} [FiniteField F]
    (env : Environment F) (input : AddwOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a, b := Eval.eval env input.b,
         cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real } :
        AddwOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_aluTypeInputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Readers.ALUTypeReader.Inputs (Expression F)) :
    Eval.eval env input =
      ({ cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real,
         is_trusted := Eval.eval env input.is_trusted,
         clk_high := Eval.eval env input.clk_high, clk_low := Eval.eval env input.clk_low,
         pc := Eval.eval env input.pc, opcode := Eval.eval env input.opcode,
         wv0 := Eval.eval env input.wv0, wv1 := Eval.eval env input.wv1,
         wv2 := Eval.eval env input.wv2, wv3 := Eval.eval env input.wv3 } :
        Readers.ALUTypeReader.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_addwChipDirectOutput
    (input : AddwChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 3)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((AddwChip.elaborated (p := p)).output
          (varFromOffset AddwChip.Inputs 0) (size AddwChip.Inputs)) =
      addwChipColumnsOfInput input locals := by
  rw [AddwChip.directOutput_eq]
  rw [← CircuitType.eval_expression, AddwChip.eval_columns]
  unfold addwChipColumnsOfInput
  rw [Extracted.AddwCols.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [AddwChip.eval_inputs, AddwChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  constructor
  · rw [Extracted.AddwOperation.mk.injEq]
    constructor
    · rw [eval_extractedAddwOperation_value]
      ext i hi
      interval_cases i
      · rw [← ProvableType.getElem_eval_fields
          (Environment.fromArray (inputFirstRow input locals) data)
          (Vector.mapRange 2 fun i => var { index := size AddwChip.Inputs + i })
          0 (by decide), Vector.getElem_mapRange]
        exact eval_local_inputFirstRow input locals data 0 (by decide)
      · rw [← ProvableType.getElem_eval_fields
          (Environment.fromArray (inputFirstRow input locals) data)
          (Vector.mapRange 2 fun i => var { index := size AddwChip.Inputs + i })
          1 (by decide), Vector.getElem_mapRange]
        exact eval_local_inputFirstRow input locals data 1 (by decide)
    · rw [Extracted.U16MSBOperation.mk.injEq]
      simpa only [eval_extractedAddwOperation, eval_extractedU16MSBOperation,
        ProvableType.eval_field] using
          (eval_local_inputFirstRow input locals data 2 (by decide))
  · exact hinputEval.1

def addwChipRowCodec : ChipRowCodec AddwChip.Inputs Extracted.AddwCols
    (AddwChip.circuit (p := p)) where
  assignment cols data := {
    row := addwChipPhysicalRow cols
    input := addwChipInput cols
    width_eq := by
      rw [addwChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        AddwChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (AddwChip.circuit (p := p)) (addwChipInput cols)
        (addwChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((AddwChip.main _).output _) = _
      rw [AddwChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_addwChipDirectOutput (p := p) (addwChipInput cols)
        (addwChipLocals cols) data).trans (addwChipColumnsOfInput_roundtrip cols) }

theorem addwChip_lookups_empty :
    (⟨AddwChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    AddwChip.circuit_main_eq]
  simp [AddwChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddwOperation.circuit, AddwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.main, circuit_norm]

set_option maxHeartbeats 1000000 in
private theorem addwOperationAssertions
    (env : Environment (ZMod p)) (input : Var AddwOperation.Inputs (ZMod p))
    (offset : ℕ) (a b : Word (ZMod p)) (cols : Extracted.AddwOperation (ZMod p))
    (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hcols : ProvableStruct.eval env input.cols = cols)
    (hreal : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0) (Extracted.AddwOperation.asserts a b cols isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((AddwOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, AddwOperation.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Extracted.AddwOperation.asserts,
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
    rw [← ProvableStruct.eval_eq_eval, eval_extractedAddwOperation,
      eval_extractedU16MSBOperation] at h
    simpa only [ProvableType.eval_field] using h
  have hr : Expression.eval env input.is_real = isReal := by
    have h := hreal
    rw [← ProvableStruct.eval_eq_eval, eval_addwOperationInputs] at h
    simpa only [ProvableType.eval_field] using h
  have heval (x : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) x)[0] = Expression.eval env x := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval]
  rw [ha0, ha1, hb0, hb1, hv0, hv1, hmsb, hr, hreal]
  simp

set_option maxHeartbeats 1000000 in
private theorem aluTypeAssertions
    (env : Environment (ZMod p)) (input : Var Readers.ALUTypeReader.Inputs (ZMod p))
    (offset : ℕ) (clkHigh clkLow opcode isReal isTrusted : ZMod p)
    (pc : Vector (ZMod p) 3) (writeValue : Word (ZMod p))
    (cols : Extracted.ALUTypeReader (ZMod p))
    (hreal : (ProvableStruct.eval env input).is_real = isReal)
    (htrusted : (ProvableStruct.eval env input).is_trusted = isTrusted)
    (hcols : ProvableStruct.eval env input.cols = cols)
    (hwrite0 : Expression.eval env input.wv0 = writeValue[0])
    (hwrite1 : Expression.eval env input.wv1 = writeValue[1])
    (hwrite2 : Expression.eval env input.wv2 = writeValue[2])
    (hwrite3 : Expression.eval env input.wv3 = writeValue[3])
    (htrust : isTrusted = isReal) :
    (List.Forall (· = 0)
        (Extracted.ALUTypeReader.asserts clkHigh clkLow pc opcode writeValue cols
          isReal isTrusted) ∧ cols.op_a_0 = 0) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env ((Readers.ALUTypeReader.main input).operations offset)) ∧
        cols.op_a_0 = 0) := by
  simp only [nativeAssertZeros, Readers.ALUTypeReader.main, circuit_norm]
  simp only [Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    circuit_norm, constraints_formalAssertion_toSubcircuit]
  simp only [List.map_append, List.map_cons, List.forall_append, List.forall_cons]
  simp only [CanonicalReader.registerAccessTimestampAssertions]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [Extracted.ALUTypeReader.asserts, List.Forall]
  have hrealEval : Expression.eval env input.is_real = isReal := by
    have h := congrArg (fun x => x.is_real) (ProvableStruct.eval_eq_eval env input)
    rw [eval_aluTypeInputs] at h
    have heq : Expression.eval env input.is_real =
        (ProvableStruct.eval env input).is_real := by
      simpa only [ProvableType.eval_field] using h
    exact heq.trans hreal
  have htrustedEval : Expression.eval env input.is_trusted = isTrusted := by
    have h := congrArg (fun x => x.is_trusted) (ProvableStruct.eval_eq_eval env input)
    rw [eval_aluTypeInputs] at h
    have heq : Expression.eval env input.is_trusted =
        (ProvableStruct.eval env input).is_trusted := by
      simpa only [ProvableType.eval_field] using h
    exact heq.trans htrusted
  have hcolsEval : Eval.eval env input.cols = cols :=
    (ProvableStruct.eval_eq_eval env input.cols).trans hcols
  rw [Readers.ALUTypeReader.eval_cols] at hcolsEval
  have hopA0 : Expression.eval env input.cols.op_a_0 = cols.op_a_0 := by
    simpa only [ProvableType.eval_field] using congrArg (fun x => x.op_a_0) hcolsEval
  have himm : Expression.eval env input.cols.imm_c = cols.imm_c := by
    simpa only [ProvableType.eval_field] using congrArg (fun x => x.imm_c) hcolsEval
  have hopC : Eval.eval env input.cols.op_c = cols.op_c := by
    exact congrArg (fun x => x.op_c) hcolsEval
  have hopCPrev : Eval.eval env input.cols.op_c_memory.prev_value =
      cols.op_c_memory.prev_value := by
    have h := congrArg (fun x => x.op_c_memory) hcolsEval
    change Eval.eval env input.cols.op_c_memory = cols.op_c_memory at h
    rw [Readers.ALUTypeReader.eval_accessCols] at h
    exact congrArg (fun x => x.prev_value) h
  have hopC0 : Expression.eval env input.cols.op_c[0] = cols.op_c[0] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c 0 (by decide)).trans
      (congrArg (fun x => x[0]) hopC)
  have hopC1 : Expression.eval env input.cols.op_c[1] = cols.op_c[1] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c 1 (by decide)).trans
      (congrArg (fun x => x[1]) hopC)
  have hopC2 : Expression.eval env input.cols.op_c[2] = cols.op_c[2] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c 2 (by decide)).trans
      (congrArg (fun x => x[2]) hopC)
  have hopC3 : Expression.eval env input.cols.op_c[3] = cols.op_c[3] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c 3 (by decide)).trans
      (congrArg (fun x => x[3]) hopC)
  have hprev0 : Expression.eval env input.cols.op_c_memory.prev_value[0] =
      cols.op_c_memory.prev_value[0] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c_memory.prev_value 0
      (by decide)).trans (congrArg (fun x => x[0]) hopCPrev)
  have hprev1 : Expression.eval env input.cols.op_c_memory.prev_value[1] =
      cols.op_c_memory.prev_value[1] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c_memory.prev_value 1
      (by decide)).trans (congrArg (fun x => x[1]) hopCPrev)
  have hprev2 : Expression.eval env input.cols.op_c_memory.prev_value[2] =
      cols.op_c_memory.prev_value[2] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c_memory.prev_value 2
      (by decide)).trans (congrArg (fun x => x[2]) hopCPrev)
  have hprev3 : Expression.eval env input.cols.op_c_memory.prev_value[3] =
      cols.op_c_memory.prev_value[3] :=
    (ProvableType.getElem_eval_fields env input.cols.op_c_memory.prev_value 3
      (by decide)).trans (congrArg (fun x => x[3]) hopCPrev)
  simp only [eval_sub, Expression.eval]
  rw [hopA0, himm, hopC0, hopC1, hopC2, hopC3, hprev0, hprev1, hprev2, hprev3,
    hrealEval, htrustedEval, hwrite0, hwrite1, hwrite2, hwrite3, htrust]
  constructor <;> rintro ⟨h, hzero⟩ <;> refine ⟨?_, hzero⟩ <;>
    simp only [hzero, zero_mul, sub_zero, true_and, and_true] at h ⊢ <;> tauto

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private def addw_chip_value (offset : ℕ) : Vector (Expression (ZMod p)) 2 :=
  Vector.mapRange 2 fun i => var { index := offset + i }

private def addw_chip_msb (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 2 }

set_option maxHeartbeats 1000000 in
private theorem addw_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0) (nativeAssertZeros env ((AddwChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddwOperation.main
              ⟨input.op_b_val, input.op_c_val,
                ⟨addw_chip_value offset, ⟨addw_chip_msb offset⟩⟩,
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
                (addw_chip_value offset)[0], (addw_chip_value offset)[1],
                addw_chip_msb offset * 65535, addw_chip_msb offset * 65535⟩).operations
                  (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a,
                #v[(addw_chip_value offset)[0], (addw_chip_value offset)[1],
                  addw_chip_msb offset * 65535, addw_chip_msb offset * 65535],
                input.is_real⟩).operations (offset + 3))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field) (input.adapter.op_a_0, 0)).operations
              (offset + 3))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0) := by
  simp only [nativeAssertZeros, AddwChip.main, addw_chip_value, addw_chip_msb,
    Readers.CPUState.circuit, AddwOperation.circuit, Readers.ALUTypeReader.circuit,
    Readers.RegisterWrite.circuit, circuit_norm, List.map_append, List.forall_append]

set_option maxHeartbeats 4000000 in
theorem addwChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddwCols (ZMod p))
    (hbind : BindsChipOutput AddwChip.main env input offset cols) :
    List.Forall (· = 0) (addwChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((AddwChip.main input).operations offset)) := by
  let value : Vector (Expression (ZMod p)) 2 := addw_chip_value offset
  let msb : Expression (ZMod p) := addw_chip_msb offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let rustValue : Vector (ZMod p) 2 :=
    #v[(Eval.eval env value)[0], (Eval.eval env value)[1]]
  let rustMsb : ZMod p := Eval.eval env msb
  let rustOperation : Extracted.AddwOperation (ZMod p) :=
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
  let opInput : Var AddwOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, ⟨value, ⟨msb⟩⟩, input.is_real⟩
  have ha : (ProvableStruct.eval env opInput).a = rustA := by
    simp only [opInput, rustA, adapterValue, AddwChip.Inputs.op_b_val,
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
    simp only [opInput, rustB, adapterValue, AddwChip.Inputs.op_c_val,
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
    rw [Extracted.AddwOperation.mk.injEq]
    constructor
    · ext i hi
      interval_cases i
      · rfl
      · rfl
    · rw [Extracted.U16MSBOperation.mk.injEq]
      rw [eval_extractedU16MSBOperation]
  have hOp := addwOperationAssertions (p := p) env opInput (offset + 3)
    rustA rustB rustOperation isReal ha hb hOpCols (by
      simp only [opInput, isReal, ProvableStruct.structEvalLiteralProc])
  let rustAdapter : Extracted.ALUTypeReader (ZMod p) := adapterValue
  let aluInput : Var Readers.ALUTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 19,
      value[0], value[1], msb * 65535, msb * 65535⟩
  have hopAdapter : Expression.eval env input.adapter.op_a_0 = rustAdapter.op_a_0 := by
    calc
      _ = (Eval.eval env input.adapter).op_a_0 :=
        (Readers.ALUTypeReader.eval_opA0 env input.adapter).symm
      _ = (ProvableStruct.eval env input.adapter).op_a_0 :=
        congrArg (fun x => x.op_a_0) (ProvableStruct.eval_eq_eval env input.adapter)
      _ = _ := rfl
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 :=
    (Readers.ALUTypeReader.eval_opA0 env input.adapter).symm
  have hAlu := aluTypeAssertions (p := p) env aluInput (offset + 3)
    stateValue.clk_high (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) 19
    isReal isReal #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustWriteValue rustAdapter
    (by simp only [aluInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [aluInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [aluInput, rustAdapter, adapterValue])
    (by simpa only [aluInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by simpa only [aluInput, rustWriteValue, rustValue,
      ProvableStruct.structEvalLiteralProc, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by simp only [aluInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ])
    (by simp only [aluInput, rustWriteValue, rustMsb,
      ProvableType.eval_field, Expression.eval,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a,
      #v[value[0], value[1], msb * 65535, msb * 65535], input.is_real⟩
  replace hbind := BindsChipOutput.ofElaborated (AddwChip.elaborated (p := p)) hbind
  rw [AddwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedAddwOperation,
    eval_extractedU16MSBOperation] at hbind
  subst cols
  rw [addw_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, addwChipOracle,
    ChipOracle.identity, id_eq]
  simp only [Extracted.AddwCols.asserts, List.forall_append, List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustA, rustB, rustValue, rustMsb, rustOperation, adapterValue,
    isReal, opInput, value, msb, addw_chip_value, addw_chip_msb] at hOp
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  dsimp [stateValue, rustWriteValue, rustValue, rustMsb, rustAdapter,
    adapterValue, isReal, aluInput, value, msb, addw_chip_value,
    addw_chip_msb] at hAlu
  simp_rw [← ProvableStruct.eval_eq_eval] at hOp hCpu hAlu
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hAluG⟩, hGate, hOpA0, _⟩
    have hOpN := hOp.mp hOpG
    have hCpuN := hCpu.mp hCpuG
    have hAluN := (hAlu.mp
      ⟨(by simpa only [vec4_eta] using hAluG), hOpA0⟩).1
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
    exact ⟨hCpuN, hOpN, hAluN, hWriteN, hEqN, hGateN⟩
  · rintro ⟨hCpuN, hOpN, hAluN, _hWriteN, hEqN, hGateN⟩
    have hCpuG := hCpu.mpr hCpuN
    have hOpG := hOp.mpr hOpN
    have hEqSem :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0
        (offset + 3)).mp hEqN
    have hOpA0 : (Eval.eval env input.adapter).op_a_0 = 0 := by
      rw [← hopEval]
      simpa only [Expression.eval] using hEqSem
    have hAluG := (hAlu.mpr ⟨hAluN, hOpA0⟩).1
    have hGate : Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGateN
    refine ⟨⟨⟨hOpG, hCpuG⟩, ?_⟩, hGate, hOpA0, trivial⟩
    simpa only [vec4_eta] using hAluG

set_option maxHeartbeats 2000000 in
theorem addwChip_constraints_constructive
    (rustCols : Extracted.AddwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := addwChipRowCodec.assignment
      (addwChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (addwChipOracle.assertZeros rustCols) ↔
      (⟨AddwChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := addwChipOracle.deconfigure rustCols
  let assignment := addwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AddwChip.main assignment.environment
      (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AddwChip.circuit_main_eq] at h
    exact h
  have hlegacy := addwChip_constraints_faithful (p := p) assignment.environment
    (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (addwChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨AddwChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, AddwChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (AddwChip.circuit (p := p))
      assignment.environment addwChip_lookups_empty).symm

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

set_option maxHeartbeats 2000000 in
theorem addwChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddwCols (ZMod p))
    (hbind : BindsChipOutput AddwChip.main env input offset cols) :
    List.Perm (nativeAccesses env ((AddwChip.main input).operations offset))
      (addwChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated (AddwChip.elaborated (p := p)) hbind
  rw [AddwChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedAddwOperation,
    eval_extractedU16MSBOperation] at hbind
  subst cols
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((AddwChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, AddwChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      AddwOperation.circuit, AddwOperation.main,
      U16MSBOperation.circuit, U16MSBOperation.main, Gadgets.Equality.main,
      FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses, ChipOracle.nativeInteractions,
    addwChipOracle, ChipOracle.identity, id_eq]
  apply addwcols_interactions_faithful_syntactic
  all_goals
    simp only [eval_cpuState, Readers.ALUTypeReader.eval_cols,
      eval_registerAccessCols, eval_registerAccessTimestamp,
      ProvableType.eval_field,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mapRange,
      Expression.eval, Nat.add_zero]

set_option maxHeartbeats 2000000 in
theorem addwChip_interactions_constructive
    (rustCols : Extracted.AddwCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := addwChipRowCodec.assignment
      (addwChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨AddwChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (addwChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := addwChipOracle.deconfigure rustCols
  let assignment := addwChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AddwChip.main assignment.environment
      (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AddwChip.circuit_main_eq] at h
    exact h
  have hlegacy := addwChip_interactions_faithful (p := p) assignment.environment
    (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AddwChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations (AddwChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, AddwChip.circuit_main_eq] using hlegacy

theorem addwChip_faithful :
    ChipFaithful (p := p) AddwChip.Inputs Extracted.AddwCols Extracted.AddwCols
      AddwChip.circuit addwChipRowCodec addwChipOracle where
  constraints := addwChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (addwChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
