import SP1Clean.Faithful.ChipOracle
import SP1Clean.Native.Chips.AddiChip.Defs
import SP1Clean.Proofs.Chips.AddiChip.Formal
import SP1Clean.Extracted.AddiChip

/-! # Whole-chip faithfulness — native Addi row ↔ pinned SP1 Rust AIR

`addiChip_faithful` compares every native assertion and emitted bus interaction with the complete
extracted Rust `AddiCols` oracle, including padding rows. The native add gadget and Rust's
`AddOperation` remain independent decompositions; they meet only through the completed chip row.
The I-type destination write that Clean factors into `RegisterWrite` is recombined with the reader
before the Memory interaction multiset is compared. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def addiChipOracle :
    ChipOracle (ZMod p) Extracted.AddiCols Extracted.AddiCols :=
  ChipOracle.identity Extracted.AddiCols.asserts Extracted.AddiCols.interactions

def addiChipInput {F : Type} (cols : Extracted.AddiCols F) : AddiChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

def addiChipPhysicalRow {F : Type} (cols : Extracted.AddiCols F) : Array F :=
  inputFirstRow (addiChipInput cols) cols.add_operation.value

def addiChipColumnsOfInput {F : Type} (input : AddiChip.Inputs F) (value : Word F) :
    Extracted.AddiCols F :=
  ⟨input.state, input.adapter, ⟨value⟩, input.is_real⟩

@[circuit_norm] theorem eval_extractedAddOperation {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.AddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } : Extracted.AddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem addiChipColumnsOfInput_roundtrip {F : Type} (cols : Extracted.AddiCols F) :
    addiChipColumnsOfInput (addiChipInput cols) cols.add_operation.value = cols := by
  cases cols
  rfl

theorem eval_addiChipDirectOutput
    (input : AddiChip.Inputs (ZMod p)) (value : Word (ZMod p))
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input value) data)
        ((AddiChip.elaborated (p := p)).output
          (varFromOffset AddiChip.Inputs 0) (size AddiChip.Inputs)) =
      addiChipColumnsOfInput input value := by
  rw [AddiChip.directOutput_eq]
  rw [← CircuitType.eval_expression, AddiChip.eval_columns]
  unfold addiChipColumnsOfInput
  rw [Extracted.AddiCols.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input value data
  rw [AddiChip.eval_inputs, AddiChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2
  constructor
  · rw [Extracted.AddOperation.mk.injEq]
    rw [eval_extractedAddOperation]
    ext i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input value) data)
      (Vector.mapRange 4 fun i => var { index := size AddiChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    exact eval_local_inputFirstRow input value data i hi
  · exact hinputEval.1

def addiChipRowCodec : ChipRowCodec AddiChip.Inputs Extracted.AddiCols
    (AddiChip.circuit (p := p)) where
  assignment cols data := {
    row := addiChipPhysicalRow cols
    input := addiChipInput cols
    width_eq := by
      rw [addiChipPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
        AddiChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (AddiChip.circuit (p := p)) (addiChipInput cols)
        cols.add_operation.value data
    rowOutput_eq := by
      change ProvableType.eval _ ((AddiChip.main _).output _) = _
      rw [AddiChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk, Air.Flat.Component.rowOffset_mk]
      exact (eval_addiChipDirectOutput (p := p) (addiChipInput cols)
        cols.add_operation.value data).trans (addiChipColumnsOfInput_roundtrip cols) }

theorem addiChip_lookups_empty :
    (⟨AddiChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    AddiChip.circuit_main_eq]
  simp [AddiChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, Gadgets.Equality.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 2000000 in
private theorem addi_operation_assertions_local
    (env : Environment (ZMod p)) (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b value : Word (ZMod p)) (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hv : (ProvableStruct.eval env input.cols).value = value)
    (hr : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.AddOperation.asserts a b { value := value } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((AddOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, AddOperation.main, Extracted.AddOperation.asserts,
    circuit_norm]
  rw [ha, hb, hv, hr]

private theorem forall_nil_iff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private def addi_chip_value (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

set_option maxHeartbeats 1000000 in
private theorem addi_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0) (nativeAssertZeros env ((AddiChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddOperation.main
              ⟨input.op_b_val, input.op_c_val, { value := addi_chip_value offset },
                input.is_real⟩).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReader.main
              ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 1,
                (addi_chip_value offset)[0], (addi_chip_value offset)[1],
                (addi_chip_value offset)[2], (addi_chip_value offset)[3]⟩).operations
                  (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, addi_chip_value offset, input.is_real⟩).operations
                  (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field) (input.adapter.op_a_0, 0)).operations
              (offset + 4))) ∧
        Expression.eval env (input.is_real * (input.is_real - 1)) = 0) := by
  simp only [nativeAssertZeros, AddiChip.main, addi_chip_value, Readers.CPUState.circuit,
    AddOperation.circuit, Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]

set_option maxHeartbeats 4000000 in
theorem addiChip_constraints_faithful
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hbind : BindsChipOutput AddiChip.main env input offset cols) :
    List.Forall (· = 0) (addiChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((AddiChip.main input).operations offset)) := by
  let value : Word (Expression (ZMod p)) := addi_chip_value offset
  let stateValue := ProvableStruct.eval env input.state
  let adapterValue := ProvableStruct.eval env input.adapter
  let rustValue : Word (ZMod p) :=
    #v[(Eval.eval env value)[0], (Eval.eval env value)[1],
      (Eval.eval env value)[2], (Eval.eval env value)[3]]
  let rustA : Word (ZMod p) :=
    #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
      adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
  let rustB : Word (ZMod p) :=
    #v[adapterValue.op_c_imm[0], adapterValue.op_c_imm[1],
      adapterValue.op_c_imm[2], adapterValue.op_c_imm[3]]
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
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, { value := value }, input.is_real⟩
  have ha : (ProvableStruct.eval env addInput).a = rustA := by
    simp only [addInput, rustA, adapterValue, AddiChip.Inputs.op_b_val,
      ProvableStruct.structEvalLiteralProc]
    have hOuter : (ProvableStruct.eval env input.adapter).op_b_memory =
        Eval.eval env input.adapter.op_b_memory := rfl
    rw [hOuter, ProvableStruct.eval_eq_eval]
    have hPrev : (ProvableStruct.eval env input.adapter.op_b_memory).prev_value =
        Eval.eval env input.adapter.op_b_memory.prev_value := rfl
    rw [hPrev]
    ext i hi
    interval_cases i <;> simp
  have hb : (ProvableStruct.eval env addInput).b = rustB := by
    simp only [addInput, rustB, adapterValue, AddiChip.Inputs.op_c_val,
      ProvableStruct.structEvalLiteralProc]
    have hImm : (ProvableStruct.eval env input.adapter).op_c_imm =
        Eval.eval env input.adapter.op_c_imm := rfl
    rw [hImm]
    ext i hi
    interval_cases i <;> simp
  have hv : (ProvableStruct.eval env addInput.cols).value = rustValue := by
    simp only [addInput, rustValue, ProvableStruct.structEvalLiteralProc]
    ext i hi
    interval_cases i <;> simp
  have hAdd := addi_operation_assertions_local (p := p) env addInput (offset + 4)
    rustA rustB rustValue isReal ha hb hv (by
      simp only [addInput, isReal, ProvableStruct.structEvalLiteralProc])
  let rustAdapter : Extracted.ITypeReader (ZMod p) :=
    { op_a := adapterValue.op_a
      op_a_memory :=
        { prev_value :=
            #v[adapterValue.op_a_memory.prev_value[0], adapterValue.op_a_memory.prev_value[1],
              adapterValue.op_a_memory.prev_value[2], adapterValue.op_a_memory.prev_value[3]]
          access_timestamp := adapterValue.op_a_memory.access_timestamp }
      op_a_0 := adapterValue.op_a_0
      op_b := adapterValue.op_b
      op_b_memory :=
        { prev_value :=
            #v[adapterValue.op_b_memory.prev_value[0], adapterValue.op_b_memory.prev_value[1],
              adapterValue.op_b_memory.prev_value[2], adapterValue.op_b_memory.prev_value[3]]
          access_timestamp := adapterValue.op_b_memory.access_timestamp }
      op_c_imm :=
        #v[adapterValue.op_c_imm[0], adapterValue.op_c_imm[1],
          adapterValue.op_c_imm[2], adapterValue.op_c_imm[3]] }
  let itypeInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 1,
      value[0], value[1], value[2], value[3]⟩
  have hopAdapter : Expression.eval env input.adapter.op_a_0 = adapterValue.op_a_0 := by
    simp [adapterValue, ProvableStruct.eval, circuit_norm]
  have hIType := CanonicalReader.iTypeAssertions (p := p) env itypeInput (offset + 4)
    stateValue.clk_high (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536) 1
    isReal isReal #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustValue rustAdapter
    (by simp only [itypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simp only [itypeInput, isReal, ProvableStruct.structEvalLiteralProc])
    (by simpa only [itypeInput, rustAdapter] using hopAdapter)
    (by simpa only [itypeInput, rustValue,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by simpa only [itypeInput, rustValue,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by simpa only [itypeInput, rustValue,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 2 (by decide)))
    (by simpa only [itypeInput, rustValue,
      ProvableStruct.structEvalLiteralProc, ProvableType.eval_field,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using
        (ProvableType.getElem_eval_fields env value 3 (by decide))) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, value, input.is_real⟩
  have hopEval : Expression.eval env input.adapter.op_a_0 =
      (Eval.eval env input.adapter).op_a_0 := by
    rw [ProvableStruct.eval_eq_eval]
    exact hopAdapter
  replace hbind := BindsChipOutput.ofElaborated (AddiChip.elaborated (p := p)) hbind
  rw [AddiChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedAddOperation] at hbind
  subst cols
  rw [addi_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, addiChipOracle, ChipOracle.identity, id_eq]
  simp only [Extracted.AddiCols.asserts, List.forall_append]
  simp only [List.forall_cons]
  rw [forall_nil_iff]
  dsimp [rustA, rustB, rustValue, adapterValue, isReal, addInput,
    value, addi_chip_value] at hAdd
  dsimp [rustState, rustNextPc, stateValue, isReal, cpuInput] at hCpu
  dsimp [stateValue, rustValue, rustAdapter, adapterValue, isReal,
    itypeInput, value, addi_chip_value] at hIType
  simp_rw [← ProvableStruct.eval_eq_eval] at hAdd hCpu hIType
  constructor
  · rintro ⟨⟨⟨hAddG, hCpuG⟩, hITypeG⟩, hGate, hOp, _⟩
    have hAddN := hAdd.mp hAddG
    have hCpuN := hCpu.mp hCpuG
    have hITypeN := (hIType.mp ⟨hITypeG, hOp⟩).1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput (offset + 4)).mpr trivial
    have hEqSem : Expression.eval env input.adapter.op_a_0 =
        Expression.eval env (0 : Expression (ZMod p)) := by
      rw [hopEval, hOp]
      rfl
    have hEqN :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0 (offset + 4)).mpr hEqSem
    have hGateN : Expression.eval env (input.is_real * (input.is_real - 1)) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGate
    exact ⟨hCpuN, hAddN, hITypeN, hWriteN, hEqN, hGateN⟩
  · rintro ⟨hCpuN, hAddN, hITypeN, _hWriteN, hEqN, hGateN⟩
    have hCpuG := hCpu.mpr hCpuN
    have hAddG := hAdd.mpr hAddN
    have hEqSem :=
      (CanonicalReader.equalityAssertions env input.adapter.op_a_0 0 (offset + 4)).mp hEqN
    have hOp : (Eval.eval env input.adapter).op_a_0 = 0 := by
      rw [← hopEval]
      simpa only [Expression.eval] using hEqSem
    have hITypeG := (hIType.mpr ⟨hITypeN, hOp⟩).1
    have hGate : Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := by
      simpa only [eval_mul, eval_sub, Expression.eval] using hGateN
    exact ⟨⟨⟨hAddG, hCpuG⟩, hITypeG⟩, hGate, hOp, trivial⟩

set_option maxHeartbeats 2000000 in
theorem addiChip_constraints_constructive
    (rustCols : Extracted.AddiCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := addiChipRowCodec.assignment
      (addiChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (addiChipOracle.assertZeros rustCols) ↔
      (⟨AddiChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := addiChipOracle.deconfigure rustCols
  let assignment := addiChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AddiChip.main assignment.environment
      (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AddiChip.circuit_main_eq] at h
    exact h
  have hlegacy := addiChip_constraints_faithful (p := p) assignment.environment
    (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (addiChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨AddiChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk, AddiChip.circuit_main_eq] using hlegacy
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros (AddiChip.circuit (p := p))
      assignment.environment addiChip_lookups_empty).symm

open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem addicols_state_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hreal : Expression.eval env input.is_real = cols.is_real)
    (hclkHigh : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (hclk0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hclk1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hpc0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (hpc1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (hpc2 : Expression.eval env input.state.pc[2] = cols.state.pc[2]) :
    (((AddiChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
        (AbstractInteraction.toAccess env) =
      ((Extracted.AddiCols.interactions cols).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.State) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) stateChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [AddiChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions,
    toAccess_pushIf_state, toAccess_pullIf_state, heq]
  simp [circuit_norm, toAccess_pushIf_state, toAccess_pullIf_state,
    Gadgets.Equality.main,
    Extracted.AddiCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    hreal, hclkHigh, hclk0, hclk1, hpc0, hpc1, hpc2]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem addicols_program_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hreal : Expression.eval env input.is_real = cols.is_real)
    (hpc0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (hpc1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (hpc2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (hopA : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (hopB : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (hopA0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0)
    (himm0 : Expression.eval env input.adapter.op_c_imm[0] = cols.adapter.op_c_imm[0])
    (himm1 : Expression.eval env input.adapter.op_c_imm[1] = cols.adapter.op_c_imm[1])
    (himm2 : Expression.eval env input.adapter.op_c_imm[2] = cols.adapter.op_c_imm[2])
    (himm3 : Expression.eval env input.adapter.op_c_imm[3] = cols.adapter.op_c_imm[3]) :
    (((AddiChip.main input).operations offset).interactionsWith programChannel.toRaw).map
        (AbstractInteraction.toAccess env) =
      (((Extracted.AddiCols.interactions cols).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Program)).map
            LookupAccessList.negMult := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) programChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  have hk := fun (g : Expression (ZMod p))
      (message : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))) =>
    toAccess_pullIf_program env g message
  simp only [AddiChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  simp [circuit_norm, hk, Gadgets.Equality.main,
    LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.AddiCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Opcode.ofNat, ConstraintCoe.coe_eq_val,
    hreal, hpc0, hpc1, hpc2, hopA, hopB, hopA0,
    himm0, himm1, himm2, himm3]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem addicols_memory_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hreal : Expression.eval env input.is_real = cols.is_real)
    (hclkHigh : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (hclk0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hclk1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hopA : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (hopB : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (hwrite0 : env.get offset = cols.add_operation.value[0])
    (hwrite1 : env.get (offset + 1) = cols.add_operation.value[1])
    (hwrite2 : env.get (offset + 2) = cols.add_operation.value[2])
    (hwrite3 : env.get (offset + 3) = cols.add_operation.value[3])
    (hprevA : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (hvalueA0 : Expression.eval env input.adapter.op_a_memory.prev_value[0] =
      cols.adapter.op_a_memory.prev_value[0])
    (hvalueA1 : Expression.eval env input.adapter.op_a_memory.prev_value[1] =
      cols.adapter.op_a_memory.prev_value[1])
    (hvalueA2 : Expression.eval env input.adapter.op_a_memory.prev_value[2] =
      cols.adapter.op_a_memory.prev_value[2])
    (hvalueA3 : Expression.eval env input.adapter.op_a_memory.prev_value[3] =
      cols.adapter.op_a_memory.prev_value[3])
    (hprevB : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (hvalueB0 : Expression.eval env input.adapter.op_b_memory.prev_value[0] =
      cols.adapter.op_b_memory.prev_value[0])
    (hvalueB1 : Expression.eval env input.adapter.op_b_memory.prev_value[1] =
      cols.adapter.op_b_memory.prev_value[1])
    (hvalueB2 : Expression.eval env input.adapter.op_b_memory.prev_value[2] =
      cols.adapter.op_b_memory.prev_value[2])
    (hvalueB3 : Expression.eval env input.adapter.op_b_memory.prev_value[3] =
      cols.adapter.op_b_memory.prev_value[3]) :
    List.Perm
      (((((AddiChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult)
      (((Extracted.AddiCols.interactions cols).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Memory)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [AddiChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions,
    toAccess_pushIf_memory, toAccess_pullIf_memory, heq]
  simp [circuit_norm, toAccess_pushIf_memory, toAccess_pullIf_memory,
    Gadgets.Equality.main, LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.AddiCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    hreal, hclkHigh, hclk0, hclk1, hopA, hopB,
    hwrite0, hwrite1, hwrite2, hwrite3, hprevA,
    hvalueA0, hvalueA1, hvalueA2, hvalueA3, hprevB,
    hvalueB0, hvalueB1, hvalueB2, hvalueB3]
  exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_])

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem addicols_byte_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hreal : Expression.eval env input.is_real = cols.is_real)
    (hclk0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hclk1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hwrite0 : env.get offset = cols.add_operation.value[0])
    (hwrite1 : env.get (offset + 1) = cols.add_operation.value[1])
    (hwrite2 : env.get (offset + 2) = cols.add_operation.value[2])
    (hwrite3 : env.get (offset + 3) = cols.add_operation.value[3])
    (hprevA : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (hdiffA : Expression.eval env input.adapter.op_a_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
    (hprevB : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (hdiffB : Expression.eval env input.adapter.op_b_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_b_memory.access_timestamp.diff_low_limb) :
    List.Perm
      ((((AddiChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env))
      (((Extracted.AddiCols.interactions cols).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Byte)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt h
  have hk : ∀ (g : Expression (ZMod p)) (row : ByteRow (Expression (ZMod p))),
      AbstractInteraction.toAccess env ((pulledIf (channel := byteChannel) g row).toRaw) =
        (InteractionKind.Byte, "SP1Byte",
          [(Expression.eval env row.opcode).val, (Expression.eval env row.a).val,
           (Expression.eval env row.b).val, (Expression.eval env row.c).val],
          signedVal (Expression.eval env (-g))) :=
    fun g row => toAccess_pullIf_byte env g row
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [AddiChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, hk, heq]
  simp [circuit_norm, hk, Gadgets.Equality.main,
    Extracted.AddiCols.interactions, Extracted.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    Extracted.Interaction.toAccess_byte, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, ZMod.val_zero, hreal, hclk0, hclk1,
    hwrite0, hwrite1, hwrite2, hwrite3,
    hprevA, hdiffA, hprevB, hdiffB, h6, h3]
  exact
    (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _, _])).append_right
      [_, _, _, _]

set_option maxHeartbeats 2000000 in
private theorem addicols_interactions_faithful_syntactic
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hreal : Expression.eval env input.is_real = cols.is_real)
    (hclkHigh : Expression.eval env input.state.clk_high = cols.state.clk_high)
    (hclk0 : Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hclk1 : Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hpc0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (hpc1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (hpc2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (hopA : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (hopB : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (hopA0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0)
    (himm0 : Expression.eval env input.adapter.op_c_imm[0] = cols.adapter.op_c_imm[0])
    (himm1 : Expression.eval env input.adapter.op_c_imm[1] = cols.adapter.op_c_imm[1])
    (himm2 : Expression.eval env input.adapter.op_c_imm[2] = cols.adapter.op_c_imm[2])
    (himm3 : Expression.eval env input.adapter.op_c_imm[3] = cols.adapter.op_c_imm[3])
    (hwrite0 : env.get offset = cols.add_operation.value[0])
    (hwrite1 : env.get (offset + 1) = cols.add_operation.value[1])
    (hwrite2 : env.get (offset + 2) = cols.add_operation.value[2])
    (hwrite3 : env.get (offset + 3) = cols.add_operation.value[3])
    (hprevA : Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
      cols.adapter.op_a_memory.access_timestamp.prev_low)
    (hdiffA : Expression.eval env input.adapter.op_a_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
    (hvalueA0 : Expression.eval env input.adapter.op_a_memory.prev_value[0] =
      cols.adapter.op_a_memory.prev_value[0])
    (hvalueA1 : Expression.eval env input.adapter.op_a_memory.prev_value[1] =
      cols.adapter.op_a_memory.prev_value[1])
    (hvalueA2 : Expression.eval env input.adapter.op_a_memory.prev_value[2] =
      cols.adapter.op_a_memory.prev_value[2])
    (hvalueA3 : Expression.eval env input.adapter.op_a_memory.prev_value[3] =
      cols.adapter.op_a_memory.prev_value[3])
    (hprevB : Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
      cols.adapter.op_b_memory.access_timestamp.prev_low)
    (hdiffB : Expression.eval env input.adapter.op_b_memory.access_timestamp.diff_low_limb =
      cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
    (hvalueB0 : Expression.eval env input.adapter.op_b_memory.prev_value[0] =
      cols.adapter.op_b_memory.prev_value[0])
    (hvalueB1 : Expression.eval env input.adapter.op_b_memory.prev_value[1] =
      cols.adapter.op_b_memory.prev_value[1])
    (hvalueB2 : Expression.eval env input.adapter.op_b_memory.prev_value[2] =
      cols.adapter.op_b_memory.prev_value[2])
    (hvalueB3 : Expression.eval env input.adapter.op_b_memory.prev_value[3] =
      cols.adapter.op_b_memory.prev_value[3]) :
    List.Perm
      (((((AddiChip.main input).operations offset).interactionsWith stateChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        ((((AddiChip.main input).operations offset).interactionsWith byteChannel.toRaw).map
          (AbstractInteraction.toAccess env)) ++
        (((((AddiChip.main input).operations offset).interactionsWith memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult) ++
        (((((AddiChip.main input).operations offset).interactionsWith programChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult))
      (addiChipOracle.accesses cols) := by
  have hState := addicols_state_interactions_faithful_syntactic env input offset cols
    hreal hclkHigh hclk0 hclk1 hpc0 hpc1 hpc2
  have hProgram := addicols_program_interactions_faithful_syntactic env input offset cols
    hreal hpc0 hpc1 hpc2 hopA hopB hopA0 himm0 himm1 himm2 himm3
  have hProgram' :
      ((((AddiChip.main input).operations offset).interactionsWith
          programChannel.toRaw).map (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult =
        ((Extracted.AddiCols.interactions cols).map
          Extracted.Interaction.toAccess).filter
            (fun access => access.1 = InteractionKind.Program) := by
    rw [hProgram, LookupAccessList.map_negMult_negMult]
  have hMemory := addicols_memory_interactions_faithful_syntactic env input offset cols
    hreal hclkHigh hclk0 hclk1 hopA hopB hwrite0 hwrite1 hwrite2 hwrite3
    hprevA hvalueA0 hvalueA1 hvalueA2 hvalueA3
    hprevB hvalueB0 hvalueB1 hvalueB2 hvalueB3
  have hByte := addicols_byte_interactions_faithful_syntactic env input offset cols
    hreal hclk0 hclk1 hwrite0 hwrite1 hwrite2 hwrite3
    hprevA hdiffA hprevB hdiffB
  refine List.Perm.trans ?_ (LookupAccessList.perm_filter_by_kind _).symm
  rw [hState, hProgram']
  exact ((hByte.append_left _).append hMemory).append_right _

set_option maxHeartbeats 2000000 in
theorem addiChip_interactions_faithful
    (env : Environment (ZMod p)) (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : Extracted.AddiCols (ZMod p))
    (hbind : BindsChipOutput AddiChip.main env input offset cols) :
    List.Perm (nativeAccesses env ((AddiChip.main input).operations offset))
      (addiChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated (AddiChip.elaborated (p := p)) hbind
  rw [AddiChip.directOutput_eq] at hbind
  simp only [ProvableStruct.structEvalLiteralProc, eval_extractedAddOperation] at hbind
  subst cols
  simp only [nativeAccesses]
  have hunexpected :
      unexpectedInteractions ((AddiChip.main input).operations offset) = [] := by
    simp [unexpectedInteractions, AddiChip.main,
      Readers.CPUState.circuit, Readers.CPUState.main,
      Readers.ITypeReader.circuit, Readers.ITypeReader.main,
      Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
      Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
      Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
      AddOperation.circuit, AddOperation.main, Gadgets.Equality.main,
      FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  rw [hunexpected]
  simp only [List.map_nil, List.append_nil]
  apply addicols_interactions_faithful_syntactic
  all_goals
    simp only [eval_cpuState, Readers.ITypeReader.eval_cols,
      eval_registerAccessCols, eval_registerAccessTimestamp,
      ProvableType.eval_field,
      ← ProvableType.getElem_eval_fields, Vector.getElem_mapRange,
      Expression.eval, Nat.add_zero]

set_option maxHeartbeats 2000000 in
theorem addiChip_interactions_constructive
    (rustCols : Extracted.AddiCols (ZMod p)) (data : ProverData (ZMod p)) :
    let assignment := addiChipRowCodec.assignment
      (addiChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨AddiChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (addiChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := addiChipOracle.deconfigure rustCols
  let assignment := addiChipRowCodec.assignment cols data
  have hbind : BindsChipOutput AddiChip.main assignment.environment
      (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
      (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [AddiChip.circuit_main_eq] at h
    exact h
  have hlegacy := addiChip_interactions_faithful (p := p) assignment.environment
    (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowInputVar
    (⟨AddiChip.circuit (p := p)⟩ : Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations (AddiChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk, Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk, AddiChip.circuit_main_eq] using hlegacy

theorem addiChip_faithful :
    ChipFaithful (p := p) AddiChip.Inputs Extracted.AddiCols Extracted.AddiCols
      AddiChip.circuit addiChipRowCodec addiChipOracle where
  constraints := addiChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (addiChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
