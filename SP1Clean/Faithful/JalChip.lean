import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Jal
import SP1Clean.Proofs.Chips.JalChip.Formal

/-! # Whole-chip faithfulness — native Jal row ↔ pinned SP1 Rust AIR

`jalChip_faithful` compares the complete native Clean JAL circuit with the
v6.4.0 Rust `JalOracle.JalColumns` assertion system and interaction multiset
(after one explicit row reconfiguration) on real, `jal x0`, and padding rows.
Rust redundantly zeroes the first three link limbs at chip level in addition to
the J-type adapter's four-limb zeroing; the assertion proof preserves that
redundancy on the oracle side and proves it propositionally equivalent to the
native composition.

The row codec preserves the Rust column layout as an input prefix followed by
the four jump-target limbs and four link-address limbs.  State, Byte, Memory,
and Program accesses are compared at the complete chip boundary.  The Byte
comparison is a permutation because the native subcircuit order places CPU
checks first and alignment last, while the Rust AIR emits alignment before
the CPU and destination-timestamp checks.

Heartbeat budget: all six declared ceilings here were ~25× over and were measured away (every
floor ≤40000), so this file now runs entirely on the plain default.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Whole-chip row reconfiguration. The reader blocks are already the canonical generated substrate,
so only the native arithmetic blocks are copied into Rust's chip-private operation rows. This is not
an operation-level faithfulness claim. -/
def jalChipReconfigure {F : Type} (cols : JalChip.Columns F) :
    Extracted.JalOracle.JalColumns F :=
  { state := cols.state
    adapter := cols.adapter
    add_operation := { value := cols.add_operation.value }
    op_a_operation := { value := cols.op_a_operation.value }
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def jalChipDeconfigure {F : Type} (cols : Extracted.JalOracle.JalColumns F) :
    JalChip.Columns F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    add_operation := { value := cols.add_operation.value }
    op_a_operation := { value := cols.op_a_operation.value } }

/-- SP1 Rust's complete Jal-chip oracle, viewed from the native Lean row. -/
def jalChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F JalChip.Columns Extracted.JalOracle.JalColumns where
  reconfigure := jalChipReconfigure
  deconfigure := jalChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.JalOracle.JalColumns.asserts
  interactions := Extracted.JalOracle.JalColumns.interactions

def jalChipInput {F : Type}
    (cols : JalChip.Columns F) : JalChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

def jalChipLocals {F : Type}
    (cols : JalChip.Columns F) : Vector F 8 :=
  #v[cols.add_operation.value[0], cols.add_operation.value[1],
    cols.add_operation.value[2], cols.add_operation.value[3],
    cols.op_a_operation.value[0], cols.op_a_operation.value[1],
    cols.op_a_operation.value[2], cols.op_a_operation.value[3]]

def jalChipPhysicalRow {F : Type}
    (cols : JalChip.Columns F) : Array F :=
  inputFirstRow (jalChipInput cols) (jalChipLocals cols)

def jalChipColumnsOfInput {F : Type}
    (input : JalChip.Inputs F) (locals : Vector F 8) :
    JalChip.Columns F :=
  ⟨input.is_real, input.state, input.adapter,
    ⟨#v[locals[0], locals[1], locals[2], locals[3]]⟩,
    ⟨#v[locals[4], locals[5], locals[6], locals[7]]⟩⟩

private theorem vec3_eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem vec4_eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

@[circuit_norm] private theorem evalAddOperation
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.JalOracle.AddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.JalOracle.AddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem evalAddOperationColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : AddOperation.Columns (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        AddOperation.Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem jalChipColumnsOfInput_roundtrip {F : Type}
    (cols : JalChip.Columns F) :
    jalChipColumnsOfInput (jalChipInput cols) (jalChipLocals cols) = cols := by
  cases cols
  simp [jalChipColumnsOfInput, jalChipInput, jalChipLocals, vec4_eta]

theorem eval_jalChipDirectOutput
    (input : JalChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 8)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((JalChip.elaborated (p := p)).output
          (varFromOffset JalChip.Inputs 0) (size JalChip.Inputs)) =
      jalChipColumnsOfInput input locals := by
  rw [JalChip.directOutput_eq]
  rw [← CircuitType.eval_expression, JalChip.eval_columns]
  unfold jalChipColumnsOfInput
  rw [JalChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [JalChip.eval_inputs, JalChip.Inputs.mk.injEq] at hinputEval
  refine ⟨hinputEval.1, hinputEval.2.1, hinputEval.2.2, ?_, ?_⟩
  · rw [evalAddOperationColumns, AddOperation.Columns.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 4 fun i =>
        var { index := size JalChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using
        (eval_local_inputFirstRow input locals data 0 (by decide))
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
    · exact eval_local_inputFirstRow input locals data 3 (by decide)
  · rw [evalAddOperationColumns, AddOperation.Columns.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 4 fun i =>
        var { index := size JalChip.Inputs + 4 + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using
        (eval_local_inputFirstRow input locals data 4 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 5 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 6 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 7 (by decide))

def jalChipRowCodec :
    ChipRowCodec JalChip.Inputs JalChip.Columns
      (JalChip.circuit (p := p)) where
  assignment cols data := {
    row := jalChipPhysicalRow cols
    input := jalChipInput cols
    width_eq := by
      rw [jalChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, JalChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (JalChip.circuit (p := p))
      (jalChipInput cols) (jalChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((JalChip.main _).output _) = _
      rw [JalChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_jalChipDirectOutput (p := p) (jalChipInput cols)
        (jalChipLocals cols) data).trans
          (jalChipColumnsOfInput_roundtrip cols) }

theorem jalChip_lookups_empty :
    (⟨JalChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    JalChip.circuit_main_eq]
  simp [JalChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.JTypeReader.circuit,
    Readers.JTypeReader.main, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, AddOperation.circuit,
    AddOperation.main, Gadgets.Equality.main, circuit_norm]

private def pcWord (input : Var JalChip.Inputs (ZMod p)) :
    Word (Expression (ZMod p)) :=
  #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]

private def jumpValue (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

private def linkValue (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 4 + i }

private theorem cpuCircuitMain :
    (Readers.CPUState.circuit (p := p)).main =
      Readers.CPUState.main := rfl

private theorem cpuCircuitLocalLength
    (input : Var Readers.CPUState.Inputs (ZMod p)) :
    (Readers.CPUState.circuit (p := p)).localLength input = 0 := rfl

private theorem addCircuitMain :
    (AddOperation.circuit (p := p)).main =
      AddOperation.main := rfl

private theorem jTypeCircuitMain :
    (Readers.JTypeReader.circuit (p := p)).main =
      Readers.JTypeReader.main := rfl

private theorem jTypeCircuitLocalLength
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) :
    (Readers.JTypeReader.circuit (p := p)).localLength input = 0 := rfl

private theorem registerWriteCircuitMain :
    (Readers.RegisterWrite.circuit (p := p)).main =
      Readers.RegisterWrite.main := rfl

private theorem registerWriteCircuitLocalLength
    (input : Var Readers.RegisterWrite.Inputs (ZMod p)) :
    (Readers.RegisterWrite.circuit (p := p)).localLength input = 0 := rfl

private theorem forallNilIff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem varFields4 (offset : ℕ) :
    (varFromOffset (fields 4) offset :
      Vector (Expression (ZMod p)) 4) =
      Vector.mapRange 4 fun i => var { index := offset + i } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem addAssertions
    (env : Environment (ZMod p))
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b value : Word (ZMod p)) (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hv : (ProvableStruct.eval env input.cols).value = value)
    (hr : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.JalOracle.AddOperation.asserts (F := ZMod p)
          a b { value := value } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((AddOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, AddOperation.main,
    Extracted.JalOracle.AddOperation.asserts, circuit_norm]
  rw [ha, hb, hv, hr]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityMappedAssertions
    (env : Environment (ZMod p)) (x y : Expression (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (List.map (Expression.eval env)
          (Operations.constraints
            ((Gadgets.Equality.main (M := field)
              (x, y)).operations offset))) ↔
      Expression.eval env x = Expression.eval env y :=
  CanonicalReader.equalityAssertions env x y offset

private def nativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        ⟨input.state,
          #v[(jumpValue offset)[0], (jumpValue offset)[1],
            (jumpValue offset)[2]],
          8, input.is_real⟩).operations (offset + 8)))

private def nativeJumpAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddOperation.main
        ⟨pcWord input, input.adapter.op_b_imm,
          { value := jumpValue offset }, input.is_real⟩).operations
            (offset + 8)))

private def nativeLinkAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddOperation.main
        ⟨pcWord input, #v[4, 0, 0, 0],
          { value := linkValue offset },
          input.is_real - input.adapter.op_a_0⟩).operations
            (offset + 8)))

private def nativeJTypeMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.JTypeReader.main
        ⟨input.adapter, input.is_real, input.is_real,
          input.state.clk_high,
          input.state.clk_0_16 + input.state.clk_16_24 * 65536,
          input.state.pc, 46,
          (linkValue offset)[0], (linkValue offset)[1],
          (linkValue offset)[2], (linkValue offset)[3]⟩).operations
            (offset + 8)))

private def nativeWriteMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.RegisterWrite.main
        ⟨input.state.clk_high,
          input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
          input.adapter.op_a, linkValue offset,
          input.is_real⟩).operations (offset + 8)))

private def nativeMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  nativeCpuMeaning env input offset ∧
    nativeJumpAddMeaning env input offset ∧
    Expression.eval env ((jumpValue offset)[3]) = 0 ∧
    nativeLinkAddMeaning env input offset ∧
    Expression.eval env ((linkValue offset)[3]) = 0 ∧
    nativeJTypeMeaning env input offset ∧
    nativeWriteMeaning env input offset ∧
    Expression.eval env
      ((input.is_real - 1) * input.adapter.op_a_0) = 0 ∧
    Expression.eval env
      (input.is_real * (input.is_real - 1)) = 0

private theorem nativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalChip.main input).operations offset)) ↔
      nativeMeaning env input offset := by
  unfold nativeMeaning nativeCpuMeaning nativeJumpAddMeaning
    nativeLinkAddMeaning nativeJTypeMeaning nativeWriteMeaning
  simp only [nativeAssertZeros, JalChip.main,
    Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, subcircuitWithAssertion, assertion,
    assertZero, HasAssertEq.assert_eq, Expression.assertEquals,
    Channel.pullIf, Operations.localLength]
  simp only [Operations.constraints_append,
    Operations.constraints_witness,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_generalFormalCircuit,
    constraints_toSubcircuit_formalAssertion,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    cpuCircuitLocalLength, AddOperation.circuit_localLength,
    jTypeCircuitLocalLength,
    Gadgets.Equality.localLength_eq,
    Operations.constraints_assert,
    Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil,
    List.forall_append, List.forall_cons]
  simp only [pcWord, jumpValue, linkValue, cpuCircuitMain,
    addCircuitMain, jTypeCircuitMain, registerWriteCircuitMain,
    varFields4, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd,
    Vector.getElem_mapRange, Gadgets.Equality.circuit, forallNilIff]
  repeat' rw [equalityMappedAssertions]
  simp only [Operations.constraints_interact, Operations.constraints_nil,
    List.map_nil, forallNilIff, true_and, and_true,
    Expression.eval, eval_sub]

@[circuit_norm] private theorem evalJTypeReader
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.JTypeReader (Expression F)) :
    Eval.eval env cols =
      ({ op_a := Eval.eval env cols.op_a
         op_a_memory := Eval.eval env cols.op_a_memory
         op_a_0 := Eval.eval env cols.op_a_0
         op_b_imm := Eval.eval env cols.op_b_imm
         op_c_imm := Eval.eval env cols.op_c_imm } :
        Extracted.JTypeReader F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem evalVec4Literal {F : Type} [FiniteField F]
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

private def rustColumns
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    JalChip.Columns (ZMod p) :=
  { is_real := Expression.eval env input.is_real
    state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    add_operation := Eval.eval env
      ({ value := jumpValue offset } :
        AddOperation.Columns (Expression (ZMod p)))
    op_a_operation := Eval.eval env
      ({ value := linkValue offset } :
        AddOperation.Columns (Expression (ZMod p))) }

private def rustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      (Eval.eval env input.state)
      #v[(Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[0],
        (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[1],
        (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[2]]
      8 (Expression.eval env input.is_real))

private def rustJumpAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.JalOracle.AddOperation.asserts (F := ZMod p)
      #v[(Eval.eval env input.state).pc[0],
        (Eval.eval env input.state).pc[1],
        (Eval.eval env input.state).pc[2], 0]
      #v[(Eval.eval env input.adapter).op_b_imm[0],
        (Eval.eval env input.adapter).op_b_imm[1],
        (Eval.eval env input.adapter).op_b_imm[2],
        (Eval.eval env input.adapter).op_b_imm[3]]
      (Eval.eval env
        ({ value := jumpValue offset } :
          Extracted.JalOracle.AddOperation (Expression (ZMod p))))
      (Expression.eval env input.is_real))

private def rustLinkAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.JalOracle.AddOperation.asserts (F := ZMod p)
      #v[(Eval.eval env input.state).pc[0],
        (Eval.eval env input.state).pc[1],
        (Eval.eval env input.state).pc[2], 0]
      #v[4, 0, 0, 0]
      (Eval.eval env
        ({ value := linkValue offset } :
          Extracted.JalOracle.AddOperation (Expression (ZMod p))))
      (Expression.eval env input.is_real -
        (Eval.eval env input.adapter).op_a_0))

private def rustJTypeMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let adapter := Eval.eval env input.adapter
  let value := (Eval.eval env
    ({ value := linkValue offset } :
      Extracted.JalOracle.AddOperation (Expression (ZMod p)))).value
  List.Forall (· = 0)
      (Extracted.JTypeReader.asserts (F := ZMod p)
        (Eval.eval env input.state).clk_high
        ((Eval.eval env input.state).clk_0_16 +
          (Eval.eval env input.state).clk_16_24 * 65536)
        (Eval.eval env input.state).pc 46 value adapter
        (Expression.eval env input.is_real)
        (Expression.eval env input.is_real)) ∧
    adapter.op_a_0 * value[0] = 0 ∧
    adapter.op_a_0 * value[1] = 0 ∧
    adapter.op_a_0 * value[2] = 0

private def rustMeaning
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := rustColumns env input offset
  rustCpuMeaning env input offset ∧
    rustJumpAddMeaning env input offset ∧
    cols.add_operation.value[3] = 0 ∧
    rustLinkAddMeaning env input offset ∧
    cols.op_a_operation.value[3] = 0 ∧
    rustJTypeMeaning env input offset ∧
    True ∧
    (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
    cols.is_real * (cols.is_real - 1) = 0

omit [Fact (2 ^ 17 < p)] in
private theorem rustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (jalChipOracle.nativeAssertZeros
          (rustColumns env input offset)) ↔
      rustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, jalChipOracle,
    jalChipReconfigure]
  rw [Extracted.JalOracle.JalColumns.asserts]
  unfold rustMeaning rustCpuMeaning rustJumpAddMeaning
    rustLinkAddMeaning rustJTypeMeaning
  dsimp only [rustColumns]
  simp only [Extracted.CPUState.asserts,
    Extracted.JTypeReader.asserts, List.forall_append, List.Forall,
    evalAddOperation, evalAddOperationColumns, vec4_eta, sub_zero, true_and]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem cpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    rustCpuMeaning env input offset ↔
      nativeCpuMeaning env input offset := by
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[(jumpValue offset)[0], (jumpValue offset)[1],
        (jumpValue offset)[2]],
      8, input.is_real⟩
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[(Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[0],
      (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[1],
      (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[2]]
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput (offset + 8)
    (Eval.eval env input.state) rustNextPc 8
    (Expression.eval env input.is_real) (by
      simp only [cpuInput, ProvableStruct.structEvalLiteralProc])
  dsimp only [cpuInput, rustNextPc] at hCpu
  unfold rustCpuMeaning nativeCpuMeaning
  exact hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem jumpAddMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    rustJumpAddMeaning env input offset ↔
      nativeJumpAddMeaning env input offset := by
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨pcWord input, input.adapter.op_b_imm,
      { value := jumpValue offset }, input.is_real⟩
  let rustA : Word (ZMod p) :=
    #v[(Eval.eval env input.state).pc[0],
      (Eval.eval env input.state).pc[1],
      (Eval.eval env input.state).pc[2], 0]
  let rustB : Word (ZMod p) :=
    #v[(Eval.eval env input.adapter).op_b_imm[0],
      (Eval.eval env input.adapter).op_b_imm[1],
      (Eval.eval env input.adapter).op_b_imm[2],
      (Eval.eval env input.adapter).op_b_imm[3]]
  let rustValue : Extracted.JalOracle.AddOperation (ZMod p) :=
    Eval.eval env
      ({ value := jumpValue offset } :
        Extracted.JalOracle.AddOperation (Expression (ZMod p)))
  have hAdd := addAssertions (p := p) env addInput (offset + 8)
    rustA rustB rustValue.value (Expression.eval env input.is_real)
    (by
      simp only [addInput, rustA, pcWord,
        ProvableStruct.structEvalLiteralProc]
      rw [evalVec4Literal, eval_cpuState]
      simp only [← ProvableType.getElem_eval_fields, Expression.eval])
    (by
      simp only [addInput, rustB,
        ProvableStruct.structEvalLiteralProc]
      rw [evalJTypeReader]
      exact (vec4_eta _).symm)
    (by
      simp only [addInput, rustValue,
        ProvableStruct.structEvalLiteralProc]
      rw [evalAddOperation])
    (by simp only [addInput,
      ProvableStruct.structEvalLiteralProc])
  dsimp only [addInput, rustA, rustB, rustValue,
    pcWord, jumpValue] at hAdd
  unfold rustJumpAddMeaning nativeJumpAddMeaning
  exact hAdd

omit [Fact (2 ^ 17 < p)] in
private theorem linkAddMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    rustLinkAddMeaning env input offset ↔
      nativeLinkAddMeaning env input offset := by
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨pcWord input, #v[4, 0, 0, 0],
      { value := linkValue offset },
      input.is_real - input.adapter.op_a_0⟩
  let rustA : Word (ZMod p) :=
    #v[(Eval.eval env input.state).pc[0],
      (Eval.eval env input.state).pc[1],
      (Eval.eval env input.state).pc[2], 0]
  let rustValue : Extracted.JalOracle.AddOperation (ZMod p) :=
    Eval.eval env
      ({ value := linkValue offset } :
        Extracted.JalOracle.AddOperation (Expression (ZMod p)))
  let rustGate : ZMod p :=
    Expression.eval env input.is_real -
      (Eval.eval env input.adapter).op_a_0
  have hAdd := addAssertions (p := p) env addInput (offset + 8)
    rustA #v[4, 0, 0, 0] rustValue.value rustGate
    (by
      simp only [addInput, rustA, pcWord,
        ProvableStruct.structEvalLiteralProc]
      rw [evalVec4Literal, eval_cpuState]
      simp only [← ProvableType.getElem_eval_fields, Expression.eval])
    (by
      simp only [addInput, ProvableStruct.structEvalLiteralProc]
      rw [evalVec4Literal]
      rfl)
    (by
      simp only [addInput, rustValue,
        ProvableStruct.structEvalLiteralProc]
      rw [evalAddOperation])
    (by
      simp only [addInput, rustGate,
        ProvableStruct.structEvalLiteralProc]
      rw [eval_sub, evalJTypeReader]
      simp only [ProvableType.eval_field])
  dsimp only [addInput, rustA, rustValue, rustGate,
    pcWord, linkValue] at hAdd
  unfold rustLinkAddMeaning nativeLinkAddMeaning
  exact hAdd

private theorem jTypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    rustJTypeMeaning env input offset ↔
      nativeJTypeMeaning env input offset := by
  let value : Word (Expression (ZMod p)) := linkValue offset
  let readerInput : Var Readers.JTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real,
      input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 46, value[0], value[1], value[2], value[3]⟩
  let rustValue : Word (ZMod p) :=
    (Eval.eval env
      ({ value := value } :
        Extracted.JalOracle.AddOperation (Expression (ZMod p)))).value
  have hRustValue : rustValue = Eval.eval env value := by
    simp only [rustValue]
    rw [evalAddOperation]
  have hopA0 :
      Expression.eval env input.adapter.op_a_0 =
        (Eval.eval env input.adapter).op_a_0 := by
    rw [evalJTypeReader]
    simp only [ProvableType.eval_field]
  have hJType := CanonicalReader.jTypeAssertions
    (p := p) env readerInput (offset + 8)
    (Eval.eval env input.state).clk_high
    ((Eval.eval env input.state).clk_0_16 +
      (Eval.eval env input.state).clk_16_24 * 65536)
    46 (Expression.eval env input.is_real)
    (Expression.eval env input.is_real)
    (Eval.eval env input.state).pc rustValue
    (Eval.eval env input.adapter)
    (by simp only [readerInput,
      ProvableStruct.structEvalLiteralProc])
    (by simp only [readerInput,
      ProvableStruct.structEvalLiteralProc])
    (by simpa only [readerInput] using hopA0)
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 0 (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 1 (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 2 (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 3 (by decide)))
    rfl
  unfold rustJTypeMeaning nativeJTypeMeaning
  dsimp only
  rw [hJType]
  constructor
  · exact And.left
  · intro hNative
    refine ⟨hNative, ?_⟩
    have hRust := hJType.mpr hNative
    rw [Extracted.JTypeReader.asserts] at hRust
    simp only [List.Forall, sub_zero] at hRust
    exact ⟨hRust.2.1, hRust.2.2.1, hRust.2.2.2.1⟩

omit [Fact (2 ^ 17 < p)] in
private theorem writeMeaningTrue
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    nativeWriteMeaning env input offset ↔ True := by
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, linkValue offset, input.is_real⟩
  have hWrite := CanonicalReader.registerWriteAssertions
    env writeInput (offset + 8)
  dsimp only [writeInput, linkValue] at hWrite
  unfold nativeWriteMeaning
  exact hWrite

private theorem rustMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    rustMeaning env input offset ↔
      nativeMeaning env input offset := by
  unfold rustMeaning nativeMeaning
  rw [cpuMeaningFaithful, jumpAddMeaningFaithful,
    linkAddMeaningFaithful, jTypeMeaningFaithful,
    writeMeaningTrue]
  dsimp only [rustColumns]
  simp only [evalAddOperationColumns, evalJTypeReader,
    ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, eval_sub, Expression.eval,
    true_and]

private theorem constraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (jalChipOracle.nativeAssertZeros
          (rustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalChip.main input).operations offset)) :=
  (rustAssertionsDecompose (p := p) env input offset).trans
    ((rustMeaningFaithful (p := p) env input offset).trans
      (nativeConstraintsDecompose (p := p) env input offset).symm)

theorem jalChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : JalChip.Columns (ZMod p))
    (hbind : BindsChipOutput JalChip.main env input offset cols) :
    List.Forall (· = 0)
        (jalChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (JalChip.elaborated (p := p)) hbind
  rw [JalChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    JalChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change rustColumns env input offset = cols at hbind
  rw [← hbind]
  exact constraintsFaithfulOutput (p := p) env input offset

theorem jalChipConstraintsConstructive
    (rustCols : Extracted.JalOracle.JalColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := jalChipRowCodec.assignment
      (jalChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (jalChipOracle.assertZeros rustCols) ↔
      (⟨JalChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := jalChipOracle.deconfigure rustCols
  let assignment := jalChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput JalChip.main assignment.environment
        (⟨JalChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨JalChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [JalChip.circuit_main_eq] at h
    exact h
  have hfaithful := jalChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨JalChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨JalChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (jalChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨JalChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      JalChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (JalChip.circuit (p := p))
      assignment.environment jalChip_lookups_empty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private theorem stateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    (((JalChip.exposedStateInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      (((Extracted.JalOracle.JalColumns.interactions
          (jalChipReconfigure (rustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.State)) := by
  have hStatePull :
      ∀ (gate : Expression (ZMod p))
        (msg : Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((stateChannel (p := p)).pulledIf gate msg).toRaw) =
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
        (msg : Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((stateChannel (p := p)).pushedIf mult msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_state env mult msg
  simp only [JalChip.exposedStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [jalChipReconfigure, Extracted.JalOracle.JalColumns.interactions,
    Extracted.JalOracle.AddOperation.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    rustColumns, jumpValue, eval_cpuState, evalJTypeReader,
    evalAddOperationColumns, ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field, Expression.eval]

private theorem permFourBlocks {α : Type}
    (a b c d : List α) :
    List.Perm (a ++ b ++ c ++ d) (b ++ d ++ a ++ c) := by
  have hab : List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ c ++ d) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right (c ++ d)
  have htail : List.Perm (b ++ a ++ c ++ d)
      (b ++ d ++ a ++ c) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a ++ c) (l₂ := d)).append_left b
  exact hab.trans htail

private theorem byteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((JalChip.exposedByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))
      (((Extracted.JalOracle.JalColumns.interactions
          (jalChipReconfigure (rustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have h3 : (3 : ZMod p).val = 3 := val_3_zmod_p
  have hBytePull :
      ∀ (gate : Expression (ZMod p))
        (msg : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((byteChannel (p := p)).pulledIf gate msg).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env msg.opcode).val,
             (Expression.eval env msg.a).val,
             (Expression.eval env msg.b).val,
             (Expression.eval env msg.c).val],
            signedVal (Expression.eval env (-gate))) :=
    fun gate msg => toAccess_pullIf_byte env gate msg
  simp only [JalChip.exposedByteInteractions,
    List.map_cons, List.map_nil, hBytePull]
  simp [jalChipReconfigure, Extracted.JalOracle.JalColumns.interactions,
    Extracted.JalOracle.AddOperation.interactions,
    rustColumns, jumpValue, linkValue,
    eval_cpuState, evalJTypeReader, evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, h6, h3,
    Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Nat.add_assoc]
  simp only [← ProvableStruct.eval_eq_eval,
    JalChip.eval_inputs, eval_cpuState, evalJTypeReader,
    eval_registerAccessCols,
    eval_registerAccessTimestamp, ProvableType.eval_field,
    Expression.eval, eval_sub, neg_sub]
  exact permFourBlocks
    [_, _] [_, _, _, _, _, _, _, _] [_, _] [_]

private theorem memoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((JalChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.JalOracle.JalColumns.interactions
          (jalChipReconfigure (rustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Memory)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p))
        (msg : Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((memoryChannel (p := p)).pulledIf gate msg).toRaw) =
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
        (msg : Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((memoryChannel (p := p)).pushedIf mult msg).toRaw) =
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
  simp only [JalChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [jalChipReconfigure, Extracted.JalOracle.JalColumns.interactions,
    Extracted.JalOracle.AddOperation.interactions,
    rustColumns, jumpValue, linkValue,
    eval_cpuState, evalJTypeReader, evalAddOperationColumns,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Nat.add_assoc]

private theorem programInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((JalChip.exposedProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.JalOracle.JalColumns.interactions
          (jalChipReconfigure (rustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have h46 : (46 : ZMod p).val = 46 := by
    have h : (46 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      omega
    exact ZMod.val_natCast_of_lt h
  have hProgramPull :
      ∀ (gate : Expression (ZMod p))
        (msg : Channels.ProgramMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            (((programChannel (p := p)).pulledIf gate msg).toRaw) =
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
  simp only [JalChip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [jalChipReconfigure, Extracted.JalOracle.JalColumns.interactions,
    Extracted.JalOracle.AddOperation.interactions,
    rustColumns, eval_cpuState, evalJTypeReader,
    evalAddOperationColumns, ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, Expression.eval,
    LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Opcode.ofNat, h46]

private theorem unexpectedInteractionsEmpty
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((JalChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((JalChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (JalChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [JalChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem jalChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : JalChip.Columns (ZMod p))
    (hbind : BindsChipOutput JalChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((JalChip.main input).operations offset))
      (jalChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (JalChip.elaborated (p := p)) hbind
  rw [JalChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    JalChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change rustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.JalOracle.JalColumns.interactions
      (jalChipReconfigure (rustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [unexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, jalChipOracle]
  rw [JalChip.interactionsWith_state_eq,
    JalChip.interactionsWith_byte_eq,
    JalChip.interactionsWith_memory_eq,
    JalChip.interactionsWith_program_eq]
  have hState :=
    stateInteractionsFaithful (p := p) env input offset
  have hByte :=
    byteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    memoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    programInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind
      rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hMemory, hProgram]
  simpa only [List.append_assoc] using
    (hByte.append_left _).append_right _

theorem jalChipInteractionsConstructive
    (rustCols : Extracted.JalOracle.JalColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := jalChipRowCodec.assignment
      (jalChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨JalChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (jalChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := jalChipOracle.deconfigure rustCols
  let assignment := jalChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput JalChip.main assignment.environment
        (⟨JalChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨JalChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [JalChip.circuit_main_eq] at h
    exact h
  have hfaithful := jalChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨JalChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨JalChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (JalChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    JalChip.circuit_main_eq] using hfaithful

theorem jalChip_faithful :
    ChipFaithful (p := p) JalChip.Inputs
      JalChip.Columns Extracted.JalOracle.JalColumns
      JalChip.circuit jalChipRowCodec jalChipOracle where
  constraints := jalChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (jalChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
