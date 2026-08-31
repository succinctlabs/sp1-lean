import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.Jalr
import SP1Clean.Proofs.Chips.JalrChip.Formal

/-! # Whole-chip faithfulness — native Jalr row ↔ pinned SP1 Rust AIR

`jalrChip_faithful` compares the complete native Clean JALR circuit with the
v6.4.0 Rust `JalrOracle.JalrColumns` assertion system and interaction multiset
(after one explicit row reconfiguration) on real, `jalr x0`, and padding rows.
Rust redundantly zeroes the first three link limbs at chip level in addition to
the I-type adapter's four-limb zeroing; the assertion proof preserves that
redundancy on the oracle side and proves it propositionally equivalent to the
native composition.

The row codec preserves the Rust column layout as an input prefix followed by
the four jump-target limbs, four link-address limbs, and the cleared low-bit
witness. State, Byte, Memory,
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
def jalrChipReconfigure {F : Type} (cols : JalrChip.Columns F) :
    Extracted.JalrOracle.JalrColumns F :=
  { state := cols.state
    adapter := cols.adapter
    is_real := cols.is_real
    add_operation := { value := cols.add_operation.value }
    op_a_operation := { value := cols.op_a_operation.value }
    lsb := cols.lsb }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def jalrChipDeconfigure {F : Type} (cols : Extracted.JalrOracle.JalrColumns F) :
    JalrChip.Columns F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    add_operation := { value := cols.add_operation.value }
    op_a_operation := { value := cols.op_a_operation.value }
    lsb := cols.lsb }

/-- SP1 Rust's complete Jalr-chip oracle, viewed from the native Lean row. -/
def jalrChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F JalrChip.Columns Extracted.JalrOracle.JalrColumns where
  reconfigure := jalrChipReconfigure
  deconfigure := jalrChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.JalrOracle.JalrColumns.asserts
  interactions := Extracted.JalrOracle.JalrColumns.interactions

def jalrChipInput {F : Type}
    (cols : JalrChip.Columns F) : JalrChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter }

def jalrChipLocals {F : Type}
    (cols : JalrChip.Columns F) : Vector F 9 :=
  #v[cols.add_operation.value[0], cols.add_operation.value[1],
    cols.add_operation.value[2], cols.add_operation.value[3],
    cols.op_a_operation.value[0], cols.op_a_operation.value[1],
    cols.op_a_operation.value[2], cols.op_a_operation.value[3],
    cols.lsb]

def jalrChipPhysicalRow {F : Type}
    (cols : JalrChip.Columns F) : Array F :=
  inputFirstRow (jalrChipInput cols) (jalrChipLocals cols)

def jalrChipColumnsOfInput {F : Type}
    (input : JalrChip.Inputs F) (locals : Vector F 9) :
    JalrChip.Columns F :=
  ⟨input.is_real, input.state, input.adapter,
    ⟨#v[locals[0], locals[1], locals[2], locals[3]]⟩,
    ⟨#v[locals[4], locals[5], locals[6], locals[7]]⟩,
    locals[8]⟩

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
    (cols : Extracted.JalrOracle.AddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.JalrOracle.AddOperation F) := by
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

theorem jalrChipColumnsOfInput_roundtrip {F : Type}
    (cols : JalrChip.Columns F) :
    jalrChipColumnsOfInput (jalrChipInput cols) (jalrChipLocals cols) = cols := by
  cases cols
  simp [jalrChipColumnsOfInput, jalrChipInput, jalrChipLocals, vec4_eta]

theorem eval_jalrChipDirectOutput
    (input : JalrChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 9)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((JalrChip.elaborated (p := p)).output
          (varFromOffset JalrChip.Inputs 0) (size JalrChip.Inputs)) =
      jalrChipColumnsOfInput input locals := by
  rw [JalrChip.directOutput_eq]
  rw [← CircuitType.eval_expression, JalrChip.eval_columns]
  unfold jalrChipColumnsOfInput
  rw [JalrChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [JalrChip.eval_inputs, JalrChip.Inputs.mk.injEq] at hinputEval
  refine ⟨hinputEval.1, hinputEval.2.1, hinputEval.2.2, ?_, ?_, ?_⟩
  · rw [evalAddOperationColumns, AddOperation.Columns.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 4 fun i =>
        var { index := size JalrChip.Inputs + i }) i hi]
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
        var { index := size JalrChip.Inputs + 4 + i }) i hi]
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
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size JalrChip.Inputs + 8 })).trans
        (eval_local_inputFirstRow input locals data 8 (by decide))

def jalrChipRowCodec :
    ChipRowCodec JalrChip.Inputs JalrChip.Columns
      (JalrChip.circuit (p := p)) where
  assignment cols data := {
    row := jalrChipPhysicalRow cols
    input := jalrChipInput cols
    width_eq := by
      rw [jalrChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, JalrChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (JalrChip.circuit (p := p))
      (jalrChipInput cols) (jalrChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((JalrChip.main _).output _) = _
      rw [JalrChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_jalrChipDirectOutput (p := p) (jalrChipInput cols)
        (jalrChipLocals cols) data).trans
          (jalrChipColumnsOfInput_roundtrip cols) }

theorem jalrChip_lookups_empty :
    (⟨JalrChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    JalrChip.circuit_main_eq]
  simp [JalrChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.ITypeReader.circuit,
    Readers.ITypeReader.main, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, AddOperation.circuit,
    AddOperation.main, Gadgets.Equality.main, circuit_norm]

private def pcWord (input : Var JalrChip.Inputs (ZMod p)) :
    Word (Expression (ZMod p)) :=
  #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0]

private def jumpValue (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

private def linkValue (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 4 + i }

private def lsbValue (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 8 }

private theorem cpuCircuitMain :
    (Readers.CPUState.circuit (p := p)).main =
      Readers.CPUState.main := rfl

private theorem cpuCircuitLocalLength
    (input : Var Readers.CPUState.Inputs (ZMod p)) :
    (Readers.CPUState.circuit (p := p)).localLength input = 0 := rfl

private theorem addCircuitMain :
    (AddOperation.circuit (p := p)).main =
      AddOperation.main := rfl

private theorem iTypeCircuitMain :
    (Readers.ITypeReader.circuit (p := p)).main =
      Readers.ITypeReader.main := rfl

private theorem iTypeCircuitLocalLength
    (input : Var Readers.ITypeReader.Inputs (ZMod p)) :
    (Readers.ITypeReader.circuit (p := p)).localLength input = 0 := rfl

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
        (Extracted.JalrOracle.AddOperation.asserts (F := ZMod p)
          a b { value := value } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((AddOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, AddOperation.main,
    Extracted.JalrOracle.AddOperation.asserts, circuit_norm]
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
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        ⟨input.state,
          #v[(jumpValue offset)[0] - lsbValue offset, (jumpValue offset)[1],
            (jumpValue offset)[2]],
          8, input.is_real⟩).operations (offset + 9)))

private def nativeJumpAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddOperation.main
        ⟨#v[input.adapter.op_b_memory.prev_value[0],
            input.adapter.op_b_memory.prev_value[1],
            input.adapter.op_b_memory.prev_value[2],
            input.adapter.op_b_memory.prev_value[3]],
          input.adapter.op_c_imm,
          { value := jumpValue offset }, input.is_real⟩).operations
            (offset + 9)))

private def nativeLinkAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddOperation.main
        ⟨pcWord input, #v[4, 0, 0, 0],
          { value := linkValue offset },
          input.is_real - input.adapter.op_a_0⟩).operations
            (offset + 9)))

private def nativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReader.main
        ⟨input.adapter, input.is_real, input.is_real,
          input.state.clk_high,
          input.state.clk_0_16 + input.state.clk_16_24 * 65536,
          input.state.pc, 47,
          (linkValue offset)[0], (linkValue offset)[1],
          (linkValue offset)[2], (linkValue offset)[3]⟩).operations
            (offset + 9)))

private def nativeWriteMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.RegisterWrite.main
        ⟨input.state.clk_high,
          input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
          input.adapter.op_a, linkValue offset,
          input.is_real⟩).operations (offset + 9)))

private def nativeMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  Expression.eval env
      (lsbValue offset * (lsbValue offset - 1)) = 0 ∧
    nativeCpuMeaning env input offset ∧
    nativeJumpAddMeaning env input offset ∧
    Expression.eval env ((jumpValue offset)[3]) = 0 ∧
    nativeLinkAddMeaning env input offset ∧
    Expression.eval env ((linkValue offset)[3]) = 0 ∧
    nativeITypeMeaning env input offset ∧
    nativeWriteMeaning env input offset ∧
    Expression.eval env
      ((input.is_real - 1) * input.adapter.op_a_0) = 0 ∧
    Expression.eval env
      (input.is_real * (input.is_real - 1)) = 0

private theorem nativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalrChip.main input).operations offset)) ↔
      nativeMeaning env input offset := by
  unfold nativeMeaning nativeCpuMeaning nativeJumpAddMeaning
    nativeLinkAddMeaning nativeITypeMeaning nativeWriteMeaning
  simp only [nativeAssertZeros, JalrChip.main,
    Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, witnessField,
    subcircuitWithAssertion, assertion,
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
    iTypeCircuitLocalLength,
    Gadgets.Equality.localLength_eq,
    Operations.constraints_assert,
    Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil,
    List.forall_append, List.forall_cons]
  simp only [pcWord, jumpValue, linkValue, lsbValue, cpuCircuitMain,
    addCircuitMain, iTypeCircuitMain, registerWriteCircuitMain,
    varFields4, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd,
    Vector.getElem_mapRange, Gadgets.Equality.circuit, forallNilIff]
  repeat' rw [equalityMappedAssertions]
  simp only [Operations.constraints_interact, Operations.constraints_nil,
    List.map_nil, forallNilIff, true_and, and_true,
    Expression.eval, eval_sub]

@[circuit_norm] private theorem evalITypeReader
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.ITypeReader (Expression F)) :
    Eval.eval env cols =
      ({ op_a := Eval.eval env cols.op_a
         op_a_memory := Eval.eval env cols.op_a_memory
         op_a_0 := Eval.eval env cols.op_a_0
         op_b := Eval.eval env cols.op_b
         op_b_memory := Eval.eval env cols.op_b_memory
         op_c_imm := Eval.eval env cols.op_c_imm } :
        Extracted.ITypeReader F) := by
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
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    JalrChip.Columns (ZMod p) :=
  { is_real := Expression.eval env input.is_real
    state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    add_operation := Eval.eval env
      ({ value := jumpValue offset } :
        AddOperation.Columns (Expression (ZMod p)))
    op_a_operation := Eval.eval env
      ({ value := linkValue offset } :
        AddOperation.Columns (Expression (ZMod p)))
    lsb := Expression.eval env (lsbValue offset) }

private def rustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      (Eval.eval env input.state)
      #v[(Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[0] -
          Expression.eval env (lsbValue offset),
        (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[1],
        (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[2]]
      8 (Expression.eval env input.is_real))

private def rustJumpAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.JalrOracle.AddOperation.asserts (F := ZMod p)
      #v[(Eval.eval env input.adapter).op_b_memory.prev_value[0],
        (Eval.eval env input.adapter).op_b_memory.prev_value[1],
        (Eval.eval env input.adapter).op_b_memory.prev_value[2],
        (Eval.eval env input.adapter).op_b_memory.prev_value[3]]
      #v[(Eval.eval env input.adapter).op_c_imm[0],
        (Eval.eval env input.adapter).op_c_imm[1],
        (Eval.eval env input.adapter).op_c_imm[2],
        (Eval.eval env input.adapter).op_c_imm[3]]
      (Eval.eval env
        ({ value := jumpValue offset } :
          Extracted.JalrOracle.AddOperation (Expression (ZMod p))))
      (Expression.eval env input.is_real))

private def rustLinkAddMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.JalrOracle.AddOperation.asserts (F := ZMod p)
      #v[(Eval.eval env input.state).pc[0],
        (Eval.eval env input.state).pc[1],
        (Eval.eval env input.state).pc[2], 0]
      #v[4, 0, 0, 0]
      (Eval.eval env
        ({ value := linkValue offset } :
          Extracted.JalrOracle.AddOperation (Expression (ZMod p))))
      (Expression.eval env input.is_real -
        (Eval.eval env input.adapter).op_a_0))

private def rustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let adapter := Eval.eval env input.adapter
  let value := (Eval.eval env
    ({ value := linkValue offset } :
      Extracted.JalrOracle.AddOperation (Expression (ZMod p)))).value
  List.Forall (· = 0)
      (Extracted.ITypeReader.asserts (F := ZMod p)
        (Eval.eval env input.state).clk_high
        ((Eval.eval env input.state).clk_0_16 +
          (Eval.eval env input.state).clk_16_24 * 65536)
        (Eval.eval env input.state).pc 47 value adapter
        (Expression.eval env input.is_real)
        (Expression.eval env input.is_real)) ∧
    adapter.op_a_0 * value[0] = 0 ∧
    adapter.op_a_0 * value[1] = 0 ∧
    adapter.op_a_0 * value[2] = 0

private def rustMeaning
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := rustColumns env input offset
  rustJumpAddMeaning env input offset ∧
    rustCpuMeaning env input offset ∧
    rustITypeMeaning env input offset ∧
    rustLinkAddMeaning env input offset ∧
    cols.is_real * (cols.is_real - 1) = 0 ∧
    cols.add_operation.value[3] = 0 ∧
    cols.lsb * (cols.lsb - 1) = 0 ∧
    (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
    cols.op_a_operation.value[3] = 0 ∧
    True

omit [Fact (2 ^ 17 < p)] in
private theorem rustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (jalrChipOracle.nativeAssertZeros
          (rustColumns env input offset)) ↔
      rustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, jalrChipOracle,
    jalrChipReconfigure]
  rw [Extracted.JalrOracle.JalrColumns.asserts]
  unfold rustMeaning rustCpuMeaning rustJumpAddMeaning
    rustLinkAddMeaning rustITypeMeaning
  dsimp only [rustColumns]
  simp only [Extracted.CPUState.asserts,
    Extracted.ITypeReader.asserts, List.forall_append, List.Forall,
    evalAddOperation, evalAddOperationColumns, vec4_eta, sub_zero]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem cpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    rustCpuMeaning env input offset ↔
      nativeCpuMeaning env input offset := by
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[(jumpValue offset)[0] - lsbValue offset, (jumpValue offset)[1],
        (jumpValue offset)[2]],
      8, input.is_real⟩
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[(Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[0] -
        Expression.eval env (lsbValue offset),
      (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[1],
      (Eval.eval env (jumpValue (p := p) offset) : Word (ZMod p))[2]]
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput (offset + 9)
    (Eval.eval env input.state) rustNextPc 8
    (Expression.eval env input.is_real) (by
      simp only [cpuInput, ProvableStruct.structEvalLiteralProc])
  dsimp only [cpuInput, rustNextPc] at hCpu
  unfold rustCpuMeaning nativeCpuMeaning
  exact hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem jumpAddMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    rustJumpAddMeaning env input offset ↔
      nativeJumpAddMeaning env input offset := by
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨#v[input.adapter.op_b_memory.prev_value[0],
        input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2],
        input.adapter.op_b_memory.prev_value[3]],
      input.adapter.op_c_imm,
      { value := jumpValue offset }, input.is_real⟩
  let rustA : Word (ZMod p) :=
    #v[(Eval.eval env input.adapter).op_b_memory.prev_value[0],
      (Eval.eval env input.adapter).op_b_memory.prev_value[1],
      (Eval.eval env input.adapter).op_b_memory.prev_value[2],
      (Eval.eval env input.adapter).op_b_memory.prev_value[3]]
  let rustB : Word (ZMod p) :=
    #v[(Eval.eval env input.adapter).op_c_imm[0],
      (Eval.eval env input.adapter).op_c_imm[1],
      (Eval.eval env input.adapter).op_c_imm[2],
      (Eval.eval env input.adapter).op_c_imm[3]]
  let rustValue : Extracted.JalrOracle.AddOperation (ZMod p) :=
    Eval.eval env
      ({ value := jumpValue offset } :
        Extracted.JalrOracle.AddOperation (Expression (ZMod p)))
  have hAdd := addAssertions (p := p) env addInput (offset + 9)
    rustA rustB rustValue.value (Expression.eval env input.is_real)
    (by
      simp only [addInput, rustA,
        ProvableStruct.structEvalLiteralProc]
      rw [evalVec4Literal, evalITypeReader]
      simp only [eval_registerAccessCols]
      apply Vector.ext
      intro i hi
      interval_cases i
      · simpa only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero] using
          (ProvableType.getElem_eval_fields env
            input.adapter.op_b_memory.prev_value 0 (by decide))
      · simpa only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_succ, List.getElem_cons_zero] using
          (ProvableType.getElem_eval_fields env
            input.adapter.op_b_memory.prev_value 1 (by decide))
      · simpa only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_succ, List.getElem_cons_zero] using
          (ProvableType.getElem_eval_fields env
            input.adapter.op_b_memory.prev_value 2 (by decide))
      · simpa only [Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_succ, List.getElem_cons_zero] using
          (ProvableType.getElem_eval_fields env
            input.adapter.op_b_memory.prev_value 3 (by decide)))
    (by
      simp only [addInput, rustB,
        ProvableStruct.structEvalLiteralProc]
      rw [evalITypeReader]
      exact (vec4_eta _).symm)
    (by
      simp only [addInput, rustValue,
        ProvableStruct.structEvalLiteralProc]
      rw [evalAddOperation])
    (by simp only [addInput,
      ProvableStruct.structEvalLiteralProc])
  dsimp only [addInput, rustA, rustB, rustValue,
    jumpValue] at hAdd
  unfold rustJumpAddMeaning nativeJumpAddMeaning
  exact hAdd

omit [Fact (2 ^ 17 < p)] in
private theorem linkAddMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
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
  let rustValue : Extracted.JalrOracle.AddOperation (ZMod p) :=
    Eval.eval env
      ({ value := linkValue offset } :
        Extracted.JalrOracle.AddOperation (Expression (ZMod p)))
  let rustGate : ZMod p :=
    Expression.eval env input.is_real -
      (Eval.eval env input.adapter).op_a_0
  have hAdd := addAssertions (p := p) env addInput (offset + 9)
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
      rw [eval_sub, evalITypeReader]
      simp only [ProvableType.eval_field])
  dsimp only [addInput, rustA, rustValue, rustGate,
    pcWord, linkValue] at hAdd
  unfold rustLinkAddMeaning nativeLinkAddMeaning
  exact hAdd

private theorem iTypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    rustITypeMeaning env input offset ↔
      nativeITypeMeaning env input offset := by
  let value : Word (Expression (ZMod p)) := linkValue offset
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real,
      input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 47, value[0], value[1], value[2], value[3]⟩
  let rustValue : Word (ZMod p) :=
    (Eval.eval env
      ({ value := value } :
        Extracted.JalrOracle.AddOperation (Expression (ZMod p)))).value
  have hRustValue : rustValue = Eval.eval env value := by
    simp only [rustValue]
    rw [evalAddOperation]
  have hopA0 :
      Expression.eval env input.adapter.op_a_0 =
        (Eval.eval env input.adapter).op_a_0 := by
    rw [evalITypeReader]
    simp only [ProvableType.eval_field]
  have hIType := CanonicalReader.iTypeAssertionsExact
    (p := p) env readerInput (offset + 9)
    (Eval.eval env input.state).clk_high
    ((Eval.eval env input.state).clk_0_16 +
      (Eval.eval env input.state).clk_16_24 * 65536)
    47 (Expression.eval env input.is_real)
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
  unfold rustITypeMeaning nativeITypeMeaning
  dsimp only
  rw [hIType]
  constructor
  · exact And.left
  · intro hNative
    refine ⟨hNative, ?_⟩
    have hRust := hIType.mpr hNative
    rw [Extracted.ITypeReader.asserts] at hRust
    simp only [List.Forall, sub_zero] at hRust
    exact ⟨hRust.2.1, hRust.2.2.1, hRust.2.2.2.1⟩

omit [Fact (2 ^ 17 < p)] in
private theorem writeMeaningTrue
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    nativeWriteMeaning env input offset ↔ True := by
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, linkValue offset, input.is_real⟩
  have hWrite := CanonicalReader.registerWriteAssertions
    env writeInput (offset + 9)
  dsimp only [writeInput, linkValue] at hWrite
  unfold nativeWriteMeaning
  exact hWrite

private theorem rustMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    rustMeaning env input offset ↔
      nativeMeaning env input offset := by
  unfold rustMeaning nativeMeaning
  rw [cpuMeaningFaithful, jumpAddMeaningFaithful,
    linkAddMeaningFaithful, iTypeMeaningFaithful,
    writeMeaningTrue]
  dsimp only [rustColumns]
  simp only [evalAddOperationColumns, evalITypeReader,
    ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, eval_sub, Expression.eval,
    true_and]
  tauto

private theorem constraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (jalrChipOracle.nativeAssertZeros
          (rustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalrChip.main input).operations offset)) :=
  (rustAssertionsDecompose (p := p) env input offset).trans
    ((rustMeaningFaithful (p := p) env input offset).trans
      (nativeConstraintsDecompose (p := p) env input offset).symm)

theorem jalrChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : JalrChip.Columns (ZMod p))
    (hbind : BindsChipOutput JalrChip.main env input offset cols) :
    List.Forall (· = 0)
        (jalrChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((JalrChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (JalrChip.elaborated (p := p)) hbind
  rw [JalrChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    JalrChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change rustColumns env input offset = cols at hbind
  rw [← hbind]
  exact constraintsFaithfulOutput (p := p) env input offset

theorem jalrChipConstraintsConstructive
    (rustCols : Extracted.JalrOracle.JalrColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := jalrChipRowCodec.assignment
      (jalrChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols) ↔
      (⟨JalrChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := jalrChipOracle.deconfigure rustCols
  let assignment := jalrChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput JalrChip.main assignment.environment
        (⟨JalrChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨JalrChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [JalrChip.circuit_main_eq] at h
    exact h
  have hfaithful := jalrChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨JalrChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨JalrChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨JalrChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      JalrChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (JalrChip.circuit (p := p))
      assignment.environment jalrChip_lookups_empty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private theorem stateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    (((JalrChip.exposedStateInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      (((Extracted.JalrOracle.JalrColumns.interactions
          (jalrChipReconfigure (rustColumns env input offset))).map
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
  simp only [JalrChip.exposedStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [jalrChipReconfigure, Extracted.JalrOracle.JalrColumns.interactions,
    Extracted.JalrOracle.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    rustColumns, jumpValue, lsbValue, eval_cpuState, evalITypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field, Expression.eval]
  simp only [eval_sub, Expression.eval]

private theorem permFiveBlocks {α : Type}
    (a b c d e : List α) :
    List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ a ++ d ++ c ++ e) := by
  have hab : List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ c ++ d) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right (c ++ d)
  have hab' : List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ a ++ c ++ d ++ e) := hab.append_right e
  have htail : List.Perm (b ++ a ++ c ++ d ++ e)
      (b ++ a ++ d ++ c ++ e) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := c) (l₂ := d)).append_left
        (b ++ a)).append_right e
  exact hab'.trans htail

private theorem byteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((JalrChip.exposedByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))
      (((Extracted.JalrOracle.JalrColumns.interactions
          (jalrChipReconfigure (rustColumns env input offset))).map
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
  simp only [JalrChip.exposedByteInteractions,
    List.map_cons, List.map_nil, hBytePull]
  simp [jalrChipReconfigure, Extracted.JalrOracle.JalrColumns.interactions,
    Extracted.JalrOracle.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    rustColumns, jumpValue, linkValue, lsbValue,
    eval_cpuState, evalITypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, h6, h3,
    Extracted.Interaction.toAccess, Extracted.Dir.sign, Nat.add_assoc]
  simp only [← ProvableStruct.eval_eq_eval,
    JalrChip.eval_inputs, eval_cpuState, evalITypeReader,
    eval_registerAccessCols,
    eval_registerAccessTimestamp, ProvableType.eval_field,
    Expression.eval, eval_sub, neg_sub]
  exact permFiveBlocks
    [_, _] [_, _, _, _] [_, _, _, _] [_, _, _, _] [_]

private theorem memoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((JalrChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.JalrOracle.JalrColumns.interactions
          (jalrChipReconfigure (rustColumns env input offset))).map
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
  simp only [JalrChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [jalrChipReconfigure, Extracted.JalrOracle.JalrColumns.interactions,
    Extracted.JalrOracle.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    rustColumns, jumpValue, linkValue, lsbValue,
    eval_cpuState, evalITypeReader,
    evalAddOperationColumns,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Nat.add_assoc]
  exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_])

private theorem programInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((JalrChip.exposedProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.JalrOracle.JalrColumns.interactions
          (jalrChipReconfigure (rustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have h47 : (47 : ZMod p).val = 47 := by
    have h : (47 : ℕ) < p := by
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
  simp only [JalrChip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [jalrChipReconfigure, Extracted.JalrOracle.JalrColumns.interactions,
    Extracted.JalrOracle.AddOperation.interactions,
    Extracted.CPUState.interactions, Extracted.ITypeReader.interactions,
    rustColumns, lsbValue, eval_cpuState, evalITypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, Expression.eval,
    LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Opcode.ofNat, h47]

private theorem unexpectedInteractionsEmpty
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((JalrChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((JalrChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (JalrChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [JalrChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem jalrChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : JalrChip.Columns (ZMod p))
    (hbind : BindsChipOutput JalrChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((JalrChip.main input).operations offset))
      (jalrChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (JalrChip.elaborated (p := p)) hbind
  rw [JalrChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    JalrChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change rustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.JalrOracle.JalrColumns.interactions
      (jalrChipReconfigure (rustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [unexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, jalrChipOracle]
  rw [JalrChip.interactionsWith_state_eq,
    JalrChip.interactionsWith_byte_eq,
    JalrChip.interactionsWith_memory_eq,
    JalrChip.interactionsWith_program_eq]
  have hState :=
    stateInteractionsFaithful (p := p) env input offset
  have hByte :=
    byteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    memoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    programInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind_of_exit_nil rustAccesses
      (Extracted.map_toAccess_exit_filter _)).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem jalrChipInteractionsConstructive
    (rustCols : Extracted.JalrOracle.JalrColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := jalrChipRowCodec.assignment
      (jalrChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨JalrChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (jalrChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := jalrChipOracle.deconfigure rustCols
  let assignment := jalrChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput JalrChip.main assignment.environment
        (⟨JalrChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨JalrChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [JalrChip.circuit_main_eq] at h
    exact h
  have hfaithful := jalrChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨JalrChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨JalrChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (JalrChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    JalrChip.circuit_main_eq] using hfaithful

theorem jalrChip_faithful :
    ChipFaithful (p := p) JalrChip.Inputs
      JalrChip.Columns Extracted.JalrOracle.JalrColumns
      JalrChip.circuit jalrChipRowCodec jalrChipOracle where
  constraints := jalrChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (jalrChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
