import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.UType
import SP1Clean.Proofs.Chips.UTypeChip.Formal

/-! # Whole-chip faithfulness — native UType row ↔ pinned SP1 Rust AIR

`uTypeChip_faithful` compares the complete native Clean UType circuit with the
v6.4.0 Rust `UTypeColumns` assertion system and interaction multiset, on real
and padding rows. The physical-row codec preserves the Rust column layout:
the native input prefix is followed by the three addend limbs and four
`AddOperation` result limbs.

The proof keeps CPU, add, J-type-reader, register-write, and scalar assertion
systems behind folded boundaries. In particular, it includes Rust's
`when_not(is_real).assert_zero(op_a_0)` padding constraint without importing it
as an assumption. State, Byte, Memory, and Program interactions are compared
as exact trace-level access lists; the Memory and Program projections use the
dual orientation built into `nativeAccesses`.

Heartbeat budget: all six declared ceilings here were ~25× over and were
measured away (every floor ≤40000), so this file now runs entirely on the
plain default.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Whole-chip row reconfiguration. The reader blocks are already the canonical generated substrate,
so only the native arithmetic block is copied into Rust's chip-private operation row. This is not an
operation-level faithfulness claim. -/
def uTypeChipReconfigure {F : Type} (cols : UTypeChip.Columns F) :
    Extracted.UTypeOracle.UTypeColumns F :=
  { state := cols.state
    adapter := cols.adapter
    addend := cols.addend
    add_operation := { value := cols.add_operation.value }
    is_auipc := cols.is_auipc
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def uTypeChipDeconfigure {F : Type} (cols : Extracted.UTypeOracle.UTypeColumns F) :
    UTypeChip.Columns F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    addend := cols.addend
    add_operation := { value := cols.add_operation.value }
    is_auipc := cols.is_auipc }

/-- SP1 Rust's complete U-type-chip oracle, viewed from the native Lean row. -/
def uTypeChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F UTypeChip.Columns Extracted.UTypeOracle.UTypeColumns where
  reconfigure := uTypeChipReconfigure
  deconfigure := uTypeChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.UTypeOracle.UTypeColumns.asserts
  interactions := Extracted.UTypeOracle.UTypeColumns.interactions

def uTypeChipInput {F : Type}
    (cols : UTypeChip.Columns F) : UTypeChip.Inputs F :=
  { is_real := cols.is_real, state := cols.state, adapter := cols.adapter,
    is_auipc := cols.is_auipc }

def uTypeChipLocals {F : Type}
    (cols : UTypeChip.Columns F) : Vector F 7 :=
  #v[cols.addend[0], cols.addend[1], cols.addend[2],
    cols.add_operation.value[0], cols.add_operation.value[1],
    cols.add_operation.value[2], cols.add_operation.value[3]]

def uTypeChipPhysicalRow {F : Type}
    (cols : UTypeChip.Columns F) : Array F :=
  inputFirstRow (uTypeChipInput cols) (uTypeChipLocals cols)

def uTypeChipColumnsOfInput {F : Type}
    (input : UTypeChip.Inputs F) (locals : Vector F 7) :
    UTypeChip.Columns F :=
  ⟨input.is_real, input.state, input.adapter, #v[locals[0], locals[1], locals[2]],
    ⟨#v[locals[3], locals[4], locals[5], locals[6]]⟩,
    input.is_auipc⟩

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

@[circuit_norm] private theorem eval_extractedAddOperation
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.UTypeOracle.AddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.UTypeOracle.AddOperation F) := by
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

private theorem evalVec3Literal {F : Type} [FiniteField F]
    (env : Environment F) (a b c : Expression F) :
    Eval.eval env (#v[a, b, c] : Vector (Expression F) 3) =
      #v[Expression.eval env a, Expression.eval env b,
        Expression.eval env c] := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env
    (#v[a, b, c] : Vector (Expression F) 3) i hi]
  interval_cases i <;> rfl

private theorem evalVec4Literal {F : Type} [FiniteField F]
    (env : Environment F) (a b c d : Expression F) :
    Eval.eval env
        (#v[a, b, c, d] :
          Vector (Expression F) 4) =
      #v[Expression.eval env a, Expression.eval env b,
        Expression.eval env c, Expression.eval env d] := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields env
    (#v[a, b, c, d] : Vector (Expression F) 4) i hi]
  interval_cases i <;> rfl

theorem uTypeChipColumnsOfInput_roundtrip {F : Type}
    (cols : UTypeChip.Columns F) :
    uTypeChipColumnsOfInput (uTypeChipInput cols) (uTypeChipLocals cols) = cols := by
  cases cols
  simp [uTypeChipColumnsOfInput, uTypeChipInput, uTypeChipLocals,
    vec3_eta, vec4_eta]

theorem eval_uTypeChipDirectOutput
    (input : UTypeChip.Inputs (ZMod p)) (locals : Vector (ZMod p) 7)
    (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((UTypeChip.elaborated (p := p)).output
          (varFromOffset UTypeChip.Inputs 0) (size UTypeChip.Inputs)) =
      uTypeChipColumnsOfInput input locals := by
  rw [UTypeChip.directOutput_eq]
  rw [← CircuitType.eval_expression, UTypeChip.eval_columns]
  unfold uTypeChipColumnsOfInput
  rw [UTypeChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [UTypeChip.eval_inputs, UTypeChip.Inputs.mk.injEq] at hinputEval
  constructor
  · exact hinputEval.1
  constructor
  · exact hinputEval.2.1
  constructor
  · exact hinputEval.2.2.1
  constructor
  · apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (#v[var { index := size UTypeChip.Inputs },
        var { index := size UTypeChip.Inputs + 1 },
        var { index := size UTypeChip.Inputs + 2 }] :
        Vector (Expression (ZMod p)) 3) i hi]
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using
        (eval_local_inputFirstRow input locals data 0 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ] using
        (eval_local_inputFirstRow input locals data 1 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ] using
        (eval_local_inputFirstRow input locals data 2 (by decide))
  constructor
  · rw [AddOperation.Columns.mk.injEq]
    rw [evalAddOperationColumns]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 4 fun i =>
        var { index := size UTypeChip.Inputs + 3 + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using
        (eval_local_inputFirstRow input locals data 3 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 4 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 5 (by decide))
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_assoc] using
        (eval_local_inputFirstRow input locals data 6 (by decide))
  · exact hinputEval.2.2.2

def uTypeChipRowCodec :
    ChipRowCodec UTypeChip.Inputs UTypeChip.Columns
      (UTypeChip.circuit (p := p)) where
  assignment cols data := {
    row := uTypeChipPhysicalRow cols
    input := uTypeChipInput cols
    width_eq := by
      rw [uTypeChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, UTypeChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (UTypeChip.circuit (p := p))
      (uTypeChipInput cols) (uTypeChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((UTypeChip.main _).output _) = _
      rw [UTypeChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_uTypeChipDirectOutput (p := p) (uTypeChipInput cols)
        (uTypeChipLocals cols) data).trans
          (uTypeChipColumnsOfInput_roundtrip cols) }

theorem uTypeChip_lookups_empty :
    (⟨UTypeChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    UTypeChip.circuit_main_eq]
  simp [UTypeChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.JTypeReader.circuit, Readers.JTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    AddOperation.circuit, AddOperation.main, Gadgets.Equality.main,
    circuit_norm]

private def uTypeChipAddend (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  #v[var ⟨offset⟩, var ⟨offset + 1⟩, var ⟨offset + 2⟩, 0]

private def uTypeChipValue (offset : ℕ) :
    Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 3 + i }

private theorem forallNilIff {alpha : Type} (pred : alpha → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

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

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem varFields3 (offset : ℕ) :
    (varFromOffset (fields 3) offset :
      Vector (Expression (ZMod p)) 3) =
      #v[var ⟨offset⟩, var ⟨offset + 1⟩,
        var ⟨offset + 2⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem varFields4 (offset : ℕ) :
    (varFromOffset (fields 4) offset :
      Vector (Expression (ZMod p)) 4) =
      Vector.mapRange 4 fun i =>
        var { index := offset + i } := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem addOperationAssertions
    (env : Environment (ZMod p))
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b value : Word (ZMod p)) (isReal : ZMod p)
    (ha : (ProvableStruct.eval env input).a = a)
    (hb : (ProvableStruct.eval env input).b = b)
    (hv : (ProvableStruct.eval env input.cols).value = value)
    (hr : (ProvableStruct.eval env input).is_real = isReal) :
    List.Forall (· = 0)
        (Extracted.UTypeOracle.AddOperation.asserts (F := ZMod p)
          a b { value := value } isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((AddOperation.main input).operations offset)) := by
  simp [nativeAssertZeros, AddOperation.main,
    Extracted.UTypeOracle.AddOperation.asserts, circuit_norm]
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

private def uTypeNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.CPUState.main
          ⟨input.state,
            #v[input.state.pc[0] + 4,
              input.state.pc[1], input.state.pc[2]],
            8, input.is_real⟩).operations (offset + 7)))

private def uTypeNativeAddMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((AddOperation.main
          ⟨uTypeChipAddend offset, input.adapter.op_b_imm,
            { value := uTypeChipValue offset },
            input.is_real - input.adapter.op_a_0⟩).operations
              (offset + 7)))

private def uTypeNativeJTypeMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.JTypeReader.main
          ⟨input.adapter, input.is_real, input.is_real,
            input.state.clk_high,
            input.state.clk_0_16 +
              input.state.clk_16_24 * 65536,
            input.state.pc,
            input.is_auipc * 48 +
              (1 - input.is_auipc) * 49,
            (uTypeChipValue offset)[0],
            (uTypeChipValue offset)[1],
            (uTypeChipValue offset)[2],
            (uTypeChipValue offset)[3]⟩).operations
              (offset + 7)))

private def uTypeNativeWriteMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.RegisterWrite.main
          ⟨input.state.clk_high,
            input.state.clk_0_16 +
              input.state.clk_16_24 * 65536 + 4,
            input.adapter.op_a, uTypeChipValue offset,
            input.is_real⟩).operations (offset + 7)))

private def uTypeNativeScalarMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  Expression.eval env
      ((uTypeChipAddend offset)[0] -
        input.is_auipc * input.state.pc[0]) = 0 ∧
    Expression.eval env
      ((uTypeChipAddend offset)[1] -
        input.is_auipc * input.state.pc[1]) = 0 ∧
    Expression.eval env
      ((uTypeChipAddend offset)[2] -
        input.is_auipc * input.state.pc[2]) = 0 ∧
    Expression.eval env
      (input.is_auipc * (input.is_auipc - 1)) = 0 ∧
    Expression.eval env
      ((input.is_real - 1) * input.adapter.op_a_0) = 0 ∧
    Expression.eval env
      (input.is_real * (input.is_real - 1)) = 0

private def uTypeAssertionMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  uTypeNativeCpuMeaning env input offset ∧
    uTypeNativeAddMeaning env input offset ∧
    uTypeNativeJTypeMeaning env input offset ∧
    uTypeNativeWriteMeaning env input offset ∧
    uTypeNativeScalarMeaning env input offset

private theorem uTypeChipConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((UTypeChip.main input).operations offset)) ↔
      uTypeAssertionMeaning env input offset := by
  unfold uTypeAssertionMeaning uTypeNativeCpuMeaning
    uTypeNativeAddMeaning uTypeNativeJTypeMeaning
    uTypeNativeWriteMeaning uTypeNativeScalarMeaning
  simp only [nativeAssertZeros, UTypeChip.main,
    Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVector, witnessVectorIR, subcircuitWithAssertion, assertion,
    assertZero, HasAssertEq.assert_eq, Expression.assertEquals,
    Operations.localLength]
  simp only [Operations.constraints_append,
    Operations.constraints_witness,
    Operations.constraints_subcircuit,
    constraints_toSubcircuit_generalFormalCircuit,
    constraints_toSubcircuit_formalAssertion,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    cpuCircuitLocalLength,
    AddOperation.circuit_localLength,
    jTypeCircuitLocalLength,
    registerWriteCircuitLocalLength,
    Gadgets.Equality.localLength_eq,
    Operations.constraints_assert, Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil,
    List.forall_append, List.forall_cons]
  simp only [uTypeChipAddend, uTypeChipValue]
  simp only [cpuCircuitMain, addCircuitMain, jTypeCircuitMain,
    registerWriteCircuitMain,
    varFields3, varFields4,
    forallNilIff, true_and, and_true, Nat.add_zero,
    Nat.add_assoc, Nat.reduceAdd,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [Gadgets.Equality.circuit]
  repeat' rw [equalityMappedAssertions]
  simp only [eval_sub, Expression.eval, sub_eq_zero]

private theorem registerAccessEta {F : Type}
    (cols : Extracted.RegisterAccessCols F) :
    ({ prev_value :=
        #v[cols.prev_value[0], cols.prev_value[1],
          cols.prev_value[2], cols.prev_value[3]]
       access_timestamp :=
        { prev_low := cols.access_timestamp.prev_low
          diff_low_limb := cols.access_timestamp.diff_low_limb } } :
      Extracted.RegisterAccessCols F) = cols := by
  cases cols
  simp [vec4_eta]

private theorem cpuStateEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Extracted.CPUState F) = cols := by
  cases cols
  simp [vec3_eta]

private theorem jTypeEta {F : Type}
    (cols : Extracted.JTypeReader F) :
    ({ op_a := cols.op_a
       op_a_memory :=
        { prev_value :=
            #v[cols.op_a_memory.prev_value[0],
              cols.op_a_memory.prev_value[1],
              cols.op_a_memory.prev_value[2],
              cols.op_a_memory.prev_value[3]]
          access_timestamp :=
            { prev_low :=
                cols.op_a_memory.access_timestamp.prev_low
              diff_low_limb :=
                cols.op_a_memory.access_timestamp.diff_low_limb } }
       op_a_0 := cols.op_a_0
       op_b_imm :=
        #v[cols.op_b_imm[0], cols.op_b_imm[1],
          cols.op_b_imm[2], cols.op_b_imm[3]]
       op_c_imm :=
        #v[cols.op_c_imm[0], cols.op_c_imm[1],
          cols.op_c_imm[2], cols.op_c_imm[3]] } :
      Extracted.JTypeReader F) = cols := by
  cases cols
  simp [vec4_eta]

private theorem addOperationEta {F : Type}
    (cols : Extracted.UTypeOracle.AddOperation F) :
    ({ value :=
        #v[cols.value[0], cols.value[1],
          cols.value[2], cols.value[3]] } :
      Extracted.UTypeOracle.AddOperation F) = cols := by
  cases cols
  simp [vec4_eta]

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeColumnsAssertsDecompose
    (cols : Extracted.UTypeOracle.UTypeColumns (ZMod p)) :
    Extracted.UTypeOracle.UTypeColumns.asserts cols =
      Extracted.CPUState.asserts cols.state
        #v[cols.state.pc[0] + 4,
          cols.state.pc[1], cols.state.pc[2]]
        8 cols.is_real ++
      Extracted.UTypeOracle.AddOperation.asserts (F := ZMod p)
        #v[cols.addend[0], cols.addend[1],
          cols.addend[2], 0]
        #v[cols.adapter.op_b_imm[0],
          cols.adapter.op_b_imm[1],
          cols.adapter.op_b_imm[2],
          cols.adapter.op_b_imm[3]]
        cols.add_operation
        (cols.is_real - cols.adapter.op_a_0) ++
      Extracted.JTypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 +
          cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_auipc * 48 +
          (1 - cols.is_auipc) * 49)
        cols.add_operation.value cols.adapter
        cols.is_real cols.is_real ++
      [ cols.is_real * (cols.is_real - 1),
        cols.is_auipc * (cols.is_auipc - 1),
        cols.addend[0] -
          cols.is_auipc * cols.state.pc[0],
        cols.addend[1] -
          cols.is_auipc * cols.state.pc[1],
        cols.addend[2] -
          cols.is_auipc * cols.state.pc[2],
        0,
        (cols.is_real - 1) * cols.adapter.op_a_0 ] := by
  rw [Extracted.UTypeOracle.UTypeColumns.asserts]
  rw [cpuStateEta, addOperationEta, jTypeEta,
    vec3_eta, vec4_eta cols.add_operation.value]
  simp only [mul_zero, add_zero, sub_zero]

private def uTypeRustColumns
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    UTypeChip.Columns (ZMod p) :=
  { is_real := Expression.eval env input.is_real
    state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    addend := Eval.eval env
      (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
        var ⟨offset + 2⟩] :
        Vector (Expression (ZMod p)) 3)
    add_operation := Eval.eval env
      ({ value := uTypeChipValue offset } :
        AddOperation.Columns (Expression (ZMod p)))
    is_auipc := Expression.eval env input.is_auipc }

private def uTypeRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (_offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.CPUState.asserts (Eval.eval env input.state)
      #v[(Eval.eval env input.state).pc[0] + 4,
        (Eval.eval env input.state).pc[1],
        (Eval.eval env input.state).pc[2]]
      8 (Expression.eval env input.is_real))

private def uTypeRustAddMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.UTypeOracle.AddOperation.asserts (F := ZMod p)
      #v[(Eval.eval env
          (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
            var ⟨offset + 2⟩] :
            Vector (Expression (ZMod p)) 3))[0],
        (Eval.eval env
          (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
            var ⟨offset + 2⟩] :
            Vector (Expression (ZMod p)) 3))[1],
        (Eval.eval env
          (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
            var ⟨offset + 2⟩] :
            Vector (Expression (ZMod p)) 3))[2],
        (0 : ZMod p)]
      #v[(Eval.eval env input.adapter).op_b_imm[0],
        (Eval.eval env input.adapter).op_b_imm[1],
        (Eval.eval env input.adapter).op_b_imm[2],
        (Eval.eval env input.adapter).op_b_imm[3]]
      (Eval.eval env
        ({ value := uTypeChipValue offset } :
          Extracted.UTypeOracle.AddOperation (Expression (ZMod p))))
      (Expression.eval env input.is_real -
        (Eval.eval env input.adapter).op_a_0))

private def uTypeRustJTypeMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (Extracted.JTypeReader.asserts (F := ZMod p)
      (Eval.eval env input.state).clk_high
      ((Eval.eval env input.state).clk_0_16 +
        (Eval.eval env input.state).clk_16_24 * 65536)
      (Eval.eval env input.state).pc
      (Expression.eval env input.is_auipc * 48 +
        (1 - Expression.eval env input.is_auipc) * 49)
      (Eval.eval env
        ({ value := uTypeChipValue offset } :
          Extracted.UTypeOracle.AddOperation (Expression (ZMod p)))).value
      (Eval.eval env input.adapter)
      (Expression.eval env input.is_real)
      (Expression.eval env input.is_real))

private def uTypeRustScalarMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let addend := Eval.eval env
    (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
      var ⟨offset + 2⟩] :
      Vector (Expression (ZMod p)) 3)
  let state := Eval.eval env input.state
  let adapter := Eval.eval env input.adapter
  let isAuipc := Expression.eval env input.is_auipc
  let isReal := Expression.eval env input.is_real
  isReal * (isReal - 1) = 0 ∧
    isAuipc * (isAuipc - 1) = 0 ∧
    addend[0] - isAuipc * state.pc[0] = 0 ∧
    addend[1] - isAuipc * state.pc[1] = 0 ∧
    addend[2] - isAuipc * state.pc[2] = 0 ∧
    True ∧
    (isReal - 1) * adapter.op_a_0 = 0

private def uTypeRustAssertionMeaning
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  uTypeRustCpuMeaning env input offset ∧
    uTypeRustAddMeaning env input offset ∧
    uTypeRustJTypeMeaning env input offset ∧
    uTypeRustScalarMeaning env input offset

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (uTypeChipOracle.nativeAssertZeros
          (uTypeRustColumns env input offset)) ↔
      uTypeRustAssertionMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros,
    uTypeChipOracle, uTypeChipReconfigure]
  rw [uTypeColumnsAssertsDecompose]
  simp only [List.forall_append, List.forall_cons,
    forallNilIff, and_true]
  unfold uTypeRustAssertionMeaning uTypeRustCpuMeaning
    uTypeRustAddMeaning uTypeRustJTypeMeaning
    uTypeRustScalarMeaning
  dsimp only [uTypeRustColumns]
  simp only [eval_extractedAddOperation, evalAddOperationColumns]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeRustCpuMeaning env input offset ↔
      uTypeNativeCpuMeaning env input offset := by
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4,
        input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[(Eval.eval env input.state).pc[0] + 4,
      (Eval.eval env input.state).pc[1],
      (Eval.eval env input.state).pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput (offset + 7)
    (Eval.eval env input.state) rustNextPc 8
    (Expression.eval env input.is_real) (by
      simp only [cpuInput, ProvableStruct.structEvalLiteralProc])
  dsimp only [cpuInput, rustNextPc] at hCpu
  unfold uTypeRustCpuMeaning uTypeNativeCpuMeaning
  exact hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeAddMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeRustAddMeaning env input offset ↔
      uTypeNativeAddMeaning env input offset := by
  let addend : Word (Expression (ZMod p)) :=
    uTypeChipAddend offset
  let value : Word (Expression (ZMod p)) :=
    uTypeChipValue offset
  let addInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨addend, input.adapter.op_b_imm,
      { value := value },
      input.is_real - input.adapter.op_a_0⟩
  let rustAddend3 : Vector (ZMod p) 3 :=
    Eval.eval env
      (#v[var ⟨offset⟩, var ⟨offset + 1⟩,
        var ⟨offset + 2⟩] :
        Vector (Expression (ZMod p)) 3)
  let rustAddend : Word (ZMod p) :=
    #v[rustAddend3[0], rustAddend3[1],
      rustAddend3[2], 0]
  let rustImm : Word (ZMod p) :=
    #v[(Eval.eval env input.adapter).op_b_imm[0],
      (Eval.eval env input.adapter).op_b_imm[1],
      (Eval.eval env input.adapter).op_b_imm[2],
      (Eval.eval env input.adapter).op_b_imm[3]]
  let rustValue : Extracted.UTypeOracle.AddOperation (ZMod p) :=
    Eval.eval env
      ({ value := value } :
        Extracted.UTypeOracle.AddOperation (Expression (ZMod p)))
  let rustIsReal : ZMod p :=
    Expression.eval env input.is_real -
      (Eval.eval env input.adapter).op_a_0
  have hr :
      (ProvableStruct.eval env addInput).is_real =
        rustIsReal := by
    simp only [addInput, rustIsReal,
      ProvableStruct.structEvalLiteralProc]
    rw [eval_sub]
    rw [evalJTypeReader]
    simp only [ProvableType.eval_field]
  have hAdd := addOperationAssertions (p := p)
    env addInput (offset + 7)
    rustAddend rustImm rustValue.value rustIsReal
    (by
      simp only [addInput, rustAddend, rustAddend3, addend,
        uTypeChipAddend, ProvableStruct.structEvalLiteralProc]
      rw [evalVec4Literal, evalVec3Literal]
      simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        Expression.eval])
    (by
      simp only [addInput, rustImm,
        ProvableStruct.structEvalLiteralProc]
      rw [evalJTypeReader]
      exact (vec4_eta _).symm)
    (by
      simp only [addInput, rustValue,
        ProvableStruct.structEvalLiteralProc]
      rw [eval_extractedAddOperation])
    hr
  dsimp only [addInput, rustAddend, rustAddend3, rustImm,
    rustValue, rustIsReal, addend, value,
    uTypeChipAddend, uTypeChipValue] at hAdd
  unfold uTypeRustAddMeaning uTypeNativeAddMeaning
  exact hAdd

private theorem uTypeJTypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeRustJTypeMeaning env input offset ↔
      uTypeNativeJTypeMeaning env input offset := by
  let value : Word (Expression (ZMod p)) :=
    uTypeChipValue offset
  let readerInput : Var Readers.JTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real,
      input.state.clk_high,
      input.state.clk_0_16 +
        input.state.clk_16_24 * 65536,
      input.state.pc,
      input.is_auipc * 48 +
        (1 - input.is_auipc) * 49,
      value[0], value[1], value[2], value[3]⟩
  let rustValue : Word (ZMod p) :=
    (Eval.eval env
      ({ value := value } :
        Extracted.UTypeOracle.AddOperation (Expression (ZMod p)))).value
  have hRustValue :
      rustValue = Eval.eval env value := by
    simp only [rustValue]
    rw [eval_extractedAddOperation]
  have hopA0 :
      Expression.eval env input.adapter.op_a_0 =
        (Eval.eval env input.adapter).op_a_0 := by
    rw [evalJTypeReader]
    simp only [ProvableType.eval_field]
  have hJType := CanonicalReader.jTypeAssertions
    (p := p) env readerInput (offset + 7)
    (Eval.eval env input.state).clk_high
    ((Eval.eval env input.state).clk_0_16 +
      (Eval.eval env input.state).clk_16_24 * 65536)
    (Expression.eval env input.is_auipc * 48 +
      (1 - Expression.eval env input.is_auipc) * 49)
    (Expression.eval env input.is_real)
    (Expression.eval env input.is_real)
    (Eval.eval env input.state).pc
    rustValue
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput,
        ProvableStruct.structEvalLiteralProc])
    (by
      simpa only [readerInput] using hopA0)
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 0
            (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 1
            (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 2
            (by decide)))
    (by
      rw [hRustValue]
      simpa only [readerInput,
        ProvableStruct.structEvalLiteralProc,
        ProvableType.eval_field] using
          (ProvableType.getElem_eval_fields env value 3
            (by decide)))
    rfl
  dsimp only [readerInput, rustValue, value,
    uTypeChipValue] at hJType
  unfold uTypeRustJTypeMeaning uTypeNativeJTypeMeaning
  exact hJType

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeWriteMeaningTrue
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeNativeWriteMeaning env input offset ↔ True := by
  let value : Word (Expression (ZMod p)) :=
    uTypeChipValue offset
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 +
        input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, value, input.is_real⟩
  have hWrite :=
    CanonicalReader.registerWriteAssertions
      env writeInput (offset + 7)
  dsimp only [writeInput, value, uTypeChipValue] at hWrite
  unfold uTypeNativeWriteMeaning
  exact hWrite

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeScalarMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeRustScalarMeaning env input offset ↔
      uTypeNativeScalarMeaning env input offset := by
  have hpc0 :
      (Eval.eval env input.state.pc)[0] =
        Expression.eval env input.state.pc[0] :=
    (ProvableType.getElem_eval_fields
      env input.state.pc 0 (by decide)).symm
  have hpc1 :
      (Eval.eval env input.state.pc)[1] =
        Expression.eval env input.state.pc[1] :=
    (ProvableType.getElem_eval_fields
      env input.state.pc 1 (by decide)).symm
  have hpc2 :
      (Eval.eval env input.state.pc)[2] =
        Expression.eval env input.state.pc[2] :=
    (ProvableType.getElem_eval_fields
      env input.state.pc 2 (by decide)).symm
  unfold uTypeRustScalarMeaning uTypeNativeScalarMeaning
  dsimp only
  rw [eval_cpuState, evalJTypeReader, evalVec3Literal]
  rw [hpc0, hpc1, hpc2]
  simp only [ProvableType.eval_field,
    uTypeChipAddend,
    Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ,
    eval_sub, Expression.eval]
  tauto

private theorem uTypeRustMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    uTypeRustAssertionMeaning env input offset ↔
      uTypeAssertionMeaning env input offset := by
  unfold uTypeRustAssertionMeaning uTypeAssertionMeaning
  rw [uTypeCpuMeaningFaithful, uTypeAddMeaningFaithful,
    uTypeJTypeMeaningFaithful, uTypeWriteMeaningTrue,
    uTypeScalarMeaningFaithful]
  tauto

private theorem uTypeChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (uTypeChipOracle.nativeAssertZeros
          (uTypeRustColumns env input offset)) ↔
      uTypeAssertionMeaning env input offset :=
  (uTypeRustAssertionsDecompose
    (p := p) env input offset).trans
      (uTypeRustMeaningFaithful (p := p) env input offset)

theorem uTypeChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : UTypeChip.Columns (ZMod p))
    (hbind : BindsChipOutput UTypeChip.main env input offset cols) :
    List.Forall (· = 0)
        (uTypeChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((UTypeChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (UTypeChip.elaborated (p := p)) hbind
  rw [UTypeChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    UTypeChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change uTypeRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact (uTypeChipConstraintsFaithfulOutput
    (p := p) env input offset).trans
      (uTypeChipConstraintsDecompose
        (p := p) env input offset).symm

theorem uTypeChipConstraintsConstructive
    (rustCols : Extracted.UTypeOracle.UTypeColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := uTypeChipRowCodec.assignment
      (uTypeChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (uTypeChipOracle.assertZeros rustCols) ↔
      (⟨UTypeChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := uTypeChipOracle.deconfigure rustCols
  let assignment := uTypeChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput UTypeChip.main assignment.environment
        (⟨UTypeChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨UTypeChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [UTypeChip.circuit_main_eq] at h
    exact h
  have hfaithful := uTypeChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨UTypeChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨UTypeChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (uTypeChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨UTypeChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      UTypeChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (UTypeChip.circuit (p := p))
      assignment.environment uTypeChip_lookups_empty).symm

omit [Fact (2 ^ 17 < p)] in
private theorem uTypeColumnsInteractionsDecompose
    (cols : Extracted.UTypeOracle.UTypeColumns (ZMod p)) :
    Extracted.UTypeOracle.UTypeColumns.interactions cols =
      Extracted.CPUState.interactions cols.state
        #v[cols.state.pc[0] + 4,
          cols.state.pc[1], cols.state.pc[2]]
        8 cols.is_real ++
      Extracted.UTypeOracle.AddOperation.interactions
        #v[cols.addend[0], cols.addend[1],
          cols.addend[2], 0]
        #v[cols.adapter.op_b_imm[0],
          cols.adapter.op_b_imm[1],
          cols.adapter.op_b_imm[2],
          cols.adapter.op_b_imm[3]]
        cols.add_operation
        (cols.is_real - cols.adapter.op_a_0) ++
      Extracted.JTypeReader.interactions
        cols.state.clk_high
        (cols.state.clk_0_16 +
          cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_auipc * 48 +
          (1 - cols.is_auipc) * 49)
        cols.add_operation.value cols.adapter
        cols.is_real cols.is_real := by
  rw [Extracted.UTypeOracle.UTypeColumns.interactions]
  rw [cpuStateEta, addOperationEta, jTypeEta,
    vec3_eta, vec4_eta cols.add_operation.value]
  simp only [List.append_nil]

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private theorem uTypeStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    (((UTypeChip.exposedStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      (((Extracted.UTypeOracle.UTypeColumns.interactions
          (uTypeChipReconfigure (uTypeRustColumns env input offset))).map
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
  simp only [UTypeChip.exposedStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [uTypeColumnsInteractionsDecompose, uTypeChipReconfigure,
    Extracted.CPUState.interactions,
    Extracted.UTypeOracle.AddOperation.interactions,
    Extracted.JTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    uTypeRustColumns, eval_cpuState, evalJTypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, Expression.eval]

private theorem uTypeByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    (((UTypeChip.exposedByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)) =
      (((Extracted.UTypeOracle.UTypeColumns.interactions
          (uTypeChipReconfigure (uTypeRustColumns env input offset))).map
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
  simp only [UTypeChip.exposedByteInteractions,
    List.map_cons, List.map_nil, hBytePull]
  simp [uTypeColumnsInteractionsDecompose, uTypeChipReconfigure,
    Extracted.CPUState.interactions,
    Extracted.UTypeOracle.AddOperation.interactions,
    Extracted.JTypeReader.interactions,
    uTypeRustColumns, uTypeChipValue,
    eval_cpuState, evalJTypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange,
    ProvableType.eval_field, Expression.eval,
    ConstraintCoe.coe_eq_val, h6, h3]
  simp only [← ProvableStruct.eval_eq_eval,
    eval_cpuState, evalJTypeReader,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ProvableType.eval_field, Expression.eval, eval_sub,
    neg_sub]
  simp [Extracted.Interaction.toAccess,
    Extracted.Dir.sign, ← ProvableStruct.eval_eq_eval,
    Nat.add_assoc]

private theorem uTypeMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((UTypeChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.UTypeOracle.UTypeColumns.interactions
          (uTypeChipReconfigure (uTypeRustColumns env input offset))).map
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
  simp only [UTypeChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [uTypeColumnsInteractionsDecompose, uTypeChipReconfigure,
    Extracted.CPUState.interactions,
    Extracted.UTypeOracle.AddOperation.interactions,
    Extracted.JTypeReader.interactions,
    uTypeRustColumns, uTypeChipValue,
    eval_cpuState, evalJTypeReader,
    evalAddOperationColumns,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange,
    ProvableType.eval_field, Expression.eval,
    LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Nat.add_assoc]

private theorem uTypeProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((UTypeChip.exposedProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.UTypeOracle.UTypeColumns.interactions
          (uTypeChipReconfigure (uTypeRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
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
  simp only [UTypeChip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [uTypeColumnsInteractionsDecompose, uTypeChipReconfigure,
    Extracted.CPUState.interactions,
    Extracted.UTypeOracle.AddOperation.interactions,
    Extracted.JTypeReader.interactions,
    uTypeRustColumns, eval_cpuState, evalJTypeReader,
    evalAddOperationColumns,
    ← ProvableType.getElem_eval_fields,
    ProvableType.eval_field, eval_sub, Expression.eval,
    LookupAccessList.negMult, signedVal_neg hp2,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Opcode.ofNat, ConstraintCoe.coe_eq_val]

private theorem uTypeUnexpectedInteractionsEmpty
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((UTypeChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((UTypeChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (UTypeChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [UTypeChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem uTypeChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : UTypeChip.Columns (ZMod p))
    (hbind : BindsChipOutput UTypeChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((UTypeChip.main input).operations offset))
      (uTypeChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (UTypeChip.elaborated (p := p)) hbind
  rw [UTypeChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    UTypeChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change uTypeRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.UTypeOracle.UTypeColumns.interactions
      (uTypeChipReconfigure (uTypeRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [uTypeUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, uTypeChipOracle]
  rw [UTypeChip.interactionsWith_state_eq,
    UTypeChip.interactionsWith_byte_eq,
    UTypeChip.interactionsWith_memory_eq,
    UTypeChip.interactionsWith_program_eq]
  have hState :=
    uTypeStateInteractionsFaithful
      (p := p) env input offset
  have hByte :=
    uTypeByteInteractionsFaithful
      (p := p) env input offset
  have hMemory :=
    uTypeMemoryInteractionsFaithful
      (p := p) env input offset
  have hProgram :=
    uTypeProgramInteractionsFaithful
      (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind
      rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hByte, hMemory, hProgram]

theorem uTypeChipInteractionsConstructive
    (rustCols : Extracted.UTypeOracle.UTypeColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := uTypeChipRowCodec.assignment
      (uTypeChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨UTypeChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (uTypeChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := uTypeChipOracle.deconfigure rustCols
  let assignment := uTypeChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput UTypeChip.main assignment.environment
        (⟨UTypeChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨UTypeChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [UTypeChip.circuit_main_eq] at h
    exact h
  have hfaithful := uTypeChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨UTypeChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨UTypeChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (UTypeChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    UTypeChip.circuit_main_eq] using hfaithful

theorem uTypeChip_faithful :
    ChipFaithful (p := p) UTypeChip.Inputs
      UTypeChip.Columns Extracted.UTypeOracle.UTypeColumns
      UTypeChip.circuit uTypeChipRowCodec
      uTypeChipOracle where
  constraints := uTypeChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (uTypeChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
