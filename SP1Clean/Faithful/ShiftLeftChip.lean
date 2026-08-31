import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.ShiftLeft
import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal

/-! # Whole-chip faithfulness — ShiftLeft

This module compares the complete native Clean ShiftLeft row with the complete constraint and
interaction system extracted from SP1 v6.4.0's `ShiftLeftChip`. The comparison is whole-chip:
the native proof-oriented decomposition may differ from Rust's internal operation layout, while the
decoded row, all `assertZero`s, and the full bus-interaction multiset agree exactly.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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

private theorem vec6_eta {F : Type} (value : Vector F 6) :
    #v[value[0], value[1], value[2], value[3], value[4], value[5]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem cpuState_eta {F : Type} (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high, clk_16_24 := cols.clk_16_24,
       clk_0_16 := cols.clk_0_16,
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Extracted.CPUState F) = cols := by
  cases cols
  simp only
  rw [vec3_eta]

private theorem registerAccess_eta {F : Type}
    (cols : Extracted.RegisterAccessCols F) :
    ({ prev_value :=
        #v[cols.prev_value[0], cols.prev_value[1],
          cols.prev_value[2], cols.prev_value[3]],
       access_timestamp := cols.access_timestamp } :
      Extracted.RegisterAccessCols F) = cols := by
  cases cols
  simp only
  rw [vec4_eta]

private theorem aluTypeReader_eta {F : Type}
    (cols : Extracted.ALUTypeReader F) :
    ({ op_a := cols.op_a,
       op_a_memory := {
         prev_value :=
           #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
             cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]],
         access_timestamp := cols.op_a_memory.access_timestamp },
       op_a_0 := cols.op_a_0,
       op_b := cols.op_b,
       op_b_memory := {
         prev_value :=
           #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
             cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]],
         access_timestamp := cols.op_b_memory.access_timestamp },
       op_c := #v[cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3]],
       op_c_memory := {
         prev_value :=
           #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
             cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]],
         access_timestamp := cols.op_c_memory.access_timestamp },
       imm_c := cols.imm_c } : Extracted.ALUTypeReader F) = cols := by
  cases cols
  simp only [vec4_eta]

/-- Whole-chip row reconfiguration. The reader blocks and the shift columns are already the
canonical generated substrate; the SLLW MSB block is copied into Rust's chip-private embedded
`U16MSBOperation` row. This is not an operation-level faithfulness claim. -/
def shiftLeftChipReconfigure {F : Type} (cols : ShiftLeftChip.Columns F) :
    Extracted.ShiftLeftOracle.ShiftLeftCols F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    c_bits := cols.c_bits
    v_01 := cols.v_01
    v_012 := cols.v_012
    v_0123 := cols.v_0123
    shift_u16 := cols.shift_u16
    lower_limb := cols.lower_limb
    higher_limb := cols.higher_limb
    limb_result := cols.limb_result
    sllw_msb := { msb := cols.sllw_msb.msb }
    is_sll := cols.is_sll
    is_sllw := cols.is_sllw
    is_sllw_imm := cols.is_sllw_imm }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def shiftLeftChipDeconfigure {F : Type} (cols : Extracted.ShiftLeftOracle.ShiftLeftCols F) :
    ShiftLeftChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    c_bits := cols.c_bits
    v_01 := cols.v_01
    v_012 := cols.v_012
    v_0123 := cols.v_0123
    shift_u16 := cols.shift_u16
    lower_limb := cols.lower_limb
    higher_limb := cols.higher_limb
    limb_result := cols.limb_result
    sllw_msb := { msb := cols.sllw_msb.msb }
    is_sll := cols.is_sll
    is_sllw := cols.is_sllw
    is_sllw_imm := cols.is_sllw_imm }

/-- SP1 Rust's complete ShiftLeft-chip oracle, viewed from the native Lean row. -/
def shiftLeftChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F ShiftLeftChip.Columns Extracted.ShiftLeftOracle.ShiftLeftCols where
  reconfigure := shiftLeftChipReconfigure
  deconfigure := shiftLeftChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.ShiftLeftOracle.ShiftLeftCols.asserts
  interactions := Extracted.ShiftLeftOracle.ShiftLeftCols.interactions

/- Namespace bridges between the ShiftLeft oracle's embedded chip-private `U16MSBOperation` copy
and the canonical standalone generated module. The two bodies are rendered from the same compiler
output, so each bridge is a definitional unfolding, not a mathematical claim. -/

private theorem shiftLeftOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.ShiftLeftOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.ShiftLeftOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem shiftLeftOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.ShiftLeftOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.ShiftLeftOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftExtractedAssertionsDecompose
    (cols : ShiftLeftChip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.ShiftLeftOracle.ShiftLeftCols.asserts
          (shiftLeftChipReconfigure cols)) ↔
      (List.Forall (· = 0)
          (Extracted.U16MSBOperation.asserts (F := ZMod p)
            cols.a[1] cols.sllw_msb cols.is_sllw) ∧
       List.Forall (· = 0)
          (Extracted.CPUState.asserts cols.state
            #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
            8 (cols.is_sll + cols.is_sllw)) ∧
       List.Forall (· = 0)
          (Extracted.ALUTypeReader.asserts cols.state.clk_high
            (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
            cols.state.pc (cols.is_sll * 6 + cols.is_sllw * 21)
            cols.a cols.adapter (cols.is_sll + cols.is_sllw)
            (cols.is_sll + cols.is_sllw)) ∧
       ShiftLeftChip.AssertSpec cols) := by
  simp only [Extracted.ShiftLeftOracle.ShiftLeftCols.asserts, List.forall_append]
  dsimp only [shiftLeftChipReconfigure]
  simp only [shiftLeftOracle_u16msb_asserts_eq]
  rw [cpuState_eta cols.state, aluTypeReader_eta cols.adapter]
  simp only [ShiftLeftChip.AssertSpec, ShiftLeftChip.CoreSpec, List.Forall]
  simp only [vec3_eta, vec4_eta]
  tauto

def shiftLeftChipInput {F : Type} [Add F]
    (cols : ShiftLeftChip.Columns F) : ShiftLeftChip.Inputs F :=
  { is_real := cols.is_sll + cols.is_sllw
    state := cols.state
    adapter := cols.adapter }

def shiftLeftChipLocals {F : Type}
    (cols : ShiftLeftChip.Columns F) : Vector F 33 :=
  #v[
    cols.a[0], cols.a[1], cols.a[2], cols.a[3],
    cols.c_bits[0], cols.c_bits[1], cols.c_bits[2],
    cols.c_bits[3], cols.c_bits[4], cols.c_bits[5],
    cols.v_01, cols.v_012, cols.v_0123,
    cols.shift_u16[0], cols.shift_u16[1],
    cols.shift_u16[2], cols.shift_u16[3],
    cols.lower_limb[0], cols.lower_limb[1],
    cols.lower_limb[2], cols.lower_limb[3],
    cols.higher_limb[0], cols.higher_limb[1],
    cols.higher_limb[2], cols.higher_limb[3],
    cols.limb_result[0], cols.limb_result[1],
    cols.limb_result[2], cols.limb_result[3],
    cols.sllw_msb.msb, cols.is_sll, cols.is_sllw,
    cols.is_sllw_imm]

def shiftLeftChipPhysicalRow {F : Type} [Add F]
    (cols : ShiftLeftChip.Columns F) : Array F :=
  inputFirstRow (shiftLeftChipInput cols)
    (shiftLeftChipLocals cols)

def shiftLeftChipColumnsOfInput {F : Type}
    (input : ShiftLeftChip.Inputs F) (locals : Vector F 33) :
    ShiftLeftChip.Columns F :=
  { state := input.state
    adapter := input.adapter
    a := #v[locals[0], locals[1], locals[2], locals[3]]
    c_bits := #v[locals[4], locals[5], locals[6],
      locals[7], locals[8], locals[9]]
    v_01 := locals[10]
    v_012 := locals[11]
    v_0123 := locals[12]
    shift_u16 := #v[locals[13], locals[14], locals[15], locals[16]]
    lower_limb := #v[locals[17], locals[18], locals[19], locals[20]]
    higher_limb := #v[locals[21], locals[22], locals[23], locals[24]]
    limb_result := #v[locals[25], locals[26], locals[27], locals[28]]
    sllw_msb := { msb := locals[29] }
    is_sll := locals[30]
    is_sllw := locals[31]
    is_sllw_imm := locals[32] }

theorem shiftLeftChipColumnsOfInput_roundtrip {F : Type} [Add F]
    (cols : ShiftLeftChip.Columns F) :
    shiftLeftChipColumnsOfInput (shiftLeftChipInput cols)
        (shiftLeftChipLocals cols) = cols := by
  unfold shiftLeftChipColumnsOfInput shiftLeftChipInput
  rw [ShiftLeftChip.Columns.mk.injEq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

@[circuit_norm] private theorem evalU16MSB
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem evalU16Inputs
    {F : Type} [FiniteField F] (env : Environment F)
    (input : Var U16MSBOperation.Inputs F) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a
         cols := Eval.eval env input.cols
         is_real := Eval.eval env input.is_real } :
        U16MSBOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem evalLocalVector
    {F : Type} [FiniteField F]
    {Input : TypeMap} [ProvableType Input]
    (input : Input F) {m : ℕ} (locals : Vector F m)
    (data : ProverData F) (base n : ℕ) (hbase : base + n ≤ m) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (varFromOffset (F := F) (Vector · n) (size Input + base)) =
      Vector.ofFn fun i =>
        locals[base + i.val]'(by
          have hi : i.val < n := i.isLt
          omega) := by
  apply Vector.ext
  intro i hi
  have hlocal : base + i < m := by omega
  rw [← ProvableType.getElem_eval_fields
    (Environment.fromArray (inputFirstRow input locals) data)
    (varFromOffset (F := F) (Vector · n) (size Input + base)) i hi]
  rw [ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    Vector.getElem_ofFn]
  simpa only [Nat.add_assoc] using
    (eval_local_inputFirstRow input locals data (base + i) hlocal)

theorem eval_shiftLeftChipDirectOutput
    (input : ShiftLeftChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 33)
    (data : ProverData (ZMod p)) :
    ProvableType.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        ((ShiftLeftChip.elaborated (p := p)).output
          (varFromOffset ShiftLeftChip.Inputs 0)
          (size ShiftLeftChip.Inputs)) =
      shiftLeftChipColumnsOfInput input locals := by
  rw [ShiftLeftChip.directOutput_eq]
  rw [← CircuitType.eval_expression, ShiftLeftChip.eval_columns]
  unfold shiftLeftChipColumnsOfInput
  rw [ShiftLeftChip.Columns.mk.injEq]
  dsimp only
  have hinput := eval_inputFirstRow input locals data
  rw [ShiftLeftChip.eval_inputs, ShiftLeftChip.Inputs.mk.injEq] at hinput
  constructor
  · exact hinput.2.1
  constructor
  · exact hinput.2.2
  constructor
  · have h := evalLocalVector input locals data 0 4 (by omega)
    simp only [Nat.add_zero] at h
    rw [h]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 4 6 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 10 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 11 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 12 (by decide))
  constructor
  · rw [evalLocalVector input locals data 13 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 17 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 21 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 25 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalU16MSB, Extracted.U16MSBOperation.mk.injEq]
    simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 29 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 30 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 31 (by decide))
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 32 (by decide))

def shiftLeftChipRowCodec :
    ChipRowCodec ShiftLeftChip.Inputs ShiftLeftChip.Columns
      (ShiftLeftChip.circuit (p := p)) where
  assignment cols data := {
    row := shiftLeftChipPhysicalRow cols
    input := shiftLeftChipInput cols
    width_eq := by
      rw [shiftLeftChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, ShiftLeftChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (ShiftLeftChip.circuit (p := p))
        (shiftLeftChipInput cols) (shiftLeftChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((ShiftLeftChip.main _).output _) = _
      rw [ShiftLeftChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_shiftLeftChipDirectOutput (p := p)
        (shiftLeftChipInput cols) (shiftLeftChipLocals cols) data).trans
          (shiftLeftChipColumnsOfInput_roundtrip cols) }

theorem shiftLeftChip_lookups_empty :
    (⟨ShiftLeftChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq,
    Air.Flat.Component.rowOperations_mk,
    ShiftLeftChip.circuit_main_eq]
  simp [ShiftLeftChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.ALUTypeReader.circuit,
    Readers.ALUTypeReader.main, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    U16MSBOperation.circuit,
    U16MSBOperation.main, ShiftLeftCore.circuit,
    ShiftLeftCore.main, Gadgets.Equality.main, circuit_norm]

private def slA (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

private def slCBits (offset : ℕ) : Vector (Expression (ZMod p)) 6 :=
  Vector.mapRange 6 fun i => var { index := offset + 4 + i }

private def slShiftU16 (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 13 + i }

private def slLower (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 17 + i }

private def slHigher (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 21 + i }

private def slLimbResult (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 25 + i }

private def slSll (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 30 }

private def slSllw (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 31 }

private def slGate (offset : ℕ) : Expression (ZMod p) :=
  slSll offset + slSllw offset

private def slCols
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    Var ShiftLeftChip.Columns (ZMod p) :=
  { state := input.state
    adapter := input.adapter
    a := slA offset
    c_bits := slCBits offset
    v_01 := var { index := offset + 10 }
    v_012 := var { index := offset + 11 }
    v_0123 := var { index := offset + 12 }
    shift_u16 := slShiftU16 offset
    lower_limb := slLower offset
    higher_limb := slHigher offset
    limb_result := slLimbResult offset
    sllw_msb := { msb := var { index := offset + 29 } }
    is_sll := slSll offset
    is_sllw := slSllw offset
    is_sllw_imm := var { index := offset + 32 } }

private def slAluInput
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  { cols := input.adapter
    is_real := slGate offset
    is_trusted := slGate offset
    clk_high := input.state.clk_high
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536
    pc := input.state.pc
    opcode := slSll offset * 6 + slSllw offset * 21
    wv0 := (slA offset)[0]
    wv1 := (slA offset)[1]
    wv2 := (slA offset)[2]
    wv3 := (slA offset)[3] }

private def slNativeMeaning
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.CPUState.main
          ⟨input.state,
            #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
            8, input.is_real⟩).operations offset)) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨(slA offset)[1], { msb := var { index := offset + 29 } },
            slSllw offset⟩).operations (offset + 33))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.ALUTypeReader.main
          (slAluInput input offset)).operations (offset + 33))) ∧
  Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
  Expression.eval env (input.is_real - slGate offset) = 0 ∧
  Expression.eval env (slGate offset * (slGate offset - 1)) = 0 ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (slSll offset * (slSll offset - 1), 0)).operations
            (offset + 33))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (slSllw offset * (slSllw offset - 1), 0)).operations
            (offset + 33))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((ShiftLeftCore.main (slCols input offset)).operations
          (offset + 33)))

private theorem shiftLeftNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftLeftChip.main input).operations offset)) ↔
      slNativeMeaning env input offset := by
  unfold nativeAssertZeros
  rw [ShiftLeftChip.constraints_decompose]
  simp only [slNativeMeaning, slA, slCBits, slShiftU16,
    slLower, slHigher, slLimbResult, slSll, slSllw, slGate,
    slCols, slAluInput, ShiftLeftChip.aluReaderInput,
    ShiftLeftChip.coreInput_eq,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    ← ProvableStruct.eval_eq_eval, ShiftLeftChip.eval_inputs,
    ProvableType.eval_field, eval_sub, Expression.eval,
    nativeAssertZeros, Nat.add_zero]

private def shiftLeftRustColumns
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    ShiftLeftChip.Columns (ZMod p) :=
  Eval.eval env (slCols input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_eq
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    shiftLeftRustColumns env input offset =
      { state := Eval.eval env input.state
        adapter := Eval.eval env input.adapter
        a := Eval.eval env (slA (p := p) offset)
        c_bits := Eval.eval env (slCBits (p := p) offset)
        v_01 := Expression.eval env (var { index := offset + 10 })
        v_012 := Expression.eval env (var { index := offset + 11 })
        v_0123 := Expression.eval env (var { index := offset + 12 })
        shift_u16 := Eval.eval env (slShiftU16 (p := p) offset)
        lower_limb := Eval.eval env (slLower (p := p) offset)
        higher_limb := Eval.eval env (slHigher (p := p) offset)
        limb_result := Eval.eval env (slLimbResult (p := p) offset)
        sllw_msb :=
          Eval.eval env
            ({ msb := var { index := offset + 29 } } :
              Var Extracted.U16MSBOperation (ZMod p))
        is_sll := Expression.eval env (slSll (p := p) offset)
        is_sllw := Expression.eval env (slSllw (p := p) offset)
        is_sllw_imm :=
          Expression.eval env (var { index := offset + 32 }) } := by
  unfold shiftLeftRustColumns slCols
  rw [ShiftLeftChip.eval_columns]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_state
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).state =
      Eval.eval env input.state := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_adapter
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).adapter =
      Eval.eval env input.adapter := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_a
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).a =
      Eval.eval env (slA (p := p) offset) := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_isSll
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).is_sll =
      Expression.eval env (slSll offset) := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns]
  exact ProvableType.eval_field env (slSll offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_isSllw
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).is_sllw =
      Expression.eval env (slSllw offset) := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns]
  exact ProvableType.eval_field env (slSllw offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustColumns_sllwMsb
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftLeftRustColumns env input offset).sllw_msb.msb =
      Expression.eval env (var { index := offset + 29 }) := by
  unfold shiftLeftRustColumns
  rw [ShiftLeftChip.eval_columns, evalU16MSB]
  exact ProvableType.eval_field env (var { index := offset + 29 })

private def slRustMeaning
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := shiftLeftRustColumns env input offset
  List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.a[1] cols.sllw_msb cols.is_sllw) ∧
  List.Forall (· = 0)
      (Extracted.CPUState.asserts (F := ZMod p) cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_sll + cols.is_sllw)) ∧
  List.Forall (· = 0)
      (Extracted.ALUTypeReader.asserts (F := ZMod p) cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc (cols.is_sll * 6 + cols.is_sllw * 21)
        cols.a cols.adapter (cols.is_sll + cols.is_sllw)
        (cols.is_sll + cols.is_sllw)) ∧
  ShiftLeftChip.AssertSpec cols

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (shiftLeftChipOracle.nativeAssertZeros
          (shiftLeftRustColumns env input offset)) ↔
      slRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, shiftLeftChipOracle,
    slRustMeaning]
  exact shiftLeftExtractedAssertionsDecompose
    (shiftLeftRustColumns env input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem nativeU16MSBAssertionList
    (env : Environment (ZMod p))
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env
        ((U16MSBOperation.main input).operations offset) =
      [Expression.eval env (input.is_real * (input.is_real - 1)),
       (ProvableStruct.eval env input).cols.msb *
         ((ProvableStruct.eval env input).cols.msb - 1)] := by
  simp [nativeAssertZeros, U16MSBOperation.main,
    Gadgets.Equality.main, circuit_norm]
  have heval (value : Expression (ZMod p)) :
      Expression.eval env (toElements (M := field) value)[0] =
        Expression.eval env value := rfl
  simp_rw [heval]
  simp only [eval_sub, Expression.eval, sub_zero]
  rw [← ProvableStruct.eval_eq_eval, evalU16Inputs, evalU16MSB]
  have hscalar :
      Eval.eval env input.cols.msb =
        Expression.eval env input.cols.msb := by
    exact ProvableType.eval_field env input.cols.msb
  rw [hscalar]

omit [Fact (2 ^ 17 < p)] in
private theorem u16MSBAssertions
    (env : Environment (ZMod p))
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ)
    (a msb isReal : ZMod p)
    (hreal : Expression.eval env input.is_real = isReal)
    (hmsb : Expression.eval env input.cols.msb = msb) :
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts a ⟨msb⟩ isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main input).operations offset)) := by
  have hmsbEval :
      (ProvableStruct.eval env input).cols.msb =
        Expression.eval env input.cols.msb := by
    have h := congrArg (fun value => value.cols.msb)
      (ProvableStruct.eval_eq_eval env input)
    rw [evalU16Inputs, evalU16MSB] at h
    simpa only [CircuitType.eval_expression,
      ProvableType.eval_field] using h.symm
  rw [nativeU16MSBAssertionList]
  simp only [Extracted.U16MSBOperation.asserts, List.Forall,
    eval_sub, Expression.eval, hreal, hmsbEval, hmsb]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftCoreAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftLeftCore.main (slCols input offset)).operations
            (offset + 33))) ↔
      ShiftLeftChip.CoreSpec (Eval.eval env (slCols input offset)) := by
  let ops :=
    (ShiftLeftCore.main (slCols input offset)).operations (offset + 33)
  have hlookups : ops.lookups = [] := by
    simp only [ops, ShiftLeftCore.main, Gadgets.Equality.main, circuit_norm]
  have hconstraints :
      ops.ConstraintsHold env ↔
        List.Forall (· = 0) (nativeAssertZeros env ops) := by
    rw [Operations.ConstraintsHold, hlookups]
    simp only [nativeAssertZeros, List.forall_iff_forall_mem,
      List.mem_map, List.not_mem_nil, false_implies]
    constructor
    · intro h value
      rintro ⟨expression, hexpression, rfl⟩
      exact h.1 expression hexpression
    · intro h
      refine ⟨?_, fun _ => trivial⟩
      intro expression hexpression
      exact h (Expression.eval env expression) ⟨expression, hexpression, rfl⟩
  constructor
  · intro h
    have hfull : ops.ConstraintsHold env := hconstraints.mpr h
    have hguarantees : ops.FullGuarantees env := by
      have equalityInteractions (x y : Expression (ZMod p)) (n : ℕ) :
          ((Gadgets.Equality.main (M := field) (x, y)).operations n).interactions = [] := by
        simp only [Gadgets.Equality.main, circuit_norm]
      simp only [ops, Operations.FullGuarantees, ShiftLeftCore.main,
        FormalAssertion.toSubcircuit_interactions, equalityInteractions,
        circuit_norm]
    let colsValue := ProvableStruct.eval env (slCols input offset)
    have hvalue :
        colsValue = Eval.eval env (slCols input offset) :=
      (ProvableStruct.eval_eq_eval env (slCols input offset)).symm
    have hs := (FormalAssertion.original_soundness
      (ShiftLeftCore.circuit (p := p)) (offset + 33) env
      (slCols input offset) colsValue
      (ProvableStruct.eval_eq_eval env (slCols input offset))
      trivial hfull hguarantees).1
    rwa [hvalue] at hs
  · intro hspec
    let proverEnv : ProverEnvironment (ZMod p) :=
      { toEnvironment := env
        hint := ProverHint.empty (ZMod p) }
    have huses :
        proverEnv.UsesLocalWitnesses (offset + 33) ops := by
      have hlen : ops.localLength = 0 := by
        simp only [ops, ShiftLeftCore.main, circuit_norm]
      rw [ProverEnvironment.usesLocalWitnesses_iff_flat,
        ProverEnvironment.usesLocalWitnessesFlat_iff_extends]
      intro i
      have hi : i.val < ops.localLength := by
        simpa only [FlatOperation.localLength_toFlat] using i.isLt
      rw [hlen] at hi
      omega
    let colsValue := ProvableStruct.eval env (slCols input offset)
    have hvalue :
        Eval.eval env (slCols input offset) = colsValue :=
      ProvableStruct.eval_eq_eval env (slCols input offset)
    have hspecValue : ShiftLeftChip.CoreSpec colsValue := by
      rwa [hvalue] at hspec
    have hfull : ops.ConstraintsHold proverEnv :=
      (FormalAssertion.original_completeness
        (ShiftLeftCore.circuit (p := p)) (offset + 33) proverEnv
        (slCols input offset) colsValue
        (by
          calc
            eval proverEnv (slCols input offset) =
                ProvableType.eval proverEnv.toEnvironment
                  (slCols input offset) := by
                    rw [CircuitType.eval_prover]
                    rfl
            _ = ProvableStruct.eval env (slCols input offset) := by
              dsimp only [proverEnv]
              calc
                ProvableType.eval env (slCols input offset) =
                    eval env (slCols input offset) :=
                  (CircuitType.eval_verifier env (slCols input offset)).symm
                _ = ProvableStruct.eval env (slCols input offset) :=
                  ProvableStruct.eval_eq_eval env (slCols input offset)
            _ = colsValue := rfl)
        trivial huses hspecValue).1
    change ops.ConstraintsHold env at hfull
    exact hconstraints.mp hfull

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftGateEval
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    Expression.eval env (slGate offset) =
      (shiftLeftRustColumns env input offset).is_sll +
        (shiftLeftRustColumns env input offset).is_sllw := by
  simp only [slGate, Expression.eval]
  rw [shiftLeftRustColumns_isSll, shiftLeftRustColumns_isSllw]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftCpuAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    let cols := shiftLeftRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.CPUState.asserts cols.state
          #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
          8 (cols.is_sll + cols.is_sllw)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.CPUState.main
            ⟨input.state,
              #v[input.state.pc[0] + 4,
                input.state.pc[1], input.state.pc[2]],
              8, input.is_real⟩).operations offset)) := by
  dsimp only
  let cols := shiftLeftRustColumns env input offset
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4,
        input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  have hreal :
      (ProvableStruct.eval env cpuInput).is_real =
        cols.is_sll + cols.is_sllw := by
    calc
      (ProvableStruct.eval env cpuInput).is_real =
          Expression.eval env input.is_real := by
        simp only [cpuInput, ProvableStruct.structEvalLiteralProc]
      _ = Expression.eval env (slGate offset) := hinputReal
      _ = cols.is_sll + cols.is_sllw := by
        exact shiftLeftGateEval env input offset
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput offset cols.state
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
    8 (cols.is_sll + cols.is_sllw) hreal
  dsimp only [cpuInput, cols] at hCpu
  exact hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftU16Assertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftLeftRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts (F := ZMod p)
          cols.a[1] cols.sllw_msb cols.is_sllw) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨(slA offset)[1],
              { msb := var { index := offset + 29 } },
              slSllw offset⟩).operations (offset + 33))) := by
  dsimp only
  let cols := shiftLeftRustColumns env input offset
  let u16Input : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨(slA offset)[1],
      { msb := var { index := offset + 29 } },
      slSllw offset⟩
  have hU16 := u16MSBAssertions env u16Input (offset + 33)
    cols.a[1] cols.sllw_msb.msb cols.is_sllw
    (shiftLeftRustColumns_isSllw env input offset).symm
    (shiftLeftRustColumns_sllwMsb env input offset).symm
  dsimp only [u16Input, cols] at hU16
  exact hU16

private theorem shiftLeftAluAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftLeftRustColumns env input offset
    (List.Forall (· = 0)
        (Extracted.ALUTypeReader.asserts cols.state.clk_high
          (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
          cols.state.pc (cols.is_sll * 6 + cols.is_sllw * 21)
          cols.a cols.adapter (cols.is_sll + cols.is_sllw)
          (cols.is_sll + cols.is_sllw)) ∧
        cols.adapter.op_a_0 = 0) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              (slAluInput input offset)).operations (offset + 33))) ∧
        cols.adapter.op_a_0 = 0) := by
  dsimp only
  let cols := shiftLeftRustColumns env input offset
  let aluInput := slAluInput input offset
  have hreal :
      (ProvableStruct.eval env aluInput).is_real =
        cols.is_sll + cols.is_sllw := by
    calc
      (ProvableStruct.eval env aluInput).is_real =
          Expression.eval env (slGate offset) := by
        simp only [aluInput, slAluInput,
          ProvableStruct.structEvalLiteralProc]
      _ = cols.is_sll + cols.is_sllw :=
        shiftLeftGateEval env input offset
  have htrusted :
      (ProvableStruct.eval env aluInput).is_trusted =
        cols.is_sll + cols.is_sllw := by
    calc
      (ProvableStruct.eval env aluInput).is_trusted =
          Expression.eval env (slGate offset) := by
        simp only [aluInput, slAluInput,
          ProvableStruct.structEvalLiteralProc]
      _ = cols.is_sll + cols.is_sllw :=
        shiftLeftGateEval env input offset
  have hcols :
      ProvableStruct.eval env aluInput.cols = cols.adapter := by
    change ProvableStruct.eval env input.adapter = cols.adapter
    rw [shiftLeftRustColumns_adapter]
    exact (ProvableStruct.eval_eq_eval env input.adapter).symm
  have ha := shiftLeftRustColumns_a env input offset
  have hw0 :
      Expression.eval env aluInput.wv0 = cols.a[0] := by
    exact (ProvableType.getElem_eval_fields env (slA offset) 0
      (by decide)).trans (congrArg (fun value => value[0]) ha.symm)
  have hw1 :
      Expression.eval env aluInput.wv1 = cols.a[1] := by
    exact (ProvableType.getElem_eval_fields env (slA offset) 1
      (by decide)).trans (congrArg (fun value => value[1]) ha.symm)
  have hw2 :
      Expression.eval env aluInput.wv2 = cols.a[2] := by
    exact (ProvableType.getElem_eval_fields env (slA offset) 2
      (by decide)).trans (congrArg (fun value => value[2]) ha.symm)
  have hw3 :
      Expression.eval env aluInput.wv3 = cols.a[3] := by
    exact (ProvableType.getElem_eval_fields env (slA offset) 3
      (by decide)).trans (congrArg (fun value => value[3]) ha.symm)
  have hAlu := CanonicalReader.aluTypeAssertions
    (p := p) env aluInput (offset + 33)
    cols.state.clk_high
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
    (cols.is_sll * 6 + cols.is_sllw * 21)
    (cols.is_sll + cols.is_sllw)
    (cols.is_sll + cols.is_sllw)
    cols.state.pc cols.a cols.adapter
    hreal htrusted hcols hw0 hw1 hw2 hw3 rfl
  dsimp only [aluInput, cols] at hAlu
  exact hAlu

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftCoreSpec_opA0
    (cols : ShiftLeftChip.Columns (ZMod p)) :
    ShiftLeftChip.CoreSpec cols → cols.adapter.op_a_0 = 0 := by
  simp only [ShiftLeftChip.CoreSpec]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftSllAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftLeftRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (slSll offset * (slSll offset - 1), 0)).operations
              (offset + 33))) ↔
      cols.is_sll * (cols.is_sll - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftLeftRustColumns_isSll]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftSllwAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftLeftRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (slSllw offset * (slSllw offset - 1), 0)).operations
              (offset + 33))) ↔
      cols.is_sllw * (cols.is_sllw - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftLeftRustColumns_isSllw]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftCoreAssertionsRust
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftLeftCore.main (slCols input offset)).operations
            (offset + 33))) ↔
      ShiftLeftChip.CoreSpec
        (shiftLeftRustColumns env input offset) := by
  exact shiftLeftCoreAssertions env input offset

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftInputBoolean
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ↔
      let cols := shiftLeftRustColumns env input offset
      (cols.is_sll + cols.is_sllw) *
        (cols.is_sll + cols.is_sllw - 1) = 0 := by
  dsimp only
  simp only [Expression.eval]
  rw [eval_sub, hinputReal, shiftLeftGateEval env input offset]
  simp only [Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftGateBoolean
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    Expression.eval env (slGate offset * (slGate offset - 1)) = 0 ↔
      let cols := shiftLeftRustColumns env input offset
      (cols.is_sll + cols.is_sllw) *
        (cols.is_sll + cols.is_sllw - 1) = 0 := by
  dsimp only
  simp only [Expression.eval]
  rw [eval_sub, shiftLeftGateEval env input offset]
  simp only [Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftSelectorLink
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    Expression.eval env (input.is_real - slGate offset) = 0 := by
  rw [eval_sub, hinputReal, sub_self]

private theorem shiftLeftMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    slRustMeaning env input offset ↔
      slNativeMeaning env input offset := by
  let cols := shiftLeftRustColumns env input offset
  have hCpu := shiftLeftCpuAssertions env input offset hinputReal
  have hU16 := shiftLeftU16Assertions env input offset
  have hAlu := shiftLeftAluAssertions env input offset
  have hSll := shiftLeftSllAssertions env input offset
  have hSllw := shiftLeftSllwAssertions env input offset
  have hCore := shiftLeftCoreAssertionsRust env input offset
  have hInputBool := shiftLeftInputBoolean env input offset hinputReal
  have hGateBool := shiftLeftGateBoolean env input offset
  have hLink := shiftLeftSelectorLink env input offset hinputReal
  have hCoreOpA0 :
      ShiftLeftChip.CoreSpec cols → cols.adapter.op_a_0 = 0 :=
    shiftLeftCoreSpec_opA0 cols
  have hNativeCoreOpA0 :
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((ShiftLeftCore.main (slCols input offset)).operations
              (offset + 33))) →
        cols.adapter.op_a_0 = 0 :=
    fun h => hCoreOpA0 (hCore.mp h)
  unfold slRustMeaning slNativeMeaning
  dsimp only [cols] at hCpu hU16 hAlu hSll hSllw hCore hInputBool hCoreOpA0 hNativeCoreOpA0
  dsimp only [cols]
  simp only [ShiftLeftChip.AssertSpec]
  constructor
  · rintro ⟨hU16Rust, hCpuRust, hAluRust, hGateRust,
      hSllRust, hSllwRust, hCoreRust⟩
    have hU16Native := hU16.mp hU16Rust
    have hCpuNative := hCpu.mp hCpuRust
    have hCoreNative := hCore.mpr hCoreRust
    have hopA0 := hCoreOpA0 hCoreRust
    have hAluNative := (hAlu.mp ⟨hAluRust, hopA0⟩).1
    have hInputNative := hInputBool.mpr hGateRust
    have hGateNative := hGateBool.mpr hGateRust
    have hSllNative := hSll.mpr hSllRust
    have hSllwNative := hSllw.mpr hSllwRust
    exact ⟨hCpuNative, hU16Native, hAluNative,
      hInputNative, hLink, hGateNative,
      hSllNative, hSllwNative, hCoreNative⟩
  · rintro ⟨hCpuNative, hU16Native, hAluNative, _hInputNative,
      _hLinkNative, hGateNative, hSllNative, hSllwNative,
      hCoreNative⟩
    have hU16Rust := hU16.mpr hU16Native
    have hCpuRust := hCpu.mpr hCpuNative
    have hCoreRust := hCore.mp hCoreNative
    have hopA0 := hNativeCoreOpA0 hCoreNative
    have hAluRust := (hAlu.mpr ⟨hAluNative, hopA0⟩).1
    have hGateRust := hGateBool.mp hGateNative
    have hSllRust := hSll.mp hSllNative
    have hSllwRust := hSllw.mp hSllwNative
    exact ⟨hU16Rust, hCpuRust, hAluRust,
      hGateRust, hSllRust, hSllwRust, hCoreRust⟩

private theorem shiftLeftConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    List.Forall (· = 0)
        (shiftLeftChipOracle.nativeAssertZeros
          (shiftLeftRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftLeftChip.main input).operations offset)) :=
  (shiftLeftExtractedAssertionsDecompose
      (shiftLeftRustColumns env input offset)).trans
    ((shiftLeftMeaningFaithful env input offset hinputReal).trans
      (shiftLeftNativeAssertionsDecompose env input offset).symm)

private theorem shiftLeftRustColumns_eq_output
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    shiftLeftRustColumns env input offset =
      Eval.eval env
        ((ShiftLeftChip.elaborated (p := p)).output input offset) := by
  rw [ShiftLeftChip.directOutput_eq]
  unfold shiftLeftRustColumns slCols slA slCBits slShiftU16
    slLower slHigher slLimbResult slSll slSllw
  rw [ShiftLeftChip.eval_columns, ShiftLeftChip.eval_columns]
  simp only [ProvableType.varFromOffset_fields]

theorem shiftLeftChip_constraints_faithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : ShiftLeftChip.Columns (ZMod p))
    (hbind : BindsChipOutput ShiftLeftChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    List.Forall (· = 0)
        (shiftLeftChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftLeftChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (ShiftLeftChip.elaborated (p := p)) hbind
  rw [← ProvableStruct.eval_eq_eval] at hbind
  have hcolumns : shiftLeftRustColumns env input offset = cols :=
    (shiftLeftRustColumns_eq_output env input offset).trans hbind
  rw [← hcolumns]
  exact shiftLeftConstraintsFaithfulOutput env input offset hinputReal

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftChipLocals_thirty {F : Type}
    (cols : ShiftLeftChip.Columns F) :
    (shiftLeftChipLocals cols)[30] = cols.is_sll := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftChipLocals_thirtyOne {F : Type}
    (cols : ShiftLeftChip.Columns F) :
    (shiftLeftChipLocals cols)[31] = cols.is_sllw := by
  rfl

private theorem shiftLeftChipRowCodec_inputReal
    (cols : ShiftLeftChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftLeftChipRowCodec.assignment cols data
    Expression.eval assignment.environment
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar.is_real =
      Expression.eval assignment.environment
        (slGate
          (⟨ShiftLeftChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowOffset) := by
  dsimp only
  let assignment := shiftLeftChipRowCodec.assignment cols data
  rw [Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk]
  have hInput :
      Expression.eval
          (Environment.fromArray
            (inputFirstRow (shiftLeftChipInput cols)
              (shiftLeftChipLocals cols)) data)
          (varFromOffset ShiftLeftChip.Inputs 0).is_real =
        (shiftLeftChipInput cols).is_real := by
    rw [← ShiftLeftChip.eval_inputIsReal]
    exact congrArg (fun value => value.is_real)
      (eval_inputFirstRow (shiftLeftChipInput cols)
        (shiftLeftChipLocals cols) data)
  have hSll := eval_local_inputFirstRow (shiftLeftChipInput cols)
    (shiftLeftChipLocals cols) data 30 (by decide)
  have hSllw := eval_local_inputFirstRow (shiftLeftChipInput cols)
    (shiftLeftChipLocals cols) data 31 (by decide)
  change
    Expression.eval assignment.environment
        (varFromOffset ShiftLeftChip.Inputs 0).is_real =
      assignment.environment.get (size ShiftLeftChip.Inputs + 30) +
        assignment.environment.get (size ShiftLeftChip.Inputs + 31)
  rw [show assignment.environment =
      Environment.fromArray
        (inputFirstRow (shiftLeftChipInput cols)
          (shiftLeftChipLocals cols)) data by rfl]
  rw [hInput]
  simp only [shiftLeftChipInput]
  simp only [Expression.eval] at hSll hSllw
  rw [shiftLeftChipLocals_thirty] at hSll
  rw [shiftLeftChipLocals_thirtyOne] at hSllw
  simp only [shiftLeftChipInput] at hSll hSllw
  exact (congrArg₂ (· + ·) hSll hSllw).symm

theorem shiftLeftChip_constraints_constructive
    (rustCols : Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftLeftChipRowCodec.assignment
      (shiftLeftChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (shiftLeftChipOracle.assertZeros rustCols) ↔
      (⟨ShiftLeftChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := shiftLeftChipOracle.deconfigure rustCols
  let assignment := shiftLeftChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput ShiftLeftChip.main assignment.environment
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [ShiftLeftChip.circuit_main_eq] at h
    exact h
  have hinputReal :
      Expression.eval assignment.environment
          (⟨ShiftLeftChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowInputVar.is_real =
        Expression.eval assignment.environment
          (slGate
            (⟨ShiftLeftChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOffset) :=
    shiftLeftChipRowCodec_inputReal cols data
  have hfaithful := shiftLeftChip_constraints_faithful
    assignment.environment
    (⟨ShiftLeftChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨ShiftLeftChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind hinputReal
  have hassertions :
      List.Forall (· = 0)
          (shiftLeftChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨ShiftLeftChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      ShiftLeftChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (ShiftLeftChip.circuit (p := p))
      assignment.environment shiftLeftChip_lookups_empty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
private theorem shiftLeftRealEval
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    Expression.eval env input.is_real =
      (shiftLeftRustColumns env input offset).is_sll +
        (shiftLeftRustColumns env input offset).is_sllw :=
  hinputReal.trans (shiftLeftGateEval env input offset)

private theorem shiftLeftStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    (((ShiftLeftChip.exposedStateInteractions input).map
            ChannelInteraction.toRaw).map
              (AbstractInteraction.toAccess env)) =
      (((Extracted.ShiftLeftOracle.ShiftLeftCols.interactions
          (shiftLeftChipReconfigure (shiftLeftRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.State)) := by
  have hReal := shiftLeftRealEval env input offset hinputReal
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
  simp only [ShiftLeftChip.exposedStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.ShiftLeftOracle.ShiftLeftCols.interactions,
    shiftLeftChipReconfigure,
    Extracted.ShiftLeftOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    shiftLeftRustColumns_state,
    ← ProvableStruct.eval_eq_eval,
    Expression.eval, hReal]

private theorem shiftLeftByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    List.Perm
      (((ShiftLeftChip.exposedByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))
      (((Extracted.ShiftLeftOracle.ShiftLeftCols.interactions
          (shiftLeftChipReconfigure (shiftLeftRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have h3 : (3 : ZMod p).val = 3 := val_3_zmod_p
  have hRealVars :
      Expression.eval env input.is_real =
        Expression.eval env (slSll offset) +
          Expression.eval env (slSllw offset) := by
    rw [hinputReal]
    simp only [slGate, Expression.eval]
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
  rw [shiftLeftRustColumns_eq]
  simp only [ShiftLeftChip.exposedByteInteractions,
    List.map_cons, List.map_nil, hBytePull]
  simp [Extracted.ShiftLeftOracle.ShiftLeftCols.interactions,
    shiftLeftChipReconfigure,
    Extracted.ShiftLeftOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    slA, slCBits,
    slLower, slHigher, slSll, slSllw,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp, evalU16MSB,
    eval_sub, Expression.eval,
    h6, h3, hRealVars,
    ShiftLeftChip.exposedGate, Nat.add_assoc]
  simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
    eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval]
  exact
    (List.perm_append_comm
      (l₁ := [_, _]) (l₂ := [_])).append_right
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _]

private theorem shiftLeftMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((ShiftLeftChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.ShiftLeftOracle.ShiftLeftCols.interactions
          (shiftLeftChipReconfigure (shiftLeftRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Memory)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hNegFlags :
      -env.get (offset + 31) + -env.get (offset + 30) =
        -(env.get (offset + 30) + env.get (offset + 31)) := by
    ring
  have hDoubleNeg :
      -signedVal (-env.get (offset + 31) + -env.get (offset + 30)) =
        signedVal (env.get (offset + 30) + env.get (offset + 31)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  have hNegReal :
      -signedVal (env.get (offset + 30) + env.get (offset + 31)) =
        signedVal (-env.get (offset + 31) + -env.get (offset + 30)) := by
    rw [hNegFlags, signedVal_neg hp2]
  have hNegOpC :
      -signedVal
          (env.get (offset + 30) + env.get (offset + 31) -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            (env.get (offset + 30) + env.get (offset + 31))) := by
    rw [(by ring :
      Expression.eval env input.adapter.imm_c -
          (env.get (offset + 30) + env.get (offset + 31)) =
        -(env.get (offset + 30) + env.get (offset + 31) -
          Expression.eval env input.adapter.imm_c)), signedVal_neg hp2]
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
  rw [shiftLeftRustColumns_eq]
  simp only [ShiftLeftChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.ShiftLeftOracle.ShiftLeftCols.interactions,
    shiftLeftChipReconfigure,
    Extracted.ShiftLeftOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    slA, slSll, slSllw, ShiftLeftChip.exposedGate,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2]
  simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
    eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field]
  simp only [eval_sub, Expression.eval,
    hDoubleNeg, hNegReal, hNegOpC]
  exact (List.perm_append_comm
    (l₁ := [_, _, _, _]) (l₂ := [_])).append_left [_]

private theorem shiftLeftProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((ShiftLeftChip.exposedProgramInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.ShiftLeftOracle.ShiftLeftCols.interactions
          (shiftLeftChipReconfigure (shiftLeftRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hNegFlags :
      -env.get (offset + 31) + -env.get (offset + 30) =
        -(env.get (offset + 30) + env.get (offset + 31)) := by
    ring
  have hDoubleNeg :
      -signedVal (-env.get (offset + 31) + -env.get (offset + 30)) =
        signedVal (env.get (offset + 30) + env.get (offset + 31)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
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
  rw [shiftLeftRustColumns_eq]
  simp only [ShiftLeftChip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.ShiftLeftOracle.ShiftLeftCols.interactions,
    shiftLeftChipReconfigure,
    Extracted.ShiftLeftOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    slA, slSll, slSllw,
    ShiftLeftChip.exposedGate, ShiftLeftChip.exposedOpcode,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Opcode.ofNat, h6, hDoubleNeg]

private theorem shiftLeftUnexpectedInteractionsEmpty
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((ShiftLeftChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((ShiftLeftChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (ShiftLeftChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [ShiftLeftChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem shiftLeftChip_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : ShiftLeftChip.Columns (ZMod p))
    (hbind : BindsChipOutput ShiftLeftChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (slGate offset)) :
    List.Perm
      (nativeAccesses env
        ((ShiftLeftChip.main input).operations offset))
      (shiftLeftChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (ShiftLeftChip.elaborated (p := p)) hbind
  rw [← ProvableStruct.eval_eq_eval] at hbind
  have hcolumns : shiftLeftRustColumns env input offset = cols :=
    (shiftLeftRustColumns_eq_output env input offset).trans hbind
  subst cols
  let rustAccesses :=
    (Extracted.ShiftLeftOracle.ShiftLeftCols.interactions
      (shiftLeftChipReconfigure (shiftLeftRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [shiftLeftUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, shiftLeftChipOracle]
  rw [ShiftLeftChip.interactionsWith_main_state_exposed_eq,
    ShiftLeftChip.interactionsWith_main_byte_eq,
    ShiftLeftChip.interactionsWith_main_memory_eq,
    ShiftLeftChip.interactionsWith_main_program_eq]
  have hState :=
    shiftLeftStateInteractionsFaithful
      (p := p) env input offset hinputReal
  have hByte :=
    shiftLeftByteInteractionsFaithful
      (p := p) env input offset hinputReal
  have hMemory :=
    shiftLeftMemoryInteractionsFaithful
      (p := p) env input offset
  have hProgram :=
    shiftLeftProgramInteractionsFaithful
      (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind_of_exit_nil rustAccesses
      (Extracted.map_toAccess_exit_filter _)).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem shiftLeftChip_interactions_constructive
    (rustCols : Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftLeftChipRowCodec.assignment
      (shiftLeftChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (shiftLeftChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := shiftLeftChipOracle.deconfigure rustCols
  let assignment := shiftLeftChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput ShiftLeftChip.main assignment.environment
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨ShiftLeftChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [ShiftLeftChip.circuit_main_eq] at h
    exact h
  have hfaithful := shiftLeftChip_interactions_faithful
    (p := p) assignment.environment
    (⟨ShiftLeftChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨ShiftLeftChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
    (shiftLeftChipRowCodec_inputReal cols data)
  rw [nativeAccesses_component_eq_rowOperations
    (ShiftLeftChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    ShiftLeftChip.circuit_main_eq] using hfaithful

theorem shiftLeftChip_faithful :
    ChipFaithful (p := p) ShiftLeftChip.Inputs
      ShiftLeftChip.Columns Extracted.ShiftLeftOracle.ShiftLeftCols
      ShiftLeftChip.circuit shiftLeftChipRowCodec
      shiftLeftChipOracle where
  constraints := shiftLeftChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (shiftLeftChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
