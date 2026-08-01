import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.ShiftRight
import SP1Clean.Proofs.Chips.ShiftRightChip.Formal

/-! # Whole-chip faithfulness — ShiftRight

This module compares the complete native Clean ShiftRight row with the complete constraint and
interaction system extracted from the pinned SP1 v6.3.1 `ShiftRightChip`. The comparison is
whole-chip: the native proof-oriented decomposition may differ from Rust's internal operation
layout, while the decoded row, all `assertZero`s, and the full bus-interaction multiset agree
exactly.
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
canonical generated substrate; the two MSB blocks are copied into Rust's chip-private embedded
`U16MSBOperation` rows. This is not an operation-level faithfulness claim. -/
def shiftRightChipReconfigure {F : Type} (cols : ShiftRightChip.Columns F) :
    Extracted.ShiftRightOracle.ShiftRightCols F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    b_msb := { msb := cols.b_msb.msb }
    srw_msb := { msb := cols.srw_msb.msb }
    c_bits := cols.c_bits
    sra_msb_v0123 := cols.sra_msb_v0123
    v_0123 := cols.v_0123
    v_012 := cols.v_012
    v_01 := cols.v_01
    lower_limb := cols.lower_limb
    higher_limb := cols.higher_limb
    limb_result := cols.limb_result
    shift_u16 := cols.shift_u16
    is_srl := cols.is_srl
    is_sra := cols.is_sra
    is_srlw := cols.is_srlw
    is_sraw := cols.is_sraw
    is_w_imm := cols.is_w_imm }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def shiftRightChipDeconfigure {F : Type} (cols : Extracted.ShiftRightOracle.ShiftRightCols F) :
    ShiftRightChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    b_msb := { msb := cols.b_msb.msb }
    srw_msb := { msb := cols.srw_msb.msb }
    c_bits := cols.c_bits
    sra_msb_v0123 := cols.sra_msb_v0123
    v_0123 := cols.v_0123
    v_012 := cols.v_012
    v_01 := cols.v_01
    lower_limb := cols.lower_limb
    higher_limb := cols.higher_limb
    limb_result := cols.limb_result
    shift_u16 := cols.shift_u16
    is_srl := cols.is_srl
    is_sra := cols.is_sra
    is_srlw := cols.is_srlw
    is_sraw := cols.is_sraw
    is_w_imm := cols.is_w_imm }

/-- SP1 Rust's complete ShiftRight-chip oracle, viewed from the native Lean row. -/
def shiftRightChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F ShiftRightChip.Columns Extracted.ShiftRightOracle.ShiftRightCols where
  reconfigure := shiftRightChipReconfigure
  deconfigure := shiftRightChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.ShiftRightOracle.ShiftRightCols.asserts
  interactions := Extracted.ShiftRightOracle.ShiftRightCols.interactions

/- Namespace bridges between the ShiftRight oracle's embedded chip-private `U16MSBOperation` copy
and the canonical standalone generated module. The two bodies are rendered from the same compiler
output, so each bridge is a definitional unfolding, not a mathematical claim. -/

private theorem shiftRightOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.ShiftRightOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.ShiftRightOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem shiftRightOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.ShiftRightOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.ShiftRightOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightExtractedAssertionsDecompose
    (cols : ShiftRightChip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.ShiftRightOracle.ShiftRightCols.asserts
          (shiftRightChipReconfigure cols)) ↔
      (List.Forall (· = 0)
          (Extracted.U16MSBOperation.asserts (F := ZMod p)
            cols.adapter.op_b_memory.prev_value[3]
            cols.b_msb cols.is_sra) ∧
       List.Forall (· = 0)
          (Extracted.U16MSBOperation.asserts (F := ZMod p)
            cols.adapter.op_b_memory.prev_value[1]
            cols.b_msb cols.is_sraw) ∧
       List.Forall (· = 0)
          (Extracted.U16MSBOperation.asserts (F := ZMod p)
            cols.a[1] cols.srw_msb (cols.is_srlw + cols.is_sraw)) ∧
       List.Forall (· = 0)
          (Extracted.CPUState.asserts cols.state
            #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
            8 (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ∧
       List.Forall (· = 0)
          (Extracted.ALUTypeReader.asserts cols.state.clk_high
            (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
            cols.state.pc
            (cols.is_srl * 7 + cols.is_sra * 8 +
              cols.is_srlw * 22 + cols.is_sraw * 23)
            cols.a cols.adapter
            (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
            (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ∧
       ShiftRightChip.AssertSpec cols) := by
  simp only [Extracted.ShiftRightOracle.ShiftRightCols.asserts, List.forall_append]
  dsimp only [shiftRightChipReconfigure]
  simp only [shiftRightOracle_u16msb_asserts_eq]
  rw [cpuState_eta cols.state, aluTypeReader_eta cols.adapter]
  simp only [ShiftRightChip.AssertSpec, ShiftRightChip.CoreSpec, List.Forall,
    Nat.cast_one, Nat.cast_ofNat]
  simp only [vec3_eta, vec4_eta]
  tauto

def shiftRightChipInput {F : Type} [Add F]
    (cols : ShiftRightChip.Columns F) : ShiftRightChip.Inputs F :=
  { is_real := cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
    state := cols.state
    adapter := cols.adapter }

def shiftRightChipLocals {F : Type}
    (cols : ShiftRightChip.Columns F) : Vector F 37 :=
  #v[
    cols.a[0], cols.a[1], cols.a[2], cols.a[3],
    cols.b_msb.msb, cols.srw_msb.msb,
    cols.c_bits[0], cols.c_bits[1], cols.c_bits[2],
    cols.c_bits[3], cols.c_bits[4], cols.c_bits[5],
    cols.sra_msb_v0123, cols.v_0123, cols.v_012, cols.v_01,
    cols.lower_limb[0], cols.lower_limb[1],
    cols.lower_limb[2], cols.lower_limb[3],
    cols.higher_limb[0], cols.higher_limb[1],
    cols.higher_limb[2], cols.higher_limb[3],
    cols.limb_result[0], cols.limb_result[1],
    cols.limb_result[2], cols.limb_result[3],
    cols.shift_u16[0], cols.shift_u16[1],
    cols.shift_u16[2], cols.shift_u16[3],
    cols.is_srl, cols.is_sra, cols.is_srlw, cols.is_sraw,
    cols.is_w_imm]

def shiftRightChipPhysicalRow {F : Type} [Add F]
    (cols : ShiftRightChip.Columns F) : Array F :=
  inputFirstRow (shiftRightChipInput cols)
    (shiftRightChipLocals cols)

def shiftRightChipColumnsOfInput {F : Type}
    (input : ShiftRightChip.Inputs F) (locals : Vector F 37) :
    ShiftRightChip.Columns F :=
  { state := input.state
    adapter := input.adapter
    a := #v[locals[0], locals[1], locals[2], locals[3]]
    b_msb := { msb := locals[4] }
    srw_msb := { msb := locals[5] }
    c_bits := #v[locals[6], locals[7], locals[8],
      locals[9], locals[10], locals[11]]
    sra_msb_v0123 := locals[12]
    v_0123 := locals[13]
    v_012 := locals[14]
    v_01 := locals[15]
    lower_limb := #v[locals[16], locals[17], locals[18], locals[19]]
    higher_limb := #v[locals[20], locals[21], locals[22], locals[23]]
    limb_result := #v[locals[24], locals[25], locals[26], locals[27]]
    shift_u16 := #v[locals[28], locals[29], locals[30], locals[31]]
    is_srl := locals[32]
    is_sra := locals[33]
    is_srlw := locals[34]
    is_sraw := locals[35]
    is_w_imm := locals[36] }

theorem shiftRightChipColumnsOfInput_roundtrip {F : Type} [Add F]
    (cols : ShiftRightChip.Columns F) :
    shiftRightChipColumnsOfInput (shiftRightChipInput cols)
        (shiftRightChipLocals cols) = cols := by
  unfold shiftRightChipColumnsOfInput shiftRightChipInput
  rw [ShiftRightChip.Columns.mk.injEq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rfl
  constructor
  · rfl
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

theorem eval_shiftRightChipDirectOutput
    (input : ShiftRightChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 37)
    (data : ProverData (ZMod p)) :
    ProvableType.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        ((ShiftRightChip.elaborated (p := p)).output
          (varFromOffset ShiftRightChip.Inputs 0)
          (size ShiftRightChip.Inputs)) =
      shiftRightChipColumnsOfInput input locals := by
  rw [ShiftRightChip.directOutput_eq]
  rw [← CircuitType.eval_expression, ShiftRightChip.eval_columns]
  unfold shiftRightChipColumnsOfInput
  rw [ShiftRightChip.Columns.mk.injEq]
  dsimp only
  have hinput := eval_inputFirstRow input locals data
  rw [ShiftRightChip.eval_inputs, ShiftRightChip.Inputs.mk.injEq] at hinput
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
  · rw [evalU16MSB, Extracted.U16MSBOperation.mk.injEq]
    simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 4 (by decide))
  constructor
  · rw [evalU16MSB, Extracted.U16MSBOperation.mk.injEq]
    simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 5 (by decide))
  constructor
  · rw [evalLocalVector input locals data 6 6 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 12 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 13 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 14 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 15 (by decide))
  constructor
  · rw [evalLocalVector input locals data 16 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 20 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 24 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · rw [evalLocalVector input locals data 28 4 (by omega)]
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 32 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 33 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 34 (by decide))
  constructor
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 35 (by decide))
  · simpa only [ProvableType.eval_field] using
      (eval_local_inputFirstRow input locals data 36 (by decide))

def shiftRightChipRowCodec :
    ChipRowCodec ShiftRightChip.Inputs ShiftRightChip.Columns
      (ShiftRightChip.circuit (p := p)) where
  assignment cols data := {
    row := shiftRightChipPhysicalRow cols
    input := shiftRightChipInput cols
    width_eq := by
      rw [shiftRightChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, ShiftRightChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (ShiftRightChip.circuit (p := p))
        (shiftRightChipInput cols) (shiftRightChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((ShiftRightChip.main _).output _) = _
      rw [ShiftRightChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_shiftRightChipDirectOutput (p := p)
        (shiftRightChipInput cols) (shiftRightChipLocals cols) data).trans
          (shiftRightChipColumnsOfInput_roundtrip cols) }

theorem shiftRightChip_lookups_empty :
    (⟨ShiftRightChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq,
    Air.Flat.Component.rowOperations_mk,
    ShiftRightChip.circuit_main_eq]
  simp [ShiftRightChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.ALUTypeReader.circuit,
    Readers.ALUTypeReader.main, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    U16MSBOperation.circuit,
    U16MSBOperation.main, ShiftRightCore.circuit,
    ShiftRightCore.main, Gadgets.Equality.main, circuit_norm]

private def srA (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + i }

private def srCBits (offset : ℕ) : Vector (Expression (ZMod p)) 6 :=
  Vector.mapRange 6 fun i => var { index := offset + 6 + i }

private def srLower (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 16 + i }

private def srHigher (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 20 + i }

private def srLimbResult (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 24 + i }

private def srShiftU16 (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 28 + i }

private def srSrl (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 32 }

private def srSra (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 33 }

private def srSrlw (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 34 }

private def srSraw (offset : ℕ) : Expression (ZMod p) :=
  var { index := offset + 35 }

private def srGate (offset : ℕ) : Expression (ZMod p) :=
  srSrl offset + srSra offset + srSrlw offset + srSraw offset

private def srCols
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    Var ShiftRightChip.Columns (ZMod p) :=
  { state := input.state
    adapter := input.adapter
    a := srA offset
    b_msb := { msb := var { index := offset + 4 } }
    srw_msb := { msb := var { index := offset + 5 } }
    c_bits := srCBits offset
    sra_msb_v0123 := var { index := offset + 12 }
    v_0123 := var { index := offset + 13 }
    v_012 := var { index := offset + 14 }
    v_01 := var { index := offset + 15 }
    lower_limb := srLower offset
    higher_limb := srHigher offset
    limb_result := srLimbResult offset
    shift_u16 := srShiftU16 offset
    is_srl := srSrl offset
    is_sra := srSra offset
    is_srlw := srSrlw offset
    is_sraw := srSraw offset
    is_w_imm := var { index := offset + 36 } }

private def srAluInput
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.ALUTypeReader.Inputs (ZMod p) :=
  { cols := input.adapter
    is_real := input.is_real
    is_trusted := input.is_real
    clk_high := input.state.clk_high
    clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536
    pc := input.state.pc
    opcode := srSrl offset * 7 + srSra offset * 8 +
      srSrlw offset * 22 + srSraw offset * 23
    wv0 := (srA offset)[0]
    wv1 := (srA offset)[1]
    wv2 := (srA offset)[2]
    wv3 := (srA offset)[3] }

private def srNativeMeaning
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.CPUState.main
          ⟨input.state,
            #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
            8, input.is_real⟩).operations offset)) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨input.adapter.op_b_memory.prev_value[3],
            { msb := var { index := offset + 4 } },
            srSra offset⟩).operations (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨input.adapter.op_b_memory.prev_value[1],
            { msb := var { index := offset + 4 } },
            srSraw offset⟩).operations (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((U16MSBOperation.main
          ⟨(srA offset)[1], { msb := var { index := offset + 5 } },
            srSrlw offset + srSraw offset⟩).operations (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Readers.ALUTypeReader.main
          (srAluInput input offset)).operations (offset + 37))) ∧
  Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ∧
  Expression.eval env (input.is_real - srGate offset) = 0 ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (srSrl offset * (srSrl offset - 1), 0)).operations
            (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (srSra offset * (srSra offset - 1), 0)).operations
            (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (srSrlw offset * (srSrlw offset - 1), 0)).operations
            (offset + 37))) ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((Gadgets.Equality.main (M := field)
          (srSraw offset * (srSraw offset - 1), 0)).operations
            (offset + 37))) ∧
  Expression.eval env (srGate offset * (srGate offset - 1)) = 0 ∧
  List.Forall (· = 0)
      (nativeAssertZeros env
        ((ShiftRightCore.main (srCols input offset)).operations
          (offset + 37)))

private theorem shiftRightNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftRightChip.main input).operations offset)) ↔
      srNativeMeaning env input offset := by
  unfold nativeAssertZeros
  rw [ShiftRightChip.constraints_decompose]
  simp only [srNativeMeaning, srA, srCBits, srLower, srHigher,
    srLimbResult, srShiftU16, srSrl, srSra, srSrlw, srSraw,
    srGate, srCols, srAluInput, ShiftRightChip.aluReaderInput,
    ShiftRightChip.coreInput_eq,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    ← ProvableStruct.eval_eq_eval, ShiftRightChip.eval_inputs,
    ProvableType.eval_field, eval_sub, Expression.eval,
    nativeAssertZeros, Nat.add_zero]

private def shiftRightRustColumns
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    ShiftRightChip.Columns (ZMod p) :=
  Eval.eval env (srCols input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_eq
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    shiftRightRustColumns env input offset =
      { state := Eval.eval env input.state
        adapter := Eval.eval env input.adapter
        a := Eval.eval env (srA (p := p) offset)
        b_msb := Eval.eval env
          ({ msb := var { index := offset + 4 } } :
            Var Extracted.U16MSBOperation (ZMod p))
        srw_msb := Eval.eval env
          ({ msb := var { index := offset + 5 } } :
            Var Extracted.U16MSBOperation (ZMod p))
        c_bits := Eval.eval env (srCBits (p := p) offset)
        sra_msb_v0123 := Expression.eval env (var { index := offset + 12 })
        v_0123 := Expression.eval env (var { index := offset + 13 })
        v_012 := Expression.eval env (var { index := offset + 14 })
        v_01 := Expression.eval env (var { index := offset + 15 })
        lower_limb := Eval.eval env (srLower (p := p) offset)
        higher_limb := Eval.eval env (srHigher (p := p) offset)
        limb_result := Eval.eval env (srLimbResult (p := p) offset)
        shift_u16 := Eval.eval env (srShiftU16 (p := p) offset)
        is_srl := Expression.eval env (srSrl (p := p) offset)
        is_sra := Expression.eval env (srSra (p := p) offset)
        is_srlw := Expression.eval env (srSrlw (p := p) offset)
        is_sraw := Expression.eval env (srSraw (p := p) offset)
        is_w_imm := Expression.eval env (var { index := offset + 36 }) } := by
  unfold shiftRightRustColumns srCols
  rw [ShiftRightChip.eval_columns]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_state
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).state =
      Eval.eval env input.state := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_adapter
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).adapter =
      Eval.eval env input.adapter := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_a
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).a =
      Eval.eval env (srA (p := p) offset) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_bMsb
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).b_msb.msb =
      Expression.eval env (var { index := offset + 4 }) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns, evalU16MSB]
  exact ProvableType.eval_field env (var { index := offset + 4 })

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_srwMsb
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).srw_msb.msb =
      Expression.eval env (var { index := offset + 5 }) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  simp only [evalU16MSB]
  exact ProvableType.eval_field env (var { index := offset + 5 })

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_isSrl
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).is_srl =
      Expression.eval env (srSrl offset) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  exact ProvableType.eval_field env (srSrl offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_isSra
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).is_sra =
      Expression.eval env (srSra offset) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  exact ProvableType.eval_field env (srSra offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_isSrlw
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).is_srlw =
      Expression.eval env (srSrlw offset) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  exact ProvableType.eval_field env (srSrlw offset)

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustColumns_isSraw
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    (shiftRightRustColumns env input offset).is_sraw =
      Expression.eval env (srSraw offset) := by
  unfold shiftRightRustColumns
  rw [ShiftRightChip.eval_columns]
  exact ProvableType.eval_field env (srSraw offset)

private def srRustMeaning
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := shiftRightRustColumns env input offset
  List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.adapter.op_b_memory.prev_value[3]
        cols.b_msb cols.is_sra) ∧
  List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.adapter.op_b_memory.prev_value[1]
        cols.b_msb cols.is_sraw) ∧
  List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.a[1] cols.srw_msb (cols.is_srlw + cols.is_sraw)) ∧
  List.Forall (· = 0)
      (Extracted.CPUState.asserts (F := ZMod p) cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ∧
  List.Forall (· = 0)
      (Extracted.ALUTypeReader.asserts (F := ZMod p) cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_srl * 7 + cols.is_sra * 8 +
          cols.is_srlw * 22 + cols.is_sraw * 23)
        cols.a cols.adapter
        (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
        (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ∧
  ShiftRightChip.AssertSpec cols

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (shiftRightChipOracle.nativeAssertZeros
          (shiftRightRustColumns env input offset)) ↔
      srRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, shiftRightChipOracle,
    srRustMeaning]
  exact shiftRightExtractedAssertionsDecompose
    (shiftRightRustColumns env input offset)

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
-- Measured floor bracket (40000, 60000] after the `simp only` narrowing; kept at ~4x.
set_option maxHeartbeats 240000 in
private theorem shiftRightCoreAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftRightCore.main (srCols input offset)).operations
            (offset + 37))) ↔
      ShiftRightChip.CoreSpec (Eval.eval env (srCols input offset)) := by
  let ops :=
    (ShiftRightCore.main (srCols input offset)).operations (offset + 37)
  have hlookups : ops.lookups = [] := by
    simp only [ops, ShiftRightCore.main, Gadgets.Equality.main, circuit_norm]
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
      simp only [ops, Operations.FullGuarantees, ShiftRightCore.main,
        FormalAssertion.toSubcircuit_interactions, equalityInteractions,
        circuit_norm]
    let colsValue := ProvableStruct.eval env (srCols input offset)
    have hvalue :
        colsValue = Eval.eval env (srCols input offset) :=
      (ProvableStruct.eval_eq_eval env (srCols input offset)).symm
    have hs := (FormalAssertion.original_soundness
      (ShiftRightCore.circuit (p := p)) (offset + 37) env
      (srCols input offset) colsValue
      (ProvableStruct.eval_eq_eval env (srCols input offset))
      trivial hfull hguarantees).1
    rwa [hvalue] at hs
  · intro hspec
    let proverEnv : ProverEnvironment (ZMod p) :=
      { toEnvironment := env
        hint := ProverHint.empty (ZMod p) }
    have huses :
        proverEnv.UsesLocalWitnesses (offset + 37) ops := by
      have hlen : ops.localLength = 0 := by
        simp only [ops, ShiftRightCore.main, circuit_norm]
      rw [ProverEnvironment.usesLocalWitnesses_iff_flat,
        ProverEnvironment.usesLocalWitnessesFlat_iff_extends]
      intro i
      have hi : i.val < ops.localLength := by
        simpa only [FlatOperation.localLength_toFlat] using i.isLt
      rw [hlen] at hi
      omega
    let colsValue := ProvableStruct.eval env (srCols input offset)
    have hvalue :
        Eval.eval env (srCols input offset) = colsValue :=
      ProvableStruct.eval_eq_eval env (srCols input offset)
    have hspecValue : ShiftRightChip.CoreSpec colsValue := by
      rwa [hvalue] at hspec
    have hfull : ops.ConstraintsHold proverEnv :=
      (FormalAssertion.original_completeness
        (ShiftRightCore.circuit (p := p)) (offset + 37) proverEnv
        (srCols input offset) colsValue
        (by
          calc
            eval proverEnv (srCols input offset) =
                ProvableType.eval proverEnv.toEnvironment
                  (srCols input offset) := by
                    rw [CircuitType.eval_prover]
                    rfl
            _ = ProvableStruct.eval env (srCols input offset) := by
              dsimp only [proverEnv]
              calc
                ProvableType.eval env (srCols input offset) =
                    eval env (srCols input offset) :=
                  (CircuitType.eval_verifier env (srCols input offset)).symm
                _ = ProvableStruct.eval env (srCols input offset) :=
                  ProvableStruct.eval_eq_eval env (srCols input offset)
            _ = colsValue := rfl)
        trivial huses hspecValue).1
    change ops.ConstraintsHold env at hfull
    exact hconstraints.mp hfull

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightGateEval
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    Expression.eval env (srGate offset) =
      (shiftRightRustColumns env input offset).is_srl +
        (shiftRightRustColumns env input offset).is_sra +
        (shiftRightRustColumns env input offset).is_srlw +
        (shiftRightRustColumns env input offset).is_sraw := by
  simp only [srGate, Expression.eval]
  rw [shiftRightRustColumns_isSrl, shiftRightRustColumns_isSra,
    shiftRightRustColumns_isSrlw, shiftRightRustColumns_isSraw]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightCpuAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.CPUState.asserts cols.state
          #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
          8 (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.CPUState.main
            ⟨input.state,
              #v[input.state.pc[0] + 4,
                input.state.pc[1], input.state.pc[2]],
              8, input.is_real⟩).operations offset)) := by
  dsimp only
  let cols := shiftRightRustColumns env input offset
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4,
        input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  have hreal :
      (ProvableStruct.eval env cpuInput).is_real =
        cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw := by
    calc
      (ProvableStruct.eval env cpuInput).is_real =
          Expression.eval env input.is_real := by
        simp only [cpuInput, ProvableStruct.structEvalLiteralProc]
      _ = Expression.eval env (srGate offset) := hinputReal
      _ = cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw := by
        exact shiftRightGateEval env input offset
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpuInput offset cols.state
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
    8 (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) hreal
  dsimp only [cpuInput, cols] at hCpu
  exact hCpu

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightU16B3Assertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts (F := ZMod p)
          cols.adapter.op_b_memory.prev_value[3]
          cols.b_msb cols.is_sra) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.adapter.op_b_memory.prev_value[3],
              { msb := var { index := offset + 4 } },
              srSra offset⟩).operations (offset + 37))) := by
  dsimp only
  let cols := shiftRightRustColumns env input offset
  let u16Input : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨input.adapter.op_b_memory.prev_value[3],
      { msb := var { index := offset + 4 } },
      srSra offset⟩
  have hU16 := u16MSBAssertions env u16Input (offset + 37)
    cols.adapter.op_b_memory.prev_value[3]
    cols.b_msb.msb cols.is_sra
    (shiftRightRustColumns_isSra env input offset).symm
    (shiftRightRustColumns_bMsb env input offset).symm
  dsimp only [u16Input, cols] at hU16
  exact hU16

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightU16B1Assertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts (F := ZMod p)
          cols.adapter.op_b_memory.prev_value[1]
          cols.b_msb cols.is_sraw) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨input.adapter.op_b_memory.prev_value[1],
              { msb := var { index := offset + 4 } },
              srSraw offset⟩).operations (offset + 37))) := by
  dsimp only
  let cols := shiftRightRustColumns env input offset
  let u16Input : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨input.adapter.op_b_memory.prev_value[1],
      { msb := var { index := offset + 4 } },
      srSraw offset⟩
  have hU16 := u16MSBAssertions env u16Input (offset + 37)
    cols.adapter.op_b_memory.prev_value[1]
    cols.b_msb.msb cols.is_sraw
    (shiftRightRustColumns_isSraw env input offset).symm
    (shiftRightRustColumns_bMsb env input offset).symm
  dsimp only [u16Input, cols] at hU16
  exact hU16

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightU16WordAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts (F := ZMod p)
          cols.a[1] cols.srw_msb (cols.is_srlw + cols.is_sraw)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main
            ⟨(srA offset)[1],
              { msb := var { index := offset + 5 } },
              srSrlw offset + srSraw offset⟩).operations
                (offset + 37))) := by
  dsimp only
  let cols := shiftRightRustColumns env input offset
  let u16Input : Var U16MSBOperation.Inputs (ZMod p) :=
    ⟨(srA offset)[1],
      { msb := var { index := offset + 5 } },
      srSrlw offset + srSraw offset⟩
  have hreal :
      Expression.eval env (srSrlw offset + srSraw offset) =
        cols.is_srlw + cols.is_sraw := by
    simp only [Expression.eval]
    rw [shiftRightRustColumns_isSrlw,
      shiftRightRustColumns_isSraw]
  have hU16 := u16MSBAssertions env u16Input (offset + 37)
    cols.a[1] cols.srw_msb.msb (cols.is_srlw + cols.is_sraw)
    hreal
    (shiftRightRustColumns_srwMsb env input offset).symm
  dsimp only [u16Input, cols] at hU16
  exact hU16

private theorem shiftRightAluAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    let cols := shiftRightRustColumns env input offset
    (List.Forall (· = 0)
        (Extracted.ALUTypeReader.asserts cols.state.clk_high
          (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
          cols.state.pc
          (cols.is_srl * 7 + cols.is_sra * 8 +
            cols.is_srlw * 22 + cols.is_sraw * 23)
          cols.a cols.adapter
          (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
          (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)) ∧
        cols.adapter.op_a_0 = 0) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ALUTypeReader.main
              (srAluInput input offset)).operations (offset + 37))) ∧
        cols.adapter.op_a_0 = 0) := by
  dsimp only
  let cols := shiftRightRustColumns env input offset
  let aluInput := srAluInput input offset
  have hreal :
      (ProvableStruct.eval env aluInput).is_real =
        cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw := by
    calc
      (ProvableStruct.eval env aluInput).is_real =
          Expression.eval env input.is_real := by
        simp only [aluInput, srAluInput,
          ProvableStruct.structEvalLiteralProc]
      _ = Expression.eval env (srGate offset) := hinputReal
      _ = cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw :=
        shiftRightGateEval env input offset
  have htrusted :
      (ProvableStruct.eval env aluInput).is_trusted =
        cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw := by
    calc
      (ProvableStruct.eval env aluInput).is_trusted =
          Expression.eval env input.is_real := by
        simp only [aluInput, srAluInput,
          ProvableStruct.structEvalLiteralProc]
      _ = Expression.eval env (srGate offset) := hinputReal
      _ = cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw :=
        shiftRightGateEval env input offset
  have hcols :
      ProvableStruct.eval env aluInput.cols = cols.adapter := by
    change ProvableStruct.eval env input.adapter = cols.adapter
    rw [shiftRightRustColumns_adapter]
    exact (ProvableStruct.eval_eq_eval env input.adapter).symm
  have ha := shiftRightRustColumns_a env input offset
  have hw0 :
      Expression.eval env aluInput.wv0 = cols.a[0] := by
    exact (ProvableType.getElem_eval_fields env (srA offset) 0
      (by decide)).trans (congrArg (fun value => value[0]) ha.symm)
  have hw1 :
      Expression.eval env aluInput.wv1 = cols.a[1] := by
    exact (ProvableType.getElem_eval_fields env (srA offset) 1
      (by decide)).trans (congrArg (fun value => value[1]) ha.symm)
  have hw2 :
      Expression.eval env aluInput.wv2 = cols.a[2] := by
    exact (ProvableType.getElem_eval_fields env (srA offset) 2
      (by decide)).trans (congrArg (fun value => value[2]) ha.symm)
  have hw3 :
      Expression.eval env aluInput.wv3 = cols.a[3] := by
    exact (ProvableType.getElem_eval_fields env (srA offset) 3
      (by decide)).trans (congrArg (fun value => value[3]) ha.symm)
  have hAlu := CanonicalReader.aluTypeAssertions
    (p := p) env aluInput (offset + 37)
    cols.state.clk_high
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
    (cols.is_srl * 7 + cols.is_sra * 8 +
      cols.is_srlw * 22 + cols.is_sraw * 23)
    (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
    (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw)
    cols.state.pc cols.a cols.adapter
    hreal htrusted hcols hw0 hw1 hw2 hw3 rfl
  dsimp only [aluInput, cols] at hAlu
  exact hAlu

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightCoreSpec_opA0
    (cols : ShiftRightChip.Columns (ZMod p)) :
    ShiftRightChip.CoreSpec cols → cols.adapter.op_a_0 = 0 := by
  simp only [ShiftRightChip.CoreSpec]
  tauto

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightSrlAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (srSrl offset * (srSrl offset - 1), 0)).operations
              (offset + 37))) ↔
      cols.is_srl * (cols.is_srl - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftRightRustColumns_isSrl]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightSraAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (srSra offset * (srSra offset - 1), 0)).operations
              (offset + 37))) ↔
      cols.is_sra * (cols.is_sra - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftRightRustColumns_isSra]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightSrlwAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (srSrlw offset * (srSrlw offset - 1), 0)).operations
              (offset + 37))) ↔
      cols.is_srlw * (cols.is_srlw - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftRightRustColumns_isSrlw]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightSrawAssertions
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    let cols := shiftRightRustColumns env input offset
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((Gadgets.Equality.main (M := field)
            (srSraw offset * (srSraw offset - 1), 0)).operations
              (offset + 37))) ↔
      cols.is_sraw * (cols.is_sraw - 1) = 0 := by
  dsimp only
  rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rw [eval_sub]
  simp only [Expression.eval]
  rw [shiftRightRustColumns_isSraw]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightCoreAssertionsRust
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftRightCore.main (srCols input offset)).operations
            (offset + 37))) ↔
      ShiftRightChip.CoreSpec
        (shiftRightRustColumns env input offset) := by
  exact shiftRightCoreAssertions env input offset

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightInputBoolean
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    Expression.eval env (input.is_real * (input.is_real - 1)) = 0 ↔
      let cols := shiftRightRustColumns env input offset
      (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) *
        (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw - 1) = 0 := by
  dsimp only
  simp only [Expression.eval]
  rw [eval_sub, hinputReal, shiftRightGateEval env input offset]
  simp only [Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightGateBoolean
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    Expression.eval env (srGate offset * (srGate offset - 1)) = 0 ↔
      let cols := shiftRightRustColumns env input offset
      (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) *
        (cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw - 1) = 0 := by
  dsimp only
  simp only [Expression.eval]
  rw [eval_sub, shiftRightGateEval env input offset]
  simp only [Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightSelectorLink
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    Expression.eval env (input.is_real - srGate offset) = 0 := by
  rw [eval_sub, hinputReal, sub_self]

private theorem shiftRightMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    srRustMeaning env input offset ↔
      srNativeMeaning env input offset := by
  let cols := shiftRightRustColumns env input offset
  have hCpu := shiftRightCpuAssertions env input offset hinputReal
  have hU16B3 := shiftRightU16B3Assertions env input offset
  have hU16B1 := shiftRightU16B1Assertions env input offset
  have hU16Word := shiftRightU16WordAssertions env input offset
  have hAlu := shiftRightAluAssertions env input offset hinputReal
  have hSrl := shiftRightSrlAssertions env input offset
  have hSra := shiftRightSraAssertions env input offset
  have hSrlw := shiftRightSrlwAssertions env input offset
  have hSraw := shiftRightSrawAssertions env input offset
  have hCore := shiftRightCoreAssertionsRust env input offset
  have hInputBool := shiftRightInputBoolean env input offset hinputReal
  have hGateBool := shiftRightGateBoolean env input offset
  have hLink := shiftRightSelectorLink env input offset hinputReal
  have hCoreOpA0 :
      ShiftRightChip.CoreSpec cols → cols.adapter.op_a_0 = 0 :=
    shiftRightCoreSpec_opA0 cols
  have hNativeCoreOpA0 :
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((ShiftRightCore.main (srCols input offset)).operations
              (offset + 37))) →
        cols.adapter.op_a_0 = 0 :=
    fun h => hCoreOpA0 (hCore.mp h)
  unfold srRustMeaning srNativeMeaning
  dsimp only [cols] at hCpu hU16B3 hU16B1 hU16Word hAlu
  dsimp only [cols] at hSrl hSra hSrlw hSraw hCore hInputBool
  dsimp only [cols] at hCoreOpA0 hNativeCoreOpA0
  dsimp only [cols]
  simp only [ShiftRightChip.AssertSpec]
  constructor
  · rintro ⟨hU16B3Rust, hU16B1Rust, hU16WordRust,
      hCpuRust, hAluRust, hSrlRust, hSraRust, hSrlwRust,
      hSrawRust, hGateRust, hCoreRust⟩
    have hU16B3Native := hU16B3.mp hU16B3Rust
    have hU16B1Native := hU16B1.mp hU16B1Rust
    have hU16WordNative := hU16Word.mp hU16WordRust
    have hCpuNative := hCpu.mp hCpuRust
    have hCoreNative := hCore.mpr hCoreRust
    have hopA0 := hCoreOpA0 hCoreRust
    have hAluNative := (hAlu.mp ⟨hAluRust, hopA0⟩).1
    have hInputNative := hInputBool.mpr hGateRust
    have hGateNative := hGateBool.mpr hGateRust
    have hSrlNative := hSrl.mpr hSrlRust
    have hSraNative := hSra.mpr hSraRust
    have hSrlwNative := hSrlw.mpr hSrlwRust
    have hSrawNative := hSraw.mpr hSrawRust
    exact ⟨hCpuNative, hU16B3Native, hU16B1Native,
      hU16WordNative, hAluNative, hInputNative, hLink,
      hSrlNative, hSraNative, hSrlwNative, hSrawNative,
      hGateNative, hCoreNative⟩
  · rintro ⟨hCpuNative, hU16B3Native, hU16B1Native,
      hU16WordNative, hAluNative, _hInputNative,
      _hLinkNative, hSrlNative, hSraNative, hSrlwNative,
      hSrawNative, hGateNative, hCoreNative⟩
    have hU16B3Rust := hU16B3.mpr hU16B3Native
    have hU16B1Rust := hU16B1.mpr hU16B1Native
    have hU16WordRust := hU16Word.mpr hU16WordNative
    have hCpuRust := hCpu.mpr hCpuNative
    have hCoreRust := hCore.mp hCoreNative
    have hopA0 := hNativeCoreOpA0 hCoreNative
    have hAluRust := (hAlu.mpr ⟨hAluNative, hopA0⟩).1
    have hGateRust := hGateBool.mp hGateNative
    have hSrlRust := hSrl.mp hSrlNative
    have hSraRust := hSra.mp hSraNative
    have hSrlwRust := hSrlw.mp hSrlwNative
    have hSrawRust := hSraw.mp hSrawNative
    exact ⟨hU16B3Rust, hU16B1Rust, hU16WordRust,
      hCpuRust, hAluRust, hSrlRust, hSraRust,
      hSrlwRust, hSrawRust, hGateRust, hCoreRust⟩

private theorem shiftRightConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    List.Forall (· = 0)
        (shiftRightChipOracle.nativeAssertZeros
          (shiftRightRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftRightChip.main input).operations offset)) :=
  (shiftRightExtractedAssertionsDecompose
      (shiftRightRustColumns env input offset)).trans
    ((shiftRightMeaningFaithful env input offset hinputReal).trans
      (shiftRightNativeAssertionsDecompose env input offset).symm)

private theorem shiftRightRustColumns_eq_output
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    shiftRightRustColumns env input offset =
      Eval.eval env
        ((ShiftRightChip.elaborated (p := p)).output input offset) := by
  rw [ShiftRightChip.directOutput_eq]
  unfold shiftRightRustColumns srCols srA srCBits srShiftU16
    srLower srHigher srLimbResult srSrl srSra srSrlw srSraw
  rw [ShiftRightChip.eval_columns, ShiftRightChip.eval_columns]
  simp only [ProvableType.varFromOffset_fields]

theorem shiftRightChip_constraints_faithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : ShiftRightChip.Columns (ZMod p))
    (hbind : BindsChipOutput ShiftRightChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    List.Forall (· = 0)
        (shiftRightChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((ShiftRightChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (ShiftRightChip.elaborated (p := p)) hbind
  rw [← ProvableStruct.eval_eq_eval] at hbind
  have hcolumns : shiftRightRustColumns env input offset = cols :=
    (shiftRightRustColumns_eq_output env input offset).trans hbind
  rw [← hcolumns]
  exact shiftRightConstraintsFaithfulOutput env input offset hinputReal

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightChipLocals_thirtyTwo {F : Type}
    (cols : ShiftRightChip.Columns F) :
    (shiftRightChipLocals cols)[32] = cols.is_srl := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightChipLocals_thirtyThree {F : Type}
    (cols : ShiftRightChip.Columns F) :
    (shiftRightChipLocals cols)[33] = cols.is_sra := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightChipLocals_thirtyFour {F : Type}
    (cols : ShiftRightChip.Columns F) :
    (shiftRightChipLocals cols)[34] = cols.is_srlw := by
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightChipLocals_thirtyFive {F : Type}
    (cols : ShiftRightChip.Columns F) :
    (shiftRightChipLocals cols)[35] = cols.is_sraw := by
  rfl

private theorem shiftRightChipRowCodec_inputReal
    (cols : ShiftRightChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftRightChipRowCodec.assignment cols data
    Expression.eval assignment.environment
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar.is_real =
      Expression.eval assignment.environment
        (srGate
          (⟨ShiftRightChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowOffset) := by
  dsimp only
  let assignment := shiftRightChipRowCodec.assignment cols data
  rw [Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk]
  have hInput :
      Expression.eval
          (Environment.fromArray
            (inputFirstRow (shiftRightChipInput cols)
              (shiftRightChipLocals cols)) data)
          (varFromOffset ShiftRightChip.Inputs 0).is_real =
        (shiftRightChipInput cols).is_real := by
    rw [← ShiftRightChip.eval_inputIsReal]
    exact congrArg (fun value => value.is_real)
      (eval_inputFirstRow (shiftRightChipInput cols)
        (shiftRightChipLocals cols) data)
  have hSrl := eval_local_inputFirstRow (shiftRightChipInput cols)
    (shiftRightChipLocals cols) data 32 (by decide)
  have hSra := eval_local_inputFirstRow (shiftRightChipInput cols)
    (shiftRightChipLocals cols) data 33 (by decide)
  have hSrlw := eval_local_inputFirstRow (shiftRightChipInput cols)
    (shiftRightChipLocals cols) data 34 (by decide)
  have hSraw := eval_local_inputFirstRow (shiftRightChipInput cols)
    (shiftRightChipLocals cols) data 35 (by decide)
  change
    Expression.eval assignment.environment
        (varFromOffset ShiftRightChip.Inputs 0).is_real =
      assignment.environment.get (size ShiftRightChip.Inputs + 32) +
        assignment.environment.get (size ShiftRightChip.Inputs + 33) +
        assignment.environment.get (size ShiftRightChip.Inputs + 34) +
        assignment.environment.get (size ShiftRightChip.Inputs + 35)
  rw [show assignment.environment =
      Environment.fromArray
        (inputFirstRow (shiftRightChipInput cols)
          (shiftRightChipLocals cols)) data by rfl]
  rw [hInput]
  simp only [shiftRightChipInput]
  simp only [Expression.eval] at hSrl hSra hSrlw hSraw
  rw [shiftRightChipLocals_thirtyTwo] at hSrl
  rw [shiftRightChipLocals_thirtyThree] at hSra
  rw [shiftRightChipLocals_thirtyFour] at hSrlw
  rw [shiftRightChipLocals_thirtyFive] at hSraw
  simp only [shiftRightChipInput] at hSrl hSra hSrlw hSraw
  rw [hSrl, hSra, hSrlw, hSraw]

theorem shiftRightChip_constraints_constructive
    (rustCols : Extracted.ShiftRightOracle.ShiftRightCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftRightChipRowCodec.assignment
      (shiftRightChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (shiftRightChipOracle.assertZeros rustCols) ↔
      (⟨ShiftRightChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := shiftRightChipOracle.deconfigure rustCols
  let assignment := shiftRightChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput ShiftRightChip.main assignment.environment
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [ShiftRightChip.circuit_main_eq] at h
    exact h
  have hinputReal :
      Expression.eval assignment.environment
          (⟨ShiftRightChip.circuit (p := p)⟩ :
            Air.Flat.Component (ZMod p)).rowInputVar.is_real =
        Expression.eval assignment.environment
          (srGate
            (⟨ShiftRightChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOffset) :=
    shiftRightChipRowCodec_inputReal cols data
  have hfaithful := shiftRightChip_constraints_faithful
    assignment.environment
    (⟨ShiftRightChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨ShiftRightChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind hinputReal
  have hassertions :
      List.Forall (· = 0)
          (shiftRightChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨ShiftRightChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      ShiftRightChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (ShiftRightChip.circuit (p := p))
      assignment.environment shiftRightChip_lookups_empty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

omit [Fact (2 ^ 17 < p)] in
private theorem shiftRightRealEval
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    Expression.eval env input.is_real =
      (shiftRightRustColumns env input offset).is_srl +
        (shiftRightRustColumns env input offset).is_sra +
        (shiftRightRustColumns env input offset).is_srlw +
        (shiftRightRustColumns env input offset).is_sraw :=
  hinputReal.trans (shiftRightGateEval env input offset)

private theorem shiftRightStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    (((ShiftRightChip.exposedStateInteractions input).map
            ChannelInteraction.toRaw).map
              (AbstractInteraction.toAccess env)) =
      (((Extracted.ShiftRightOracle.ShiftRightCols.interactions
          (shiftRightChipReconfigure (shiftRightRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.State)) := by
  have hReal := shiftRightRealEval env input offset hinputReal
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
  simp only [ShiftRightChip.exposedStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.ShiftRightOracle.ShiftRightCols.interactions,
    shiftRightChipReconfigure,
    Extracted.ShiftRightOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    shiftRightRustColumns_state,
    ← ProvableStruct.eval_eq_eval,
    Expression.eval, hReal]

private theorem shiftRightByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    List.Perm
      (((ShiftRightChip.exposedByteInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))
      (((Extracted.ShiftRightOracle.ShiftRightCols.interactions
          (shiftRightChipReconfigure (shiftRightRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  haveI : NeZero p :=
    ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h6 : (6 : ZMod p).val = 6 := by
    have h : (6 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      omega
    exact ZMod.val_natCast_of_lt h
  have h3 : (3 : ZMod p).val = 3 := by
    have h : (3 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      omega
    exact ZMod.val_natCast_of_lt h
  have hRealVars :
      Expression.eval env input.is_real =
        Expression.eval env (srSrl offset) +
          Expression.eval env (srSra offset) +
          Expression.eval env (srSrlw offset) +
          Expression.eval env (srSraw offset) := by
    rw [hinputReal]
    simp only [srGate, Expression.eval]
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
  rw [shiftRightRustColumns_eq]
  simp only [ShiftRightChip.exposedByteInteractions,
    List.map_cons, List.map_nil, hBytePull]
  simp [Extracted.ShiftRightOracle.ShiftRightCols.interactions,
    shiftRightChipReconfigure,
    Extracted.ShiftRightOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    srA, srCBits,
    srLower, srHigher, srSrl, srSra, srSrlw, srSraw,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp, evalU16MSB,
    eval_sub, Expression.eval,
    h6, h3, hRealVars,
    ShiftRightChip.exposedWriteGate, Nat.add_assoc]
  simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
    eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval]
  exact
    (List.perm_append_comm
      (l₁ := [_, _]) (l₂ := [_, _, _])).append_right
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _]

private theorem shiftRightMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    List.Perm
      (((((ShiftRightChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.ShiftRightOracle.ShiftRightCols.interactions
          (shiftRightChipReconfigure (shiftRightRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Memory)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hRealVars :
      Expression.eval env input.is_real =
        env.get (offset + 32) + env.get (offset + 33) +
          env.get (offset + 34) + env.get (offset + 35) := by
    rw [hinputReal]
    simp only [srGate, srSrl, srSra, srSrlw, srSraw,
      Expression.eval]
  have hNegFlags :
      -env.get (offset + 35) +
          (-env.get (offset + 34) +
            (-env.get (offset + 33) + -env.get (offset + 32))) =
        -(env.get (offset + 32) + env.get (offset + 33) +
          env.get (offset + 34) + env.get (offset + 35)) := by
    ring
  have hDoubleNeg :
      -signedVal
          (-env.get (offset + 35) +
            (-env.get (offset + 34) +
              (-env.get (offset + 33) + -env.get (offset + 32)))) =
        signedVal
          (env.get (offset + 32) + env.get (offset + 33) +
            env.get (offset + 34) + env.get (offset + 35)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
  have hNegReal :
      -signedVal
          (env.get (offset + 32) + env.get (offset + 33) +
            env.get (offset + 34) + env.get (offset + 35)) =
        signedVal
          (-env.get (offset + 35) +
            (-env.get (offset + 34) +
              (-env.get (offset + 33) + -env.get (offset + 32)))) := by
    rw [hNegFlags, signedVal_neg hp2]
  have hNegOpC :
      -signedVal
          (env.get (offset + 32) + env.get (offset + 33) +
            env.get (offset + 34) + env.get (offset + 35) -
            Expression.eval env input.adapter.imm_c) =
        signedVal
          (Expression.eval env input.adapter.imm_c -
            (env.get (offset + 32) + env.get (offset + 33) +
              env.get (offset + 34) + env.get (offset + 35))) := by
    rw [(by ring :
      Expression.eval env input.adapter.imm_c -
          (env.get (offset + 32) + env.get (offset + 33) +
            env.get (offset + 34) + env.get (offset + 35)) =
        -(env.get (offset + 32) + env.get (offset + 33) +
          env.get (offset + 34) + env.get (offset + 35) -
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
  rw [shiftRightRustColumns_eq]
  simp only [ShiftRightChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.ShiftRightOracle.ShiftRightCols.interactions,
    shiftRightChipReconfigure,
    Extracted.ShiftRightOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    srA, srSrl, srSra, srSrlw, srSraw,
    ShiftRightChip.exposedWriteGate,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, hRealVars]
  simp only [← ProvableStruct.eval_eq_eval, eval_cpuState,
    eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field]
  simp only [eval_sub]
  rw [hRealVars]
  simp only [hDoubleNeg, hNegReal, hNegOpC]
  exact (List.perm_append_comm
    (l₁ := [_, _, _, _]) (l₂ := [_])).append_left [_]

private theorem shiftRightProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    (((((ShiftRightChip.exposedProgramInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.ShiftRightOracle.ShiftRightCols.interactions
          (shiftRightChipReconfigure (shiftRightRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have hRealVars :
      Expression.eval env input.is_real =
        env.get (offset + 32) + env.get (offset + 33) +
          env.get (offset + 34) + env.get (offset + 35) := by
    rw [hinputReal]
    simp only [srGate, srSrl, srSra, srSrlw, srSraw,
      Expression.eval]
  have hNegFlags :
      -env.get (offset + 35) +
          (-env.get (offset + 34) +
            (-env.get (offset + 33) + -env.get (offset + 32))) =
        -(env.get (offset + 32) + env.get (offset + 33) +
          env.get (offset + 34) + env.get (offset + 35)) := by
    ring
  have hDoubleNeg :
      -signedVal
          (-env.get (offset + 35) +
            (-env.get (offset + 34) +
              (-env.get (offset + 33) + -env.get (offset + 32)))) =
        signedVal
          (env.get (offset + 32) + env.get (offset + 33) +
            env.get (offset + 34) + env.get (offset + 35)) := by
    rw [hNegFlags, signedVal_neg hp2, neg_neg]
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
  rw [shiftRightRustColumns_eq]
  simp only [ShiftRightChip.exposedProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.ShiftRightOracle.ShiftRightCols.interactions,
    shiftRightChipReconfigure,
    Extracted.ShiftRightOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ALUTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    srA, srSrl, srSra, srSrlw, srSraw,
    ShiftRightChip.exposedOpcode,
    eval_cpuState, eval_aluTypeReader, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Opcode.ofNat, hRealVars]
  exact hDoubleNeg

private theorem shiftRightUnexpectedInteractionsEmpty
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((ShiftRightChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((ShiftRightChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (ShiftRightChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [ShiftRightChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem shiftRightChip_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : ShiftRightChip.Columns (ZMod p))
    (hbind : BindsChipOutput ShiftRightChip.main env input offset cols)
    (hinputReal :
      Expression.eval env input.is_real =
        Expression.eval env (srGate offset)) :
    List.Perm
      (nativeAccesses env
        ((ShiftRightChip.main input).operations offset))
      (shiftRightChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (ShiftRightChip.elaborated (p := p)) hbind
  rw [← ProvableStruct.eval_eq_eval] at hbind
  have hcolumns : shiftRightRustColumns env input offset = cols :=
    (shiftRightRustColumns_eq_output env input offset).trans hbind
  subst cols
  let rustAccesses :=
    (Extracted.ShiftRightOracle.ShiftRightCols.interactions
      (shiftRightChipReconfigure (shiftRightRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [shiftRightUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, shiftRightChipOracle]
  rw [ShiftRightChip.interactionsWith_main_state_exposed_eq,
    ShiftRightChip.interactionsWith_main_byte_eq,
    ShiftRightChip.interactionsWith_main_memory_eq,
    ShiftRightChip.interactionsWith_main_program_eq]
  have hState :=
    shiftRightStateInteractionsFaithful
      (p := p) env input offset hinputReal
  have hByte :=
    shiftRightByteInteractionsFaithful
      (p := p) env input offset hinputReal
  have hMemory :=
    shiftRightMemoryInteractionsFaithful
      (p := p) env input offset hinputReal
  have hProgram :=
    shiftRightProgramInteractionsFaithful
      (p := p) env input offset hinputReal
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem shiftRightChip_interactions_constructive
    (rustCols : Extracted.ShiftRightOracle.ShiftRightCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := shiftRightChipRowCodec.assignment
      (shiftRightChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (shiftRightChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := shiftRightChipOracle.deconfigure rustCols
  let assignment := shiftRightChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput ShiftRightChip.main assignment.environment
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨ShiftRightChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [ShiftRightChip.circuit_main_eq] at h
    exact h
  have hfaithful := shiftRightChip_interactions_faithful
    (p := p) assignment.environment
    (⟨ShiftRightChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨ShiftRightChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
    (shiftRightChipRowCodec_inputReal cols data)
  rw [nativeAccesses_component_eq_rowOperations
    (ShiftRightChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    ShiftRightChip.circuit_main_eq] using hfaithful

theorem shiftRightChip_faithful :
    ChipFaithful (p := p) ShiftRightChip.Inputs
      ShiftRightChip.Columns Extracted.ShiftRightOracle.ShiftRightCols
      ShiftRightChip.circuit shiftRightChipRowCodec
      shiftRightChipOracle where
  constraints := shiftRightChip_constraints_constructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (shiftRightChip_interactions_constructive (p := p) rustCols data)

end SP1Clean.Faithful
