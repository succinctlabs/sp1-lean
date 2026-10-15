import SP1Clean.Extracted.MulOperation
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.RTypeReader
import SP1Clean.Faithful.U16MSBOperation
import SP1Clean.Faithful.U16toU8OperationSafe
import SP1Clean.Extracted.ChipOracle.Mul
import SP1Clean.Proofs.Chips.MulChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `Mul`

This file relates the native Clean `MulChip` row to the complete Rust-generated row-level oracle
for pinned SP1 v6.4.0.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open SP1Clean.Circuits.Types
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Copy the shared `Circuits.Types.MulOperation` arithmetic block into the Mul oracle's chip-private
`MulOperation` row (same field names; the two nested byte-decomposition blocks and the MSB block are
rebuilt into the oracle's embedded struct copies). -/
def mulOracleOperation {F : Type} (cols : Circuits.Types.MulOperation F) :
    Extracted.MulOracle.MulOperation F :=
  { carry := cols.carry
    product := cols.product
    b_lower_byte := { low_bytes := cols.b_lower_byte.low_bytes }
    c_lower_byte := { low_bytes := cols.c_lower_byte.low_bytes }
    b_msb := cols.b_msb
    c_msb := cols.c_msb
    product_msb := { msb := cols.product_msb.msb }
    b_sign_extend := cols.b_sign_extend
    c_sign_extend := cols.c_sign_extend }

/-- Inverse of `mulOracleOperation`. -/
def mulNativeOperation {F : Type} (cols : Extracted.MulOracle.MulOperation F) :
    Circuits.Types.MulOperation F :=
  { carry := cols.carry
    product := cols.product
    b_lower_byte := { low_bytes := cols.b_lower_byte.low_bytes }
    c_lower_byte := { low_bytes := cols.c_lower_byte.low_bytes }
    b_msb := cols.b_msb
    c_msb := cols.c_msb
    product_msb := { msb := cols.product_msb.msb }
    b_sign_extend := cols.b_sign_extend
    c_sign_extend := cols.c_sign_extend }

/-- Whole-chip row reconfiguration. The reader blocks and the flag/result columns are already the
canonical generated substrate; the arithmetic block is copied into Rust's chip-private operation
row. This is not an operation-level faithfulness claim. -/
def mulChipReconfigure {F : Type} (cols : MulChip.Columns F) :
    Extracted.MulOracle.MulCols F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    mul_operation := mulOracleOperation cols.mul_operation
    is_mul := cols.is_mul
    is_mulh := cols.is_mulh
    is_mulhu := cols.is_mulhu
    is_mulhsu := cols.is_mulhsu
    is_mulw := cols.is_mulw }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def mulChipDeconfigure {F : Type} (cols : Extracted.MulOracle.MulCols F) :
    MulChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    mul_operation := mulNativeOperation cols.mul_operation
    is_mul := cols.is_mul
    is_mulh := cols.is_mulh
    is_mulhu := cols.is_mulhu
    is_mulhsu := cols.is_mulhsu
    is_mulw := cols.is_mulw }

/-- SP1 Rust's complete Mul-chip oracle, viewed from the native Lean row. -/
def mulChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F MulChip.Columns Extracted.MulOracle.MulCols where
  reconfigure := mulChipReconfigure
  deconfigure := mulChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.MulOracle.MulCols.asserts
  interactions := Extracted.MulOracle.MulCols.interactions

def mulChipInput {F : Type} (cols : MulChip.Columns F) : MulChip.Inputs F :=
  { state := cols.state
    adapter := cols.adapter
    isMul := cols.is_mul
    isMulh := cols.is_mulh
    isMulhu := cols.is_mulhu
    isMulhsu := cols.is_mulhsu
    isMulw := cols.is_mulw }

def mulChipLocals {F : Type} (cols : MulChip.Columns F) : Vector F 49 :=
  Vector.cast (by rfl) (toElements cols.mul_operation ++ cols.a)

def mulChipPhysicalRow {F : Type} (cols : MulChip.Columns F) : Array F :=
  inputFirstRow (mulChipInput cols) (mulChipLocals cols)

def mulChipOperationOfLocals {F : Type} (locals : Vector F 49) :
    Circuits.Types.MulOperation F :=
  fromElements (Vector.cast (by rfl) (locals.take 45))

def mulChipAOfLocals {F : Type} (locals : Vector F 49) : Word F :=
  Vector.cast (by rfl) (locals.drop 45)

def mulChipColumnsOfInput {F : Type}
    (input : MulChip.Inputs F) (locals : Vector F 49) : MulChip.Columns F :=
  ⟨input.state, input.adapter, mulChipAOfLocals locals, mulChipOperationOfLocals locals,
    input.isMul, input.isMulh, input.isMulhu, input.isMulhsu, input.isMulw⟩

private theorem mulChipOperationOfLocals_roundtrip {F : Type}
    (cols : MulChip.Columns F) :
    mulChipOperationOfLocals (mulChipLocals cols) =
      cols.mul_operation := by
  refine (ProvableType.ext_iff (α := Circuits.Types.MulOperation) _ _).mpr
    (fun i hi => ?_)
  unfold mulChipOperationOfLocals mulChipLocals
  rw [ProvableType.toElements_fromElements, Vector.getElem_cast,
    Vector.getElem_take, Vector.getElem_cast]
  have hsize : size Circuits.Types.MulOperation = 45 := rfl
  rw [hsize] at hi
  simp [hsize, hi]

private theorem mulChipAOfLocals_roundtrip {F : Type}
    (cols : MulChip.Columns F) :
    mulChipAOfLocals (mulChipLocals cols) = cols.a := by
  apply Vector.ext
  intro i hi
  unfold mulChipAOfLocals mulChipLocals
  rw [Vector.getElem_cast, Vector.getElem_drop, Vector.getElem_cast,
    Vector.getElem_append_right (by have : size Circuits.Types.MulOperation = 45 := rfl; omega)
      (by have : size Circuits.Types.MulOperation = 45 := rfl; omega)]
  congr 1
  have : size Circuits.Types.MulOperation = 45 := rfl
  omega

theorem mulChipColumnsOfInput_roundtrip {F : Type} (cols : MulChip.Columns F) :
    mulChipColumnsOfInput (mulChipInput cols) (mulChipLocals cols) = cols := by
  unfold mulChipColumnsOfInput mulChipInput
  rw [MulChip.Columns.mk.injEq]
  exact ⟨rfl, rfl, mulChipAOfLocals_roundtrip cols,
    mulChipOperationOfLocals_roundtrip cols, rfl, rfl, rfl, rfl, rfl⟩

omit [Fact (2 ^ 24 < p)] in
private theorem eval_mulChipOperationOfLocals
    (input : MulChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 49) (data : ProverData (ZMod p)) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (varFromOffset Circuits.Types.MulOperation (F := ZMod p)
          (size MulChip.Inputs)) =
      mulChipOperationOfLocals locals := by
  refine (ProvableType.ext_iff (α := Circuits.Types.MulOperation) _ _).mpr
    (fun i hi => ?_)
  rw [ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  unfold mulChipOperationOfLocals
  rw [ProvableType.toElements_fromElements, Vector.getElem_cast,
    Vector.getElem_take]
  have hlocal := eval_local_inputFirstRow input locals data i (by
    have hsize : size Circuits.Types.MulOperation = 45 := rfl
    rw [hsize] at hi
    omega)
  simp only [Expression.eval] at hlocal
  simpa only [Nat.add_assoc] using hlocal

omit [Fact (2 ^ 24 < p)] in
private theorem eval_mulChipAOfLocals
    (input : MulChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 49) (data : ProverData (ZMod p)) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 4 (fun i =>
          (var { index := size MulChip.Inputs + 45 + i } :
            Expression (ZMod p))) : Word (Expression (ZMod p))) =
      mulChipAOfLocals locals := by
  apply Vector.ext
  intro i hi
  rw [show
      (Eval.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 4 (fun i =>
          (var { index := size MulChip.Inputs + 45 + i } :
            Expression (ZMod p))) : Word (Expression (ZMod p))))[i] =
        Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data)
          (Vector.mapRange 4 (fun i =>
            (var { index := size MulChip.Inputs + 45 + i } :
              Expression (ZMod p))) : Word (Expression (ZMod p)))[i] from
      (ProvableType.getElem_eval_fields
        (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 4 (fun i =>
          (var { index := size MulChip.Inputs + 45 + i } :
            Expression (ZMod p))) : Word (Expression (ZMod p)))
        i hi).symm]
  rw [Vector.getElem_mapRange]
  unfold mulChipAOfLocals
  rw [Vector.getElem_cast, Vector.getElem_drop]
  have hlocal := eval_local_inputFirstRow input locals data (45 + i) (by
    omega)
  simpa only [Nat.add_assoc] using hlocal

theorem eval_mulChipDirectOutput
    (input : MulChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 49) (data : ProverData (ZMod p)) :
    ProvableType.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        ((MulChip.elaborated (p := p)).output
          (varFromOffset MulChip.Inputs 0) (size MulChip.Inputs)) =
      mulChipColumnsOfInput input locals := by
  rw [MulChip.directOutput_eq]
  rw [← CircuitType.eval_expression, MulChip.eval_columns]
  unfold mulChipColumnsOfInput
  rw [MulChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [MulChip.eval_inputs, MulChip.Inputs.mk.injEq] at hinputEval
  exact ⟨hinputEval.1, hinputEval.2.1, eval_mulChipAOfLocals input locals data,
    eval_mulChipOperationOfLocals input locals data, hinputEval.2.2⟩

def mulChipRowCodec :
    ChipRowCodec MulChip.Inputs MulChip.Columns
      (MulChip.circuit (p := p)) where
  assignment cols data := {
    row := mulChipPhysicalRow cols
    input := mulChipInput cols
    width_eq := by
      rw [mulChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, MulChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (MulChip.circuit (p := p))
        (mulChipInput cols) (mulChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((MulChip.main _).output _) = _
      rw [MulChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (eval_mulChipDirectOutput (p := p) (mulChipInput cols)
        (mulChipLocals cols) data).trans
          (mulChipColumnsOfInput_roundtrip cols) }

private def mul_chip_operation (offset : ℕ) :
    Var Circuits.Types.MulOperation (ZMod p) :=
  varFromOffset Circuits.Types.MulOperation offset

private def mul_chip_a (offset : ℕ) : Word (Expression (ZMod p)) :=
  Vector.mapRange 4 fun i => var { index := offset + 45 + i }

private theorem forall_nil_iff {α : Type} (pred : α → Prop) :
    List.Forall pred [] ↔ True := Iff.rfl

private theorem forall_singleton_append {α : Type} {pred : α → Prop}
    {x : α} {xs : List α} (hx : pred x) (hxs : List.Forall pred xs) :
    List.Forall pred ([x] ++ xs) := by
  simpa only [List.forall_append, List.Forall, true_and] using And.intro hx hxs

private theorem forall_cons_elim {α : Type} {pred : α → Prop}
    {x : α} {xs : List α} (h : List.Forall pred (x :: xs)) :
    pred x ∧ List.Forall pred xs := by
  simpa only [List.forall_cons] using h

private theorem forall_singleton_append_elim
    {α : Type} {pred : α → Prop} {x : α} {xs : List α}
    (h : List.Forall pred ([x] ++ xs)) :
    pred x ∧ List.Forall pred xs := by
  simpa only [List.forall_append, List.Forall, true_and] using h

omit [Fact (2 ^ 24 < p)] in
private theorem mul_pred_of_bool {x : ZMod p} (h : x = 0 ∨ x = 1) :
    x * (x - 1) = 0 := by
  rcases h with h | h <;> simp [h]

private theorem mul_chip_constraints_decompose
    (env : Environment (ZMod p)) (input : Var MulChip.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((MulChip.main input).operations offset)) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              ⟨input.state,
                #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
                8, input.is_real⟩).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((MulOperation.main
              ⟨input.op_b_val, input.op_c_val, mul_chip_operation offset,
                input.is_real, input.isMul,
                input.isMulh, input.isMulhu,
                input.isMulhsu, input.isMulw, mul_chip_a offset⟩).operations
                  (offset + 49))) ∧
        Expression.eval env
          (input.isMul * (input.isMul - 1)) = 0 ∧
        Expression.eval env
          (input.isMulh * (input.isMulh - 1)) = 0 ∧
        Expression.eval env
          (input.isMulhu * (input.isMulhu - 1)) = 0 ∧
        Expression.eval env
          (input.isMulhsu * (input.isMulhsu - 1)) = 0 ∧
        Expression.eval env
          (input.isMulw * (input.isMulw - 1)) = 0 ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 ∧
        Expression.eval env input.adapter.op_a_0 = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RTypeReader.main
              ⟨input.adapter, input.is_real, input.is_real,
                input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536,
                input.state.pc,
                input.isMul * 11 +
                  input.isMulh * 12 +
                  input.isMulhu * 13 +
                  input.isMulhsu * 14 +
                  input.isMulw * 24,
                (mul_chip_a offset)[0], (mul_chip_a offset)[1],
                (mul_chip_a offset)[2], (mul_chip_a offset)[3]⟩).operations
                  (offset + 49))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              ⟨input.state.clk_high,
                input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
                input.adapter.op_a, mul_chip_a offset,
                input.is_real⟩).operations (offset + 49)))) := by
  simp only [nativeAssertZeros, MulChip.main,
    Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness, witnessIR,
    subcircuitWithAssertion, assertion, assertZero,
    Operations.localLength]
  simp only [Operations.constraints_append,
    Operations.constraints_witness,
    Operations.constraints_subcircuit,
    GeneralFormalCircuit.toSubcircuit_constraints,
    FormalAssertion.toSubcircuit_constraints,
    GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength,
    MulOperation.circuit_localLength,
    Readers.RTypeReader.circuit_localLength,
    Operations.constraints_assert, Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil,
    List.forall_append, List.forall_cons, forall_nil_iff]
  simp only [MulChip.Inputs.is_real, mul_chip_operation,
    mul_chip_a, Readers.CPUState.circuit,
    MulOperation.circuit, Readers.RTypeReader.circuit,
    Readers.RegisterWrite.circuit, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd, show size Circuits.Types.MulOperation = 45 by rfl,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange,
    true_and, and_true]

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

private theorem vec16_eta {F : Type} (value : Vector F 16) :
    #v[value[0], value[1], value[2], value[3],
      value[4], value[5], value[6], value[7],
      value[8], value[9], value[10], value[11],
      value[12], value[13], value[14], value[15]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem u16toU8_eta {F : Type}
    (cols : Circuits.Types.U16toU8Operation F) :
    ({ low_bytes :=
        #v[cols.low_bytes[0], cols.low_bytes[1],
          cols.low_bytes[2], cols.low_bytes[3]] } :
      Circuits.Types.U16toU8Operation F) = cols := by
  cases cols
  simp only
  rw [vec4_eta]

private theorem cpuState_eta {F : Type} (cols : Circuits.Types.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := #v[cols.pc[0], cols.pc[1], cols.pc[2]] } :
      Circuits.Types.CPUState F) = cols := by
  cases cols
  simp only
  rw [vec3_eta]

private theorem registerAccess_eta {F : Type}
    (cols : Circuits.Types.RegisterAccessCols F) :
    ({ prev_value :=
        #v[cols.prev_value[0], cols.prev_value[1],
          cols.prev_value[2], cols.prev_value[3]]
       access_timestamp := cols.access_timestamp } :
      Circuits.Types.RegisterAccessCols F) = cols := by
  cases cols
  simp only
  rw [vec4_eta]

private theorem rTypeReader_eta {F : Type}
    (cols : Circuits.Types.RTypeReader F) :
    ({ op_a := cols.op_a
       op_a_memory :=
        { prev_value :=
            #v[cols.op_a_memory.prev_value[0],
              cols.op_a_memory.prev_value[1],
              cols.op_a_memory.prev_value[2],
              cols.op_a_memory.prev_value[3]]
          access_timestamp := cols.op_a_memory.access_timestamp }
       op_a_0 := cols.op_a_0
       op_b := cols.op_b
       op_b_memory :=
        { prev_value :=
            #v[cols.op_b_memory.prev_value[0],
              cols.op_b_memory.prev_value[1],
              cols.op_b_memory.prev_value[2],
              cols.op_b_memory.prev_value[3]]
          access_timestamp := cols.op_b_memory.access_timestamp }
       op_c := cols.op_c
       op_c_memory :=
        { prev_value :=
            #v[cols.op_c_memory.prev_value[0],
              cols.op_c_memory.prev_value[1],
              cols.op_c_memory.prev_value[2],
              cols.op_c_memory.prev_value[3]]
          access_timestamp := cols.op_c_memory.access_timestamp } } :
      Circuits.Types.RTypeReader F) = cols := by
  cases cols
  simp only
  rw [registerAccess_eta, registerAccess_eta, registerAccess_eta]

private theorem mulOperation_eta {F : Type}
    (cols : Circuits.Types.MulOperation F) :
    ({ carry :=
        #v[cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3],
          cols.carry[4], cols.carry[5], cols.carry[6], cols.carry[7],
          cols.carry[8], cols.carry[9], cols.carry[10], cols.carry[11],
          cols.carry[12], cols.carry[13], cols.carry[14], cols.carry[15]]
       product :=
        #v[cols.product[0], cols.product[1], cols.product[2], cols.product[3],
          cols.product[4], cols.product[5], cols.product[6], cols.product[7],
          cols.product[8], cols.product[9], cols.product[10], cols.product[11],
          cols.product[12], cols.product[13], cols.product[14], cols.product[15]]
       b_lower_byte :=
        { low_bytes :=
            #v[cols.b_lower_byte.low_bytes[0],
              cols.b_lower_byte.low_bytes[1],
              cols.b_lower_byte.low_bytes[2],
              cols.b_lower_byte.low_bytes[3]] }
       c_lower_byte :=
        { low_bytes :=
            #v[cols.c_lower_byte.low_bytes[0],
              cols.c_lower_byte.low_bytes[1],
              cols.c_lower_byte.low_bytes[2],
              cols.c_lower_byte.low_bytes[3]] }
       b_msb := cols.b_msb
       c_msb := cols.c_msb
       product_msb := { msb := cols.product_msb.msb }
       b_sign_extend := cols.b_sign_extend
       c_sign_extend := cols.c_sign_extend } :
      Circuits.Types.MulOperation F) = cols := by
  cases cols with
  | mk carry product bLower cLower bMsb cMsb productMsb bSign cSign =>
      cases bLower
      cases cLower
      cases productMsb
      simp only
      rw [vec16_eta, vec16_eta, vec4_eta, vec4_eta]

/- Namespace bridges between the Mul oracle's embedded chip-private helper copies and the canonical
standalone generated modules. The two bodies are rendered from the same compiler output, so each
bridge is a definitional unfolding, not a mathematical claim. They let every heavy `MulOperation`
lemma below stay stated once against the standalone module (also consumed by the DivRem chip). -/

private theorem mulOracleOperation_eta {F : Type}
    (cols : Circuits.Types.MulOperation F) :
    ({ carry :=
        #v[cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3],
          cols.carry[4], cols.carry[5], cols.carry[6], cols.carry[7],
          cols.carry[8], cols.carry[9], cols.carry[10], cols.carry[11],
          cols.carry[12], cols.carry[13], cols.carry[14], cols.carry[15]]
       product :=
        #v[cols.product[0], cols.product[1], cols.product[2], cols.product[3],
          cols.product[4], cols.product[5], cols.product[6], cols.product[7],
          cols.product[8], cols.product[9], cols.product[10], cols.product[11],
          cols.product[12], cols.product[13], cols.product[14], cols.product[15]]
       b_lower_byte :=
        { low_bytes :=
            #v[cols.b_lower_byte.low_bytes[0],
              cols.b_lower_byte.low_bytes[1],
              cols.b_lower_byte.low_bytes[2],
              cols.b_lower_byte.low_bytes[3]] }
       c_lower_byte :=
        { low_bytes :=
            #v[cols.c_lower_byte.low_bytes[0],
              cols.c_lower_byte.low_bytes[1],
              cols.c_lower_byte.low_bytes[2],
              cols.c_lower_byte.low_bytes[3]] }
       b_msb := cols.b_msb
       c_msb := cols.c_msb
       product_msb := { msb := cols.product_msb.msb }
       b_sign_extend := cols.b_sign_extend
       c_sign_extend := cols.c_sign_extend } :
      Extracted.MulOracle.MulOperation F) = mulOracleOperation cols := by
  rw [mulOracleOperation, Extracted.MulOracle.MulOperation.mk.injEq]
  refine ⟨vec16_eta _, vec16_eta _, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
    · rw [Extracted.MulOracle.U16toU8Operation.mk.injEq]
      exact vec4_eta _

private theorem mulOracle_u16tou8safe_value_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values : Vector F 4) (low_bytes : Vector F 4) (is_real : F) :
    Extracted.MulOracle.U16toU8OperationSafe.value u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.value u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.MulOracle.U16toU8OperationSafe.value,
    Extracted.U16toU8OperationSafe.value]

private theorem mulOracle_u16tou8safe_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values : Vector F 4) (low_bytes : Vector F 4) (is_real : F) :
    Extracted.MulOracle.U16toU8OperationSafe.asserts u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.asserts u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.MulOracle.U16toU8OperationSafe.asserts,
    Extracted.U16toU8OperationSafe.asserts]

private theorem mulOracle_u16tou8safe_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (u16_values : Vector F 4) (low_bytes : Vector F 4) (is_real : F) :
    Extracted.MulOracle.U16toU8OperationSafe.interactions u16_values
        ⟨low_bytes⟩ is_real =
      Extracted.U16toU8OperationSafe.interactions u16_values ⟨low_bytes⟩ is_real := by
  rw [Extracted.MulOracle.U16toU8OperationSafe.interactions,
    Extracted.U16toU8OperationSafe.interactions]

private theorem mulOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.MulOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.MulOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem mulOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.MulOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.MulOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

/-- The Mul oracle's embedded `MulOperation.asserts` copy agrees with the canonical standalone
module on every reconfigured arithmetic block. -/
private theorem mulOracle_mulOperation_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (cols : Circuits.Types.MulOperation F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.MulOracle.MulOperation.asserts a b c (mulOracleOperation cols)
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.asserts a b c cols
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.MulOracle.MulOperation.asserts, Extracted.MulOperation.asserts]
  simp only [mulOracleOperation, mulOracle_u16tou8safe_value_eq,
    mulOracle_u16tou8safe_asserts_eq, mulOracle_u16msb_asserts_eq]

/-- Interaction-list half of `mulOracle_mulOperation_asserts_eq`. -/
private theorem mulOracle_mulOperation_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b c : Word F) (cols : Circuits.Types.MulOperation F)
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : F) :
    Extracted.MulOracle.MulOperation.interactions a b c (mulOracleOperation cols)
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu =
      Extracted.MulOperation.interactions a b c cols
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu := by
  rw [Extracted.MulOracle.MulOperation.interactions,
    Extracted.MulOperation.interactions]
  simp only [mulOracleOperation, mulOracle_u16tou8safe_value_eq,
    mulOracle_u16tou8safe_interactions_eq, mulOracle_u16msb_interactions_eq]

@[circuit_norm] private theorem eval_mulOperationColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    Eval.eval env cols =
      ({ carry := Eval.eval env cols.carry
         product := Eval.eval env cols.product
         b_lower_byte := Eval.eval env cols.b_lower_byte
         c_lower_byte := Eval.eval env cols.c_lower_byte
         b_msb := Eval.eval env cols.b_msb
         c_msb := Eval.eval env cols.c_msb
         product_msb := Eval.eval env cols.product_msb
         b_sign_extend := Eval.eval env cols.b_sign_extend
         c_sign_extend := Eval.eval env cols.c_sign_extend } :
        Circuits.Types.MulOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_u16MsbColumns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Circuits.Types.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_u16toU8Columns
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.U16toU8Operation (Expression F)) :
    Eval.eval env cols =
      ({ low_bytes := Eval.eval env cols.low_bytes } :
        Circuits.Types.U16toU8Operation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_mulOperationInputs
    {F : Type} [FiniteField F] (env : Environment F)
    (input : MulOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ b := Eval.eval env input.b
         c := Eval.eval env input.c
         cols := Eval.eval env input.cols
         is_real := Eval.eval env input.is_real
         is_mul := Eval.eval env input.is_mul
         is_mulh := Eval.eval env input.is_mulh
         is_mulhu := Eval.eval env input.is_mulhu
         is_mulhsu := Eval.eval env input.is_mulhsu
         is_mulw := Eval.eval env input.is_mulw
         a := Eval.eval env input.a } :
        MulOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem eval_mulOperation_productMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    (Eval.eval env cols).product_msb.msb =
      Expression.eval env cols.product_msb.msb := by
  rw [eval_mulOperationColumns, eval_u16MsbColumns]
  simp only [ProvableType.eval_field]

@[circuit_norm] private theorem eval_mulOperation_bMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    (Eval.eval env cols).b_msb = Expression.eval env cols.b_msb := by
  rw [eval_mulOperationColumns]
  simp only [ProvableType.eval_field]

@[circuit_norm] private theorem eval_mulOperation_cMsb
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    (Eval.eval env cols).c_msb = Expression.eval env cols.c_msb := by
  rw [eval_mulOperationColumns]
  simp only [ProvableType.eval_field]

@[circuit_norm] private theorem eval_mulOperation_bSign
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    (Eval.eval env cols).b_sign_extend =
      Expression.eval env cols.b_sign_extend := by
  rw [eval_mulOperationColumns]
  simp only [ProvableType.eval_field]

@[circuit_norm] private theorem eval_mulOperation_cSign
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F)) :
    (Eval.eval env cols).c_sign_extend =
      Expression.eval env cols.c_sign_extend := by
  rw [eval_mulOperationColumns]
  simp only [ProvableType.eval_field]

@[circuit_norm] private theorem eval_mulOperation_product
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).product[i] =
      Expression.eval env cols.product[i] := by
  rw [eval_mulOperationColumns]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.product i hi).symm

@[circuit_norm] private theorem eval_mulOperation_carry
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F))
    (i : ℕ) (hi : i < 16) :
    (Eval.eval env cols).carry[i] =
      Expression.eval env cols.carry[i] := by
  rw [eval_mulOperationColumns]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.carry i hi).symm

@[circuit_norm] private theorem eval_mulOperation_bLower
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).b_lower_byte.low_bytes[i] =
      Expression.eval env cols.b_lower_byte.low_bytes[i] := by
  rw [eval_mulOperationColumns,
    eval_u16toU8Columns env cols.b_lower_byte]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.b_lower_byte.low_bytes i hi).symm

@[circuit_norm] private theorem eval_mulOperation_cLower
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Circuits.Types.MulOperation (Expression F))
    (i : ℕ) (hi : i < 4) :
    (Eval.eval env cols).c_lower_byte.low_bytes[i] =
      Expression.eval env cols.c_lower_byte.low_bytes[i] := by
  rw [eval_mulOperationColumns,
    eval_u16toU8Columns env cols.c_lower_byte]
  simpa only using
    (ProvableType.getElem_eval_fields env cols.c_lower_byte.low_bytes i hi).symm

private theorem eval_word_getElem
    {F : Type} [FiniteField F] (env : Environment F)
    (word : Word (Expression F)) (i : ℕ) (hi : i < 4) :
    (Eval.eval env word)[i] = Expression.eval env word[i] :=
  (ProvableType.getElem_eval_fields env word i hi).symm

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value0 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[0] =
      cols.low_bytes[0] := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value1 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[1] =
      (w[0] - cols.low_bytes[0]) * 256⁻¹ := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value2 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[2] =
      cols.low_bytes[1] := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value3 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[3] =
      (w[1] - cols.low_bytes[1]) * 256⁻¹ := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value4 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[4] =
      cols.low_bytes[2] := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value5 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[5] =
      (w[2] - cols.low_bytes[2]) * 256⁻¹ := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value6 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[6] =
      cols.low_bytes[3] := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem u16Value7 (w : Word (ZMod p))
    (cols : Circuits.Types.U16toU8Operation (ZMod p)) (isReal : ZMod p) :
    (Extracted.U16toU8OperationSafe.value w cols isReal)[7] =
      (w[3] - cols.low_bytes[3]) * 256⁻¹ := by
  rw [Extracted.U16toU8OperationSafe.value]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem mulCols_asserts_decompose
    (cols : MulChip.Columns (ZMod p)) :
    Extracted.MulOracle.MulCols.asserts (mulChipReconfigure cols) =
      Extracted.MulOperation.asserts cols.a
        cols.adapter.op_b_memory.prev_value
        cols.adapter.op_c_memory.prev_value cols.mul_operation
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
        cols.is_mul cols.is_mulh cols.is_mulw cols.is_mulhu cols.is_mulhsu ++
      Extracted.CPUState.asserts cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) ++
      Extracted.RTypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_mul * 11 + cols.is_mulh * 12 +
          cols.is_mulhu * 13 + cols.is_mulhsu * 14 + cols.is_mulw * 24)
        cols.a cols.adapter
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) ++
      [ cols.is_mul * (cols.is_mul - 1),
        cols.is_mulh * (cols.is_mulh - 1),
        cols.is_mulhu * (cols.is_mulhu - 1),
        cols.is_mulw * (cols.is_mulw - 1),
        cols.is_mulhsu * (cols.is_mulhsu - 1),
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) *
          (cols.is_mul + cols.is_mulh + cols.is_mulhu +
            cols.is_mulhsu + cols.is_mulw - 1),
        cols.adapter.op_a_0 ] := by
  rw [Extracted.MulOracle.MulCols.asserts]
  dsimp only [mulChipReconfigure, mulOracleOperation]
  rw [mulOracleOperation_eta, mulOracle_mulOperation_asserts_eq,
    cpuState_eta, rTypeReader_eta,
    vec4_eta, vec4_eta, vec4_eta, vec3_eta]

private theorem mulFlags_all_zero
    {isMul isMulh isMulhu isMulhsu isMulw : ZMod p}
    (hm : isMul = 0 ∨ isMul = 1)
    (hmh : isMulh = 0 ∨ isMulh = 1)
    (hmu : isMulhu = 0 ∨ isMulhu = 1)
    (hms : isMulhsu = 0 ∨ isMulhsu = 1)
    (hmw : isMulw = 0 ∨ isMulw = 1)
    (hsum : isMul + isMulh + isMulhu + isMulhsu + isMulw = 0) :
    isMul = 0 ∧ isMulh = 0 ∧ isMulhu = 0 ∧ isMulhsu = 0 ∧ isMulw = 0 := by
  have hp := Fact.out (p := 2 ^ 24 < p)
  have hmVal := MulOperation.bool_val hm
  have hmhVal := MulOperation.bool_val hmh
  have hmuVal := MulOperation.bool_val hmu
  have hmsVal := MulOperation.bool_val hms
  have hmwVal := MulOperation.bool_val hmw
  have hcast :
      isMul + isMulh + isMulhu + isMulhsu + isMulw =
        ((isMul.val + isMulh.val + isMulhu.val + isMulhsu.val +
          isMulw.val : ℕ) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  rw [hcast] at hsum
  have hlt :
      isMul.val + isMulh.val + isMulhu.val + isMulhsu.val +
        isMulw.val < p := by
    omega
  have hz :
      isMul.val + isMulh.val + isMulhu.val + isMulhsu.val +
        isMulw.val = 0 := by
    have h := congrArg ZMod.val hsum
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at h
  exact ⟨(ZMod.val_eq_zero isMul).mp (by omega),
    (ZMod.val_eq_zero isMulh).mp (by omega),
    (ZMod.val_eq_zero isMulhu).mp (by omega),
    (ZMod.val_eq_zero isMulhsu).mp (by omega),
    (ZMod.val_eq_zero isMulw).mp (by omega)⟩

private theorem mulSignExtend_bool
    {isMul isMulh isMulhu isMulhsu isMulw bMsb cMsb
      bSign cSign : ZMod p}
    (hm : isMul = 0 ∨ isMul = 1)
    (hmh : isMulh = 0 ∨ isMulh = 1)
    (hmu : isMulhu = 0 ∨ isMulhu = 1)
    (hms : isMulhsu = 0 ∨ isMulhsu = 1)
    (hmw : isMulw = 0 ∨ isMulw = 1)
    (hsum :
      isMul + isMulh + isMulhu + isMulhsu + isMulw = 0 ∨
      isMul + isMulh + isMulhu + isMulhsu + isMulw = 1)
    (hb : bMsb = 0 ∨ bMsb = 1)
    (hc : cMsb = 0 ∨ cMsb = 1)
    (hbSign : bSign = (isMulh + isMulhsu) * bMsb)
    (hcSign : cSign = isMulh * cMsb) :
    (bSign = 0 ∨ bSign = 1) ∧ (cSign = 0 ∨ cSign = 1) := by
  rcases hsum with hsum | hsum
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      mulFlags_all_zero hm hmh hmu hms hmw hsum
    simp at hbSign hcSign
    subst bSign
    subst cSign
    simp
  · rcases MulOperation.oneHot_of_sum_one hm hmh hmu hms hmw hsum with
      h | h | h | h | h
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      simp at hbSign hcSign
      subst bSign
      subst cSign
      simp
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      simp at hbSign hcSign
      subst bSign
      subst cSign
      exact ⟨hb, hc⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      simp at hbSign hcSign
      subst bSign
      subst cSign
      simp
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      simp at hbSign hcSign
      subst bSign
      subst cSign
      exact ⟨hb, Or.inl rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      simp at hbSign hcSign
      subst bSign
      subst cSign
      simp

set_option linter.unusedSimpArgs false in
theorem mulOperation_assertions_forward
    (env : Environment (ZMod p))
    (input : Var MulOperation.Inputs (ZMod p)) (offset : ℕ)
    (hRust :
      List.Forall (· = 0)
        (Extracted.MulOperation.asserts (Eval.eval env input.a)
          (Eval.eval env input.b) (Eval.eval env input.c)
          (Eval.eval env input.cols)
          (Expression.eval env input.is_real)
          (Expression.eval env input.is_mul)
          (Expression.eval env input.is_mulh)
          (Expression.eval env input.is_mulw)
          (Expression.eval env input.is_mulhu)
          (Expression.eval env input.is_mulhsu))) :
    List.Forall (· = 0)
        (nativeAssertZeros env ((MulOperation.main input).operations offset)) := by
  rw [Extracted.MulOperation.asserts] at hRust
  simp only [Extracted.U16toU8OperationSafe.asserts,
    Extracted.U16MSBOperation.asserts, List.forall_append,
    List.Forall, true_and] at hRust
  obtain ⟨⟨hw0, hpmsb⟩, hbdef, hcdef,
    hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7,
    hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15,
    ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, ho11,
    hbmsb, hcmsb, _hbsign, _hcsign,
    hm, hmh, hmu, hms, _hw1, hsum, hr, hbimp, hcimp⟩ := hRust
  simp only [nativeAssertZeros, MulOperation.main,
    Circuit.operations, Circuit.bind_def, assertion, assertZero,
    Operations.localLength]
  simp only [Operations.constraints_append,
    Operations.constraints_subcircuit,
    FormalAssertion.toSubcircuit_constraints,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_assert, Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil]
  simp only [U16toU8OperationSafe.circuit,
    U16toU8OperationSafe.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.circuit,
    circuit_norm]
  repeat' rw [CanonicalReader.equalityAssertionList]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [circuit_norm] using hr
  · simpa only [circuit_norm] using hr
  · simpa only [circuit_norm] using hr
  · constructor
    · simpa only [circuit_norm] using hw0
    · refine forall_singleton_append ?_ ?_
      · simp only [eval_sub, eval_mul, Expression.eval, sub_zero]
        rw [← eval_mulOperation_productMsb env input.cols]
        exact hpmsb
      · refine forall_singleton_append ?_ ?_
        · simp only [eval_sub, eval_mul, Expression.eval, sub_zero]
          rw [← eval_mulOperation_bMsb env input.cols]
          exact hbmsb
        · refine forall_singleton_append ?_ ?_
          · simp only [eval_sub, eval_mul, Expression.eval, sub_zero]
            rw [← eval_mulOperation_cMsb env input.cols]
            exact hcmsb
          · refine forall_singleton_append ?_ ?_
            · simp only [eval_sub, eval_add, eval_mul, Expression.eval]
              rw [← eval_mulOperation_bSign env input.cols,
                ← eval_mulOperation_bMsb env input.cols]
              exact hbdef
            · refine forall_singleton_append ?_ ?_
              · simp only [eval_sub, eval_mul, Expression.eval]
                rw [← eval_mulOperation_cSign env input.cols,
                  ← eval_mulOperation_cMsb env input.cols]
                exact hcdef
              · refine forall_singleton_append ?_ ?_
                · simp only [eval_sub, eval_mul, Expression.eval, sub_zero]
                  rw [← eval_mulOperation_bSign env input.cols,
                    ← eval_mulOperation_bMsb env input.cols]
                  exact hbimp
                · refine forall_singleton_append ?_ ?_
                  · simp only [eval_sub, eval_mul, Expression.eval, sub_zero]
                    rw [← eval_mulOperation_cSign env input.cols,
                      ← eval_mulOperation_cMsb env input.cols]
                    exact hcimp
                  · refine forall_singleton_append ?_ ?_
                    · have hp0' := hp0
                      simp only [vec4_eta, u16toU8_eta, u16Value0,
                        eval_mulOperation_product,
                        eval_mulOperation_carry,
                        eval_mulOperation_bLower,
                        eval_mulOperation_cLower,
                        eval_word_getElem, zero_add] at hp0'
                      simp only [eval_sub, eval_mul, Expression.eval,
                        sub_zero]
                      exact hp0'
                    · refine forall_singleton_append ?_ ?_
                      · have hp1' := hp1
                        simp only [vec4_eta, u16toU8_eta,
                          u16Value0, u16Value1, u16Value2, u16Value3,
                          u16Value4, u16Value5, u16Value6, u16Value7,
                          eval_mulOperation_product,
                          eval_mulOperation_carry,
                          eval_mulOperation_bLower,
                          eval_mulOperation_cLower,
                          eval_word_getElem, zero_add] at hp1'
                        simp only [eval_sub, eval_mul, eval_add,
                          Expression.eval, sub_zero]
                        exact hp1'
                      · refine forall_singleton_append ?_ ?_
                        · have hp2' := hp2
                          simp only [vec4_eta, u16toU8_eta,
                            u16Value0, u16Value1, u16Value2, u16Value3,
                            u16Value4, u16Value5, u16Value6, u16Value7,
                            eval_mulOperation_product,
                            eval_mulOperation_carry,
                            eval_mulOperation_bLower,
                            eval_mulOperation_cLower,
                            eval_word_getElem, zero_add] at hp2'
                          simp only [eval_sub, eval_mul, eval_add,
                            Expression.eval, sub_zero]
                          exact hp2'
                        · refine forall_singleton_append ?_ ?_
                          · have hp3' := hp3
                            simp only [vec4_eta, u16toU8_eta,
                              u16Value0, u16Value1, u16Value2, u16Value3,
                              u16Value4, u16Value5, u16Value6, u16Value7,
                              eval_mulOperation_product,
                              eval_mulOperation_carry,
                              eval_mulOperation_bLower,
                              eval_mulOperation_cLower,
                              eval_word_getElem, zero_add] at hp3'
                            simp only [eval_sub, eval_mul, eval_add,
                              Expression.eval, sub_zero]
                            exact hp3'
                          · refine forall_singleton_append ?_ ?_
                            · have hp4' := hp4
                              simp only [vec4_eta, u16toU8_eta,
                                u16Value0, u16Value1, u16Value2,
                                u16Value3, u16Value4, u16Value5,
                                u16Value6, u16Value7,
                                eval_mulOperation_product,
                                eval_mulOperation_carry,
                                eval_mulOperation_bLower,
                                eval_mulOperation_cLower,
                                eval_word_getElem, zero_add] at hp4'
                              simp only [eval_sub, eval_mul, eval_add,
                                Expression.eval, sub_zero]
                              exact hp4'
                            · refine forall_singleton_append ?_ ?_
                              · have hp5' := hp5
                                simp only [vec4_eta, u16toU8_eta,
                                  u16Value0, u16Value1, u16Value2,
                                  u16Value3, u16Value4, u16Value5,
                                  u16Value6, u16Value7,
                                  eval_mulOperation_product,
                                  eval_mulOperation_carry,
                                  eval_mulOperation_bLower,
                                  eval_mulOperation_cLower,
                                  eval_word_getElem, zero_add] at hp5'
                                simp only [eval_sub, eval_mul, eval_add,
                                  Expression.eval, sub_zero]
                                exact hp5'
                              · refine forall_singleton_append ?_ ?_
                                · have hp6' := hp6
                                  simp only [vec4_eta, u16toU8_eta,
                                    u16Value0, u16Value1, u16Value2,
                                    u16Value3, u16Value4, u16Value5,
                                    u16Value6, u16Value7,
                                    eval_mulOperation_product,
                                    eval_mulOperation_carry,
                                    eval_mulOperation_bLower,
                                    eval_mulOperation_cLower,
                                    eval_word_getElem, zero_add] at hp6'
                                  simp only [eval_sub, eval_mul, eval_add,
                                    Expression.eval, sub_zero]
                                  exact hp6'
                                · refine forall_singleton_append ?_ ?_
                                  · have hp7' := hp7
                                    simp only [vec4_eta, u16toU8_eta,
                                      u16Value0, u16Value1, u16Value2,
                                      u16Value3, u16Value4, u16Value5,
                                      u16Value6, u16Value7,
                                      eval_mulOperation_product,
                                      eval_mulOperation_carry,
                                      eval_mulOperation_bLower,
                                      eval_mulOperation_cLower,
                                      eval_word_getElem, zero_add] at hp7'
                                    simp only [eval_sub, eval_mul, eval_add,
                                      Expression.eval, sub_zero]
                                    exact hp7'
                                  · refine forall_singleton_append ?_ ?_
                                    · have hp8' := hp8
                                      simp only [vec4_eta, u16toU8_eta,
                                        u16Value0, u16Value1, u16Value2,
                                        u16Value3, u16Value4, u16Value5,
                                        u16Value6, u16Value7,
                                        eval_mulOperation_product,
                                        eval_mulOperation_carry,
                                        eval_mulOperation_bLower,
                                        eval_mulOperation_cLower,
                                        eval_mulOperation_bSign,
                                        eval_mulOperation_cSign,
                                        eval_word_getElem,
                                        Vector.getElem_mk,
                                        List.getElem_toArray,
                                        List.getElem_cons_zero,
                                        List.getElem_cons_succ,
                                        zero_add] at hp8'
                                      simp only [eval_sub, eval_mul,
                                        eval_add, Expression.eval,
                                        sub_zero]
                                      exact hp8'
                                    · refine forall_singleton_append ?_ ?_
                                      · have hp9' := hp9
                                        simp only [vec4_eta,
                                          u16toU8_eta, u16Value0,
                                          u16Value1, u16Value2, u16Value3,
                                          u16Value4, u16Value5, u16Value6,
                                          u16Value7,
                                          eval_mulOperation_product,
                                          eval_mulOperation_carry,
                                          eval_mulOperation_bLower,
                                          eval_mulOperation_cLower,
                                          eval_mulOperation_bSign,
                                          eval_mulOperation_cSign,
                                          eval_word_getElem,
                                          Vector.getElem_mk,
                                          List.getElem_toArray,
                                          List.getElem_cons_zero,
                                          List.getElem_cons_succ,
                                          zero_add] at hp9'
                                        simp only [eval_sub, eval_mul,
                                          eval_add, Expression.eval,
                                          sub_zero]
                                        exact hp9'
                                      · refine
                                          forall_singleton_append ?_ ?_
                                        · have hp10' := hp10
                                          simp only [vec4_eta,
                                            u16toU8_eta, u16Value0,
                                            u16Value1, u16Value2,
                                            u16Value3, u16Value4,
                                            u16Value5, u16Value6,
                                            u16Value7,
                                            eval_mulOperation_product,
                                            eval_mulOperation_carry,
                                            eval_mulOperation_bLower,
                                            eval_mulOperation_cLower,
                                            eval_mulOperation_bSign,
                                            eval_mulOperation_cSign,
                                            eval_word_getElem,
                                            Vector.getElem_mk,
                                            List.getElem_toArray,
                                            List.getElem_cons_zero,
                                            List.getElem_cons_succ,
                                            zero_add] at hp10'
                                          simp only [eval_sub, eval_mul,
                                            eval_add, Expression.eval,
                                            sub_zero]
                                          exact hp10'
                                        · refine
                                            forall_singleton_append ?_ ?_
                                          · have hp11' := hp11
                                            simp only [vec4_eta,
                                              u16toU8_eta, u16Value0,
                                              u16Value1, u16Value2,
                                              u16Value3, u16Value4,
                                              u16Value5, u16Value6,
                                              u16Value7,
                                              eval_mulOperation_product,
                                              eval_mulOperation_carry,
                                              eval_mulOperation_bLower,
                                              eval_mulOperation_cLower,
                                              eval_mulOperation_bSign,
                                              eval_mulOperation_cSign,
                                              eval_word_getElem,
                                              Vector.getElem_mk,
                                              List.getElem_toArray,
                                              List.getElem_cons_zero,
                                              List.getElem_cons_succ,
                                              zero_add] at hp11'
                                            simp only [eval_sub, eval_mul,
                                              eval_add, Expression.eval,
                                              sub_zero]
                                            exact hp11'
                                          · refine
                                              forall_singleton_append
                                                ?_ ?_
                                            · have hp12' := hp12
                                              simp only [vec4_eta,
                                                u16toU8_eta, u16Value0,
                                                u16Value1, u16Value2,
                                                u16Value3, u16Value4,
                                                u16Value5, u16Value6,
                                                u16Value7,
                                                eval_mulOperation_product,
                                                eval_mulOperation_carry,
                                                eval_mulOperation_bLower,
                                                eval_mulOperation_cLower,
                                                eval_mulOperation_bSign,
                                                eval_mulOperation_cSign,
                                                eval_word_getElem,
                                                Vector.getElem_mk,
                                                List.getElem_toArray,
                                                List.getElem_cons_zero,
                                                List.getElem_cons_succ,
                                                zero_add] at hp12'
                                              simp only [eval_sub,
                                                eval_mul, eval_add,
                                                Expression.eval,
                                                sub_zero]
                                              exact hp12'
                                            · refine
                                                forall_singleton_append
                                                  ?_ ?_
                                              · have hp13' := hp13
                                                simp only [vec4_eta,
                                                  u16toU8_eta, u16Value0,
                                                  u16Value1, u16Value2,
                                                  u16Value3, u16Value4,
                                                  u16Value5, u16Value6,
                                                  u16Value7,
                                                  eval_mulOperation_product,
                                                  eval_mulOperation_carry,
                                                  eval_mulOperation_bLower,
                                                  eval_mulOperation_cLower,
                                                  eval_mulOperation_bSign,
                                                  eval_mulOperation_cSign,
                                                  eval_word_getElem,
                                                  Vector.getElem_mk,
                                                  List.getElem_toArray,
                                                  List.getElem_cons_zero,
                                                  List.getElem_cons_succ,
                                                  zero_add] at hp13'
                                                simp only [eval_sub,
                                                  eval_mul, eval_add,
                                                  Expression.eval,
                                                  sub_zero]
                                                exact hp13'
                                              · refine
                                                  forall_singleton_append
                                                    ?_ ?_
                                                · have hp14' := hp14
                                                  simp only [vec4_eta,
                                                    u16toU8_eta, u16Value0,
                                                    u16Value1, u16Value2,
                                                    u16Value3, u16Value4,
                                                    u16Value5, u16Value6,
                                                    u16Value7,
                                                    eval_mulOperation_product,
                                                    eval_mulOperation_carry,
                                                    eval_mulOperation_bLower,
                                                    eval_mulOperation_cLower,
                                                    eval_mulOperation_bSign,
                                                    eval_mulOperation_cSign,
                                                    eval_word_getElem,
                                                    Vector.getElem_mk,
                                                    List.getElem_toArray,
                                                    List.getElem_cons_zero,
                                                    List.getElem_cons_succ,
                                                    zero_add] at hp14'
                                                  simp only [eval_sub,
                                                    eval_mul, eval_add,
                                                    Expression.eval,
                                                    sub_zero]
                                                  exact hp14'
                                                · refine
                                                    forall_singleton_append
                                                      ?_ ?_
                                                  · have hp15' := hp15
                                                    simp only [vec4_eta,
                                                      u16toU8_eta,
                                                      u16Value0, u16Value1,
                                                      u16Value2, u16Value3,
                                                      u16Value4, u16Value5,
                                                      u16Value6, u16Value7,
                                                      eval_mulOperation_product,
                                                      eval_mulOperation_carry,
                                                      eval_mulOperation_bLower,
                                                      eval_mulOperation_cLower,
                                                      eval_mulOperation_bSign,
                                                      eval_mulOperation_cSign,
                                                      eval_word_getElem,
                                                      Vector.getElem_mk,
                                                      List.getElem_toArray,
                                                      List.getElem_cons_zero,
                                                      List.getElem_cons_succ,
                                                      zero_add] at hp15'
                                                    simp only [eval_sub,
                                                      eval_mul, eval_add,
                                                      Expression.eval,
                                                      sub_zero]
                                                    exact hp15'
                                                  · simpa only [List.Forall, ← ProvableStruct.eval_eq_eval,
                                                      eval_mulOperationInputs, eval_mulOperation_product,
                                                      eval_mulOperation_productMsb, eval_word_getElem,
                                                      eval_sub, eval_mul, eval_add, Expression.eval]
                                                      using And.intro ho0 (And.intro ho1 (And.intro ho2
                                                        (And.intro ho3 (And.intro ho4 (And.intro ho5
                                                          (And.intro ho6 (And.intro ho7 (And.intro ho8
                                                            (And.intro ho9 (And.intro ho10 ho11))))))))))

local macro "close_mul_constraint" h:term : tactic =>
  `(tactic| simpa only [← ProvableStruct.eval_eq_eval, eval_mulOperationInputs,
      vec4_eta, u16toU8_eta,
      u16Value0, u16Value1, u16Value2, u16Value3,
      u16Value4, u16Value5, u16Value6, u16Value7,
      eval_mulOperation_product, eval_mulOperation_carry,
      eval_mulOperation_bLower, eval_mulOperation_cLower,
      eval_mulOperation_bSign, eval_mulOperation_cSign, eval_mulOperation_productMsb,
      eval_word_getElem, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, eval_sub, eval_mul, eval_add,
      Expression.eval, sub_zero, zero_add] using $h)

set_option linter.unusedSimpArgs false in
theorem mulOperation_assertions_backward
    (env : Environment (ZMod p))
    (input : Var MulOperation.Inputs (ZMod p)) (offset : ℕ)
    (hNative :
      List.Forall (· = 0)
        (nativeAssertZeros env ((MulOperation.main input).operations offset)))
    (hm : Expression.eval env input.is_mul *
        (Expression.eval env input.is_mul - 1) = 0)
    (hmh : Expression.eval env input.is_mulh *
        (Expression.eval env input.is_mulh - 1) = 0)
    (hmu : Expression.eval env input.is_mulhu *
        (Expression.eval env input.is_mulhu - 1) = 0)
    (hms : Expression.eval env input.is_mulhsu *
        (Expression.eval env input.is_mulhsu - 1) = 0)
    (hmw : Expression.eval env input.is_mulw *
        (Expression.eval env input.is_mulw - 1) = 0)
    (hsum :
      let sum := Expression.eval env input.is_mul +
        Expression.eval env input.is_mulh +
        Expression.eval env input.is_mulhu +
        Expression.eval env input.is_mulhsu +
        Expression.eval env input.is_mulw
      sum * (sum - 1) = 0) :
    List.Forall (· = 0)
      (Extracted.MulOperation.asserts (Eval.eval env input.a)
        (Eval.eval env input.b) (Eval.eval env input.c)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real)
        (Expression.eval env input.is_mul)
        (Expression.eval env input.is_mulh)
        (Expression.eval env input.is_mulw)
        (Expression.eval env input.is_mulhu)
        (Expression.eval env input.is_mulhsu)) := by
  simp only [nativeAssertZeros, MulOperation.main,
    Circuit.operations, Circuit.bind_def, assertion, assertZero,
    Operations.localLength] at hNative
  simp only [Operations.constraints_append,
    Operations.constraints_subcircuit,
    FormalAssertion.toSubcircuit_constraints,
    FormalAssertion.toSubcircuit_localLength,
    Operations.constraints_assert, Operations.constraints_nil,
    List.map_append, List.map_cons, List.map_nil] at hNative
  simp only [U16toU8OperationSafe.circuit,
    U16toU8OperationSafe.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.circuit,
    circuit_norm] at hNative
  repeat' rw [CanonicalReader.equalityAssertionList] at hNative
  obtain ⟨hr, -, -, hTail⟩ := hNative
  obtain ⟨hw0, hTail⟩ := forall_cons_elim hTail
  obtain ⟨hpmsb, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hbmsb, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hcmsb, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hbdef, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hcdef, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hbimp, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hcimp, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp0, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp1, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp2, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp3, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp4, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp5, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp6, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp7, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp8, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp9, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp10, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp11, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp12, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp13, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp14, hTail⟩ := forall_singleton_append_elim hTail
  obtain ⟨hp15, hTail⟩ := forall_singleton_append_elim hTail
  simp only [List.Forall] at hTail
  obtain ⟨ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, ho11⟩ := hTail
  have hm' := bool_of_mul_pred hm
  have hmh' := bool_of_mul_pred hmh
  have hmu' := bool_of_mul_pred hmu
  have hms' := bool_of_mul_pred hms
  have hmw' := bool_of_mul_pred hmw
  have hsum' := bool_of_mul_pred hsum
  have hr' :
      Expression.eval env input.is_real *
        (Expression.eval env input.is_real - 1) = 0 := hr
  have hw0' :
      Expression.eval env input.is_mulw *
        (Expression.eval env input.is_mulw - 1) = 0 := hw0
  have hpmsb' :
      (Eval.eval env input.cols).product_msb.msb *
        ((Eval.eval env input.cols).product_msb.msb - 1) = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval, sub_zero] at hpmsb
    rw [eval_mulOperation_productMsb]
    exact hpmsb
  have hbmsb' :
      (Eval.eval env input.cols).b_msb *
        ((Eval.eval env input.cols).b_msb - 1) = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval, sub_zero] at hbmsb
    rw [eval_mulOperation_bMsb]
    exact hbmsb
  have hcmsb' :
      (Eval.eval env input.cols).c_msb *
        ((Eval.eval env input.cols).c_msb - 1) = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval, sub_zero] at hcmsb
    rw [eval_mulOperation_cMsb]
    exact hcmsb
  have hbdef' :
      (Eval.eval env input.cols).b_sign_extend -
        (Expression.eval env input.is_mulh +
          Expression.eval env input.is_mulhsu) *
          (Eval.eval env input.cols).b_msb = 0 := by
    simp only [eval_sub, eval_mul, eval_add, Expression.eval] at hbdef
    rw [eval_mulOperation_bSign, eval_mulOperation_bMsb]
    exact hbdef
  have hcdef' :
      (Eval.eval env input.cols).c_sign_extend -
        Expression.eval env input.is_mulh *
          (Eval.eval env input.cols).c_msb = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval] at hcdef
    rw [eval_mulOperation_cSign, eval_mulOperation_cMsb]
    exact hcdef
  have hbimp' :
      (Eval.eval env input.cols).b_sign_extend *
        ((Eval.eval env input.cols).b_msb - 1) = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval, sub_zero] at hbimp
    rw [eval_mulOperation_bSign, eval_mulOperation_bMsb]
    exact hbimp
  have hcimp' :
      (Eval.eval env input.cols).c_sign_extend *
        ((Eval.eval env input.cols).c_msb - 1) = 0 := by
    simp only [eval_sub, eval_mul, Expression.eval, sub_zero] at hcimp
    rw [eval_mulOperation_cSign, eval_mulOperation_cMsb]
    exact hcimp
  have hSignBool := mulSignExtend_bool hm' hmh' hmu' hms' hmw'
    hsum' (bool_of_mul_pred hbmsb') (bool_of_mul_pred hcmsb')
    (sub_eq_zero.mp hbdef') (sub_eq_zero.mp hcdef')
  rw [Extracted.MulOperation.asserts]
  simp only [Extracted.U16toU8OperationSafe.asserts,
    Extracted.U16MSBOperation.asserts, List.forall_append,
    List.Forall, true_and]
  refine ⟨⟨hw0', hpmsb'⟩, hbdef', hcdef', ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by close_mul_constraint ho0,
    by close_mul_constraint ho1,
    by close_mul_constraint ho2,
    by close_mul_constraint ho3,
    by close_mul_constraint ho4,
    by close_mul_constraint ho5,
    by close_mul_constraint ho6,
    by close_mul_constraint ho7,
    by close_mul_constraint ho8,
    by close_mul_constraint ho9,
    by close_mul_constraint ho10,
    by close_mul_constraint ho11,
    hbmsb', hcmsb', mul_pred_of_bool hSignBool.1,
    mul_pred_of_bool hSignBool.2, hm, hmh, hmu, hms, hmw, hsum, hr',
    hbimp', hcimp'⟩
  · close_mul_constraint hp0
  · close_mul_constraint hp1
  · close_mul_constraint hp2
  · close_mul_constraint hp3
  · close_mul_constraint hp4
  · close_mul_constraint hp5
  · close_mul_constraint hp6
  · close_mul_constraint hp7
  · close_mul_constraint hp8
  · close_mul_constraint hp9
  · close_mul_constraint hp10
  · close_mul_constraint hp11
  · close_mul_constraint hp12
  · close_mul_constraint hp13
  · close_mul_constraint hp14
  · close_mul_constraint hp15

private theorem mulChip_constraints_faithful
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : MulChip.Columns (ZMod p))
    (hbind : BindsChipOutput MulChip.main env input offset cols) :
    List.Forall (· = 0) (mulChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env ((MulChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (MulChip.elaborated (p := p)) hbind
  rw [MulChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval, MulChip.eval_columns] at hbind
  subst cols
  let operation : Var Circuits.Types.MulOperation (ZMod p) :=
    mul_chip_operation offset
  let a : Word (Expression (ZMod p)) := mul_chip_a offset
  let stateValue := Eval.eval env input.state
  let adapterValue := Eval.eval env input.adapter
  let rustOperation : Circuits.Types.MulOperation (ZMod p) :=
    Eval.eval env operation
  let rustA : Word (ZMod p) := Eval.eval env a
  let rustB : Word (ZMod p) :=
    (Eval.eval env input.adapter).op_b_memory.prev_value
  let rustC : Word (ZMod p) :=
    (Eval.eval env input.adapter).op_c_memory.prev_value
  let rustIsMul := Expression.eval env (input.isMul)
  let rustIsMulh := Expression.eval env (input.isMulh)
  let rustIsMulhu := Expression.eval env (input.isMulhu)
  let rustIsMulhsu := Expression.eval env (input.isMulhsu)
  let rustIsMulw := Expression.eval env (input.isMulw)
  let rustIsReal := Expression.eval env (input.is_real)
  let rustOpcode := Expression.eval env
    (input.isMul * 11 +
      input.isMulh * 12 +
      input.isMulhu * 13 +
      input.isMulhsu * 14 +
      input.isMulw * 24)
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  let rustState : Circuits.Types.CPUState (ZMod p) := stateValue
  let rustNextPc : Vector (ZMod p) 3 :=
    #v[stateValue.pc[0] + 4, stateValue.pc[1], stateValue.pc[2]]
  have hCpu := CanonicalReader.cpuStateAssertions (p := p) env cpuInput
    offset rustState rustNextPc 8 rustIsReal (by
      simp only [cpuInput, rustIsReal, ProvableStruct.structEvalLiteralProc])
  let opInput : Var MulOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val, operation,
      input.is_real, input.isMul,
      input.isMulh, input.isMulhu,
      input.isMulhsu, input.isMulw, mul_chip_a offset⟩
  have hB : Eval.eval env opInput.b = rustB := by
    simp only [opInput, rustB, MulChip.Inputs.op_b_val]
    calc
      _ = (Eval.eval env input.adapter.op_b_memory).prev_value := by
        exact (congrArg (fun value => value.prev_value)
          (Readers.RTypeReader.eval_registerAccessCols env
            input.adapter.op_b_memory)).symm
      _ = (Eval.eval env input.adapter).op_b_memory.prev_value := by
        exact congrArg (fun value => value.prev_value)
          (congrArg (fun value => value.op_b_memory)
            (Readers.RTypeReader.eval_cols env input.adapter)).symm
  have hC : Eval.eval env opInput.c = rustC := by
    simp only [opInput, rustC, MulChip.Inputs.op_c_val]
    calc
      _ = (Eval.eval env input.adapter.op_c_memory).prev_value := by
        exact (congrArg (fun value => value.prev_value)
          (Readers.RTypeReader.eval_registerAccessCols env
            input.adapter.op_c_memory)).symm
      _ = (Eval.eval env input.adapter).op_c_memory.prev_value := by
        exact congrArg (fun value => value.prev_value)
          (congrArg (fun value => value.op_c_memory)
            (Readers.RTypeReader.eval_cols env input.adapter)).symm
  let rustAdapter : Circuits.Types.RTypeReader (ZMod p) := adapterValue
  let rtypeInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real,
      input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc,
      input.isMul * 11 +
        input.isMulh * 12 +
        input.isMulhu * 13 +
        input.isMulhsu * 14 +
        input.isMulw * 24,
      a[0], a[1], a[2], a[3]⟩
  have hRtypeReal :
      (ProvableStruct.eval env rtypeInput).is_real = rustIsReal := by
    simp only [rtypeInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
  have hRtypeTrusted :
      (ProvableStruct.eval env rtypeInput).is_trusted = rustIsReal := by
    simp only [rtypeInput, rustIsReal, ProvableStruct.structEvalLiteralProc]
  have hopA0 :
      Expression.eval env input.adapter.op_a_0 =
        rustAdapter.op_a_0 := by
    simpa only [rustAdapter, adapterValue] using
      (Readers.RTypeReader.eval_opA0 env input.adapter).symm
  have hRtype := CanonicalReader.rTypeAssertions (p := p) env
    rtypeInput (offset + 49)
    stateValue.clk_high
    (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536)
    rustOpcode rustIsReal rustIsReal
    #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
    rustA rustAdapter hRtypeReal hRtypeTrusted hopA0
    (by
      simpa only [rtypeInput, rustA] using
        (ProvableType.getElem_eval_fields env a 0 (by decide)))
    (by
      simpa only [rtypeInput, rustA] using
        (ProvableType.getElem_eval_fields env a 1 (by decide)))
    (by
      simpa only [rtypeInput, rustA] using
        (ProvableType.getElem_eval_fields env a 2 (by decide)))
    (by
      simpa only [rtypeInput, rustA] using
        (ProvableType.getElem_eval_fields env a 3 (by decide))) rfl
  let writeInput : Var Readers.RegisterWrite.Inputs (ZMod p) :=
    ⟨input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
      input.adapter.op_a, a, input.is_real⟩
  rw [mul_chip_constraints_decompose]
  simp only [ChipOracle.nativeAssertZeros, mulChipOracle]
  rw [mulCols_asserts_decompose]
  simp only [List.forall_append, List.forall_cons]
  rw [forall_nil_iff]
  constructor
  · rintro ⟨⟨⟨hOpG, hCpuG⟩, hRtypeG⟩,
      hm, hmh, hmu, hmw, hms, hsum, hopA0G, _⟩
    have hOpOracle :
        List.Forall (· = 0)
          (Extracted.MulOperation.asserts rustA rustB rustC
            rustOperation rustIsReal rustIsMul rustIsMulh rustIsMulw
            rustIsMulhu rustIsMulhsu) := by
      simpa only [rustA, rustB, rustC, rustOperation,
        rustIsReal, rustIsMul, rustIsMulh, rustIsMulw,
        rustIsMulhu, rustIsMulhsu, operation, a,
        mul_chip_operation, mul_chip_a, MulChip.Inputs.is_real,
        eval_add, ProvableType.eval_field, Nat.add_zero,
        Expression.eval] using hOpG
    have hOpInputOracle :
        List.Forall (· = 0)
          (Extracted.MulOperation.asserts rustA
            (Eval.eval env opInput.b) (Eval.eval env opInput.c)
            (Eval.eval env opInput.cols)
            (Expression.eval env opInput.is_real)
            (Expression.eval env opInput.is_mul)
            (Expression.eval env opInput.is_mulh)
            (Expression.eval env opInput.is_mulw)
            (Expression.eval env opInput.is_mulhu)
            (Expression.eval env opInput.is_mulhsu)) := by
      rw [hB, hC]
      simpa only [opInput, rustOperation, operation,
        rustIsReal, rustIsMul, rustIsMulh, rustIsMulw,
        rustIsMulhu, rustIsMulhsu] using hOpOracle
    have hOpN := mulOperation_assertions_forward
      (p := p) env opInput (offset + 49) hOpInputOracle
    have hCpuOracle :
        List.Forall (· = 0)
          (Extracted.CPUState.asserts rustState rustNextPc 8
            rustIsReal) := by
      simpa only [rustState, rustNextPc, stateValue, rustIsReal,
        MulChip.Inputs.is_real, eval_add,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using
        hCpuG
    have hCpuN := hCpu.mp hCpuOracle
    have hRtypeOracle :
        List.Forall (· = 0)
          (Extracted.RTypeReader.asserts stateValue.clk_high
            (stateValue.clk_0_16 + stateValue.clk_16_24 * 65536)
            #v[stateValue.pc[0], stateValue.pc[1], stateValue.pc[2]]
            rustOpcode rustA rustAdapter rustIsReal rustIsReal) := by
      simpa only [stateValue, rustOpcode, rustA, rustAdapter,
        rustIsReal, operation, a, adapterValue,
        mul_chip_operation, mul_chip_a, MulChip.Inputs.is_real,
        eval_add, eval_mul, vec3_eta,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using
        hRtypeG
    have hRtypePairN := hRtype.mp
      ⟨hRtypeOracle, by
        simpa only [rustAdapter, adapterValue] using hopA0G⟩
    have hRtypeN := hRtypePairN.1
    have hWriteN :=
      (CanonicalReader.registerWriteAssertions env writeInput
        (offset + 49)).mpr trivial
    have hmN :
        Expression.eval env
          (input.isMul *
            (input.isMul - 1)) = 0 := by
      simpa only [eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using hm
    have hmhN :
        Expression.eval env
          (input.isMulh *
            (input.isMulh - 1)) = 0 := by
      simpa only [eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hmh
    have hmuN :
        Expression.eval env
          (input.isMulhu *
            (input.isMulhu - 1)) = 0 := by
      simpa only [eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hmu
    have hmsN :
        Expression.eval env
          (input.isMulhsu *
            (input.isMulhsu - 1)) = 0 := by
      simpa only [eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hms
    have hmwN :
        Expression.eval env
          (input.isMulw *
            (input.isMulw - 1)) = 0 := by
      simpa only [eval_mul, eval_sub,
        ProvableType.eval_field, Expression.eval] using hmw
    have hsumN :
        Expression.eval env
          (input.is_real *
            (input.is_real - 1)) = 0 := by
      simpa only [MulChip.Inputs.is_real,
        eval_mul, eval_sub, eval_add,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using hsum
    have hopA0N : Expression.eval env input.adapter.op_a_0 = 0 := by
      rw [hopA0]
      simpa only [rustAdapter, adapterValue] using hopA0G
    exact ⟨by simpa only [cpuInput] using hCpuN,
      by simpa only [opInput] using hOpN,
      hmN, hmhN, hmuN, hmsN, hmwN, hsumN, hopA0N,
      by simpa only [rtypeInput] using hRtypeN,
      by simpa only [writeInput] using hWriteN⟩
  · rintro ⟨hCpuN, hOpN,
      hmN, hmhN, hmuN, hmsN, hmwN, hsumN, hopA0N,
      hRtypeN, _hWriteN⟩
    have hmOp :
        Expression.eval env opInput.is_mul *
          (Expression.eval env opInput.is_mul - 1) = 0 := by
      simpa only [opInput, eval_mul, eval_sub,
        Expression.eval] using hmN
    have hmhOp :
        Expression.eval env opInput.is_mulh *
          (Expression.eval env opInput.is_mulh - 1) = 0 := by
      simpa only [opInput, eval_mul, eval_sub,
        Expression.eval] using hmhN
    have hmuOp :
        Expression.eval env opInput.is_mulhu *
          (Expression.eval env opInput.is_mulhu - 1) = 0 := by
      simpa only [opInput, eval_mul, eval_sub,
        Expression.eval] using hmuN
    have hmsOp :
        Expression.eval env opInput.is_mulhsu *
          (Expression.eval env opInput.is_mulhsu - 1) = 0 := by
      simpa only [opInput, eval_mul, eval_sub,
        Expression.eval] using hmsN
    have hmwOp :
        Expression.eval env opInput.is_mulw *
          (Expression.eval env opInput.is_mulw - 1) = 0 := by
      simpa only [opInput, eval_mul, eval_sub,
        Expression.eval] using hmwN
    have hsumOp :
        let sum := Expression.eval env opInput.is_mul +
          Expression.eval env opInput.is_mulh +
          Expression.eval env opInput.is_mulhu +
          Expression.eval env opInput.is_mulhsu +
          Expression.eval env opInput.is_mulw
        sum * (sum - 1) = 0 := by
      simpa only [opInput, MulChip.Inputs.is_real, eval_mul,
        eval_sub, eval_add, Expression.eval] using hsumN
    have hOpInputOracle := mulOperation_assertions_backward
      (p := p) env opInput (offset + 49) hOpN
        hmOp hmhOp hmuOp hmsOp hmwOp hsumOp
    have hOpOracle :
        List.Forall (· = 0)
          (Extracted.MulOperation.asserts rustA rustB rustC
            rustOperation rustIsReal rustIsMul rustIsMulh rustIsMulw
            rustIsMulhu rustIsMulhsu) := by
      rw [← hB, ← hC]
      simpa only [opInput, rustOperation, operation,
        rustIsReal, rustIsMul, rustIsMulh, rustIsMulw,
        rustIsMulhu, rustIsMulhsu] using hOpInputOracle
    have hCpuOracle := hCpu.mpr (by
      simpa only [cpuInput] using hCpuN)
    have hRustOpA0 : rustAdapter.op_a_0 = 0 := by
      rw [← hopA0]
      exact hopA0N
    have hRtypeOracle := (hRtype.mpr
      ⟨by simpa only [rtypeInput] using hRtypeN, hRustOpA0⟩).1
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simpa only [rustA, rustB, rustC, rustOperation,
        rustIsReal, rustIsMul, rustIsMulh, rustIsMulw,
        rustIsMulhu, rustIsMulhsu, operation, a,
        mul_chip_operation, mul_chip_a, MulChip.Inputs.is_real,
        eval_add, ProvableType.eval_field, Nat.add_zero,
        Expression.eval] using hOpOracle
    · simpa only [rustState, rustNextPc, stateValue, rustIsReal,
        MulChip.Inputs.is_real, eval_add,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using
        hCpuOracle
    · simpa only [stateValue, rustOpcode, rustA, rustAdapter,
        rustIsReal, operation, a, adapterValue,
        mul_chip_operation, mul_chip_a, MulChip.Inputs.is_real,
        eval_add, eval_mul, vec3_eta,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using
        hRtypeOracle
    · simpa only [rustIsMul, opInput,
        ProvableType.eval_field, Expression.eval, Nat.add_zero] using
        hmOp
    · simpa only [rustIsMulh, opInput,
        ProvableType.eval_field, Expression.eval] using hmhOp
    · simpa only [rustIsMulhu, opInput,
        ProvableType.eval_field, Expression.eval] using hmuOp
    · simpa only [rustIsMulw, opInput,
        ProvableType.eval_field, Expression.eval] using hmwOp
    · simpa only [rustIsMulhsu, opInput,
        ProvableType.eval_field, Expression.eval] using hmsOp
    · simpa only [rustIsReal, MulChip.Inputs.is_real,
        opInput, eval_add, ProvableType.eval_field,
        Expression.eval, Nat.add_zero] using hsumOp
    · simpa only [rustAdapter, adapterValue] using hRustOpA0

theorem mulChip_constraints_constructive
    (rustCols : Extracted.MulOracle.MulCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := mulChipRowCodec.assignment
      (mulChipOracle.deconfigure rustCols) data
    List.Forall (· = 0) (mulChipOracle.assertZeros rustCols) ↔
      ({ circuit := MulChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := mulChipOracle.deconfigure rustCols
  let assignment := mulChipRowCodec.assignment cols data
  have hbind : BindsChipOutput MulChip.main assignment.environment
      ({ circuit := MulChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowInputVar
      ({ circuit := MulChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [MulChip.circuit_main_eq] at h
    exact h
  have hfaithful := mulChip_constraints_faithful
    assignment.environment
    ({ circuit := MulChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowInputVar
    ({ circuit := MulChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0) (mulChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            ({ circuit := MulChip.circuit (p := p) } :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols, ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      MulChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (MulChip.circuit (p := p))
      assignment.environment MulChip.lookups_empty).symm

omit [Fact (2 ^ 24 < p)] in
private theorem mulCols_interactions_decompose
    (cols : MulChip.Columns (ZMod p)) :
    Extracted.MulOracle.MulCols.interactions (mulChipReconfigure cols) =
      Extracted.MulOperation.interactions cols.a
        cols.adapter.op_b_memory.prev_value
        cols.adapter.op_c_memory.prev_value cols.mul_operation
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
        cols.is_mul cols.is_mulh cols.is_mulw cols.is_mulhu cols.is_mulhsu ++
      Extracted.CPUState.interactions cols.state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) ++
      Extracted.RTypeReader.interactions cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 +
          cols.is_mulhsu * 14 + cols.is_mulw * 24)
        cols.a cols.adapter
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
        (cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) := by
  rw [Extracted.MulOracle.MulCols.interactions]
  dsimp only [mulChipReconfigure, mulOracleOperation]
  rw [mulOracleOperation_eta, mulOracle_mulOperation_interactions_eq,
    cpuState_eta, rTypeReader_eta, vec3_eta,
    vec4_eta cols.adapter.op_b_memory.prev_value,
    vec4_eta cols.adapter.op_c_memory.prev_value]
  simp only [vec4_eta, List.append_nil]

private theorem eval_sub_mul_const
    {F : Type} [Field F] (env : Environment F)
    (x y : Expression F) (xValue yValue scalar : F)
    (hx : Expression.eval env x = xValue)
    (hy : Expression.eval env y = yValue) :
    Expression.eval env ((x - y) * Expression.const scalar) =
      (xValue - yValue) * scalar := by
  simp only [eval_sub, Expression.eval, hx, hy]

open SP1Clean.Channels (byteChannel stateChannel memoryChannel programChannel)
open InteractionRecovery

theorem mulOperation_interactions_exact
    (env : Environment (ZMod p))
    (input : Var SP1Clean.MulOperation.Inputs (ZMod p)) (offset : ℕ)
    (a b c : Word (ZMod p))
    (cols : Circuits.Types.MulOperation (ZMod p))
    (is_real is_mulw : ZMod p)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_mulw : Expression.eval env input.is_mulw = is_mulw)
    (h_b0 : Expression.eval env input.b[0] = b[0])
    (h_b1 : Expression.eval env input.b[1] = b[1])
    (h_b2 : Expression.eval env input.b[2] = b[2])
    (h_b3 : Expression.eval env input.b[3] = b[3])
    (h_c0 : Expression.eval env input.c[0] = c[0])
    (h_c1 : Expression.eval env input.c[1] = c[1])
    (h_c2 : Expression.eval env input.c[2] = c[2])
    (h_c3 : Expression.eval env input.c[3] = c[3])
    (h_a1 :
      Expression.eval env input.a[1] = a[1])
    (h_blb0 :
      Expression.eval env input.cols.b_lower_byte.low_bytes[0] =
        cols.b_lower_byte.low_bytes[0])
    (h_blb1 :
      Expression.eval env input.cols.b_lower_byte.low_bytes[1] =
        cols.b_lower_byte.low_bytes[1])
    (h_blb2 :
      Expression.eval env input.cols.b_lower_byte.low_bytes[2] =
        cols.b_lower_byte.low_bytes[2])
    (h_blb3 :
      Expression.eval env input.cols.b_lower_byte.low_bytes[3] =
        cols.b_lower_byte.low_bytes[3])
    (h_clb0 :
      Expression.eval env input.cols.c_lower_byte.low_bytes[0] =
        cols.c_lower_byte.low_bytes[0])
    (h_clb1 :
      Expression.eval env input.cols.c_lower_byte.low_bytes[1] =
        cols.c_lower_byte.low_bytes[1])
    (h_clb2 :
      Expression.eval env input.cols.c_lower_byte.low_bytes[2] =
        cols.c_lower_byte.low_bytes[2])
    (h_clb3 :
      Expression.eval env input.cols.c_lower_byte.low_bytes[3] =
        cols.c_lower_byte.low_bytes[3])
    (h_bmsb : Expression.eval env input.cols.b_msb = cols.b_msb)
    (h_cmsb : Expression.eval env input.cols.c_msb = cols.c_msb)
    (h_pmsb :
      Expression.eval env input.cols.product_msb.msb =
        cols.product_msb.msb)
    (h_cy0 : Expression.eval env input.cols.carry[0] = cols.carry[0])
    (h_cy1 : Expression.eval env input.cols.carry[1] = cols.carry[1])
    (h_cy2 : Expression.eval env input.cols.carry[2] = cols.carry[2])
    (h_cy3 : Expression.eval env input.cols.carry[3] = cols.carry[3])
    (h_cy4 : Expression.eval env input.cols.carry[4] = cols.carry[4])
    (h_cy5 : Expression.eval env input.cols.carry[5] = cols.carry[5])
    (h_cy6 : Expression.eval env input.cols.carry[6] = cols.carry[6])
    (h_cy7 : Expression.eval env input.cols.carry[7] = cols.carry[7])
    (h_cy8 : Expression.eval env input.cols.carry[8] = cols.carry[8])
    (h_cy9 : Expression.eval env input.cols.carry[9] = cols.carry[9])
    (h_cy10 :
      Expression.eval env input.cols.carry[10] = cols.carry[10])
    (h_cy11 :
      Expression.eval env input.cols.carry[11] = cols.carry[11])
    (h_cy12 :
      Expression.eval env input.cols.carry[12] = cols.carry[12])
    (h_cy13 :
      Expression.eval env input.cols.carry[13] = cols.carry[13])
    (h_cy14 :
      Expression.eval env input.cols.carry[14] = cols.carry[14])
    (h_cy15 :
      Expression.eval env input.cols.carry[15] = cols.carry[15])
    (h_p0 : Expression.eval env input.cols.product[0] = cols.product[0])
    (h_p1 : Expression.eval env input.cols.product[1] = cols.product[1])
    (h_p2 : Expression.eval env input.cols.product[2] = cols.product[2])
    (h_p3 : Expression.eval env input.cols.product[3] = cols.product[3])
    (h_p4 : Expression.eval env input.cols.product[4] = cols.product[4])
    (h_p5 : Expression.eval env input.cols.product[5] = cols.product[5])
    (h_p6 : Expression.eval env input.cols.product[6] = cols.product[6])
    (h_p7 : Expression.eval env input.cols.product[7] = cols.product[7])
    (h_p8 : Expression.eval env input.cols.product[8] = cols.product[8])
    (h_p9 : Expression.eval env input.cols.product[9] = cols.product[9])
    (h_p10 :
      Expression.eval env input.cols.product[10] = cols.product[10])
    (h_p11 :
      Expression.eval env input.cols.product[11] = cols.product[11])
    (h_p12 :
      Expression.eval env input.cols.product[12] = cols.product[12])
    (h_p13 :
      Expression.eval env input.cols.product[13] = cols.product[13])
    (h_p14 :
      Expression.eval env input.cols.product[14] = cols.product[14])
    (h_p15 :
      Expression.eval env input.cols.product[15] = cols.product[15]) :
    (Extracted.MulOperation.interactions a b c cols
        is_real is_real is_real is_mulw is_real is_real).map
        Extracted.Interaction.toAccess =
      (((SP1Clean.MulOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have h3 : (3 : ZMod p).val = 3 := val_3_zmod_p
  have h5 : (5 : ZMod p).val = 5 := val_5_zmod_p
  have h6 : (6 : ZMod p).val = 6 := val_6_zmod_p
  have h16 : (16 : ZMod p).val = 16 := val_16_zmod_p
  have hk :
      ∀ (g : Expression (ZMod p))
        (s : ByteRow (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            ((pulledIf (channel := byteChannel) g s).toRaw) =
          (InteractionKind.Byte, "SP1Byte",
            [(Expression.eval env s.opcode).val,
             (Expression.eval env s.a).val,
             (Expression.eval env s.b).val,
             (Expression.eval env s.c).val],
            signedVal (Expression.eval env (-g))) :=
    fun g s => toAccess_pullIf_byte env g s
  have hvb :
      (Extracted.U16toU8OperationSafe.value
        #v[b[0], b[1], b[2], b[3]]
        { low_bytes :=
            #v[cols.b_lower_byte.low_bytes[0],
              cols.b_lower_byte.low_bytes[1],
              cols.b_lower_byte.low_bytes[2],
              cols.b_lower_byte.low_bytes[3]] } is_real)[7] =
        (b[3] - cols.b_lower_byte.low_bytes[3]) *
          (256 : ZMod p)⁻¹ := by
    simp [Extracted.U16toU8OperationSafe.value]
  have hvc :
      (Extracted.U16toU8OperationSafe.value
        #v[c[0], c[1], c[2], c[3]]
        { low_bytes :=
            #v[cols.c_lower_byte.low_bytes[0],
              cols.c_lower_byte.low_bytes[1],
              cols.c_lower_byte.low_bytes[2],
              cols.c_lower_byte.low_bytes[3]] } is_real)[7] =
        (c[3] - cols.c_lower_byte.low_bytes[3]) *
          (256 : ZMod p)⁻¹ := by
    simp [Extracted.U16toU8OperationSafe.value]
  have e3 :
      Expression.eval env (3 : Expression (ZMod p)) = 3 := by
    simp only [circuit_norm]
  have e5 :
      Expression.eval env (5 : Expression (ZMod p)) = 5 := by
    simp only [circuit_norm]
  have e6 :
      Expression.eval env (6 : Expression (ZMod p)) = 6 := by
    simp only [circuit_norm]
  have e16 :
      Expression.eval env (Expression.const (16 : ZMod p)) = 16 := by
    simp only [circuit_norm]
  have e0 :
      Expression.eval env (0 : Expression (ZMod p)) = 0 := by
    simp only [circuit_norm]
  have eob :
      Expression.eval env
          ((input.b[3] - input.cols.b_lower_byte.low_bytes[3]) *
            Expression.const (256 : ZMod p)⁻¹) =
        (b[3] - cols.b_lower_byte.low_bytes[3]) *
          (256 : ZMod p)⁻¹ := by
    exact eval_sub_mul_const env input.b[3]
      input.cols.b_lower_byte.low_bytes[3] b[3]
      cols.b_lower_byte.low_bytes[3] (256 : ZMod p)⁻¹ h_b3 h_blb3
  have eoc :
      Expression.eval env
          ((input.c[3] - input.cols.c_lower_byte.low_bytes[3]) *
            Expression.const (256 : ZMod p)⁻¹) =
        (c[3] - cols.c_lower_byte.low_bytes[3]) *
          (256 : ZMod p)⁻¹ := by
    exact eval_sub_mul_const env input.c[3]
      input.cols.c_lower_byte.low_bytes[3] c[3]
      cols.c_lower_byte.low_bytes[3] (256 : ZMod p)⁻¹ h_c3 h_clb3
  have eneg :
      Expression.eval env (-input.is_real) = -is_real := by
    simp only [circuit_norm, h_ir]
  simp only [Extracted.MulOperation.interactions, List.map_append]
  simp only [SP1Clean.MulOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    SP1Clean.U16toU8OperationSafe.circuit,
    SP1Clean.U16MSBOperation.circuit, Gadgets.Equality.main,
    List.filter_nil, List.append_nil, List.map_append]
  congr 1
  · exact u16tou8safe_interactions_faithful_syntactic env
      ⟨input.b, input.cols.b_lower_byte, input.is_real⟩ _
      #v[b[0], b[1], b[2], b[3]]
      { low_bytes :=
          #v[cols.b_lower_byte.low_bytes[0],
            cols.b_lower_byte.low_bytes[1],
            cols.b_lower_byte.low_bytes[2],
            cols.b_lower_byte.low_bytes[3]] }
      is_real h_ir h_b0 h_b1 h_b2 h_b3
      h_blb0 h_blb1 h_blb2 h_blb3
  congr 1
  · exact u16tou8safe_interactions_faithful_syntactic env
      ⟨input.c, input.cols.c_lower_byte, input.is_real⟩ _
      #v[c[0], c[1], c[2], c[3]]
      { low_bytes :=
          #v[cols.c_lower_byte.low_bytes[0],
            cols.c_lower_byte.low_bytes[1],
            cols.c_lower_byte.low_bytes[2],
            cols.c_lower_byte.low_bytes[3]] }
      is_real h_ir h_c0 h_c1 h_c2 h_c3
      h_clb0 h_clb1 h_clb2 h_clb3
  congr 1
  · exact u16msb_interactions_faithful_syntactic env
      ⟨input.a[1], input.cols.product_msb, input.is_mulw⟩ _
      a[1] cols.product_msb.msb is_mulw h_mulw h_a1 h_pmsb
  · have eneg_s :
        signedVal (Expression.eval env (-input.is_real)) =
          signedVal (-is_real) := by
      rw [eneg]
    have eob_v :
        (Expression.eval env
          ((input.b[3] - input.cols.b_lower_byte.low_bytes[3]) *
            Expression.const 256⁻¹)).val =
          ((b[3] - cols.b_lower_byte.low_bytes[3]) * 256⁻¹).val := by
      rw [eob]
    have eoc_v :
        (Expression.eval env
          ((input.c[3] - input.cols.c_lower_byte.low_bytes[3]) *
            Expression.const 256⁻¹)).val =
          ((c[3] - cols.c_lower_byte.low_bytes[3]) * 256⁻¹).val := by
      rw [eoc]
    simp only [Extracted.Interaction.toAccess_byte, hk, hvb, hvc,
      e3, e5, e6, e16, e0, eneg_s, h_bmsb, h_cmsb,
      h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6, h_cy7,
      h_cy8, h_cy9, h_cy10, h_cy11, h_cy12, h_cy13, h_cy14,
      h_cy15, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7,
      h_p8, h_p9, h_p10, h_p11, h_p12, h_p13, h_p14, h_p15,
      h3, h5, h6, h16, ZMod.val_zero]
    rw [eob_v, eoc_v]

/-- Every multiplication interaction agrees, including disabled occurrences. -/
theorem mulOperation_interactions_evaluated
    (env : Environment (ZMod p))
    (input : Var SP1Clean.MulOperation.Inputs (ZMod p)) (offset : ℕ) :
    (Extracted.MulOperation.interactions
        (Eval.eval env input.a) (Eval.eval env input.b) (Eval.eval env input.c)
        (Eval.eval env input.cols)
        (Expression.eval env input.is_real)
        (Expression.eval env input.is_mul) (Expression.eval env input.is_mulh)
        (Expression.eval env input.is_mulw) (Expression.eval env input.is_mulhu)
        (Expression.eval env input.is_mulhsu)).map Extracted.Interaction.toAccess =
      (((SP1Clean.MulOperation.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have h := mulOperation_interactions_exact env input offset
    (Eval.eval env input.a) (Eval.eval env input.b) (Eval.eval env input.c)
    (Eval.eval env input.cols)
    (Expression.eval env input.is_real) (Expression.eval env input.is_mulw)
    rfl rfl
    (eval_word_getElem env input.b 0 (by decide)).symm
    (eval_word_getElem env input.b 1 (by decide)).symm
    (eval_word_getElem env input.b 2 (by decide)).symm
    (eval_word_getElem env input.b 3 (by decide)).symm
    (eval_word_getElem env input.c 0 (by decide)).symm
    (eval_word_getElem env input.c 1 (by decide)).symm
    (eval_word_getElem env input.c 2 (by decide)).symm
    (eval_word_getElem env input.c 3 (by decide)).symm
    (eval_word_getElem env input.a 1 (by decide)).symm
    (eval_mulOperation_bLower env input.cols 0 (by decide)).symm
    (eval_mulOperation_bLower env input.cols 1 (by decide)).symm
    (eval_mulOperation_bLower env input.cols 2 (by decide)).symm
    (eval_mulOperation_bLower env input.cols 3 (by decide)).symm
    (eval_mulOperation_cLower env input.cols 0 (by decide)).symm
    (eval_mulOperation_cLower env input.cols 1 (by decide)).symm
    (eval_mulOperation_cLower env input.cols 2 (by decide)).symm
    (eval_mulOperation_cLower env input.cols 3 (by decide)).symm
    (eval_mulOperation_bMsb env input.cols).symm
    (eval_mulOperation_cMsb env input.cols).symm
    (eval_mulOperation_productMsb env input.cols).symm
    (eval_mulOperation_carry env input.cols 0 (by decide)).symm
    (eval_mulOperation_carry env input.cols 1 (by decide)).symm
    (eval_mulOperation_carry env input.cols 2 (by decide)).symm
    (eval_mulOperation_carry env input.cols 3 (by decide)).symm
    (eval_mulOperation_carry env input.cols 4 (by decide)).symm
    (eval_mulOperation_carry env input.cols 5 (by decide)).symm
    (eval_mulOperation_carry env input.cols 6 (by decide)).symm
    (eval_mulOperation_carry env input.cols 7 (by decide)).symm
    (eval_mulOperation_carry env input.cols 8 (by decide)).symm
    (eval_mulOperation_carry env input.cols 9 (by decide)).symm
    (eval_mulOperation_carry env input.cols 10 (by decide)).symm
    (eval_mulOperation_carry env input.cols 11 (by decide)).symm
    (eval_mulOperation_carry env input.cols 12 (by decide)).symm
    (eval_mulOperation_carry env input.cols 13 (by decide)).symm
    (eval_mulOperation_carry env input.cols 14 (by decide)).symm
    (eval_mulOperation_carry env input.cols 15 (by decide)).symm
    (eval_mulOperation_product env input.cols 0 (by decide)).symm
    (eval_mulOperation_product env input.cols 1 (by decide)).symm
    (eval_mulOperation_product env input.cols 2 (by decide)).symm
    (eval_mulOperation_product env input.cols 3 (by decide)).symm
    (eval_mulOperation_product env input.cols 4 (by decide)).symm
    (eval_mulOperation_product env input.cols 5 (by decide)).symm
    (eval_mulOperation_product env input.cols 6 (by decide)).symm
    (eval_mulOperation_product env input.cols 7 (by decide)).symm
    (eval_mulOperation_product env input.cols 8 (by decide)).symm
    (eval_mulOperation_product env input.cols 9 (by decide)).symm
    (eval_mulOperation_product env input.cols 10 (by decide)).symm
    (eval_mulOperation_product env input.cols 11 (by decide)).symm
    (eval_mulOperation_product env input.cols 12 (by decide)).symm
    (eval_mulOperation_product env input.cols 13 (by decide)).symm
    (eval_mulOperation_product env input.cols 14 (by decide)).symm
    (eval_mulOperation_product env input.cols 15 (by decide)).symm
  simpa only [Extracted.MulOperation.interactions] using h

private theorem mulChip_state_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : MulChip.Columns (ZMod p))
    (hReal :
      Expression.eval env input.is_real =
        cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
    (hClkHigh :
      Expression.eval env input.state.clk_high = cols.state.clk_high)
    (hClkLow :
      Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hClkHighLimb :
      Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hPc0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (hPc1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (hPc2 : Expression.eval env input.state.pc[2] = cols.state.pc[2]) :
    ((((MulChip.main input).operations offset).interactionsWith
        stateChannel.toRaw).map (AbstractInteraction.toAccess env)) =
      ((Extracted.MulOracle.MulCols.interactions (mulChipReconfigure cols)).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.State) := by
  have hStatePull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.StateMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            ((stateChannel.pulledIf gate msg).toRaw) =
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
            ((stateChannel.pushedIf mult msg).toRaw) =
          (InteractionKind.State, "SP1State",
            [(Expression.eval env msg.clk_high).val,
             (Expression.eval env msg.clk_low).val,
             (Expression.eval env msg.pc0).val,
             (Expression.eval env msg.pc1).val,
             (Expression.eval env msg.pc2).val],
            signedVal (Expression.eval env mult)) :=
    fun mult msg => toAccess_pushIf_state env mult msg
  have hPc0' :
      (ProvableStruct.eval env input.state).pc[0] = cols.state.pc[0] := by
    rw [← ProvableStruct.eval_eq_eval env input.state]
    rw [eval_cpuState]
    exact (ProvableType.getElem_eval_fields env input.state.pc 0
      (by decide)).symm.trans hPc0
  rw [MulChip.interactionsWith_state_eq]
  simp [mulCols_interactions_decompose,
    MulChip.exposedStateInteractions, hStatePull, hStatePush,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    hReal, hClkHigh, hPc1, hPc2]
  simp only [Expression.eval,
    hClkLow, hClkHighLimb, hPc0, hPc0']
  simp only [true_and, and_true, neg_one_mul]
  simpa only [MulChip.Inputs.is_real, Expression.eval, neg_add_rev] using
    congrArg (fun value : ZMod p => signedVal (-value)) hReal

private theorem mulChip_program_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : MulChip.Columns (ZMod p))
    (hMul : Expression.eval env input.isMul = cols.is_mul)
    (hMulh : Expression.eval env input.isMulh = cols.is_mulh)
    (hMulhu : Expression.eval env input.isMulhu = cols.is_mulhu)
    (hMulhsu : Expression.eval env input.isMulhsu = cols.is_mulhsu)
    (hMulw : Expression.eval env input.isMulw = cols.is_mulw)
    (hPc0 : Expression.eval env input.state.pc[0] = cols.state.pc[0])
    (hPc1 : Expression.eval env input.state.pc[1] = cols.state.pc[1])
    (hPc2 : Expression.eval env input.state.pc[2] = cols.state.pc[2])
    (hOpA : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (hOpB : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (hOpC : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (hOpA0 : Expression.eval env input.adapter.op_a_0 = cols.adapter.op_a_0) :
    (((((MulChip.main input).operations offset).interactionsWith
        programChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult) =
      ((Extracted.MulOracle.MulCols.interactions (mulChipReconfigure cols)).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Program) := by
  have hProgramPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.ProgramMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            ((programChannel.pulledIf gate msg).toRaw) =
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
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  rw [MulChip.interactionsWith_program_eq]
  simp [mulCols_interactions_decompose,
    MulChip.exposedProgramInteractions, MulChip.exposedOpcode, hProgramPull,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    LookupAccessList.negMult, signedVal_neg hp2,
    Opcode.ofNat, ConstraintCoe.coe_eq_val,
    hPc0, hPc1, hPc2, hOpA, hOpB, hOpC, hOpA0]
  simp only [Expression.eval, hMul, hMulh, hMulhu, hMulhsu, hMulw]
  rw [neg_one_mul, signedVal_neg hp2]
  simp

set_option linter.unusedSimpArgs false in
private theorem mulChip_memory_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : MulChip.Columns (ZMod p))
    (hReal :
      Expression.eval env input.is_real =
        cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw)
    (hClkHigh :
      Expression.eval env input.state.clk_high = cols.state.clk_high)
    (hClkLow :
      Expression.eval env input.state.clk_0_16 = cols.state.clk_0_16)
    (hClkHighLimb :
      Expression.eval env input.state.clk_16_24 = cols.state.clk_16_24)
    (hOpA : Expression.eval env input.adapter.op_a = cols.adapter.op_a)
    (hOpB : Expression.eval env input.adapter.op_b = cols.adapter.op_b)
    (hOpC : Expression.eval env input.adapter.op_c = cols.adapter.op_c)
    (hA0 : env.get (offset + 45) = cols.a[0])
    (hA1 : env.get (offset + 46) = cols.a[1])
    (hA2 : env.get (offset + 47) = cols.a[2])
    (hA3 : env.get (offset + 48) = cols.a[3])
    (hPrevLowA :
      Expression.eval env input.adapter.op_a_memory.access_timestamp.prev_low =
        cols.adapter.op_a_memory.access_timestamp.prev_low)
    (hPrevA0 :
      Expression.eval env input.adapter.op_a_memory.prev_value[0] =
        cols.adapter.op_a_memory.prev_value[0])
    (hPrevA1 :
      Expression.eval env input.adapter.op_a_memory.prev_value[1] =
        cols.adapter.op_a_memory.prev_value[1])
    (hPrevA2 :
      Expression.eval env input.adapter.op_a_memory.prev_value[2] =
        cols.adapter.op_a_memory.prev_value[2])
    (hPrevA3 :
      Expression.eval env input.adapter.op_a_memory.prev_value[3] =
        cols.adapter.op_a_memory.prev_value[3])
    (hPrevLowB :
      Expression.eval env input.adapter.op_b_memory.access_timestamp.prev_low =
        cols.adapter.op_b_memory.access_timestamp.prev_low)
    (hPrevB0 :
      Expression.eval env input.adapter.op_b_memory.prev_value[0] =
        cols.adapter.op_b_memory.prev_value[0])
    (hPrevB1 :
      Expression.eval env input.adapter.op_b_memory.prev_value[1] =
        cols.adapter.op_b_memory.prev_value[1])
    (hPrevB2 :
      Expression.eval env input.adapter.op_b_memory.prev_value[2] =
        cols.adapter.op_b_memory.prev_value[2])
    (hPrevB3 :
      Expression.eval env input.adapter.op_b_memory.prev_value[3] =
        cols.adapter.op_b_memory.prev_value[3])
    (hPrevLowC :
      Expression.eval env input.adapter.op_c_memory.access_timestamp.prev_low =
        cols.adapter.op_c_memory.access_timestamp.prev_low)
    (hPrevC0 :
      Expression.eval env input.adapter.op_c_memory.prev_value[0] =
        cols.adapter.op_c_memory.prev_value[0])
    (hPrevC1 :
      Expression.eval env input.adapter.op_c_memory.prev_value[1] =
        cols.adapter.op_c_memory.prev_value[1])
    (hPrevC2 :
      Expression.eval env input.adapter.op_c_memory.prev_value[2] =
        cols.adapter.op_c_memory.prev_value[2])
    (hPrevC3 :
      Expression.eval env input.adapter.op_c_memory.prev_value[3] =
        cols.adapter.op_c_memory.prev_value[3]) :
    List.Perm
      (((((MulChip.main input).operations offset).interactionsWith
        memoryChannel.toRaw).map
          (AbstractInteraction.toAccess env)).map LookupAccessList.negMult)
      (((Extracted.MulOracle.MulCols.interactions (mulChipReconfigure cols)).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Memory)) := by
  have hMemoryPull :
      ∀ (gate : Expression (ZMod p))
        (msg : SP1Clean.Channels.MemoryMsg (Expression (ZMod p))),
        AbstractInteraction.toAccess env
            ((memoryChannel.pulledIf gate msg).toRaw) =
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
            ((memoryChannel.pushedIf mult msg).toRaw) =
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
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 24 < p)
    omega
  have hNegFlags :
      -cols.is_mulw +
          (-cols.is_mulhsu + (-cols.is_mulhu + (-cols.is_mulh + -cols.is_mul))) =
        -(cols.is_mul + cols.is_mulh + cols.is_mulhu +
          cols.is_mulhsu + cols.is_mulw) := by
    ring
  rw [MulChip.interactionsWith_memory_eq]
  simp only [MulChip.exposedMemoryInteractions, List.map_cons, List.map_nil,
    hMemoryPull, hMemoryPush, List.map_map, Function.comp_apply]
  simp [mulCols_interactions_decompose,
    Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.RTypeReader.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    LookupAccessList.negMult, signedVal_neg hp2,
    hReal, hClkHigh, hClkLow, hClkHighLimb,
    hOpA, hOpB, hOpC, hA0, hA1, hA2, hA3,
    hPrevLowA, hPrevA0, hPrevA1, hPrevA2, hPrevA3,
    hPrevLowB, hPrevB0, hPrevB1, hPrevB2, hPrevB3,
    hPrevLowC, hPrevC0, hPrevC1, hPrevC2, hPrevC3]
  simp only [Expression.eval, Vector.getElem_mapRange, Nat.add_zero,
    hReal, hClkLow, hClkHighLimb, hA0, hA1, hA2, hA3,
    neg_one_mul, ZMod.val_zero]
  rw [hNegFlags]
  simp only [signedVal_neg hp2, neg_neg]
  have hRealSum := hReal
  change Expression.eval env input.isMul + Expression.eval env input.isMulh +
    Expression.eval env input.isMulhu + Expression.eval env input.isMulhsu +
    Expression.eval env input.isMulw = _ at hRealSum
  rw [hRealSum]
  exact (List.perm_append_comm
    (l₁ := [_, _, _, _]) (l₂ := [_])).append_left [_]

private theorem mulChip_byte_interactions_decompose
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MulChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      ((Readers.CPUState.main
        ⟨input.state,
          #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).operations offset).interactionsWith
          byteChannel.toRaw ++
      ((SP1Clean.MulOperation.main
        ⟨input.op_b_val, input.op_c_val, mul_chip_operation offset,
          input.is_real, input.isMul,
          input.isMulh, input.isMulhu,
          input.isMulhsu, input.isMulw, mul_chip_a offset⟩).operations
            (offset + 49)).interactionsWith byteChannel.toRaw ++
      ((Readers.RTypeReader.main
        ⟨input.adapter, input.is_real, input.is_real,
          input.state.clk_high,
          input.state.clk_0_16 + input.state.clk_16_24 * 65536,
          input.state.pc,
          input.isMul * 11 +
            input.isMulh * 12 +
            input.isMulhu * 13 +
            input.isMulhsu * 14 +
            input.isMulw * 24,
          (mul_chip_a offset)[0], (mul_chip_a offset)[1],
          (mul_chip_a offset)[2], (mul_chip_a offset)[3]⟩).operations
            (offset + 49)).interactionsWith byteChannel.toRaw := by
  simp [MulChip.main, mul_chip_operation, MulChip.Inputs.is_real,
    mul_chip_a,
    Readers.CPUState.circuit, Readers.RTypeReader.circuit,
    Readers.RegisterWrite.circuit,
    SP1Clean.MulOperation.circuit,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
  simp [Operations.interactionsWith, Readers.RegisterWrite.main,
    circuit_norm, Nat.add_assoc]

private theorem mulChip_operation_interactions_active
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    LookupAccessList.active
        ((Extracted.MulOperation.interactions (F := ZMod p)
          (Eval.eval env (mul_chip_a (p := p) offset))
          (Eval.eval env input.op_b_val)
          (Eval.eval env input.op_c_val)
          (Eval.eval env (mul_chip_operation (p := p) offset))
          (Expression.eval env (input.is_real))
          (Expression.eval env (input.isMul))
          (Expression.eval env (input.isMulh))
          (Expression.eval env (input.isMulw))
          (Expression.eval env (input.isMulhu))
          (Expression.eval env (input.isMulhsu))).map
          Extracted.Interaction.toAccess) =
      LookupAccessList.active
        (List.map (AbstractInteraction.toAccess env)
          (((SP1Clean.MulOperation.main
            ⟨input.op_b_val, input.op_c_val,
              mul_chip_operation (p := p) offset,
              input.is_real,
              input.isMul,
              input.isMulh,
              input.isMulhu,
              input.isMulhsu,
              input.isMulw, mul_chip_a offset⟩).operations
                (offset + 49)).interactionsWith byteChannel.toRaw)) := by
  let opInput : Var SP1Clean.MulOperation.Inputs (ZMod p) :=
    ⟨input.op_b_val, input.op_c_val,
      mul_chip_operation (p := p) offset,
      input.is_real,
      input.isMul,
      input.isMulh,
      input.isMulhu,
      input.isMulhsu,
      input.isMulw, mul_chip_a offset⟩
  exact congrArg LookupAccessList.active
    (mulOperation_interactions_evaluated env opInput (offset + 49))

omit [Fact (2 ^ 24 < p)] in
private theorem mulOperation_accesses_filter_byte
    (a b c : Word (ZMod p))
    (cols : Circuits.Types.MulOperation (ZMod p))
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu : ZMod p) :
    ((Extracted.MulOperation.interactions a b c cols
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Byte) =
      (Extracted.MulOperation.interactions a b c cols
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu).map
        Extracted.Interaction.toAccess := by
  simp [Extracted.MulOperation.interactions,
    Extracted.U16toU8OperationSafe.interactions,
    Extracted.U16MSBOperation.interactions,
    Extracted.Interaction.toAccess]

/-- No interaction of `MulChip.main` sits outside the chip's four declared buses. Proved through the
elaborated circuit's `channels_subset` — deliberately **without unfolding `MulChip.main`**, which is
what makes it cheap (see the note on `mulChip_interactions_faithful`). -/
private theorem mulUnexpectedInteractions_empty
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions ((MulChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈ ((MulChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown := (MulChip.circuit (p := p)).channels_subset input offset hchannel
  simp only [MulChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

-- Formerly the only anchor in this file exceeding the plain default (measured floor bracket
-- (220000, 250000], declared 300000). The whole cost was one bare non-`only` `simp` discharging the
-- `unexpectedInteractions … = []` side goal by unfolding `MulChip.main` and all eight subcircuit
-- `main`/`circuit` bodies -- a textbook whnf-into-an-expensive-value: the diagnostic counters were
-- the row-eval chain (`Eq.rec` 6006, `List.rec` 5102, `ProvableTypeList.rec` 2985,
-- `componentsToElements` 2395, `Environment.get` 3959) and the failure phase was `isDefEq` *inside*
-- that simp. Routing the side goal through `mulUnexpectedInteractions_empty`, which uses the
-- elaborated circuit's `channels_subset` and never unfolds `main` (the pattern already used by
-- Jal/Jalr/Branch/Load*/ShiftLeft), dropped the floor below 5000 -- >44x -- and the ceiling is gone.
private theorem mulChip_interactions_faithful
    (env : Environment (ZMod p))
    (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : MulChip.Columns (ZMod p))
    (hbind : BindsChipOutput MulChip.main env input offset cols) :
    List.Perm
      (LookupAccessList.active
        (nativeAccesses env ((MulChip.main input).operations offset)))
      (LookupAccessList.active (mulChipOracle.accesses cols)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (MulChip.elaborated (p := p)) hbind
  rw [MulChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval, MulChip.eval_columns] at hbind
  dsimp only at hbind
  simp only [ProvableType.eval_field] at hbind
  let rustCols : MulChip.Columns (ZMod p) :=
    { state := Eval.eval env input.state
      adapter := Eval.eval env input.adapter
      a := Eval.eval env (mul_chip_a (p := p) offset)
      mul_operation := Eval.eval env (mul_chip_operation (p := p) offset)
      is_mul := Expression.eval env (input.isMul)
      is_mulh := Expression.eval env (input.isMulh)
      is_mulhu := Expression.eval env (input.isMulhu)
      is_mulhsu := Expression.eval env (input.isMulhsu)
      is_mulw := Expression.eval env (input.isMulw) }
  change rustCols = cols at hbind
  subst cols
  have hReal :
      Expression.eval env input.is_real =
        rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
          rustCols.is_mulhsu + rustCols.is_mulw := by
    rfl
  have hStateEval := eval_cpuState env input.state
  have hStatePc :=
    congrArg (fun state : Circuits.Types.CPUState (ZMod p) => state.pc)
      hStateEval
  have hClkHigh :
      Expression.eval env input.state.clk_high =
        rustCols.state.clk_high := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.state.clk_high).symm.trans
      (congrArg
        (fun state : Circuits.Types.CPUState (ZMod p) => state.clk_high)
        hStateEval).symm
  have hClkLow :
      Expression.eval env input.state.clk_0_16 =
        rustCols.state.clk_0_16 := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.state.clk_0_16).symm.trans
      (congrArg
        (fun state : Circuits.Types.CPUState (ZMod p) => state.clk_0_16)
        hStateEval).symm
  have hClkHighLimb :
      Expression.eval env input.state.clk_16_24 =
        rustCols.state.clk_16_24 := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.state.clk_16_24).symm.trans
      (congrArg
        (fun state : Circuits.Types.CPUState (ZMod p) => state.clk_16_24)
        hStateEval).symm
  have hAdapterEval := eval_rTypeReader env input.adapter
  have hAdapterOpA :
      Expression.eval env input.adapter.op_a = rustCols.adapter.op_a := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.adapter.op_a).symm.trans
      (congrArg
        (fun adapter : Circuits.Types.RTypeReader (ZMod p) => adapter.op_a)
        hAdapterEval).symm
  have hAdapterOpB :
      Expression.eval env input.adapter.op_b = rustCols.adapter.op_b := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.adapter.op_b).symm.trans
      (congrArg
        (fun adapter : Circuits.Types.RTypeReader (ZMod p) => adapter.op_b)
        hAdapterEval).symm
  have hAdapterOpC :
      Expression.eval env input.adapter.op_c = rustCols.adapter.op_c := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.adapter.op_c).symm.trans
      (congrArg
        (fun adapter : Circuits.Types.RTypeReader (ZMod p) => adapter.op_c)
        hAdapterEval).symm
  have hAdapterOpA0 :
      Expression.eval env input.adapter.op_a_0 = rustCols.adapter.op_a_0 := by
    dsimp only [rustCols]
    exact (ProvableType.eval_field env input.adapter.op_a_0).symm.trans
      (congrArg
        (fun adapter : Circuits.Types.RTypeReader (ZMod p) => adapter.op_a_0)
        hAdapterEval).symm
  have hS := mulChip_state_interactions_faithful env input offset
    rustCols hReal hClkHigh hClkLow hClkHighLimb
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 0
        (by decide)).trans
          (congrArg (fun pc => pc[0]) hStatePc.symm))
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 1
        (by decide)).trans
          (congrArg (fun pc => pc[1]) hStatePc.symm))
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 2
        (by decide)).trans
          (congrArg (fun pc => pc[2]) hStatePc.symm))
  have hP := mulChip_program_interactions_faithful env input offset
    rustCols
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 0
        (by decide)).trans
          (congrArg (fun pc => pc[0]) hStatePc.symm))
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 1
        (by decide)).trans
          (congrArg (fun pc => pc[1]) hStatePc.symm))
    (by
      dsimp only [rustCols]
      exact (ProvableType.getElem_eval_fields env input.state.pc 2
        (by decide)).trans
          (congrArg (fun pc => pc[2]) hStatePc.symm))
    hAdapterOpA hAdapterOpB hAdapterOpC hAdapterOpA0
  have hM := mulChip_memory_interactions_faithful env input offset
    rustCols hReal hClkHigh hClkLow hClkHighLimb
    hAdapterOpA hAdapterOpB hAdapterOpC
    (by
      simp only [rustCols, ← ProvableType.getElem_eval_fields,
        mul_chip_a, Vector.getElem_mapRange, Expression.eval, Nat.add_zero])
    (by
      simp only [rustCols, ← ProvableType.getElem_eval_fields,
        mul_chip_a, Vector.getElem_mapRange, Expression.eval])
    (by
      simp only [rustCols, ← ProvableType.getElem_eval_fields,
        mul_chip_a, Vector.getElem_mapRange, Expression.eval])
    (by
      simp only [rustCols, ← ProvableType.getElem_eval_fields,
        mul_chip_a, Vector.getElem_mapRange, Expression.eval])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        eval_registerAccessTimestamp, ProvableType.eval_field])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
    (by
      simp only [rustCols, eval_rTypeReader, eval_registerAccessCols,
        ← ProvableType.getElem_eval_fields])
  have hEvalB :
      Eval.eval env input.op_b_val =
        rustCols.adapter.op_b_memory.prev_value := by
    dsimp only [MulChip.Inputs.op_b_val, rustCols]
    calc
      _ = (Eval.eval env input.adapter.op_b_memory).prev_value := by
        exact (congrArg
          (fun value : Circuits.Types.RegisterAccessCols (ZMod p) =>
            value.prev_value)
          (Readers.RTypeReader.eval_registerAccessCols env
            input.adapter.op_b_memory)).symm
      _ = (Eval.eval env input.adapter).op_b_memory.prev_value := by
        exact congrArg
          (fun value : Circuits.Types.RegisterAccessCols (ZMod p) =>
            value.prev_value)
          (congrArg
            (fun value : Circuits.Types.RTypeReader (ZMod p) =>
              value.op_b_memory)
            (Readers.RTypeReader.eval_cols env input.adapter)).symm
  have hEvalC :
      Eval.eval env input.op_c_val =
        rustCols.adapter.op_c_memory.prev_value := by
    dsimp only [MulChip.Inputs.op_c_val, rustCols]
    calc
      _ = (Eval.eval env input.adapter.op_c_memory).prev_value := by
        exact (congrArg
          (fun value : Circuits.Types.RegisterAccessCols (ZMod p) =>
            value.prev_value)
          (Readers.RTypeReader.eval_registerAccessCols env
            input.adapter.op_c_memory)).symm
      _ = (Eval.eval env input.adapter).op_c_memory.prev_value := by
        exact congrArg
          (fun value : Circuits.Types.RegisterAccessCols (ZMod p) =>
            value.prev_value)
          (congrArg
            (fun value : Circuits.Types.RTypeReader (ZMod p) =>
              value.op_c_memory)
            (Readers.RTypeReader.eval_cols env input.adapter)).symm
  have hO := mulChip_operation_interactions_active env input offset
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state,
      #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩
  have hCpuByte :=
    cpustate_byte_interactions_faithful_syntactic env cpuInput offset
      rustCols.state
      #v[rustCols.state.pc[0] + 4,
        rustCols.state.pc[1], rustCols.state.pc[2]]
      8
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)
      (by simpa only [cpuInput] using hReal)
      (by simpa only [cpuInput] using hClkLow)
      (by simpa only [cpuInput] using hClkHighLimb)
  let rtypeInput : Var Readers.RTypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real,
      input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc,
      input.isMul * 11 +
        input.isMulh * 12 +
        input.isMulhu * 13 +
        input.isMulhsu * 14 +
        input.isMulw * 24,
      (mul_chip_a offset)[0], (mul_chip_a offset)[1],
      (mul_chip_a offset)[2], (mul_chip_a offset)[3]⟩
  have hRtypeByte :=
    rtypereader_byte_interactions_faithful_syntactic env rtypeInput
      (offset + 49)
      rustCols.state.clk_high
      (rustCols.state.clk_0_16 + rustCols.state.clk_16_24 * 65536)
      rustCols.state.pc
      (rustCols.is_mul * 11 + rustCols.is_mulh * 12 +
        rustCols.is_mulhu * 13 + rustCols.is_mulhsu * 14 +
        rustCols.is_mulw * 24)
      rustCols.a rustCols.adapter
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)
      (by simpa only [rtypeInput] using hReal)
      (by
        simp only [rtypeInput, Expression.eval, hClkLow, hClkHighLimb])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
      (by
        simp only [rtypeInput, rustCols, eval_rTypeReader,
          eval_registerAccessCols, eval_registerAccessTimestamp,
          ProvableType.eval_field])
  let rustOperationAccesses : LookupAccessList :=
    (Extracted.MulOperation.interactions rustCols.a
      rustCols.adapter.op_b_memory.prev_value
      rustCols.adapter.op_c_memory.prev_value rustCols.mul_operation
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)
      rustCols.is_mul rustCols.is_mulh rustCols.is_mulw
      rustCols.is_mulhu rustCols.is_mulhsu).map
        Extracted.Interaction.toAccess
  let rustCpuAccesses : LookupAccessList :=
    (Extracted.CPUState.interactions rustCols.state
      #v[rustCols.state.pc[0] + 4,
        rustCols.state.pc[1], rustCols.state.pc[2]]
      8
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)).map
          Extracted.Interaction.toAccess
  let rustRtypeAccesses : LookupAccessList :=
    (Extracted.RTypeReader.interactions rustCols.state.clk_high
      (rustCols.state.clk_0_16 + rustCols.state.clk_16_24 * 65536)
      rustCols.state.pc
      (rustCols.is_mul * 11 + rustCols.is_mulh * 12 +
        rustCols.is_mulhu * 13 + rustCols.is_mulhsu * 14 +
        rustCols.is_mulw * 24)
      rustCols.a rustCols.adapter
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)
      (rustCols.is_mul + rustCols.is_mulh + rustCols.is_mulhu +
        rustCols.is_mulhsu + rustCols.is_mulw)).map
          Extracted.Interaction.toAccess
  let nativeCpuAccesses : LookupAccessList :=
    (((Readers.CPUState.main cpuInput).operations offset).interactionsWith
      byteChannel.toRaw).map (AbstractInteraction.toAccess env)
  let nativeOperationAccesses : LookupAccessList :=
    (((SP1Clean.MulOperation.main
      ⟨input.op_b_val, input.op_c_val,
        mul_chip_operation (p := p) offset,
        input.is_real,
        input.isMul,
        input.isMulh,
        input.isMulhu,
        input.isMulhsu,
        input.isMulw, mul_chip_a offset⟩).operations
          (offset + 49)).interactionsWith byteChannel.toRaw).map
            (AbstractInteraction.toAccess env)
  let nativeRtypeAccesses : LookupAccessList :=
    (((Readers.RTypeReader.main rtypeInput).operations
      (offset + 49)).interactionsWith byteChannel.toRaw).map
        (AbstractInteraction.toAccess env)
  have hRustByte :
      (mulChipOracle.accesses rustCols).filter
          (fun access => access.1 = InteractionKind.Byte) =
        rustOperationAccesses ++
          rustCpuAccesses.filter
            (fun access => access.1 = InteractionKind.Byte) ++
          rustRtypeAccesses.filter
            (fun access => access.1 = InteractionKind.Byte) := by
    change
      ((Extracted.MulOracle.MulCols.interactions (mulChipReconfigure rustCols)).map
        Extracted.Interaction.toAccess).filter
          (fun access => access.1 = InteractionKind.Byte) = _
    rw [mulCols_interactions_decompose]
    simp only [List.map_append, List.filter_append]
    rw [mulOperation_accesses_filter_byte]
  have hNativeByte :
      (((MulChip.main input).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env) =
        nativeCpuAccesses ++ nativeOperationAccesses ++
          nativeRtypeAccesses := by
    rw [mulChip_byte_interactions_decompose, List.map_append,
      List.map_append]
  have hCpuByte' :
      nativeCpuAccesses =
        rustCpuAccesses.filter
          (fun access => access.1 = InteractionKind.Byte) := by
    simpa only [nativeCpuAccesses, rustCpuAccesses] using hCpuByte
  have hRtypeByte' :
      nativeRtypeAccesses =
        rustRtypeAccesses.filter
          (fun access => access.1 = InteractionKind.Byte) := by
    simpa only [nativeRtypeAccesses, rustRtypeAccesses] using hRtypeByte
  have hOperationByte' :
      LookupAccessList.active rustOperationAccesses =
        LookupAccessList.active nativeOperationAccesses := by
    rw [hEvalB, hEvalC] at hO
    simpa only [rustOperationAccesses, nativeOperationAccesses,
      rustCols, MulChip.Inputs.is_real, eval_add,
      Expression.eval] using hO
  have hB :
      List.Perm
        (LookupAccessList.active
          ((((MulChip.main input).operations offset).interactionsWith
            byteChannel.toRaw).map (AbstractInteraction.toAccess env)))
        (LookupAccessList.active
          ((mulChipOracle.accesses rustCols).filter
            (fun access => access.1 = InteractionKind.Byte))) := by
    rw [hNativeByte, hRustByte, hCpuByte', hRtypeByte']
    have hOperationPerm :
        (List.filter
          (fun access => LookupAccessList.multOf access ≠ 0)
          nativeOperationAccesses).Perm
        (List.filter
          (fun access => LookupAccessList.multOf access ≠ 0)
          rustOperationAccesses) := by
      exact List.Perm.of_eq (by
        simpa only [LookupAccessList.active] using hOperationByte'.symm)
    simp only [LookupAccessList.active, List.filter_append]
    refine List.Perm.trans
      (((List.Perm.refl _).append hOperationPerm).append_right _) ?_
    exact (List.perm_append_comm (l₁ := _) (l₂ := _)).append_right _
  have hStateActive :
      List.Perm
        (LookupAccessList.active
          ((((MulChip.main input).operations offset).interactionsWith
            stateChannel.toRaw).map (AbstractInteraction.toAccess env)))
        ((LookupAccessList.active (mulChipOracle.accesses rustCols)).filter
          (fun access => access.1 = InteractionKind.State)) := by
    have h := congrArg LookupAccessList.active hS
    rw [LookupAccessList.active_filter] at h
    exact List.Perm.of_eq h
  have hByteActive := hB
  rw [LookupAccessList.active_filter] at hByteActive
  have hMemoryActive :=
    LookupAccessList.active_perm hM
  rw [LookupAccessList.active_filter] at hMemoryActive
  have hProgramActive :
      List.Perm
        (LookupAccessList.active
          (((((MulChip.main input).operations offset).interactionsWith
            programChannel.toRaw).map
              (AbstractInteraction.toAccess env)).map
                LookupAccessList.negMult))
        ((LookupAccessList.active (mulChipOracle.accesses rustCols)).filter
          (fun access => access.1 = InteractionKind.Program)) := by
    have h := congrArg LookupAccessList.active hP
    rw [LookupAccessList.active_filter] at h
    exact List.Perm.of_eq h
  have hUnexpected := mulUnexpectedInteractions_empty (p := p) input offset
  simp only [nativeAccesses]
  rw [hUnexpected]
  simp only [List.map_nil, List.append_nil]
  refine List.Perm.trans ?_
    (Extracted.active_perm_filter_by_kind_of_no_raw _
      (by simp [ChipOracle.nativeInteractions, mulChipOracle, Extracted.Interaction.IsRaw,
        Extracted.CPUState.interactions,
        Extracted.MulOracle.MulCols.interactions, Extracted.MulOracle.MulOperation.interactions,
        Extracted.MulOracle.U16MSBOperation.interactions,
        Extracted.MulOracle.U16toU8OperationSafe.interactions,
        Extracted.RTypeReader.interactions,
])).symm
  simp only [LookupAccessList.active] at hStateActive
  simp only [LookupAccessList.active] at hByteActive
  simp only [LookupAccessList.active] at hMemoryActive
  simp only [LookupAccessList.active] at hProgramActive
  simp only [LookupAccessList.active, List.filter_append]
  exact ((hStateActive.append hByteActive).append hMemoryActive).append
    hProgramActive

/-- Constructive interaction half of Mul faithfulness, for arbitrary rows. -/
theorem mulChip_interactions_constructive
    (rustCols : Extracted.MulOracle.MulCols (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := mulChipRowCodec.assignment
      (mulChipOracle.deconfigure rustCols) data
    List.Perm
      (LookupAccessList.active
        (nativeAccesses assignment.environment
          ({ circuit := MulChip.circuit (p := p) } :
            Air.Flat.Component (ZMod p)).operations))
      (LookupAccessList.active (mulChipOracle.rustAccesses rustCols)) := by
  dsimp only
  let cols := mulChipOracle.deconfigure rustCols
  let assignment := mulChipRowCodec.assignment cols data
  have hbind : BindsChipOutput MulChip.main assignment.environment
      ({ circuit := MulChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowInputVar
      ({ circuit := MulChip.circuit (p := p) } :
        Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [MulChip.circuit_main_eq] at h
    exact h
  have hfaithful := mulChip_interactions_faithful
    assignment.environment
    ({ circuit := MulChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowInputVar
    ({ circuit := MulChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (MulChip.circuit (p := p)) assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    MulChip.circuit_main_eq] using hfaithful

/-- Whole-chip faithfulness package for the complete pinned v6.4.0 Mul AIR. -/
theorem mulChip_faithful :
    ChipFaithful (p := p) MulChip.Inputs MulChip.Columns
      Extracted.MulOracle.MulCols MulChip.circuit mulChipRowCodec mulChipOracle where
  constraints := mulChip_constraints_constructive (p := p)
  interactions := fun cols data _ => mulChip_interactions_constructive (p := p) cols data

end SP1Clean.Faithful
