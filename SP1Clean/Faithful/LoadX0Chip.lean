import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.LoadX0
import SP1Clean.Proofs.Chips.LoadX0Chip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `LoadX0`

This file relates the native Clean `LoadX0Chip` row to the complete Rust-generated row-level oracle
for pinned SP1 v6.4.0. The `ChipFaithful` theorem at the bottom covers every `assertZero`
expression and the entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated LoadX0 oracle namespace. -/
def loadX0OracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.LoadX0Oracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `loadX0OracleAddressOperation`. -/
def loadX0NativeAddressOperation {F : Type} (cols : Extracted.LoadX0Oracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate (the `ITypeReaderImmutable` assertion family is an imported helper of the
oracle, not an embedded copy); the address block is copied into Rust's chip-private operation row.
This is not an operation-level faithfulness claim. -/
def loadX0ChipReconfigure {F : Type} (cols : LoadX0Chip.Columns F) :
    Extracted.LoadX0Oracle.LoadX0Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadX0OracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    is_lb := cols.is_lb
    is_lbu := cols.is_lbu
    is_lh := cols.is_lh
    is_lhu := cols.is_lhu
    is_lw := cols.is_lw
    is_lwu := cols.is_lwu
    is_ld := cols.is_ld }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def loadX0ChipDeconfigure {F : Type} (cols : Extracted.LoadX0Oracle.LoadX0Columns F) :
    LoadX0Chip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadX0NativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    is_lb := cols.is_lb
    is_lbu := cols.is_lbu
    is_lh := cols.is_lh
    is_lhu := cols.is_lhu
    is_lw := cols.is_lw
    is_lwu := cols.is_lwu
    is_ld := cols.is_ld }

/-- SP1 Rust's complete LoadX0-chip oracle, viewed from the native Lean row. -/
def loadX0ChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F LoadX0Chip.Columns Extracted.LoadX0Oracle.LoadX0Columns where
  reconfigure := loadX0ChipReconfigure
  deconfigure := loadX0ChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.LoadX0Oracle.LoadX0Columns.asserts
  interactions := Extracted.LoadX0Oracle.LoadX0Columns.interactions

/- Namespace bridges between the LoadX0 oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address-op
lemmas below stay stated once against the standalone modules (also consumed by the other load and
store chips). The `ITypeReaderImmutable` calls need no bridge — the oracle imports the canonical
module directly. -/

private theorem loadX0Oracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadX0Oracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.LoadX0Oracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem loadX0Oracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadX0Oracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.LoadX0Oracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem loadX0Oracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadX0Oracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadX0Oracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [loadX0Oracle_addrAdd_asserts_eq]

private theorem loadX0Oracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadX0Oracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadX0Oracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [loadX0Oracle_addrAdd_interactions_eq]

def loadX0ChipInput {F : Type}
    (cols : LoadX0Chip.Columns F) : LoadX0Chip.Inputs F :=
  { is_lb := cols.is_lb
    is_lbu := cols.is_lbu
    is_lh := cols.is_lh
    is_lhu := cols.is_lhu
    is_lw := cols.is_lw
    is_lwu := cols.is_lwu
    is_ld := cols.is_ld
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit }

def loadX0ChipLocals {F : Type}
    (cols : LoadX0Chip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def loadX0ChipPhysicalRow {F : Type}
    (cols : LoadX0Chip.Columns F) : Array F :=
  inputFirstRow (loadX0ChipInput cols) (loadX0ChipLocals cols)

def loadX0ChipColumnsOfInput {F : Type}
    (input : LoadX0Chip.Inputs F) (locals : Vector F 4) :
    LoadX0Chip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.is_lb, input.is_lbu,
    input.is_lh, input.is_lhu, input.is_lw, input.is_lwu, input.is_ld⟩

private theorem loadX0Vec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadX0Vec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadX0EvalVec4Components
    {F : Type} [FiniteField F] (env : Environment F)
    (value : Vector (Expression F) 4) :
    #v[(Eval.eval env value)[0], (Eval.eval env value)[1],
      (Eval.eval env value)[2], (Eval.eval env value)[3]] =
      #v[Expression.eval env value[0], Expression.eval env value[1],
        Expression.eval env value[2], Expression.eval env value[3]] := by
  apply Vector.ext
  intro i hi
  interval_cases i
  · exact (ProvableType.getElem_eval_fields env value 0 (by decide)).symm
  · exact (ProvableType.getElem_eval_fields env value 1 (by decide)).symm
  · exact (ProvableType.getElem_eval_fields env value 2 (by decide)).symm
  · exact (ProvableType.getElem_eval_fields env value 3 (by decide)).symm

private theorem loadX0AddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem loadX0CpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem loadX0ITypeEta {F : Type}
    (cols : Extracted.ITypeReader F) :
    ({ op_a := cols.op_a
       op_a_memory :=
         { prev_value := cols.op_a_memory.prev_value
           access_timestamp := cols.op_a_memory.access_timestamp }
       op_a_0 := cols.op_a_0
       op_b := cols.op_b
       op_b_memory :=
         { prev_value := cols.op_b_memory.prev_value
           access_timestamp := cols.op_b_memory.access_timestamp }
       op_c_imm := cols.op_c_imm } : Extracted.ITypeReader F) = cols := by
  cases cols with
  | mk opA opAMem opA0 opB opBMem opC =>
    cases opAMem
    cases opBMem
    rfl

theorem loadX0ChipColumnsOfInput_roundtrip {F : Type}
    (cols : LoadX0Chip.Columns F) :
    loadX0ChipColumnsOfInput
        (loadX0ChipInput cols) (loadX0ChipLocals cols) = cols := by
  cases cols
  simp [loadX0ChipColumnsOfInput, loadX0ChipInput,
    loadX0ChipLocals, loadX0Vec3Eta]

@[circuit_norm] private theorem loadX0EvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalAddrAddInput
    {F : Type} [FiniteField F] (env : Environment F)
    (input : AddrAddOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a
         b := Eval.eval env input.b
         cols := Eval.eval env input.cols
         is_real := Eval.eval env input.is_real } :
        AddrAddOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalAddressInput
    {F : Type} [FiniteField F] (env : Environment F)
    (input : AddressOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ b := Eval.eval env input.b
         cc := Eval.eval env input.cc
         offset_bit0 := Eval.eval env input.offset_bit0
         offset_bit1 := Eval.eval env input.offset_bit1
         offset_bit2 := Eval.eval env input.offset_bit2
         is_real := Eval.eval env input.is_real } :
        AddressOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalMemoryInput
    {F : Type} [FiniteField F] (env : Environment F)
    (input : Readers.MemoryAccess.Inputs (Expression F)) :
    Eval.eval env input =
      ({ mem := Eval.eval env input.mem
         clk_high := Eval.eval env input.clk_high
         clk_low := Eval.eval env input.clk_low
         addr0 := Eval.eval env input.addr0
         addr1 := Eval.eval env input.addr1
         addr2 := Eval.eval env input.addr2
         new_value := Eval.eval env input.new_value
         is_real := Eval.eval env input.is_real } :
        Readers.MemoryAccess.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalMemoryTimestamp
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessTimestamp (Expression F)) :
    Eval.eval env cols =
      ({ prev_high := Eval.eval env cols.prev_high
         prev_low := Eval.eval env cols.prev_low
         compare_low := Eval.eval env cols.compare_low
         diff_low_limb := Eval.eval env cols.diff_low_limb
         diff_high_limb := Eval.eval env cols.diff_high_limb } :
        Extracted.MemoryAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadX0EvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem evalLoadX0DirectOutput
    (input : LoadX0Chip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((LoadX0Chip.elaborated (p := p)).output
          (varFromOffset LoadX0Chip.Inputs 0)
          (size LoadX0Chip.Inputs)) =
      loadX0ChipColumnsOfInput input locals := by
  rw [LoadX0Chip.directOutput_eq]
  rw [← CircuitType.eval_expression, LoadX0Chip.eval_columns]
  unfold loadX0ChipColumnsOfInput
  rw [LoadX0Chip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [LoadX0Chip.eval_inputs, LoadX0Chip.Inputs.mk.injEq] at hinputEval
  rcases hinputEval with
    ⟨hLb, hLbu, hLh, hLhu, hLw, hLwu, hLd, hState, hAdapter,
      hMemory, hOffset⟩
  refine ⟨hState, hAdapter, ?_, hMemory, hOffset, hLb, hLbu,
    hLh, hLhu, hLw, hLwu, hLd⟩
  rw [loadX0EvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadX0EvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size LoadX0Chip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size LoadX0Chip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size LoadX0Chip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))

def loadX0ChipRowCodec :
    ChipRowCodec LoadX0Chip.Inputs LoadX0Chip.Columns
      (LoadX0Chip.circuit (p := p)) where
  assignment cols data := {
    row := loadX0ChipPhysicalRow cols
    input := loadX0ChipInput cols
    width_eq := by
      rw [loadX0ChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, LoadX0Chip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (LoadX0Chip.circuit (p := p))
        (loadX0ChipInput cols) (loadX0ChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((LoadX0Chip.main _).output _) = _
      rw [LoadX0Chip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalLoadX0DirectOutput (p := p)
        (loadX0ChipInput cols) (loadX0ChipLocals cols) data).trans
          (loadX0ChipColumnsOfInput_roundtrip cols) }

theorem loadX0ChipLookupsEmpty :
    (⟨LoadX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LoadX0Chip.circuit_main_eq]
  simp [LoadX0Chip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def loadX0AddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0EvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (loadX0AddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [loadX0AddressCols]
  rw [loadX0EvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadX0EvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def loadX0IsReal
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
    input.is_lw + input.is_lwu + input.is_ld

private def loadX0Opcode
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh +
    33 * input.is_lhu + 31 * input.is_lw + 34 * input.is_lwu +
    35 * input.is_ld

private def loadX0AddressInput
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
    input.offset_bit[1], input.offset_bit[2], loadX0IsReal input⟩

private def loadX0AddressValue
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (loadX0AddressInput input) (loadX0AddressCols offset)

private def loadX0CpuInput
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, loadX0IsReal input⟩

private def loadX0MemoryInput
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (loadX0AddressValue input offset)[0],
    (loadX0AddressValue input offset)[1],
    (loadX0AddressValue input offset)[2],
    input.memory_access.prev_value, loadX0IsReal input⟩

private def loadX0ITypeInput
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, loadX0IsReal input, loadX0IsReal input,
    input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, loadX0Opcode input⟩

private def loadX0Bool
    (selector : Expression (ZMod p)) : Expression (ZMod p) :=
  selector * (selector - (1 : Expression (ZMod p)))

private def loadX0Align2
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_ld * input.offset_bit[2]

private def loadX0Align1
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1]

private def loadX0Align0
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu +
    input.is_ld) * input.offset_bit[0]

private def loadX0OpAReal
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  loadX0IsReal input * (input.adapter.op_a_0 - 1)

private def loadX0OpAInactive
    (input : Var LoadX0Chip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (loadX0IsReal input - 1) * input.adapter.op_a_0

private theorem loadX0NativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadX0Chip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (loadX0CpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (loadX0AddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (loadX0MemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReaderImmutable.main
              (loadX0ITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lb, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lbu, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lh, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lhu, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lw, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_lwu, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Bool input.is_ld, 0)).operations (offset + 4))) ∧
        Expression.eval env (loadX0Bool (loadX0IsReal input)) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Align2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Align1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0Align0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0OpAReal input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadX0OpAInactive input, 0)).operations (offset + 4))) := by
  simp only [nativeAssertZeros, LoadX0Chip.main,
    loadX0IsReal, loadX0Opcode,
    loadX0CpuInput, loadX0AddressInput, loadX0AddressCols,
    loadX0AddressValue, loadX0MemoryInput,
    loadX0ITypeInput, loadX0Bool, loadX0Align2, loadX0Align1,
    loadX0Align0, loadX0OpAReal, loadX0OpAInactive,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit,
    Readers.ITypeReaderImmutable.circuit,
    circuit_norm, List.map_append, List.forall_append, List.forall_cons]

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0AddrAddAssertions
    (env : Environment (ZMod p))
    (input : Var AddrAddOperation.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (Extracted.AddrAddOperation.asserts
          #v[Expression.eval env input.a[0],
            Expression.eval env input.a[1],
            Expression.eval env input.a[2],
            Expression.eval env input.a[3]]
          #v[Expression.eval env input.b[0],
            Expression.eval env input.b[1],
            Expression.eval env input.b[2],
            Expression.eval env input.b[3]]
          ⟨#v[Expression.eval env input.cols.value[0],
            Expression.eval env input.cols.value[1],
            Expression.eval env input.cols.value[2]]⟩
          (Expression.eval env input.is_real)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((AddrAddOperation.main input).operations offset)) := by
  rw [Extracted.AddrAddOperation.asserts]
  simp only [nativeAssertZeros, AddrAddOperation.main, circuit_norm,
    List.map_append, List.map_cons, List.Forall]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [eval_sub, Expression.eval, add_zero, sub_zero]
  simp only [← ProvableStruct.eval_eq_eval,
    loadX0EvalAddrAddInput, loadX0EvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem loadX0AddressAssertions
    (env : Environment (ZMod p))
    (input : Var AddressOperation.Inputs (ZMod p))
    (offset : ℕ) :
    List.Forall (· = 0)
        (Extracted.AddressOperation.asserts
          #v[Expression.eval env input.b[0],
            Expression.eval env input.b[1],
            Expression.eval env input.b[2],
            Expression.eval env input.b[3]]
          #v[Expression.eval env input.cc[0],
            Expression.eval env input.cc[1],
            Expression.eval env input.cc[2],
            Expression.eval env input.cc[3]]
          (Expression.eval env input.offset_bit0)
          (Expression.eval env input.offset_bit1)
          (Expression.eval env input.offset_bit2)
          (Expression.eval env input.is_real)
          ⟨⟨#v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)]⟩, env.get (offset + 3)⟩) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((AddressOperation.main input).operations offset)) := by
  let cols := loadX0AddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := loadX0AddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, loadX0AddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    loadX0EvalAddressInput, ProvableType.eval_field,
    ProvableType.getElem_eval_fields,
    Vector.getElem_mapRange, Expression.eval, Nat.add_zero] at hAddrAdd ⊢
  rw [hAddrAdd]
  rw [CanonicalReader.equalityAssertionList]
  rw [CanonicalReader.equalityAssertionList]
  rw [CanonicalReader.equalityAssertionList]
  rw [CanonicalReader.equalityAssertionList]
  simp only [eval_sub, Expression.eval]
  simp only [List.singleton_append, List.Forall, sub_zero]
  tauto

private def loadX0MemoryAssertionValues
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p)) :
    List (ZMod p) :=
  let ts := input.mem.access_timestamp
  [ Expression.eval env (input.is_real * (input.is_real - 1)),
    Expression.eval env
      (input.is_real * (ts.compare_low * (ts.compare_low - 1))) -
        Expression.eval env 0,
    Expression.eval env
      (input.is_real * (ts.compare_low * (input.clk_high - ts.prev_high))) -
        Expression.eval env 0,
    Expression.eval env
      (input.is_real *
        ((ts.compare_low * (input.clk_low + 1) +
            (1 - ts.compare_low) * input.clk_high -
            (ts.compare_low * ts.prev_low +
              (1 - ts.compare_low) * ts.prev_high) - 1) -
          (ts.diff_low_limb + ts.diff_high_limb * 65536))) -
        Expression.eval env 0 ]

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0MemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      loadX0MemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [loadX0MemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, loadX0EvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

private def loadX0ChipRustColumns
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    LoadX0Chip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (loadX0AddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Eval.eval env input.offset_bit
    is_lb := Expression.eval env input.is_lb
    is_lbu := Expression.eval env input.is_lbu
    is_lh := Expression.eval env input.is_lh
    is_lhu := Expression.eval env input.is_lhu
    is_lw := Expression.eval env input.is_lw
    is_lwu := Expression.eval env input.is_lwu
    is_ld := Expression.eval env input.is_ld }

private def loadX0NativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (loadX0CpuInput input)).operations offset))

private def loadX0NativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (loadX0AddressInput input)).operations offset))

private def loadX0NativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (loadX0MemoryAssertionValues env
      (loadX0MemoryInput input offset))

private def loadX0NativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReaderImmutable.main
        (loadX0ITypeInput input)).operations (offset + 4)))

private def loadX0NativeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadX0NativeCpuMeaning env input offset ∧
    loadX0NativeAddressMeaning env input offset ∧
    loadX0NativeMemoryMeaning env input offset ∧
    loadX0NativeITypeMeaning env input offset ∧
    Expression.eval env (loadX0Bool input.is_lb) = 0 ∧
    Expression.eval env (loadX0Bool input.is_lbu) = 0 ∧
    Expression.eval env (loadX0Bool input.is_lh) = 0 ∧
    Expression.eval env (loadX0Bool input.is_lhu) = 0 ∧
    Expression.eval env (loadX0Bool input.is_lw) = 0 ∧
    Expression.eval env (loadX0Bool input.is_lwu) = 0 ∧
    Expression.eval env (loadX0Bool input.is_ld) = 0 ∧
    Expression.eval env (loadX0Bool (loadX0IsReal input)) = 0 ∧
    Expression.eval env (loadX0Align2 input) = 0 ∧
    Expression.eval env (loadX0Align1 input) = 0 ∧
    Expression.eval env (loadX0Align0 input) = 0 ∧
    Expression.eval env (loadX0OpAReal input) = 0 ∧
    Expression.eval env (loadX0OpAInactive input) = 0

private def loadX0RustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadX0ChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
      (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
        cols.is_lw + cols.is_lwu + cols.is_ld)
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def loadX0RustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadX0ChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
        cols.is_lw + cols.is_lwu + cols.is_ld))

private def loadX0RustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadX0ChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let isReal := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
    cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode := 29 * cols.is_lb + 32 * cols.is_lbu + 30 * cols.is_lh +
    33 * cols.is_lhu + 31 * cols.is_lw + 34 * cols.is_lwu +
    35 * cols.is_ld
  List.Forall (· = 0)
    (Extracted.ITypeReaderImmutable.asserts cols.state.clk_high clkLow
      cols.state.pc opcode
      { op_a := cols.adapter.op_a
        op_a_memory :=
          { prev_value := cols.adapter.op_a_memory.prev_value
            access_timestamp := cols.adapter.op_a_memory.access_timestamp }
        op_a_0 := cols.adapter.op_a_0
        op_b := cols.adapter.op_b
        op_b_memory :=
          { prev_value := cols.adapter.op_b_memory.prev_value
            access_timestamp := cols.adapter.op_b_memory.access_timestamp }
        op_c_imm := cols.adapter.op_c_imm }
      isReal isReal)

private def loadX0RustTailMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadX0ChipRustColumns env input offset
  let ts := cols.memory_access.access_timestamp
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let isReal := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
    cols.is_lw + cols.is_lwu + cols.is_ld
  List.Forall (· = 0)
    [ cols.is_lb * (cols.is_lb - 1),
      cols.is_lbu * (cols.is_lbu - 1),
      cols.is_lh * (cols.is_lh - 1),
      cols.is_lhu * (cols.is_lhu - 1),
      cols.is_lw * (cols.is_lw - 1),
      cols.is_lwu * (cols.is_lwu - 1),
      cols.is_ld * (cols.is_ld - 1),
      isReal * (isReal - 1),
      cols.is_ld * cols.offset_bit[2],
      (cols.is_lw + cols.is_lwu + cols.is_ld) * cols.offset_bit[1],
      (cols.is_lh + cols.is_lhu + cols.is_lw + cols.is_lwu +
        cols.is_ld) * cols.offset_bit[0],
      isReal * (isReal - 1),
      isReal * (ts.compare_low * (ts.compare_low - 1)),
      isReal * (ts.compare_low *
        (cols.state.clk_high - ts.prev_high)),
      isReal *
        ((ts.compare_low * (clkLow + 1) +
            (1 - ts.compare_low) * cols.state.clk_high -
            (ts.compare_low * ts.prev_low +
              (1 - ts.compare_low) * ts.prev_high) - 1) -
          (ts.diff_low_limb + ts.diff_high_limb * 65536)),
      isReal * (cols.adapter.op_a_0 - 1),
      (isReal - 1) * cols.adapter.op_a_0 ]

private def loadX0RustMeaning
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadX0RustAddressMeaning env input offset ∧
    loadX0RustCpuMeaning env input offset ∧
    loadX0RustITypeMeaning env input offset ∧
    loadX0RustTailMeaning env input offset

private theorem loadX0NativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadX0Chip.main input).operations offset)) ↔
      loadX0NativeMeaning env input offset := by
  rw [loadX0NativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (loadX0MemoryInput input offset)).operations (offset + 4)) =
        loadX0MemoryAssertionValues env
          (loadX0MemoryInput input offset) by
    exact loadX0MemoryAssertionList env
      (loadX0MemoryInput input offset) (offset + 4)]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rfl

private def loadX0ExtractedMeaning
    (cols : LoadX0Chip.Columns (ZMod p)) : Prop :=
  let isReal := cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
    cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode := 29 * cols.is_lb + 32 * cols.is_lbu + 30 * cols.is_lh +
    33 * cols.is_lhu + 31 * cols.is_lw + 34 * cols.is_lwu +
    35 * cols.is_ld
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let ts := cols.memory_access.access_timestamp
  List.Forall (· = 0)
      (Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2] isReal
        { addr_operation :=
            { value := cols.address_operation.addr_operation.value }
          top_two_limb_inv := cols.address_operation.top_two_limb_inv }) ∧
    List.Forall (· = 0)
      (Extracted.CPUState.asserts
        { clk_high := cols.state.clk_high
          clk_16_24 := cols.state.clk_16_24
          clk_0_16 := cols.state.clk_0_16
          pc := cols.state.pc }
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 isReal) ∧
    List.Forall (· = 0)
      (Extracted.ITypeReaderImmutable.asserts cols.state.clk_high clkLow
        cols.state.pc opcode
        { op_a := cols.adapter.op_a
          op_a_memory :=
            { prev_value := cols.adapter.op_a_memory.prev_value
              access_timestamp := cols.adapter.op_a_memory.access_timestamp }
          op_a_0 := cols.adapter.op_a_0
          op_b := cols.adapter.op_b
          op_b_memory :=
            { prev_value := cols.adapter.op_b_memory.prev_value
              access_timestamp := cols.adapter.op_b_memory.access_timestamp }
          op_c_imm := cols.adapter.op_c_imm }
        isReal isReal) ∧
    List.Forall (· = 0)
      [ cols.is_lb * (cols.is_lb - 1),
        cols.is_lbu * (cols.is_lbu - 1),
        cols.is_lh * (cols.is_lh - 1),
        cols.is_lhu * (cols.is_lhu - 1),
        cols.is_lw * (cols.is_lw - 1),
        cols.is_lwu * (cols.is_lwu - 1),
        cols.is_ld * (cols.is_ld - 1),
        isReal * (isReal - 1),
        cols.is_ld * cols.offset_bit[2],
        (cols.is_lw + cols.is_lwu + cols.is_ld) * cols.offset_bit[1],
        (cols.is_lh + cols.is_lhu + cols.is_lw + cols.is_lwu +
          cols.is_ld) * cols.offset_bit[0],
        isReal * (isReal - 1),
        isReal * (ts.compare_low * (ts.compare_low - 1)),
        isReal * (ts.compare_low * (cols.state.clk_high - ts.prev_high)),
        isReal *
          ((ts.compare_low * (clkLow + 1) +
              (1 - ts.compare_low) * cols.state.clk_high -
              (ts.compare_low * ts.prev_low +
                (1 - ts.compare_low) * ts.prev_high) - 1) -
            (ts.diff_low_limb + ts.diff_high_limb * 65536)),
        isReal * (cols.adapter.op_a_0 - 1),
        (isReal - 1) * cols.adapter.op_a_0 ]

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0ExtractedAssertionsDecompose
    (cols : LoadX0Chip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.LoadX0Oracle.LoadX0Columns.asserts
          (loadX0ChipReconfigure cols)) ↔
      loadX0ExtractedMeaning cols := by
  simp only [Extracted.LoadX0Oracle.LoadX0Columns.asserts, List.forall_append]
  dsimp only [loadX0ChipReconfigure, loadX0OracleAddressOperation]
  simp only [loadX0Oracle_address_asserts_eq]
  simp only [loadX0Vec3Eta, loadX0Vec4Eta]
  simp only [loadX0ExtractedMeaning, List.Forall]
  have hAddress := congrArg
    (fun address =>
      Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
        (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld) address)
    (loadX0AddressEta (cols := cols.address_operation))
  have hCpu := congrArg
    (fun state =>
      Extracted.CPUState.asserts state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld))
    (loadX0CpuEta (cols := cols.state))
  have hIType := congrArg
    (fun adapter =>
      Extracted.ITypeReaderImmutable.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc
        (29 * cols.is_lb + 32 * cols.is_lbu + 30 * cols.is_lh +
          33 * cols.is_lhu + 31 * cols.is_lw + 34 * cols.is_lwu +
          35 * cols.is_ld)
        adapter
        (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld)
        (cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
          cols.is_lw + cols.is_lwu + cols.is_ld))
    (loadX0ITypeEta (cols := cols.adapter))
  rw [hAddress, hCpu, hIType]
  constructor
  · rintro ⟨hABC, hTail⟩
    rcases hABC with ⟨hAB, hC⟩
    rcases hAB with ⟨hA, hB⟩
    exact ⟨hA, hB, hC, hTail⟩
  · rintro ⟨hA, hB, hC, hTail⟩
    exact ⟨⟨⟨hA, hB⟩, hC⟩, hTail⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0RustMeaning_eq
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustMeaning env input offset =
      loadX0ExtractedMeaning
        (loadX0ChipRustColumns env input offset) := by
  apply propext
  unfold loadX0RustMeaning loadX0RustAddressMeaning
    loadX0RustCpuMeaning loadX0RustITypeMeaning loadX0RustTailMeaning
    loadX0ExtractedMeaning
  simp only [loadX0Vec4Eta]

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0RustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadX0ChipOracle.nativeAssertZeros
          (loadX0ChipRustColumns env input offset)) ↔
      loadX0RustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, loadX0ChipOracle]
  rw [loadX0RustMeaning_eq]
  exact loadX0ExtractedAssertionsDecompose
    (loadX0ChipRustColumns env input offset)

private theorem loadX0AddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustAddressMeaning env input offset ↔
      loadX0NativeAddressMeaning env input offset := by
  have hAddress := loadX0AddressAssertions (p := p) env
    (loadX0AddressInput input) offset
  unfold loadX0RustAddressMeaning loadX0NativeAddressMeaning
  dsimp only [loadX0ChipRustColumns]
  rw [loadX0EvalAddressCols]
  have hb :
      #v[(Eval.eval env input.adapter).op_b_memory.prev_value[0],
        (Eval.eval env input.adapter).op_b_memory.prev_value[1],
        (Eval.eval env input.adapter).op_b_memory.prev_value[2],
        (Eval.eval env input.adapter).op_b_memory.prev_value[3]] =
        #v[Expression.eval env input.adapter.op_b_memory.prev_value[0],
          Expression.eval env input.adapter.op_b_memory.prev_value[1],
          Expression.eval env input.adapter.op_b_memory.prev_value[2],
          Expression.eval env input.adapter.op_b_memory.prev_value[3]] := by
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    rw [eval_registerAccessCols]
    dsimp only
    change
      #v[(Eval.eval env input.adapter.op_b_memory.prev_value)[0],
        (Eval.eval env input.adapter.op_b_memory.prev_value)[1],
        (Eval.eval env input.adapter.op_b_memory.prev_value)[2],
        (Eval.eval env input.adapter.op_b_memory.prev_value)[3]] = _
    exact loadX0EvalVec4Components env
      input.adapter.op_b_memory.prev_value
  have hc :
      #v[(Eval.eval env input.adapter).op_c_imm[0],
        (Eval.eval env input.adapter).op_c_imm[1],
        (Eval.eval env input.adapter).op_c_imm[2],
        (Eval.eval env input.adapter).op_c_imm[3]] =
        #v[Expression.eval env input.adapter.op_c_imm[0],
          Expression.eval env input.adapter.op_c_imm[1],
          Expression.eval env input.adapter.op_c_imm[2],
          Expression.eval env input.adapter.op_c_imm[3]] := by
    rw [Readers.ITypeReader.eval_cols]
    dsimp only
    change
      #v[(Eval.eval env input.adapter.op_c_imm)[0],
        (Eval.eval env input.adapter.op_c_imm)[1],
        (Eval.eval env input.adapter.op_c_imm)[2],
        (Eval.eval env input.adapter.op_c_imm)[3]] = _
    exact loadX0EvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [loadX0AddressInput, loadX0IsReal] at hAddress
  rw [ProvableType.getElem_eval_fields env input.offset_bit 0 (by decide),
    ProvableType.getElem_eval_fields env input.offset_bit 1 (by decide),
    ProvableType.getElem_eval_fields env input.offset_bit 2 (by decide)] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0CpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustCpuMeaning env input offset ↔
      loadX0NativeCpuMeaning env input offset := by
  let cpu := loadX0CpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env (loadX0IsReal input)) (by
      simp only [cpu, loadX0CpuInput,
        ProvableStruct.structEvalLiteralProc])
  have hNext :
      #v[(Eval.eval env input.state).pc[0] + 4,
        (Eval.eval env input.state).pc[1],
        (Eval.eval env input.state).pc[2]] =
        #v[Expression.eval env (input.state.pc[0] + 4),
          Expression.eval env input.state.pc[1],
          Expression.eval env input.state.pc[2]] := by
    rw [eval_cpuState]
    dsimp only
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, eval_add, Expression.eval] using
        congrArg (· + 4)
          (ProvableType.getElem_eval_fields env input.state.pc 0
            (by decide)).symm
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env input.state.pc 1
          (by decide)).symm
    · simpa only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero] using
        (ProvableType.getElem_eval_fields env input.state.pc 2
          (by decide)).symm
  unfold loadX0RustCpuMeaning loadX0NativeCpuMeaning
  dsimp only [loadX0ChipRustColumns]
  rw [hNext]
  simp only [cpu, loadX0CpuInput, loadX0IsReal] at hCpu
  exact hCpu

private theorem loadX0ITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustITypeMeaning env input offset ↔
      loadX0NativeITypeMeaning env input offset := by
  let readerInput := loadX0ITypeInput input
  have hIType := CanonicalReader.iTypeImmutableAssertionsExact
    (p := p) env readerInput (offset + 4)
    (Expression.eval env input.state.clk_high)
    (Expression.eval env
      (input.state.clk_0_16 + input.state.clk_16_24 * 65536))
    (Expression.eval env (loadX0Opcode input))
    (Expression.eval env (loadX0IsReal input))
    (Expression.eval env (loadX0IsReal input))
    (Eval.eval env input.state.pc)
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput, loadX0ITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadX0ITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadX0ITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      simp only [ProvableType.eval_field])
    (by
      simp only [readerInput, loadX0ITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 0 (by decide))
    (by
      simp only [readerInput, loadX0ITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 1 (by decide))
    (by
      simp only [readerInput, loadX0ITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 2 (by decide))
    (by
      simp only [readerInput, loadX0ITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      dsimp only
      rw [eval_registerAccessCols]
      exact ProvableType.getElem_eval_fields env
        input.adapter.op_a_memory.prev_value 3 (by decide))
    rfl
  unfold loadX0RustITypeMeaning loadX0NativeITypeMeaning
  dsimp only [loadX0ChipRustColumns]
  simp only [readerInput, loadX0ITypeInput] at hIType
  simpa only [loadX0ITypeInput, loadX0IsReal, loadX0Opcode,
    eval_cpuState, loadX0EvalMemoryCols, Readers.ITypeReader.eval_cols,
    ProvableType.eval_field, eval_add, eval_mul, Expression.eval] using hIType

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0TailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustTailMeaning env input offset ↔
      loadX0NativeMemoryMeaning env input offset ∧
        Expression.eval env (loadX0Bool input.is_lb) = 0 ∧
        Expression.eval env (loadX0Bool input.is_lbu) = 0 ∧
        Expression.eval env (loadX0Bool input.is_lh) = 0 ∧
        Expression.eval env (loadX0Bool input.is_lhu) = 0 ∧
        Expression.eval env (loadX0Bool input.is_lw) = 0 ∧
        Expression.eval env (loadX0Bool input.is_lwu) = 0 ∧
        Expression.eval env (loadX0Bool input.is_ld) = 0 ∧
        Expression.eval env (loadX0Bool (loadX0IsReal input)) = 0 ∧
        Expression.eval env (loadX0Align2 input) = 0 ∧
        Expression.eval env (loadX0Align1 input) = 0 ∧
        Expression.eval env (loadX0Align0 input) = 0 ∧
        Expression.eval env (loadX0OpAReal input) = 0 ∧
        Expression.eval env (loadX0OpAInactive input) = 0 := by
  unfold loadX0RustTailMeaning loadX0NativeMemoryMeaning
  dsimp only [loadX0ChipRustColumns]
  simp only [loadX0MemoryAssertionValues, loadX0MemoryInput,
    List.Forall, Readers.ITypeReader.eval_opA0,
    eval_cpuState, loadX0EvalMemoryCols,
    loadX0EvalMemoryTimestamp,
    ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    loadX0IsReal, loadX0Bool, loadX0Align2, loadX0Align1,
    loadX0Align0, loadX0OpAReal, loadX0OpAInactive,
    eval_sub, Expression.eval, sub_zero]
  ring_nf
  tauto

private theorem loadX0ChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    loadX0RustMeaning env input offset ↔
      loadX0NativeMeaning env input offset := by
  unfold loadX0RustMeaning loadX0NativeMeaning
  rw [loadX0AddressMeaningFaithful, loadX0CpuMeaningFaithful,
    loadX0ITypeMeaningFaithful, loadX0TailMeaningFaithful]
  tauto

private theorem loadX0ChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadX0ChipOracle.nativeAssertZeros
          (loadX0ChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadX0Chip.main input).operations offset)) :=
  (loadX0RustAssertionsDecompose (p := p) env input offset).trans
    ((loadX0ChipMeaningFaithful (p := p) env input offset).trans
      (loadX0NativeAssertionsDecompose (p := p) env input offset).symm)

theorem loadX0ChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadX0Chip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadX0Chip.main env input offset cols) :
    List.Forall (· = 0)
        (loadX0ChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadX0Chip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadX0Chip.elaborated (p := p)) hbind
  rw [LoadX0Chip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadX0Chip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadX0ChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact loadX0ChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem loadX0ChipConstraintsConstructive
    (rustCols : Extracted.LoadX0Oracle.LoadX0Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadX0ChipRowCodec.assignment
      (loadX0ChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (loadX0ChipOracle.assertZeros rustCols) ↔
      (⟨LoadX0Chip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := loadX0ChipOracle.deconfigure rustCols
  let assignment := loadX0ChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadX0Chip.main assignment.environment
        (⟨LoadX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadX0Chip.circuit_main_eq] at h
    exact h
  have hfaithful := loadX0ChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨LoadX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (loadX0ChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨LoadX0Chip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      LoadX0Chip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (LoadX0Chip.circuit (p := p))
      assignment.environment loadX0ChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private def loadX0StateInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf (loadX0IsReal input)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf (loadX0IsReal input)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def loadX0ProgramInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf (loadX0IsReal input)
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       loadX0Opcode input,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem loadX0StateInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadX0Chip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (loadX0StateInteractions input).map ChannelInteraction.toRaw :=
  (LoadX0Chip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (loadX0StateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadX0Chip.circuit, loadX0StateInteractions,
      loadX0IsReal, expose])

private theorem loadX0ProgramInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadX0Chip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (loadX0ProgramInteractions input).map ChannelInteraction.toRaw :=
  (LoadX0Chip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (loadX0ProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadX0Chip.circuit, loadX0ProgramInteractions,
      loadX0IsReal, loadX0Opcode, expose])

private theorem loadX0StateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((((loadX0StateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.LoadX0Oracle.LoadX0Columns.interactions
          (loadX0ChipReconfigure
            (loadX0ChipRustColumns env input offset))).map
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
  simp only [loadX0StateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.LoadX0Oracle.LoadX0Columns.interactions,
    loadX0ChipReconfigure, loadX0OracleAddressOperation,
    Extracted.LoadX0Oracle.AddressOperation.interactions,
    Extracted.LoadX0Oracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    loadX0ChipRustColumns, loadX0EvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    loadX0IsReal, Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem loadX0ProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    (((((loadX0ProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.LoadX0Oracle.LoadX0Columns.interactions
          (loadX0ChipReconfigure
            (loadX0ChipRustColumns env input offset))).map
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
  simp only [loadX0ProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.LoadX0Oracle.LoadX0Columns.interactions,
    loadX0ChipReconfigure, loadX0OracleAddressOperation,
    Extracted.LoadX0Oracle.AddressOperation.interactions,
    Extracted.LoadX0Oracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    loadX0ChipRustColumns, loadX0EvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    loadX0IsReal, loadX0Opcode, Expression.eval,
    LookupAccessList.negMult,
    Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat]
  rw [show
    -(ProvableStruct.eval env input).is_ld +
        (-(ProvableStruct.eval env input).is_lwu +
          (-(ProvableStruct.eval env input).is_lw +
            (-(ProvableStruct.eval env input).is_lhu +
              (-(ProvableStruct.eval env input).is_lh +
                (-(ProvableStruct.eval env input).is_lbu +
                  -(ProvableStruct.eval env input).is_lb))))) =
        -((ProvableStruct.eval env input).is_ld +
          (ProvableStruct.eval env input).is_lwu +
          (ProvableStruct.eval env input).is_lw +
          (ProvableStruct.eval env input).is_lhu +
          (ProvableStruct.eval env input).is_lh +
          (ProvableStruct.eval env input).is_lbu +
          (ProvableStruct.eval env input).is_lb) by
    ring_nf]
  rw [signedVal_neg hp2, neg_neg]
  congr 1
  ring_nf

private theorem loadX0PermMemoryBlocks {α : Type}
    (ram registers : List α) :
    List.Perm (ram ++ registers) (registers ++ ram) :=
  List.perm_append_comm

private theorem loadX0MemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((LoadX0Chip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.LoadX0Oracle.LoadX0Columns.interactions
          (loadX0ChipReconfigure
            (loadX0ChipRustColumns env input offset))).map
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
  simp only [LoadX0Chip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.LoadX0Oracle.LoadX0Columns.interactions,
    loadX0ChipReconfigure, loadX0OracleAddressOperation,
    Extracted.LoadX0Oracle.AddressOperation.interactions,
    Extracted.LoadX0Oracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.LoadX0Oracle.AddressOperation.value,
    loadX0ChipRustColumns, loadX0EvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadX0EvalMemoryCols, loadX0EvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval,
    LookupAccessList.negMult,
    Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  have hGateNeg :
      -(ProvableStruct.eval env input).is_ld +
          (-(ProvableStruct.eval env input).is_lwu +
            (-(ProvableStruct.eval env input).is_lw +
              (-(ProvableStruct.eval env input).is_lhu +
                (-(ProvableStruct.eval env input).is_lh +
                  (-(ProvableStruct.eval env input).is_lbu +
                    -(ProvableStruct.eval env input).is_lb))))) =
        -((ProvableStruct.eval env input).is_lb +
          (ProvableStruct.eval env input).is_lbu +
          (ProvableStruct.eval env input).is_lh +
          (ProvableStruct.eval env input).is_lhu +
          (ProvableStruct.eval env input).is_lw +
          (ProvableStruct.eval env input).is_lwu +
          (ProvableStruct.eval env input).is_ld) := by
    ring_nf
  simp only [hGateNeg, signedVal_neg hp2, neg_neg]
  exact loadX0PermMemoryBlocks [_, _] [_, _, _, _]

private def loadX0CpuByteInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def loadX0AddressByteInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, var { index := offset },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, var { index := offset + 1 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, var { index := offset + 2 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, ((var { index := offset } : Expression (ZMod p)) -
          (4 : Expression (ZMod p)) * input.offset_bit[2] -
          (2 : Expression (ZMod p)) * input.offset_bit[1] -
          input.offset_bit[0]) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def loadX0MemoryByteInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def loadX0ITypeByteInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 +
    input.state.clk_16_24 * 65536
  [ byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨3, 0, (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (loadX0IsReal input)
      ⟨3, 0, (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩ ]

private def loadX0ByteInteractions
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
    loadX0CpuByteInteractions input ++
    loadX0AddressByteInteractions input offset ++
    loadX0MemoryByteInteractions input ++
    loadX0ITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0CpuByteInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (loadX0CpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadX0CpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [loadX0CpuInput, loadX0CpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem loadX0AddressByteInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (loadX0AddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadX0AddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [loadX0AddressInput, loadX0AddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem loadX0MemoryByteInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (loadX0MemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadX0MemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [loadX0MemoryInput, loadX0MemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

private theorem loadX0ITypeByteInteractionsEq
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.main
        (loadX0ITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadX0ITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadX0ITypeInput, loadX0ITypeByteInteractions,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadX0ByteInteractionsDecompose
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadX0Chip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadX0ByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [show
      ((LoadX0Chip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (loadX0CpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (loadX0AddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (loadX0MemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReaderImmutable.main
            (loadX0ITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [LoadX0Chip.main, loadX0CpuInput, loadX0AddressInput,
    loadX0MemoryInput, loadX0AddressValue, loadX0AddressCols,
    loadX0ITypeInput, loadX0IsReal, loadX0Opcode,
    Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReaderImmutable.circuit,
    Gadgets.Equality.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Operations.interactionsWith]]
  rw [loadX0CpuByteInteractionsEq,
    loadX0AddressByteInteractionsEq,
    loadX0MemoryByteInteractionsEq,
    loadX0ITypeByteInteractionsEq]
  simp only [loadX0ByteInteractions, List.map_append]

private theorem loadX0PermFourBlocks {α : Type}
    (a b c d : List α) :
    List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ d ++ c) := by
  have hab : List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ c ++ d) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right
        (c ++ d)
  have hcd : List.Perm (c ++ d) (d ++ c) :=
    List.perm_append_comm
  exact hab.trans (by
    simpa only [List.append_assoc] using hcd.append_left (b ++ a))

private theorem loadX0ByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((LoadX0Chip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.LoadX0Oracle.LoadX0Columns.interactions
          (loadX0ChipReconfigure
            (loadX0ChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
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
  rw [loadX0ByteInteractionsDecompose]
  simp only [loadX0ByteInteractions, List.map_append]
  simp only [loadX0CpuByteInteractions,
    loadX0AddressByteInteractions, loadX0MemoryByteInteractions,
    loadX0ITypeByteInteractions,
    List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.LoadX0Oracle.LoadX0Columns.interactions,
    loadX0ChipReconfigure, loadX0OracleAddressOperation,
    Extracted.LoadX0Oracle.AddressOperation.interactions,
    Extracted.LoadX0Oracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.LoadX0Oracle.AddressOperation.value,
    loadX0ChipRustColumns, loadX0EvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadX0EvalMemoryCols, loadX0EvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    loadX0IsReal, eval_sub, Expression.eval,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    LoadX0Chip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, loadX0EvalMemoryCols,
    loadX0EvalMemoryTimestamp, ProvableType.eval_field]
  exact loadX0PermFourBlocks
    [_, _] [_, _, _, _] [_, _] [_, _, _, _]

private theorem loadX0UnexpectedInteractionsEmpty
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((LoadX0Chip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((LoadX0Chip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (LoadX0Chip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [LoadX0Chip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem loadX0ChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadX0Chip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadX0Chip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((LoadX0Chip.main input).operations offset))
      (loadX0ChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadX0Chip.elaborated (p := p)) hbind
  rw [LoadX0Chip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadX0Chip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadX0ChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.LoadX0Oracle.LoadX0Columns.interactions
      (loadX0ChipReconfigure
        (loadX0ChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [loadX0UnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, loadX0ChipOracle]
  rw [loadX0StateInteractionsEq,
    LoadX0Chip.interactionsWith_memory_eq,
    loadX0ProgramInteractionsEq]
  have hState :=
    loadX0StateInteractionsFaithful (p := p) env input offset
  have hByte :=
    loadX0ByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    loadX0MemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    loadX0ProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem loadX0ChipInteractionsConstructive
    (rustCols : Extracted.LoadX0Oracle.LoadX0Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadX0ChipRowCodec.assignment
      (loadX0ChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨LoadX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (loadX0ChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := loadX0ChipOracle.deconfigure rustCols
  let assignment := loadX0ChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadX0Chip.main assignment.environment
        (⟨LoadX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadX0Chip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadX0Chip.circuit_main_eq] at h
    exact h
  have hfaithful := loadX0ChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨LoadX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadX0Chip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (LoadX0Chip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    LoadX0Chip.circuit_main_eq] using hfaithful

theorem loadX0Chip_faithful :
    ChipFaithful (p := p) LoadX0Chip.Inputs
      LoadX0Chip.Columns Extracted.LoadX0Oracle.LoadX0Columns
      LoadX0Chip.circuit loadX0ChipRowCodec
      loadX0ChipOracle where
  constraints := loadX0ChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (loadX0ChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
