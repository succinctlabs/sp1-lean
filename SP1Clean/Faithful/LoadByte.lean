import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.LoadByte
import SP1Clean.Proofs.Chips.LoadByteChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `LoadByte`

This file relates the native Clean `LoadByteChip` row to the complete generated row-level oracle
for pinned SP1 v6.3.1. The `ChipFaithful` theorem at the bottom covers every `assertZero`
expression and the entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated LoadByte oracle namespace. -/
def loadByteOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.LoadByteOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `loadByteOracleAddressOperation`. -/
def loadByteNativeAddressOperation {F : Type} (cols : Extracted.LoadByteOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address block is copied into Rust's chip-private operation row. This is not
an operation-level faithfulness claim. -/
def loadByteChipReconfigure {F : Type} (cols : LoadByteChip.Columns F) :
    Extracted.LoadByteOracle.LoadByteColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadByteOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_limb := cols.selected_limb
    selected_limb_low_byte := cols.selected_limb_low_byte
    selected_byte := cols.selected_byte
    msb := cols.msb
    is_lb := cols.is_lb
    is_lbu := cols.is_lbu }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def loadByteChipDeconfigure {F : Type} (cols : Extracted.LoadByteOracle.LoadByteColumns F) :
    LoadByteChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadByteNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_limb := cols.selected_limb
    selected_limb_low_byte := cols.selected_limb_low_byte
    selected_byte := cols.selected_byte
    msb := cols.msb
    is_lb := cols.is_lb
    is_lbu := cols.is_lbu }

/-- SP1 Rust's complete LoadByte-chip oracle, viewed from the native Lean row. -/
def loadByteChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F LoadByteChip.Columns Extracted.LoadByteOracle.LoadByteColumns where
  reconfigure := loadByteChipReconfigure
  deconfigure := loadByteChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.LoadByteOracle.LoadByteColumns.asserts
  interactions := Extracted.LoadByteOracle.LoadByteColumns.interactions

/- Namespace bridges between the LoadByte oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address-op
lemmas below stay stated once against the standalone modules (also consumed by the other load and
store chips). -/

private theorem loadByteOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadByteOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.LoadByteOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem loadByteOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadByteOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.LoadByteOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem loadByteOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadByteOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadByteOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [loadByteOracle_addrAdd_asserts_eq]

private theorem loadByteOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadByteOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadByteOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [loadByteOracle_addrAdd_interactions_eq]

def loadByteChipInput {F : Type}
    (cols : LoadByteChip.Columns F) : LoadByteChip.Inputs F :=
  { is_lb := cols.is_lb
    is_lbu := cols.is_lbu
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_limb := cols.selected_limb
    selected_limb_low_byte := cols.selected_limb_low_byte
    selected_byte := cols.selected_byte
    msb := cols.msb }

def loadByteChipLocals {F : Type}
    (cols : LoadByteChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def loadByteChipPhysicalRow {F : Type}
    (cols : LoadByteChip.Columns F) : Array F :=
  inputFirstRow (loadByteChipInput cols) (loadByteChipLocals cols)

def loadByteChipColumnsOfInput {F : Type}
    (input : LoadByteChip.Inputs F) (locals : Vector F 4) :
    LoadByteChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.selected_limb,
    input.selected_limb_low_byte, input.selected_byte, input.msb,
    input.is_lb, input.is_lbu⟩

private theorem loadByteVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadByteVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadByteEvalVec4Components
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

private theorem loadByteAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem loadByteCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem loadByteITypeEta {F : Type}
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

theorem loadByteChipColumnsOfInput_roundtrip {F : Type}
    (cols : LoadByteChip.Columns F) :
    loadByteChipColumnsOfInput
        (loadByteChipInput cols) (loadByteChipLocals cols) = cols := by
  cases cols
  simp [loadByteChipColumnsOfInput, loadByteChipInput,
    loadByteChipLocals, loadByteVec3Eta]

@[circuit_norm] private theorem loadByteEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadByteEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadByteEvalAddrAddInput
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

@[circuit_norm] private theorem loadByteEvalAddressInput
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

@[circuit_norm] private theorem loadByteEvalMemoryInput
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

@[circuit_norm] private theorem loadByteEvalMemoryTimestamp
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

@[circuit_norm] private theorem loadByteEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem evalLoadByteDirectOutput
    (input : LoadByteChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((LoadByteChip.elaborated (p := p)).output
          (varFromOffset LoadByteChip.Inputs 0)
          (size LoadByteChip.Inputs)) =
      loadByteChipColumnsOfInput input locals := by
  rw [LoadByteChip.directOutput_eq]
  rw [← CircuitType.eval_expression, LoadByteChip.eval_columns]
  unfold loadByteChipColumnsOfInput
  rw [LoadByteChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [LoadByteChip.eval_inputs, LoadByteChip.Inputs.mk.injEq] at hinputEval
  rcases hinputEval with
    ⟨hLb, hLbu, hState, hAdapter, hMemory, hOffset, hSelectedLimb,
      hSelectedLow, hSelectedByte, hMsb⟩
  refine ⟨hState, hAdapter, ?_, hMemory, hOffset, hSelectedLimb,
    hSelectedLow, hSelectedByte, hMsb, hLb, hLbu⟩
  rw [loadByteEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadByteEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size LoadByteChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size LoadByteChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size LoadByteChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))

def loadByteChipRowCodec :
    ChipRowCodec LoadByteChip.Inputs LoadByteChip.Columns
      (LoadByteChip.circuit (p := p)) where
  assignment cols data := {
    row := loadByteChipPhysicalRow cols
    input := loadByteChipInput cols
    width_eq := by
      rw [loadByteChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, LoadByteChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (LoadByteChip.circuit (p := p))
        (loadByteChipInput cols) (loadByteChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((LoadByteChip.main _).output _) = _
      rw [LoadByteChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalLoadByteDirectOutput (p := p)
        (loadByteChipInput cols) (loadByteChipLocals cols) data).trans
          (loadByteChipColumnsOfInput_roundtrip cols) }

theorem loadByteChipLookupsEmpty :
    (⟨LoadByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LoadByteChip.circuit_main_eq]
  simp [LoadByteChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def loadByteAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (loadByteAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [loadByteAddressCols]
  rw [loadByteEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadByteEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def loadByteAddressInput
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
    input.offset_bit[1], input.offset_bit[2],
    input.is_lb + input.is_lbu⟩

private def loadByteAddressValue
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (loadByteAddressInput input) (loadByteAddressCols offset)

private def loadByteCpuInput
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_lb + input.is_lbu⟩

private def loadByteMemoryInput
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (loadByteAddressValue input offset)[0],
    (loadByteAddressValue input offset)[1],
    (loadByteAddressValue input offset)[2],
    input.memory_access.prev_value, input.is_lb + input.is_lbu⟩

private def loadByteITypeInput
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    Var Readers.ITypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_lb + input.is_lbu,
    input.is_lb + input.is_lbu, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
    input.selected_byte + 65280 * input.msb, 65535 * input.msb,
    65535 * input.msb, 65535 * input.msb⟩

private def loadByteRegisterWriteInput
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    Var Readers.RegisterWrite.Inputs (ZMod p) :=
  ⟨input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    input.adapter.op_a,
    #v[input.selected_byte + 65280 * input.msb, 65535 * input.msb,
      65535 * input.msb, 65535 * input.msb],
    input.is_lb + input.is_lbu⟩

private def loadByteSelect0
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_limb - input.memory_access.prev_value[0]) *
    (input.offset_bit[1] - (1 : Expression (ZMod p))) *
      (input.offset_bit[2] - (1 : Expression (ZMod p)))

private def loadByteSelect1
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_limb - input.memory_access.prev_value[1]) *
    input.offset_bit[1] *
      (input.offset_bit[2] - (1 : Expression (ZMod p)))

private def loadByteSelect2
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_limb - input.memory_access.prev_value[2]) *
    (input.offset_bit[1] - (1 : Expression (ZMod p))) *
      input.offset_bit[2]

private def loadByteSelect3
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_limb - input.memory_access.prev_value[3]) *
    input.offset_bit[1] * input.offset_bit[2]

private def loadByteMux
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.selected_byte -
    (input.offset_bit[0] *
        ((input.selected_limb - input.selected_limb_low_byte) *
          Expression.const ((256 : ZMod p)⁻¹)) +
      ((1 : Expression (ZMod p)) - input.offset_bit[0]) *
        input.selected_limb_low_byte)

private def loadByteMsbZero
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lbu * input.msb

private def loadByteLbBool
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lb * (input.is_lb - (1 : Expression (ZMod p)))

private def loadByteLbuBool
    (input : Var LoadByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lbu * (input.is_lbu - (1 : Expression (ZMod p)))

private theorem loadByteNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadByteChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (loadByteCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (loadByteAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (loadByteMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReader.main
              (loadByteITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              (loadByteRegisterWriteInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteSelect0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteSelect1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteSelect2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteSelect3 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteMux input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteMsbZero input, 0)).operations (offset + 4))) ∧
        Expression.eval env (loadByteLbBool input) = 0 ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadByteLbuBool input, 0)).operations (offset + 4))) ∧
        Expression.eval env
          ((input.is_lb + input.is_lbu) *
            (input.is_lb + input.is_lbu - 1)) = 0 := by
  simp only [nativeAssertZeros, LoadByteChip.main,
    loadByteCpuInput, loadByteAddressInput, loadByteAddressCols,
    loadByteAddressValue, loadByteMemoryInput,
    loadByteITypeInput, loadByteRegisterWriteInput,
    loadByteSelect0, loadByteSelect1, loadByteSelect2, loadByteSelect3,
    loadByteMux, loadByteMsbZero, loadByteLbBool, loadByteLbuBool,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit,
    Readers.ITypeReader.circuit,
    Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append, List.forall_cons]

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteAddrAddAssertions
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
    loadByteEvalAddrAddInput, loadByteEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem loadByteAddressAssertions
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
  let cols := loadByteAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := loadByteAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, loadByteAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    loadByteEvalAddressInput, ProvableType.eval_field,
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

private def loadByteMemoryAssertionValues
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
private theorem loadByteMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      loadByteMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [loadByteMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, loadByteEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

private def loadByteChipRustColumns
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    LoadByteChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (loadByteAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Eval.eval env input.offset_bit
    selected_limb := Expression.eval env input.selected_limb
    selected_limb_low_byte := Expression.eval env input.selected_limb_low_byte
    selected_byte := Expression.eval env input.selected_byte
    msb := Expression.eval env input.msb
    is_lb := Expression.eval env input.is_lb
    is_lbu := Expression.eval env input.is_lbu }

private def loadByteNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (loadByteCpuInput input)).operations offset))

private def loadByteNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (loadByteAddressInput input)).operations offset))

private def loadByteNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (loadByteMemoryAssertionValues env
      (loadByteMemoryInput input offset))

private def loadByteNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReader.main
        (loadByteITypeInput input)).operations (offset + 4)))

private def loadByteNativeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadByteNativeCpuMeaning env input offset ∧
    loadByteNativeAddressMeaning env input offset ∧
    loadByteNativeMemoryMeaning env input offset ∧
    loadByteNativeITypeMeaning env input offset ∧
    Expression.eval env (loadByteSelect0 input) = 0 ∧
    Expression.eval env (loadByteSelect1 input) = 0 ∧
    Expression.eval env (loadByteSelect2 input) = 0 ∧
    Expression.eval env (loadByteSelect3 input) = 0 ∧
    Expression.eval env (loadByteMux input) = 0 ∧
    Expression.eval env input.adapter.op_a_0 = 0 ∧
    Expression.eval env (loadByteMsbZero input) = 0 ∧
    Expression.eval env (loadByteLbBool input) = 0 ∧
    Expression.eval env (loadByteLbuBool input) = 0 ∧
    Expression.eval env
      ((input.is_lb + input.is_lbu) *
        (input.is_lb + input.is_lbu - 1)) = 0

private def loadByteRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadByteChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
      (cols.is_lb + cols.is_lbu)
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def loadByteRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadByteChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 (cols.is_lb + cols.is_lbu))

private def loadByteRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadByteChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReader.asserts cols.state.clk_high clkLow
      cols.state.pc (29 * cols.is_lb + 32 * cols.is_lbu)
      #v[cols.selected_byte + 65280 * cols.msb, 65535 * cols.msb,
        65535 * cols.msb, 65535 * cols.msb]
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
      (cols.is_lb + cols.is_lbu) (cols.is_lb + cols.is_lbu))

private def loadByteRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadByteChipRustColumns env input offset
  let ts := cols.memory_access.access_timestamp
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let isReal := cols.is_lb + cols.is_lbu
  List.Forall (· = 0)
    [ cols.is_lb * (cols.is_lb - 1),
      cols.is_lbu * (cols.is_lbu - 1),
      isReal * (isReal - 1),
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
      cols.adapter.op_a_0,
      (cols.offset_bit[1] - 1) * ((cols.offset_bit[2] - 1) *
        (cols.selected_limb - cols.memory_access.prev_value[0])),
      cols.offset_bit[1] * ((cols.offset_bit[2] - 1) *
        (cols.selected_limb - cols.memory_access.prev_value[1])),
      (cols.offset_bit[1] - 1) * (cols.offset_bit[2] *
        (cols.selected_limb - cols.memory_access.prev_value[2])),
      cols.offset_bit[1] * (cols.offset_bit[2] *
        (cols.selected_limb - cols.memory_access.prev_value[3])),
      cols.selected_byte -
        (cols.offset_bit[0] *
            ((cols.selected_limb - cols.selected_limb_low_byte) *
              (256 : ZMod p)⁻¹) +
          (1 - cols.offset_bit[0]) * cols.selected_limb_low_byte),
      cols.is_lbu * cols.msb ]

private def loadByteRustMeaning
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadByteRustAddressMeaning env input offset ∧
    loadByteRustCpuMeaning env input offset ∧
    loadByteRustITypeMeaning env input offset ∧
    loadByteRustTailMeaning env input offset

private theorem loadByteNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadByteChip.main input).operations offset)) ↔
      loadByteNativeMeaning env input offset := by
  rw [loadByteNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (loadByteMemoryInput input offset)).operations (offset + 4)) =
        loadByteMemoryAssertionValues env
          (loadByteMemoryInput input offset) by
    exact loadByteMemoryAssertionList env
      (loadByteMemoryInput input offset) (offset + 4)]
  rw [CanonicalReader.registerWriteAssertions]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval, true_and]
  rfl

private def loadByteExtractedMeaning
    (cols : LoadByteChip.Columns (ZMod p)) : Prop :=
  let isReal := cols.is_lb + cols.is_lbu
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
      (Extracted.ITypeReader.asserts cols.state.clk_high clkLow
        cols.state.pc (29 * cols.is_lb + 32 * cols.is_lbu)
        #v[cols.selected_byte + 65280 * cols.msb, 65535 * cols.msb,
          65535 * cols.msb, 65535 * cols.msb]
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
        isReal * (isReal - 1),
        isReal * (isReal - 1),
        isReal * (ts.compare_low * (ts.compare_low - 1)),
        isReal * (ts.compare_low * (cols.state.clk_high - ts.prev_high)),
        isReal *
          ((ts.compare_low * (clkLow + 1) +
              (1 - ts.compare_low) * cols.state.clk_high -
              (ts.compare_low * ts.prev_low +
                (1 - ts.compare_low) * ts.prev_high) - 1) -
            (ts.diff_low_limb + ts.diff_high_limb * 65536)),
        cols.adapter.op_a_0,
        (cols.offset_bit[1] - 1) * ((cols.offset_bit[2] - 1) *
          (cols.selected_limb - cols.memory_access.prev_value[0])),
        cols.offset_bit[1] * ((cols.offset_bit[2] - 1) *
          (cols.selected_limb - cols.memory_access.prev_value[1])),
        (cols.offset_bit[1] - 1) * (cols.offset_bit[2] *
          (cols.selected_limb - cols.memory_access.prev_value[2])),
        cols.offset_bit[1] * (cols.offset_bit[2] *
          (cols.selected_limb - cols.memory_access.prev_value[3])),
        cols.selected_byte -
          (cols.offset_bit[0] *
              ((cols.selected_limb - cols.selected_limb_low_byte) *
                (256 : ZMod p)⁻¹) +
            (1 - cols.offset_bit[0]) * cols.selected_limb_low_byte),
        cols.is_lbu * cols.msb ]

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteExtractedAssertionsDecompose
    (cols : LoadByteChip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.LoadByteOracle.LoadByteColumns.asserts
          (loadByteChipReconfigure cols)) ↔
      loadByteExtractedMeaning cols := by
  simp only [Extracted.LoadByteOracle.LoadByteColumns.asserts, List.forall_append]
  dsimp only [loadByteChipReconfigure, loadByteOracleAddressOperation]
  simp only [loadByteOracle_address_asserts_eq]
  simp only [loadByteVec3Eta, loadByteVec4Eta]
  simp only [loadByteExtractedMeaning, List.Forall, Nat.cast_one]
  have hAddress := congrArg
    (fun address =>
      Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
        (cols.is_lb + cols.is_lbu) address)
    (loadByteAddressEta (cols := cols.address_operation))
  have hCpu := congrArg
    (fun state =>
      Extracted.CPUState.asserts state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_lb + cols.is_lbu))
    (loadByteCpuEta (cols := cols.state))
  have hIType := congrArg
    (fun adapter =>
      Extracted.ITypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc (29 * cols.is_lb + 32 * cols.is_lbu)
        #v[cols.selected_byte + 65280 * cols.msb, 65535 * cols.msb,
          65535 * cols.msb, 65535 * cols.msb]
        adapter (cols.is_lb + cols.is_lbu) (cols.is_lb + cols.is_lbu))
    (loadByteITypeEta (cols := cols.adapter))
  rw [hAddress, hCpu, hIType]
  constructor
  · rintro ⟨hABC, hTail⟩
    rcases hABC with ⟨hAB, hC⟩
    rcases hAB with ⟨hA, hB⟩
    exact ⟨hA, hB, hC, hTail⟩
  · rintro ⟨hA, hB, hC, hTail⟩
    exact ⟨⟨⟨hA, hB⟩, hC⟩, hTail⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteRustMeaning_eq
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustMeaning env input offset =
      loadByteExtractedMeaning
        (loadByteChipRustColumns env input offset) := by
  apply propext
  unfold loadByteRustMeaning loadByteRustAddressMeaning
    loadByteRustCpuMeaning loadByteRustITypeMeaning loadByteRustTailMeaning
    loadByteExtractedMeaning
  simp only [loadByteVec4Eta]

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadByteChipOracle.nativeAssertZeros
          (loadByteChipRustColumns env input offset)) ↔
      loadByteRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, loadByteChipOracle]
  rw [loadByteRustMeaning_eq]
  exact loadByteExtractedAssertionsDecompose
    (loadByteChipRustColumns env input offset)

private theorem loadByteAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustAddressMeaning env input offset ↔
      loadByteNativeAddressMeaning env input offset := by
  have hAddress := loadByteAddressAssertions (p := p) env
    (loadByteAddressInput input) offset
  unfold loadByteRustAddressMeaning loadByteNativeAddressMeaning
  dsimp only [loadByteChipRustColumns]
  rw [loadByteEvalAddressCols]
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
    exact loadByteEvalVec4Components env
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
    exact loadByteEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [loadByteAddressInput] at hAddress
  rw [ProvableType.getElem_eval_fields env input.offset_bit 0 (by decide),
    ProvableType.getElem_eval_fields env input.offset_bit 1 (by decide),
    ProvableType.getElem_eval_fields env input.offset_bit 2 (by decide)] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustCpuMeaning env input offset ↔
      loadByteNativeCpuMeaning env input offset := by
  let cpu := loadByteCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env (input.is_lb + input.is_lbu)) (by
      simp only [cpu, loadByteCpuInput,
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
  unfold loadByteRustCpuMeaning loadByteNativeCpuMeaning
  dsimp only [loadByteChipRustColumns]
  rw [hNext]
  simp only [cpu, loadByteCpuInput] at hCpu
  exact hCpu

private theorem loadByteITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustITypeMeaning env input offset ↔
      loadByteNativeITypeMeaning env input offset := by
  let readerInput := loadByteITypeInput input
  have hIType := CanonicalReader.iTypeAssertionsExact
    (p := p) env readerInput (offset + 4)
    (Expression.eval env input.state.clk_high)
    (Expression.eval env
      (input.state.clk_0_16 + input.state.clk_16_24 * 65536))
    (Expression.eval env (input.is_lb * 29 + input.is_lbu * 32))
    (Expression.eval env (input.is_lb + input.is_lbu))
    (Expression.eval env (input.is_lb + input.is_lbu))
    (Eval.eval env input.state.pc)
    #v[Expression.eval env (input.selected_byte + 65280 * input.msb),
      65535 * Expression.eval env input.msb,
      65535 * Expression.eval env input.msb,
      65535 * Expression.eval env input.msb]
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput, loadByteITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadByteITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadByteITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      simp only [ProvableType.eval_field])
    (by
      simp only [readerInput, loadByteITypeInput]
      rfl)
    (by
      simp only [readerInput, loadByteITypeInput]
      rfl)
    (by
      rfl)
    (by
      rfl)
    rfl
  unfold loadByteRustITypeMeaning loadByteNativeITypeMeaning
  dsimp only [loadByteChipRustColumns]
  simp only [readerInput, loadByteITypeInput] at hIType
  simpa only [loadByteITypeInput, eval_cpuState, loadByteEvalMemoryCols,
    Readers.ITypeReader.eval_cols, ProvableType.eval_field,
    eval_add, eval_mul, Expression.eval, mul_comm] using hIType

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustTailMeaning env input offset ↔
      loadByteNativeMemoryMeaning env input offset ∧
        Expression.eval env (loadByteSelect0 input) = 0 ∧
        Expression.eval env (loadByteSelect1 input) = 0 ∧
        Expression.eval env (loadByteSelect2 input) = 0 ∧
        Expression.eval env (loadByteSelect3 input) = 0 ∧
        Expression.eval env (loadByteMux input) = 0 ∧
        Expression.eval env input.adapter.op_a_0 = 0 ∧
        Expression.eval env (loadByteMsbZero input) = 0 ∧
        Expression.eval env (loadByteLbBool input) = 0 ∧
        Expression.eval env (loadByteLbuBool input) = 0 ∧
        Expression.eval env
          ((input.is_lb + input.is_lbu) *
            (input.is_lb + input.is_lbu - 1)) = 0 := by
  unfold loadByteRustTailMeaning loadByteNativeMemoryMeaning
  dsimp only [loadByteChipRustColumns]
  simp only [loadByteMemoryAssertionValues, loadByteMemoryInput,
    List.Forall, Readers.ITypeReader.eval_opA0,
    eval_cpuState, loadByteEvalMemoryCols,
    loadByteEvalMemoryTimestamp,
    ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    loadByteSelect0, loadByteSelect1, loadByteSelect2, loadByteSelect3,
    loadByteMux, loadByteMsbZero, loadByteLbBool, loadByteLbuBool,
    eval_sub, Expression.eval, Nat.cast_one, sub_zero]
  ring_nf
  tauto

private theorem loadByteChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    loadByteRustMeaning env input offset ↔
      loadByteNativeMeaning env input offset := by
  unfold loadByteRustMeaning loadByteNativeMeaning
  rw [loadByteAddressMeaningFaithful, loadByteCpuMeaningFaithful,
    loadByteITypeMeaningFaithful, loadByteTailMeaningFaithful]
  tauto

private theorem loadByteChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadByteChipOracle.nativeAssertZeros
          (loadByteChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadByteChip.main input).operations offset)) :=
  (loadByteRustAssertionsDecompose (p := p) env input offset).trans
    ((loadByteChipMeaningFaithful (p := p) env input offset).trans
      (loadByteNativeAssertionsDecompose (p := p) env input offset).symm)

theorem loadByteChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadByteChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadByteChip.main env input offset cols) :
    List.Forall (· = 0)
        (loadByteChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadByteChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadByteChip.elaborated (p := p)) hbind
  rw [LoadByteChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadByteChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadByteChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact loadByteChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem loadByteChipConstraintsConstructive
    (rustCols : Extracted.LoadByteOracle.LoadByteColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadByteChipRowCodec.assignment
      (loadByteChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (loadByteChipOracle.assertZeros rustCols) ↔
      (⟨LoadByteChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := loadByteChipOracle.deconfigure rustCols
  let assignment := loadByteChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadByteChip.main assignment.environment
        (⟨LoadByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadByteChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadByteChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨LoadByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (loadByteChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨LoadByteChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      LoadByteChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (LoadByteChip.circuit (p := p))
      assignment.environment loadByteChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

private def loadByteStateInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def loadByteProgramInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       input.is_lb * 29 + input.is_lbu * 32,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem loadByteStateInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadByteChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (loadByteStateInteractions input).map ChannelInteraction.toRaw :=
  (LoadByteChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (loadByteStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadByteChip.circuit, loadByteStateInteractions, expose])

private theorem loadByteProgramInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadByteChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (loadByteProgramInteractions input).map ChannelInteraction.toRaw :=
  (LoadByteChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (loadByteProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadByteChip.circuit, loadByteProgramInteractions, expose])

private theorem loadByteStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((loadByteStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.LoadByteOracle.LoadByteColumns.interactions
          (loadByteChipReconfigure
            (loadByteChipRustColumns env input offset))).map
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
  simp only [loadByteStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.LoadByteOracle.LoadByteColumns.interactions,
    loadByteChipReconfigure, loadByteOracleAddressOperation,
    Extracted.LoadByteOracle.AddressOperation.interactions,
    Extracted.LoadByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadByteChipRustColumns, loadByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem loadByteProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((loadByteProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.LoadByteOracle.LoadByteColumns.interactions
          (loadByteChipReconfigure
            (loadByteChipRustColumns env input offset))).map
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
  simp only [loadByteProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.LoadByteOracle.LoadByteColumns.interactions,
    loadByteChipReconfigure, loadByteOracleAddressOperation,
    Extracted.LoadByteOracle.AddressOperation.interactions,
    Extracted.LoadByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadByteChipRustColumns, loadByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat]
  rw [show
    -(ProvableStruct.eval env input).is_lbu +
        -(ProvableStruct.eval env input).is_lb =
      -((ProvableStruct.eval env input).is_lb +
        (ProvableStruct.eval env input).is_lbu) by
    ring_nf]
  rw [signedVal_neg hp2]
  simp only [neg_neg]
  constructor
  · congr 1
    ring_nf
  · trivial

private theorem loadBytePermMemoryBlocks {α : Type}
    (ram : List α) (opAPull opBPull opBPush opAPush : α) :
    List.Perm (ram ++ [opAPull, opBPull, opBPush, opAPush])
      ([opAPull, opAPush, opBPull, opBPush] ++ ram) := by
  have hrotate :
      List.Perm (ram ++ [opAPull, opBPull, opBPush, opAPush])
        ([opAPull, opBPull, opBPush, opAPush] ++ ram) :=
    List.perm_append_comm
  have htail :
      List.Perm [opAPull, opBPull, opBPush, opAPush]
        [opAPull, opAPush, opBPull, opBPush] :=
    List.Perm.cons opAPull
      ((List.Perm.cons opBPull
        (List.Perm.swap opBPush opAPush []).symm).trans
          (List.Perm.swap opBPull opAPush [opBPush]).symm)
  exact hrotate.trans (htail.append_right ram)

private theorem loadByteMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((LoadByteChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.LoadByteOracle.LoadByteColumns.interactions
          (loadByteChipReconfigure
            (loadByteChipRustColumns env input offset))).map
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
  simp only [LoadByteChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.LoadByteOracle.LoadByteColumns.interactions,
    loadByteChipReconfigure, loadByteOracleAddressOperation,
    Extracted.LoadByteOracle.AddressOperation.interactions,
    Extracted.LoadByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadByteOracle.AddressOperation.value,
    loadByteChipRustColumns, loadByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadByteEvalMemoryCols, loadByteEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  have hGateNeg :
      -(ProvableStruct.eval env input).is_lbu +
          -(ProvableStruct.eval env input).is_lb =
        -((ProvableStruct.eval env input).is_lb +
          (ProvableStruct.eval env input).is_lbu) := by
    ring_nf
  simp only [hGateNeg, signedVal_neg hp2, neg_neg]
  exact loadBytePermMemoryBlocks [_, _] _ _ _ _

private def loadByteCpuByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def loadByteAddressByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, var { index := offset },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, var { index := offset + 1 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, var { index := offset + 2 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, ((var { index := offset } : Expression (ZMod p)) -
          (4 : Expression (ZMod p)) * input.offset_bit[2] -
          (2 : Expression (ZMod p)) * input.offset_bit[1] -
          input.offset_bit[0]) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def loadByteMemoryByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def loadByteInlineByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨3, 0, input.selected_limb_low_byte,
       (input.selected_limb - input.selected_limb_low_byte) *
         Expression.const ((256 : ZMod p)⁻¹)⟩,
    byteChannel.pulledIf input.is_lb
      ⟨5, input.msb, input.selected_byte, 0⟩ ]

private def loadByteITypeByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 +
    input.state.clk_16_24 * 65536
  [ byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨3, 0, (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨3, 0, (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩ ]

private def loadByteByteInteractions
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
    loadByteCpuByteInteractions input ++
    loadByteAddressByteInteractions input offset ++
    loadByteMemoryByteInteractions input ++
    loadByteInlineByteInteractions input ++
    loadByteITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteCpuByteInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (loadByteCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadByteCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [loadByteCpuInput, loadByteCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem loadByteAddressByteInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (loadByteAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadByteAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [loadByteAddressInput, loadByteAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem loadByteMemoryByteInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (loadByteMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadByteMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [loadByteMemoryInput, loadByteMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

private theorem loadByteITypeByteInteractionsEq
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReader.main
        (loadByteITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadByteITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadByteITypeInput, loadByteITypeByteInteractions,
    Readers.ITypeReader.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadByteByteInteractionsDecompose
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadByteChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadByteByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [show
      ((LoadByteChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (loadByteCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (loadByteAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (loadByteMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        (loadByteInlineByteInteractions input).map
          ChannelInteraction.toRaw ++
        ((Readers.ITypeReader.main
            (loadByteITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [LoadByteChip.main, loadByteCpuInput, loadByteAddressInput,
    loadByteMemoryInput, loadByteAddressValue, loadByteAddressCols,
    loadByteInlineByteInteractions, loadByteITypeInput,
    Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Gadgets.Equality.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Operations.interactionsWith]]
  rw [loadByteCpuByteInteractionsEq,
    loadByteAddressByteInteractionsEq,
    loadByteMemoryByteInteractionsEq,
    loadByteITypeByteInteractionsEq]
  simp only [loadByteByteInteractions, List.map_append]

private theorem loadBytePermFiveBlocks {α : Type}
    (a b c d e : List α) :
    List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ a ++ e ++ c ++ d) := by
  have hab : List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ a ++ c ++ d ++ e) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right
        (c ++ d ++ e)
  have hcde : List.Perm (c ++ d ++ e) (e ++ c ++ d) := by
    simpa only [List.append_assoc] using
      List.perm_append_comm (l₁ := c ++ d) (l₂ := e)
  exact hab.trans (by
    simpa only [List.append_assoc] using hcde.append_left (b ++ a))

set_option maxRecDepth 2000 in
private theorem loadByteByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((LoadByteChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.LoadByteOracle.LoadByteColumns.interactions
          (loadByteChipReconfigure
            (loadByteChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  have h6 : (6 : ZMod p).val = 6 :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) (Fact.out (p := 2 ^ 17 < p)))
  have h3 : (3 : ZMod p).val = 3 :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) (Fact.out (p := 2 ^ 17 < p)))
  have h5 : (5 : ZMod p).val = 5 :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) (Fact.out (p := 2 ^ 17 < p)))
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
  rw [loadByteByteInteractionsDecompose]
  simp only [loadByteByteInteractions, List.map_append]
  simp only [loadByteCpuByteInteractions,
    loadByteAddressByteInteractions, loadByteMemoryByteInteractions,
    loadByteInlineByteInteractions, loadByteITypeByteInteractions,
    List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.LoadByteOracle.LoadByteColumns.interactions,
    loadByteChipReconfigure, loadByteOracleAddressOperation,
    Extracted.LoadByteOracle.AddressOperation.interactions,
    Extracted.LoadByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadByteOracle.AddressOperation.value,
    loadByteChipRustColumns, loadByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadByteEvalMemoryCols, loadByteEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval,
    h6, h3, h5, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    LoadByteChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, loadByteEvalMemoryCols,
    loadByteEvalMemoryTimestamp, ProvableType.eval_field]
  exact loadBytePermFiveBlocks
    [_, _] [_, _, _, _] [_, _] [_, _] [_, _, _, _]

private theorem loadByteUnexpectedInteractionsEmpty
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((LoadByteChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((LoadByteChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (LoadByteChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [LoadByteChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem loadByteChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadByteChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadByteChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((LoadByteChip.main input).operations offset))
      (loadByteChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadByteChip.elaborated (p := p)) hbind
  rw [LoadByteChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadByteChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadByteChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.LoadByteOracle.LoadByteColumns.interactions
      (loadByteChipReconfigure
        (loadByteChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [loadByteUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, loadByteChipOracle]
  rw [loadByteStateInteractionsEq,
    LoadByteChip.interactionsWith_memory_eq,
    loadByteProgramInteractionsEq]
  have hState :=
    loadByteStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    loadByteByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    loadByteMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    loadByteProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem loadByteChipInteractionsConstructive
    (rustCols : Extracted.LoadByteOracle.LoadByteColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadByteChipRowCodec.assignment
      (loadByteChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨LoadByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (loadByteChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := loadByteChipOracle.deconfigure rustCols
  let assignment := loadByteChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadByteChip.main assignment.environment
        (⟨LoadByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadByteChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadByteChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨LoadByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (LoadByteChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    LoadByteChip.circuit_main_eq] using hfaithful

theorem loadByteChip_faithful :
    ChipFaithful (p := p) LoadByteChip.Inputs
      LoadByteChip.Columns Extracted.LoadByteOracle.LoadByteColumns
      LoadByteChip.circuit loadByteChipRowCodec
      loadByteChipOracle where
  constraints := loadByteChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (loadByteChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
