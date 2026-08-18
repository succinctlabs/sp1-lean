import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.LoadWord
import SP1Clean.Proofs.Chips.LoadWordChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `LoadWord`

This file relates the native Clean `LoadWordChip` row to the complete generated row-level oracle
for pinned SP1 v6.4.0. The `ChipFaithful` theorem at the bottom covers every `assertZero` expression and the
entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated LoadWord oracle namespace. -/
def loadWordOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.LoadWordOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `loadWordOracleAddressOperation`. -/
def loadWordNativeAddressOperation {F : Type} (cols : Extracted.LoadWordOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address and sign-bit blocks are copied into Rust's chip-private operation
rows. This is not an operation-level faithfulness claim. -/
def loadWordChipReconfigure {F : Type} (cols : LoadWordChip.Columns F) :
    Extracted.LoadWordOracle.LoadWordColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadWordOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_word := cols.selected_word
    msb := { msb := cols.msb.msb }
    is_lw := cols.is_lw
    is_lwu := cols.is_lwu }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def loadWordChipDeconfigure {F : Type} (cols : Extracted.LoadWordOracle.LoadWordColumns F) :
    LoadWordChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadWordNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_word := cols.selected_word
    msb := { msb := cols.msb.msb }
    is_lw := cols.is_lw
    is_lwu := cols.is_lwu }

/-- SP1 Rust's complete LoadWord-chip oracle, viewed from the native Lean row. -/
def loadWordChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F LoadWordChip.Columns Extracted.LoadWordOracle.LoadWordColumns where
  reconfigure := loadWordChipReconfigure
  deconfigure := loadWordChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.LoadWordOracle.LoadWordColumns.asserts
  interactions := Extracted.LoadWordOracle.LoadWordColumns.interactions

/- Namespace bridges between the LoadWord oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address- and
sign-bit-op lemmas below stay stated once against the standalone modules (also consumed by the
other load and store chips). -/

private theorem loadWordOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadWordOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.LoadWordOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem loadWordOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadWordOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.LoadWordOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem loadWordOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadWordOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadWordOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [loadWordOracle_addrAdd_asserts_eq]

private theorem loadWordOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadWordOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadWordOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [loadWordOracle_addrAdd_interactions_eq]

private theorem loadWordOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LoadWordOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.LoadWordOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem loadWordOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LoadWordOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.LoadWordOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

def loadWordChipInput {F : Type}
    (cols : LoadWordChip.Columns F) : LoadWordChip.Inputs F :=
  { is_lw := cols.is_lw
    is_lwu := cols.is_lwu
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_word := cols.selected_word
    msb := cols.msb.msb }

def loadWordChipLocals {F : Type}
    (cols : LoadWordChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def loadWordChipPhysicalRow {F : Type}
    (cols : LoadWordChip.Columns F) : Array F :=
  inputFirstRow (loadWordChipInput cols) (loadWordChipLocals cols)

def loadWordChipColumnsOfInput {F : Type}
    (input : LoadWordChip.Inputs F) (locals : Vector F 4) :
    LoadWordChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.selected_word, ⟨input.msb⟩,
    input.is_lw, input.is_lwu⟩

private theorem loadWordVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadWordVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadWordEvalVec4Components
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

private theorem loadWordAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem loadWordCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem loadWordITypeEta {F : Type}
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

theorem loadWordChipColumnsOfInput_roundtrip {F : Type}
    (cols : LoadWordChip.Columns F) :
    loadWordChipColumnsOfInput
        (loadWordChipInput cols) (loadWordChipLocals cols) = cols := by
  cases cols
  simp [loadWordChipColumnsOfInput, loadWordChipInput,
    loadWordChipLocals, loadWordVec3Eta]

@[circuit_norm] private theorem loadWordEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadWordEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadWordEvalAddrAddInput
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

@[circuit_norm] private theorem loadWordEvalAddressInput
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

@[circuit_norm] private theorem loadWordEvalMemoryInput
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

@[circuit_norm] private theorem loadWordEvalMemoryTimestamp
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

@[circuit_norm] private theorem loadWordEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadWordEvalU16MSB
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadWordEvalU16MSBInput
    {F : Type} [FiniteField F] (env : Environment F)
    (input : U16MSBOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a
         cols := Eval.eval env input.cols
         is_real := Eval.eval env input.is_real } :
        U16MSBOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem loadWordEvalU16MSBSingleton
    {F : Type} [FiniteField F] (env : Environment F)
    (value : Expression F) (target : F)
    (hvalue : Expression.eval env value = target) :
    Eval.eval env ({ msb := value } :
      Extracted.U16MSBOperation (Expression F)) =
        ({ msb := target } :
          Extracted.U16MSBOperation F) := by
  rw [loadWordEvalU16MSB, Extracted.U16MSBOperation.mk.injEq]
  exact (ProvableType.eval_field env value).trans hvalue

theorem evalLoadWordDirectOutput
    (input : LoadWordChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((LoadWordChip.elaborated (p := p)).output
          (varFromOffset LoadWordChip.Inputs 0)
          (size LoadWordChip.Inputs)) =
      loadWordChipColumnsOfInput input locals := by
  rw [LoadWordChip.directOutput_eq]
  rw [← CircuitType.eval_expression, LoadWordChip.eval_columns]
  unfold loadWordChipColumnsOfInput
  rw [LoadWordChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [LoadWordChip.eval_inputs, LoadWordChip.Inputs.mk.injEq] at hinputEval
  rcases hinputEval with
    ⟨hLw, hLwu, hState, hAdapter, hMemory, hOffset, hSelected, hMsb⟩
  have hMsbExpr :
      Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data)
          (varFromOffset LoadWordChip.Inputs 0).msb =
        input.msb :=
    (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (varFromOffset LoadWordChip.Inputs 0).msb).symm.trans hMsb
  refine ⟨hState, hAdapter, ?_, hMemory, hOffset, hSelected, ?_, hLw, hLwu⟩
  rw [loadWordEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadWordEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size LoadWordChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size LoadWordChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size LoadWordChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))
  · exact (loadWordEvalU16MSBSingleton
      (Environment.fromArray (inputFirstRow input locals) data)
      (varFromOffset LoadWordChip.Inputs 0).msb input.msb hMsbExpr)

def loadWordChipRowCodec :
    ChipRowCodec LoadWordChip.Inputs LoadWordChip.Columns
      (LoadWordChip.circuit (p := p)) where
  assignment cols data := {
    row := loadWordChipPhysicalRow cols
    input := loadWordChipInput cols
    width_eq := by
      rw [loadWordChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, LoadWordChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (LoadWordChip.circuit (p := p))
        (loadWordChipInput cols) (loadWordChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((LoadWordChip.main _).output _) = _
      rw [LoadWordChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalLoadWordDirectOutput (p := p)
        (loadWordChipInput cols) (loadWordChipLocals cols) data).trans
          (loadWordChipColumnsOfInput_roundtrip cols) }

theorem loadWordChipLookupsEmpty :
    (⟨LoadWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LoadWordChip.circuit_main_eq]
  simp [LoadWordChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    U16MSBOperation.circuit, U16MSBOperation.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def loadWordAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (loadWordAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [loadWordAddressCols]
  rw [loadWordEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadWordEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def loadWordAddressInput
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
    input.is_lw + input.is_lwu⟩

private def loadWordAddressValue
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (loadWordAddressInput input) (loadWordAddressCols offset)

private def loadWordCpuInput
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_lw + input.is_lwu⟩

private def loadWordMemoryInput
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (loadWordAddressValue input offset)[0],
    (loadWordAddressValue input offset)[1],
    (loadWordAddressValue input offset)[2],
    input.memory_access.prev_value, input.is_lw + input.is_lwu⟩

private def loadWordU16MSBInput
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    Var U16MSBOperation.Inputs (ZMod p) :=
  ⟨input.selected_word[1], ⟨input.msb⟩, input.is_lw⟩

private def loadWordITypeInput
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    Var Readers.ITypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_lw + input.is_lwu,
    input.is_lw + input.is_lwu, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
    input.selected_word[0], input.selected_word[1],
    65535 * input.msb, 65535 * input.msb⟩

private def loadWordRegisterWriteInput
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    Var Readers.RegisterWrite.Inputs (ZMod p) :=
  ⟨input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    input.adapter.op_a,
    #v[input.selected_word[0], input.selected_word[1],
      65535 * input.msb, 65535 * input.msb],
    input.is_lw + input.is_lwu⟩

private def loadWordSelect0
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_word[0] - input.memory_access.prev_value[0]) *
    (input.offset_bit - (1 : Expression (ZMod p)))

private def loadWordSelect1
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_word[1] - input.memory_access.prev_value[1]) *
    (input.offset_bit - (1 : Expression (ZMod p)))

private def loadWordSelect2
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_word[0] - input.memory_access.prev_value[2]) *
    input.offset_bit

private def loadWordSelect3
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_word[1] - input.memory_access.prev_value[3]) *
    input.offset_bit

private def loadWordMsbZero
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.msb * (input.is_lw - (1 : Expression (ZMod p)))

private def loadWordLwBool
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lw * (input.is_lw - (1 : Expression (ZMod p)))

private def loadWordLwuBool
    (input : Var LoadWordChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lwu * (input.is_lwu - (1 : Expression (ZMod p)))

private theorem loadWordNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadWordChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (loadWordCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (loadWordAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (loadWordMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((U16MSBOperation.main
              (loadWordU16MSBInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReader.main
              (loadWordITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              (loadWordRegisterWriteInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordSelect0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordSelect1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordSelect2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordSelect3 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordMsbZero input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordLwBool input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadWordLwuBool input, 0)).operations (offset + 4))) ∧
        Expression.eval env
          ((input.is_lw + input.is_lwu) *
            (input.is_lw + input.is_lwu - 1)) = 0 := by
  simp only [nativeAssertZeros, LoadWordChip.main,
    loadWordCpuInput, loadWordAddressInput, loadWordAddressCols,
    loadWordAddressValue, loadWordMemoryInput, loadWordU16MSBInput,
    loadWordITypeInput, loadWordRegisterWriteInput,
    loadWordSelect0, loadWordSelect1, loadWordSelect2, loadWordSelect3,
    loadWordMsbZero, loadWordLwBool, loadWordLwuBool,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit, U16MSBOperation.circuit,
    Readers.ITypeReader.circuit,
    Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordAddrAddAssertions
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
    loadWordEvalAddrAddInput, loadWordEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem loadWordAddressAssertions
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
  let cols := loadWordAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := loadWordAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, loadWordAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    loadWordEvalAddressInput, ProvableType.eval_field,
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

private def loadWordMemoryAssertionValues
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
private theorem loadWordMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      loadWordMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [loadWordMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, loadWordEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordNativeU16MSBAssertionList
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
  rw [← ProvableStruct.eval_eq_eval, loadWordEvalU16MSBInput,
    loadWordEvalU16MSB]
  have hscalar :
      Eval.eval env input.cols.msb =
        Expression.eval env input.cols.msb :=
    ProvableType.eval_field env input.cols.msb
  rw [hscalar]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordU16MSBAssertions
    (env : Environment (ZMod p))
    (input : Var U16MSBOperation.Inputs (ZMod p)) (offset : ℕ)
    (a msb isReal : ZMod p)
    (hreal : Expression.eval env input.is_real = isReal)
    (hmsb : Expression.eval env input.cols.msb = msb) :
    List.Forall (· = 0)
        (Extracted.U16MSBOperation.asserts (F := ZMod p)
          a ⟨msb⟩ isReal) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((U16MSBOperation.main input).operations offset)) := by
  have hmsbEval :
      (ProvableStruct.eval env input).cols.msb =
        Expression.eval env input.cols.msb := by
    have h := congrArg (fun value => value.cols.msb)
      (ProvableStruct.eval_eq_eval env input)
    rw [loadWordEvalU16MSBInput, loadWordEvalU16MSB] at h
    simpa only [CircuitType.eval_expression,
      ProvableType.eval_field] using h.symm
  rw [loadWordNativeU16MSBAssertionList]
  simp only [Extracted.U16MSBOperation.asserts, List.Forall,
    eval_sub, Expression.eval, hreal, hmsbEval, hmsb]

private def loadWordChipRustColumns
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    LoadWordChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (loadWordAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Expression.eval env input.offset_bit
    selected_word := Eval.eval env input.selected_word
    msb := Eval.eval env
      (⟨input.msb⟩ : Extracted.U16MSBOperation (Expression (ZMod p)))
    is_lw := Expression.eval env input.is_lw
    is_lwu := Expression.eval env input.is_lwu }

private def loadWordNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (loadWordCpuInput input)).operations offset))

private def loadWordNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (loadWordAddressInput input)).operations offset))

private def loadWordNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (loadWordMemoryAssertionValues env
      (loadWordMemoryInput input offset))

private def loadWordNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReader.main
        (loadWordITypeInput input)).operations (offset + 4)))

private def loadWordNativeU16MSBMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((U16MSBOperation.main
        (loadWordU16MSBInput input)).operations (offset + 4)))

private def loadWordNativeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadWordNativeCpuMeaning env input offset ∧
    loadWordNativeAddressMeaning env input offset ∧
    loadWordNativeMemoryMeaning env input offset ∧
    loadWordNativeU16MSBMeaning env input offset ∧
    loadWordNativeITypeMeaning env input offset ∧
    Expression.eval env (loadWordSelect0 input) = 0 ∧
    Expression.eval env (loadWordSelect1 input) = 0 ∧
    Expression.eval env (loadWordSelect2 input) = 0 ∧
    Expression.eval env (loadWordSelect3 input) = 0 ∧
    Expression.eval env input.adapter.op_a_0 = 0 ∧
    Expression.eval env (loadWordMsbZero input) = 0 ∧
    Expression.eval env (loadWordLwBool input) = 0 ∧
    Expression.eval env (loadWordLwuBool input) = 0 ∧
    Expression.eval env
      ((input.is_lw + input.is_lwu) *
        (input.is_lw + input.is_lwu - 1)) = 0

private def loadWordRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadWordChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      (0 : ZMod p) (0 : ZMod p) cols.offset_bit
      (cols.is_lw + cols.is_lwu)
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def loadWordRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadWordChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 (cols.is_lw + cols.is_lwu))

private def loadWordRustU16MSBMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadWordChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.U16MSBOperation.asserts (F := ZMod p)
      cols.selected_word[1] cols.msb cols.is_lw)

private def loadWordRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadWordChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReader.asserts cols.state.clk_high clkLow
      cols.state.pc (cols.is_lw * 31 + cols.is_lwu * 34)
      #v[cols.selected_word[0], cols.selected_word[1],
        65535 * cols.msb.msb, 65535 * cols.msb.msb]
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
      (cols.is_lw + cols.is_lwu) (cols.is_lw + cols.is_lwu))

private def loadWordRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadWordChipRustColumns env input offset
  let ts := cols.memory_access.access_timestamp
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let isReal := cols.is_lw + cols.is_lwu
  List.Forall (· = 0)
    [ cols.is_lw * (cols.is_lw - 1),
      cols.is_lwu * (cols.is_lwu - 1),
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
      (cols.offset_bit - 1) *
        (cols.selected_word[0] - cols.memory_access.prev_value[0]),
      (cols.offset_bit - 1) *
        (cols.selected_word[1] - cols.memory_access.prev_value[1]),
      cols.offset_bit *
        (cols.selected_word[0] - cols.memory_access.prev_value[2]),
      cols.offset_bit *
        (cols.selected_word[1] - cols.memory_access.prev_value[3]),
      (cols.is_lw - 1) * cols.msb.msb ]

private def loadWordRustMeaning
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadWordRustAddressMeaning env input offset ∧
    loadWordRustU16MSBMeaning env input offset ∧
    loadWordRustCpuMeaning env input offset ∧
    loadWordRustITypeMeaning env input offset ∧
    loadWordRustTailMeaning env input offset

private theorem loadWordNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadWordChip.main input).operations offset)) ↔
      loadWordNativeMeaning env input offset := by
  rw [loadWordNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (loadWordMemoryInput input offset)).operations (offset + 4)) =
        loadWordMemoryAssertionValues env
          (loadWordMemoryInput input offset) by
    exact loadWordMemoryAssertionList env
      (loadWordMemoryInput input offset) (offset + 4)]
  rw [CanonicalReader.registerWriteAssertions]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval, true_and]
  rfl

private def loadWordExtractedMeaning
    (cols : LoadWordChip.Columns (ZMod p)) : Prop :=
  let isReal := cols.is_lw + cols.is_lwu
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let ts := cols.memory_access.access_timestamp
  List.Forall (· = 0)
      (Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        0 0 cols.offset_bit isReal
        { addr_operation :=
            { value := cols.address_operation.addr_operation.value }
          top_two_limb_inv := cols.address_operation.top_two_limb_inv }) ∧
    List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.selected_word[1] cols.msb cols.is_lw) ∧
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
        cols.state.pc (cols.is_lw * 31 + cols.is_lwu * 34)
        #v[cols.selected_word[0], cols.selected_word[1],
          65535 * cols.msb.msb, 65535 * cols.msb.msb]
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
      [ cols.is_lw * (cols.is_lw - 1),
        cols.is_lwu * (cols.is_lwu - 1),
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
        (cols.offset_bit - 1) *
          (cols.selected_word[0] - cols.memory_access.prev_value[0]),
        (cols.offset_bit - 1) *
          (cols.selected_word[1] - cols.memory_access.prev_value[1]),
        cols.offset_bit *
          (cols.selected_word[0] - cols.memory_access.prev_value[2]),
        cols.offset_bit *
          (cols.selected_word[1] - cols.memory_access.prev_value[3]),
        (cols.is_lw - 1) * cols.msb.msb ]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordExtractedAssertionsDecompose
    (cols : LoadWordChip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.LoadWordOracle.LoadWordColumns.asserts
          (loadWordChipReconfigure cols)) ↔
      loadWordExtractedMeaning cols := by
  simp only [Extracted.LoadWordOracle.LoadWordColumns.asserts, List.forall_append]
  dsimp only [loadWordChipReconfigure, loadWordOracleAddressOperation]
  simp only [loadWordOracle_address_asserts_eq, loadWordOracle_u16msb_asserts_eq]
  simp only [loadWordVec3Eta, loadWordVec4Eta]
  simp only [loadWordExtractedMeaning, List.Forall, Nat.cast_one]
  have hAddress := congrArg
    (fun address =>
      Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        0 0 cols.offset_bit (cols.is_lw + cols.is_lwu) address)
    (loadWordAddressEta (cols := cols.address_operation))
  have hCpu := congrArg
    (fun state =>
      Extracted.CPUState.asserts state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_lw + cols.is_lwu))
    (loadWordCpuEta (cols := cols.state))
  have hIType := congrArg
    (fun adapter =>
      Extracted.ITypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc (cols.is_lw * 31 + cols.is_lwu * 34)
        #v[cols.selected_word[0], cols.selected_word[1],
          65535 * cols.msb.msb, 65535 * cols.msb.msb]
        adapter (cols.is_lw + cols.is_lwu) (cols.is_lw + cols.is_lwu))
    (loadWordITypeEta (cols := cols.adapter))
  rw [hAddress, hCpu, hIType]
  constructor
  · rintro ⟨hABCD, hTail⟩
    rcases hABCD with ⟨hABC, hD⟩
    rcases hABC with ⟨hAB, hC⟩
    rcases hAB with ⟨hA, hB⟩
    exact ⟨hA, hB, hC, hD, hTail⟩
  · rintro ⟨hA, hB, hC, hD, hTail⟩
    exact ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hTail⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordRustMeaning_eq
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustMeaning env input offset =
      loadWordExtractedMeaning
        (loadWordChipRustColumns env input offset) := by
  apply propext
  unfold loadWordRustMeaning loadWordRustAddressMeaning
    loadWordRustU16MSBMeaning loadWordRustCpuMeaning
    loadWordRustITypeMeaning loadWordRustTailMeaning
    loadWordExtractedMeaning
  simp only [loadWordVec4Eta]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadWordChipOracle.nativeAssertZeros
          (loadWordChipRustColumns env input offset)) ↔
      loadWordRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, loadWordChipOracle]
  rw [loadWordRustMeaning_eq]
  exact loadWordExtractedAssertionsDecompose
    (loadWordChipRustColumns env input offset)

private theorem loadWordAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustAddressMeaning env input offset ↔
      loadWordNativeAddressMeaning env input offset := by
  have hAddress := loadWordAddressAssertions (p := p) env
    (loadWordAddressInput input) offset
  unfold loadWordRustAddressMeaning loadWordNativeAddressMeaning
  dsimp only [loadWordChipRustColumns]
  rw [loadWordEvalAddressCols]
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
    exact loadWordEvalVec4Components env
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
    exact loadWordEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [loadWordAddressInput] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordU16MSBMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustU16MSBMeaning env input offset ↔
      loadWordNativeU16MSBMeaning env input offset := by
  have h := loadWordU16MSBAssertions (p := p) env
    (loadWordU16MSBInput input) (offset + 4)
    (Eval.eval env input.selected_word)[1]
    (Expression.eval env input.msb)
    (Expression.eval env input.is_lw) rfl rfl
  unfold loadWordRustU16MSBMeaning loadWordNativeU16MSBMeaning
  dsimp only [loadWordChipRustColumns]
  simpa only [loadWordU16MSBInput, loadWordEvalU16MSB,
    ProvableType.eval_field] using h

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustCpuMeaning env input offset ↔
      loadWordNativeCpuMeaning env input offset := by
  let cpu := loadWordCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env (input.is_lw + input.is_lwu)) (by
      simp only [cpu, loadWordCpuInput,
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
  unfold loadWordRustCpuMeaning loadWordNativeCpuMeaning
  dsimp only [loadWordChipRustColumns]
  rw [hNext]
  simp only [cpu, loadWordCpuInput] at hCpu
  exact hCpu

private theorem loadWordITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustITypeMeaning env input offset ↔
      loadWordNativeITypeMeaning env input offset := by
  let readerInput := loadWordITypeInput input
  have hIType := CanonicalReader.iTypeAssertionsExact
    (p := p) env readerInput (offset + 4)
    (Expression.eval env input.state.clk_high)
    (Expression.eval env
      (input.state.clk_0_16 + input.state.clk_16_24 * 65536))
    (Expression.eval env (input.is_lw * 31 + input.is_lwu * 34))
    (Expression.eval env (input.is_lw + input.is_lwu))
    (Expression.eval env (input.is_lw + input.is_lwu))
    (Eval.eval env input.state.pc)
    #v[(Eval.eval env input.selected_word)[0],
      (Eval.eval env input.selected_word)[1],
      65535 * Expression.eval env input.msb,
      65535 * Expression.eval env input.msb]
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput, loadWordITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadWordITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadWordITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      simp only [ProvableType.eval_field])
    (by
      simp only [readerInput, loadWordITypeInput]
      exact ProvableType.getElem_eval_fields env
        input.selected_word 0 (by decide))
    (by
      simp only [readerInput, loadWordITypeInput]
      exact ProvableType.getElem_eval_fields env
        input.selected_word 1 (by decide))
    (by
      rfl)
    (by
      rfl)
    rfl
  unfold loadWordRustITypeMeaning loadWordNativeITypeMeaning
  dsimp only [loadWordChipRustColumns]
  simp only [readerInput, loadWordITypeInput] at hIType
  simpa only [loadWordITypeInput, eval_cpuState, loadWordEvalMemoryCols,
    loadWordEvalU16MSB,
    Readers.ITypeReader.eval_cols, ProvableType.eval_field,
    eval_add, eval_mul, Expression.eval] using hIType

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustTailMeaning env input offset ↔
      loadWordNativeMemoryMeaning env input offset ∧
        Expression.eval env (loadWordSelect0 input) = 0 ∧
        Expression.eval env (loadWordSelect1 input) = 0 ∧
        Expression.eval env (loadWordSelect2 input) = 0 ∧
        Expression.eval env (loadWordSelect3 input) = 0 ∧
        Expression.eval env input.adapter.op_a_0 = 0 ∧
        Expression.eval env (loadWordMsbZero input) = 0 ∧
        Expression.eval env (loadWordLwBool input) = 0 ∧
        Expression.eval env (loadWordLwuBool input) = 0 ∧
        Expression.eval env
          ((input.is_lw + input.is_lwu) *
            (input.is_lw + input.is_lwu - 1)) = 0 := by
  unfold loadWordRustTailMeaning loadWordNativeMemoryMeaning
  dsimp only [loadWordChipRustColumns]
  simp only [loadWordMemoryAssertionValues, loadWordMemoryInput,
    List.Forall, Readers.ITypeReader.eval_opA0,
    eval_cpuState, loadWordEvalMemoryCols,
    loadWordEvalMemoryTimestamp, loadWordEvalU16MSB,
    ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    loadWordSelect0, loadWordSelect1, loadWordSelect2, loadWordSelect3,
    loadWordMsbZero, loadWordLwBool, loadWordLwuBool,
    eval_sub, Expression.eval, Nat.cast_one, sub_zero]
  ring_nf
  tauto

private theorem loadWordChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    loadWordRustMeaning env input offset ↔
      loadWordNativeMeaning env input offset := by
  unfold loadWordRustMeaning loadWordNativeMeaning
  rw [loadWordAddressMeaningFaithful, loadWordU16MSBMeaningFaithful,
    loadWordCpuMeaningFaithful,
    loadWordITypeMeaningFaithful, loadWordTailMeaningFaithful]
  tauto

private theorem loadWordChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadWordChipOracle.nativeAssertZeros
          (loadWordChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadWordChip.main input).operations offset)) :=
  (loadWordRustAssertionsDecompose (p := p) env input offset).trans
    ((loadWordChipMeaningFaithful (p := p) env input offset).trans
      (loadWordNativeAssertionsDecompose (p := p) env input offset).symm)

theorem loadWordChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadWordChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadWordChip.main env input offset cols) :
    List.Forall (· = 0)
        (loadWordChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadWordChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadWordChip.elaborated (p := p)) hbind
  rw [LoadWordChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadWordChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadWordChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact loadWordChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem loadWordChipConstraintsConstructive
    (rustCols : Extracted.LoadWordOracle.LoadWordColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadWordChipRowCodec.assignment
      (loadWordChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (loadWordChipOracle.assertZeros rustCols) ↔
      (⟨LoadWordChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := loadWordChipOracle.deconfigure rustCols
  let assignment := loadWordChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadWordChip.main assignment.environment
        (⟨LoadWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadWordChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadWordChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨LoadWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (loadWordChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨LoadWordChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      LoadWordChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (LoadWordChip.circuit (p := p))
      assignment.environment loadWordChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private def loadWordStateInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def loadWordProgramInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       input.is_lw * 31 + input.is_lwu * 34,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem loadWordStateInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadWordChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (loadWordStateInteractions input).map ChannelInteraction.toRaw :=
  (LoadWordChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (loadWordStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadWordChip.circuit, loadWordStateInteractions, expose])

private theorem loadWordProgramInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadWordChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (loadWordProgramInteractions input).map ChannelInteraction.toRaw :=
  (LoadWordChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (loadWordProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadWordChip.circuit, loadWordProgramInteractions, expose])

private theorem loadWordStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((loadWordStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.LoadWordOracle.LoadWordColumns.interactions
          (loadWordChipReconfigure
            (loadWordChipRustColumns env input offset))).map
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
  simp only [loadWordStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.LoadWordOracle.LoadWordColumns.interactions,
    loadWordChipReconfigure, loadWordOracleAddressOperation,
    Extracted.LoadWordOracle.AddressOperation.interactions,
    Extracted.LoadWordOracle.AddrAddOperation.interactions,
    Extracted.LoadWordOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadWordChipRustColumns, loadWordEvalAddressCols,
    loadWordEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem loadWordProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((loadWordProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.LoadWordOracle.LoadWordColumns.interactions
          (loadWordChipReconfigure
            (loadWordChipRustColumns env input offset))).map
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
  simp only [loadWordProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.LoadWordOracle.LoadWordColumns.interactions,
    loadWordChipReconfigure, loadWordOracleAddressOperation,
    Extracted.LoadWordOracle.AddressOperation.interactions,
    Extracted.LoadWordOracle.AddrAddOperation.interactions,
    Extracted.LoadWordOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadWordChipRustColumns, loadWordEvalAddressCols,
    loadWordEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat]
  rw [show
    -(ProvableStruct.eval env input).is_lwu +
        -(ProvableStruct.eval env input).is_lw =
      -((ProvableStruct.eval env input).is_lw +
        (ProvableStruct.eval env input).is_lwu) by
    ring_nf]
  rw [signedVal_neg hp2]
  simp only [neg_neg]

private theorem loadWordPermMemoryBlocks {α : Type}
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

private theorem loadWordMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((LoadWordChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.LoadWordOracle.LoadWordColumns.interactions
          (loadWordChipReconfigure
            (loadWordChipRustColumns env input offset))).map
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
  simp only [LoadWordChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.LoadWordOracle.LoadWordColumns.interactions,
    loadWordChipReconfigure, loadWordOracleAddressOperation,
    Extracted.LoadWordOracle.AddressOperation.interactions,
    Extracted.LoadWordOracle.AddrAddOperation.interactions,
    Extracted.LoadWordOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadWordOracle.AddressOperation.value,
    loadWordChipRustColumns, loadWordEvalAddressCols,
    loadWordEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadWordEvalMemoryCols, loadWordEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  have hGateNeg :
      -(ProvableStruct.eval env input).is_lwu +
          -(ProvableStruct.eval env input).is_lw =
        -((ProvableStruct.eval env input).is_lw +
          (ProvableStruct.eval env input).is_lwu) := by
    ring_nf
  simp only [hGateNeg, signedVal_neg hp2, neg_neg]
  exact loadWordPermMemoryBlocks [_, _] _ _ _ _

private def loadWordCpuByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def loadWordAddressByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, var { index := offset },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, var { index := offset + 1 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, var { index := offset + 2 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, ((var { index := offset } : Expression (ZMod p)) -
          (4 : Expression (ZMod p)) * input.offset_bit -
          (2 : Expression (ZMod p)) * 0 - 0) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def loadWordMemoryByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def loadWordU16MSBByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_lw
      ⟨6, (2 : Expression (ZMod p)) * input.selected_word[1] -
          input.msb * 65536,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩ ]

private def loadWordITypeByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 +
    input.state.clk_16_24 * 65536
  [ byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨3, 0, (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨3, 0, (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩ ]

private def loadWordByteInteractions
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  loadWordCpuByteInteractions input ++
    loadWordAddressByteInteractions input offset ++
    loadWordMemoryByteInteractions input ++
    loadWordU16MSBByteInteractions input ++
    loadWordITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordCpuByteInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (loadWordCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadWordCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [loadWordCpuInput, loadWordCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem loadWordAddressByteInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (loadWordAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadWordAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [loadWordAddressInput, loadWordAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordMemoryByteInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (loadWordMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadWordMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [loadWordMemoryInput, loadWordMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

omit [Fact (2 ^ 17 < p)] in
private theorem loadWordU16MSBByteInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((U16MSBOperation.main
        (loadWordU16MSBInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadWordU16MSBByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadWordU16MSBInput, loadWordU16MSBByteInteractions,
    U16MSBOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadWordITypeByteInteractionsEq
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReader.main
        (loadWordITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadWordITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadWordITypeInput, loadWordITypeByteInteractions,
    Readers.ITypeReader.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadWordByteInteractionsDecompose
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadWordChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadWordByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [show
      ((LoadWordChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (loadWordCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (loadWordAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (loadWordMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((U16MSBOperation.main
            (loadWordU16MSBInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReader.main
            (loadWordITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [LoadWordChip.main, loadWordCpuInput, loadWordAddressInput,
    loadWordMemoryInput, loadWordAddressValue, loadWordAddressCols,
    loadWordU16MSBInput, loadWordITypeInput,
    Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    U16MSBOperation.circuit,
    Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Gadgets.Equality.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Operations.interactionsWith]]
  rw [loadWordCpuByteInteractionsEq,
    loadWordAddressByteInteractionsEq,
    loadWordMemoryByteInteractionsEq,
    loadWordU16MSBByteInteractionsEq,
    loadWordITypeByteInteractionsEq]
  simp only [loadWordByteInteractions, List.map_append]

private theorem loadWordPermFiveBlocks {α : Type}
    (a b c d e : List α) :
    List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ d ++ a ++ e ++ c) := by
  have hab : List.Perm (a ++ b ++ c ++ d ++ e)
      (b ++ a ++ c ++ d ++ e) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right
        (c ++ d ++ e)
  have hacd : List.Perm (b ++ a ++ c ++ d ++ e)
      (b ++ d ++ a ++ c ++ e) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := a ++ c) (l₂ := d)).append_right e).append_left b
  have hce : List.Perm (b ++ d ++ a ++ c ++ e)
      (b ++ d ++ a ++ e ++ c) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := c) (l₂ := e)).append_left
        (b ++ d ++ a)
  exact (hab.trans hacd).trans hce

private theorem loadWordByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((LoadWordChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.LoadWordOracle.LoadWordColumns.interactions
          (loadWordChipReconfigure
            (loadWordChipRustColumns env input offset))).map
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
  rw [loadWordByteInteractionsDecompose]
  simp only [loadWordByteInteractions, List.map_append]
  simp only [loadWordCpuByteInteractions,
    loadWordAddressByteInteractions, loadWordMemoryByteInteractions,
    loadWordU16MSBByteInteractions, loadWordITypeByteInteractions,
    List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.LoadWordOracle.LoadWordColumns.interactions,
    loadWordChipReconfigure, loadWordOracleAddressOperation,
    Extracted.LoadWordOracle.AddressOperation.interactions,
    Extracted.LoadWordOracle.AddrAddOperation.interactions,
    Extracted.LoadWordOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadWordOracle.AddressOperation.value,
    loadWordChipRustColumns, loadWordEvalAddressCols,
    loadWordEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadWordEvalMemoryCols, loadWordEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    LoadWordChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, loadWordEvalMemoryCols,
    loadWordEvalMemoryTimestamp, ProvableType.eval_field]
  exact loadWordPermFiveBlocks
    [_, _] [_, _, _, _] [_, _] [_] [_, _, _, _]

private theorem loadWordUnexpectedInteractionsEmpty
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((LoadWordChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((LoadWordChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (LoadWordChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [LoadWordChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem loadWordChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadWordChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadWordChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((LoadWordChip.main input).operations offset))
      (loadWordChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadWordChip.elaborated (p := p)) hbind
  rw [LoadWordChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadWordChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadWordChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.LoadWordOracle.LoadWordColumns.interactions
      (loadWordChipReconfigure
        (loadWordChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [loadWordUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, loadWordChipOracle]
  rw [loadWordStateInteractionsEq,
    LoadWordChip.interactionsWith_memory_eq,
    loadWordProgramInteractionsEq]
  have hState :=
    loadWordStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    loadWordByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    loadWordMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    loadWordProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem loadWordChipInteractionsConstructive
    (rustCols : Extracted.LoadWordOracle.LoadWordColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadWordChipRowCodec.assignment
      (loadWordChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨LoadWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (loadWordChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := loadWordChipOracle.deconfigure rustCols
  let assignment := loadWordChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadWordChip.main assignment.environment
        (⟨LoadWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadWordChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadWordChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨LoadWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (LoadWordChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    LoadWordChip.circuit_main_eq] using hfaithful

theorem loadWordChip_faithful :
    ChipFaithful (p := p) LoadWordChip.Inputs
      LoadWordChip.Columns Extracted.LoadWordOracle.LoadWordColumns
      LoadWordChip.circuit loadWordChipRowCodec
      loadWordChipOracle where
  constraints := loadWordChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (loadWordChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
