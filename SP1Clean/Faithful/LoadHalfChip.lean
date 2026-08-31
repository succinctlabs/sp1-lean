import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.LoadHalf
import SP1Clean.Proofs.Chips.LoadHalfChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `LoadHalf`

This file relates the native Clean `LoadHalfChip` row to the complete generated row-level oracle
for pinned SP1 v6.4.0. The `ChipFaithful` theorem at the bottom covers every `assertZero`
expression and the entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated LoadHalf oracle namespace. -/
def loadHalfOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.LoadHalfOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `loadHalfOracleAddressOperation`. -/
def loadHalfNativeAddressOperation {F : Type} (cols : Extracted.LoadHalfOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address and sign-bit blocks are copied into Rust's chip-private operation
rows. This is not an operation-level faithfulness claim. -/
def loadHalfChipReconfigure {F : Type} (cols : LoadHalfChip.Columns F) :
    Extracted.LoadHalfOracle.LoadHalfColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadHalfOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_half := cols.selected_half
    msb := { msb := cols.msb.msb }
    is_lh := cols.is_lh
    is_lhu := cols.is_lhu }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def loadHalfChipDeconfigure {F : Type} (cols : Extracted.LoadHalfOracle.LoadHalfColumns F) :
    LoadHalfChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := loadHalfNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_half := cols.selected_half
    msb := { msb := cols.msb.msb }
    is_lh := cols.is_lh
    is_lhu := cols.is_lhu }

/-- SP1 Rust's complete LoadHalf-chip oracle, viewed from the native Lean row. -/
def loadHalfChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F LoadHalfChip.Columns Extracted.LoadHalfOracle.LoadHalfColumns where
  reconfigure := loadHalfChipReconfigure
  deconfigure := loadHalfChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.LoadHalfOracle.LoadHalfColumns.asserts
  interactions := Extracted.LoadHalfOracle.LoadHalfColumns.interactions

/- Namespace bridges between the LoadHalf oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address- and
sign-bit-op lemmas below stay stated once against the standalone modules (also consumed by the
other load and store chips). -/

private theorem loadHalfOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadHalfOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.LoadHalfOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem loadHalfOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.LoadHalfOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.LoadHalfOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem loadHalfOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadHalfOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadHalfOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [loadHalfOracle_addrAdd_asserts_eq]

private theorem loadHalfOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.LoadHalfOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.LoadHalfOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [loadHalfOracle_addrAdd_interactions_eq]

private theorem loadHalfOracle_u16msb_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LoadHalfOracle.U16MSBOperation.asserts a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.asserts a ⟨msb⟩ is_real := by
  rw [Extracted.LoadHalfOracle.U16MSBOperation.asserts,
    Extracted.U16MSBOperation.asserts]

private theorem loadHalfOracle_u16msb_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a msb is_real : F) :
    Extracted.LoadHalfOracle.U16MSBOperation.interactions a ⟨msb⟩ is_real =
      Extracted.U16MSBOperation.interactions a ⟨msb⟩ is_real := by
  rw [Extracted.LoadHalfOracle.U16MSBOperation.interactions,
    Extracted.U16MSBOperation.interactions]

def loadHalfChipInput {F : Type}
    (cols : LoadHalfChip.Columns F) : LoadHalfChip.Inputs F :=
  { is_lh := cols.is_lh
    is_lhu := cols.is_lhu
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    selected_half := cols.selected_half
    msb := cols.msb.msb }

def loadHalfChipLocals {F : Type}
    (cols : LoadHalfChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def loadHalfChipPhysicalRow {F : Type}
    (cols : LoadHalfChip.Columns F) : Array F :=
  inputFirstRow (loadHalfChipInput cols) (loadHalfChipLocals cols)

def loadHalfChipColumnsOfInput {F : Type}
    (input : LoadHalfChip.Inputs F) (locals : Vector F 4) :
    LoadHalfChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.selected_half, ⟨input.msb⟩,
    input.is_lh, input.is_lhu⟩

private theorem loadHalfVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadHalfVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem loadHalfEvalVec4Components
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

private theorem loadHalfAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem loadHalfCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem loadHalfITypeEta {F : Type}
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

theorem loadHalfChipColumnsOfInput_roundtrip {F : Type}
    (cols : LoadHalfChip.Columns F) :
    loadHalfChipColumnsOfInput
        (loadHalfChipInput cols) (loadHalfChipLocals cols) = cols := by
  cases cols
  simp [loadHalfChipColumnsOfInput, loadHalfChipInput,
    loadHalfChipLocals, loadHalfVec3Eta]

@[circuit_norm] private theorem loadHalfEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadHalfEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadHalfEvalAddrAddInput
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

@[circuit_norm] private theorem loadHalfEvalAddressInput
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

@[circuit_norm] private theorem loadHalfEvalMemoryInput
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

@[circuit_norm] private theorem loadHalfEvalMemoryTimestamp
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

@[circuit_norm] private theorem loadHalfEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadHalfEvalU16MSB
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.U16MSBOperation (Expression F)) :
    Eval.eval env cols =
      ({ msb := Eval.eval env cols.msb } :
        Extracted.U16MSBOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem loadHalfEvalU16MSBInput
    {F : Type} [FiniteField F] (env : Environment F)
    (input : U16MSBOperation.Inputs (Expression F)) :
    Eval.eval env input =
      ({ a := Eval.eval env input.a
         cols := Eval.eval env input.cols
         is_real := Eval.eval env input.is_real } :
        U16MSBOperation.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem loadHalfEvalU16MSBSingleton
    {F : Type} [FiniteField F] (env : Environment F)
    (value : Expression F) (target : F)
    (hvalue : Expression.eval env value = target) :
    Eval.eval env ({ msb := value } :
      Extracted.U16MSBOperation (Expression F)) =
        ({ msb := target } :
          Extracted.U16MSBOperation F) := by
  rw [loadHalfEvalU16MSB, Extracted.U16MSBOperation.mk.injEq]
  exact (ProvableType.eval_field env value).trans hvalue

theorem evalLoadHalfDirectOutput
    (input : LoadHalfChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((LoadHalfChip.elaborated (p := p)).output
          (varFromOffset LoadHalfChip.Inputs 0)
          (size LoadHalfChip.Inputs)) =
      loadHalfChipColumnsOfInput input locals := by
  rw [LoadHalfChip.directOutput_eq]
  rw [← CircuitType.eval_expression, LoadHalfChip.eval_columns]
  unfold loadHalfChipColumnsOfInput
  rw [LoadHalfChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [LoadHalfChip.eval_inputs, LoadHalfChip.Inputs.mk.injEq] at hinputEval
  rcases hinputEval with
    ⟨hLw, hLwu, hState, hAdapter, hMemory, hOffset, hSelected, hMsb⟩
  have hMsbExpr :
      Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data)
          (varFromOffset LoadHalfChip.Inputs 0).msb =
        input.msb :=
    (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (varFromOffset LoadHalfChip.Inputs 0).msb).symm.trans hMsb
  refine ⟨hState, hAdapter, ?_, hMemory, hOffset, hSelected, ?_, hLw, hLwu⟩
  rw [loadHalfEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadHalfEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size LoadHalfChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size LoadHalfChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size LoadHalfChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))
  · exact (loadHalfEvalU16MSBSingleton
      (Environment.fromArray (inputFirstRow input locals) data)
      (varFromOffset LoadHalfChip.Inputs 0).msb input.msb hMsbExpr)

def loadHalfChipRowCodec :
    ChipRowCodec LoadHalfChip.Inputs LoadHalfChip.Columns
      (LoadHalfChip.circuit (p := p)) where
  assignment cols data := {
    row := loadHalfChipPhysicalRow cols
    input := loadHalfChipInput cols
    width_eq := by
      rw [loadHalfChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, LoadHalfChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (LoadHalfChip.circuit (p := p))
        (loadHalfChipInput cols) (loadHalfChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((LoadHalfChip.main _).output _) = _
      rw [LoadHalfChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalLoadHalfDirectOutput (p := p)
        (loadHalfChipInput cols) (loadHalfChipLocals cols) data).trans
          (loadHalfChipColumnsOfInput_roundtrip cols) }

theorem loadHalfChipLookupsEmpty :
    (⟨LoadHalfChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LoadHalfChip.circuit_main_eq]
  simp [LoadHalfChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    U16MSBOperation.circuit, U16MSBOperation.main,
    Readers.ITypeReader.circuit, Readers.ITypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def loadHalfAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (loadHalfAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [loadHalfAddressCols]
  rw [loadHalfEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [loadHalfEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def loadHalfAddressInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, 0,
    input.offset_bit[0], input.offset_bit[1],
    input.is_lh + input.is_lhu⟩

private def loadHalfAddressValue
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (loadHalfAddressInput input) (loadHalfAddressCols offset)

private def loadHalfCpuInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_lh + input.is_lhu⟩

private def loadHalfMemoryInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (loadHalfAddressValue input offset)[0],
    (loadHalfAddressValue input offset)[1],
    (loadHalfAddressValue input offset)[2],
    input.memory_access.prev_value, input.is_lh + input.is_lhu⟩

private def loadHalfU16MSBInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    Var U16MSBOperation.Inputs (ZMod p) :=
  ⟨input.selected_half, ⟨input.msb⟩, input.is_lh⟩

private def loadHalfITypeInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    Var Readers.ITypeReader.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_lh + input.is_lhu,
    input.is_lh + input.is_lhu, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
    input.selected_half, 65535 * input.msb,
    65535 * input.msb, 65535 * input.msb⟩

private def loadHalfRegisterWriteInput
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    Var Readers.RegisterWrite.Inputs (ZMod p) :=
  ⟨input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
    input.adapter.op_a,
    #v[input.selected_half, 65535 * input.msb,
      65535 * input.msb, 65535 * input.msb],
    input.is_lh + input.is_lhu⟩

private def loadHalfSelect0
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_half - input.memory_access.prev_value[0]) *
    (input.offset_bit[0] - (1 : Expression (ZMod p))) *
      (input.offset_bit[1] - (1 : Expression (ZMod p)))

private def loadHalfSelect1
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_half - input.memory_access.prev_value[1]) *
    input.offset_bit[0] *
      (input.offset_bit[1] - (1 : Expression (ZMod p)))

private def loadHalfSelect2
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_half - input.memory_access.prev_value[2]) *
    (input.offset_bit[0] - (1 : Expression (ZMod p))) *
      input.offset_bit[1]

private def loadHalfSelect3
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.selected_half - input.memory_access.prev_value[3]) *
    input.offset_bit[0] * input.offset_bit[1]

private def loadHalfMsbZero
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lhu * input.msb

private def loadHalfLhBool
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lh * (input.is_lh - (1 : Expression (ZMod p)))

private def loadHalfLhuBool
    (input : Var LoadHalfChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.is_lhu * (input.is_lhu - (1 : Expression (ZMod p)))

private theorem loadHalfNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadHalfChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (loadHalfCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (loadHalfAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (loadHalfMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((U16MSBOperation.main
              (loadHalfU16MSBInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReader.main
              (loadHalfITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.RegisterWrite.main
              (loadHalfRegisterWriteInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfSelect0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfSelect1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfSelect2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfSelect3 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.adapter.op_a_0, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfMsbZero input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfLhBool input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (loadHalfLhuBool input, 0)).operations (offset + 4))) ∧
        Expression.eval env
          ((input.is_lh + input.is_lhu) *
            (input.is_lh + input.is_lhu - 1)) = 0 := by
  simp only [nativeAssertZeros, LoadHalfChip.main,
    loadHalfCpuInput, loadHalfAddressInput, loadHalfAddressCols,
    loadHalfAddressValue, loadHalfMemoryInput, loadHalfU16MSBInput,
    loadHalfITypeInput, loadHalfRegisterWriteInput,
    loadHalfSelect0, loadHalfSelect1, loadHalfSelect2, loadHalfSelect3,
    loadHalfMsbZero, loadHalfLhBool, loadHalfLhuBool,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit, U16MSBOperation.circuit,
    Readers.ITypeReader.circuit,
    Readers.RegisterWrite.circuit,
    circuit_norm, List.map_append, List.forall_append]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfAddrAddAssertions
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
    loadHalfEvalAddrAddInput, loadHalfEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem loadHalfAddressAssertions
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
  let cols := loadHalfAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := loadHalfAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, loadHalfAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    loadHalfEvalAddressInput, ProvableType.eval_field,
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

private def loadHalfMemoryAssertionValues
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
private theorem loadHalfMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      loadHalfMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [loadHalfMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, loadHalfEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfNativeU16MSBAssertionList
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
  rw [← ProvableStruct.eval_eq_eval, loadHalfEvalU16MSBInput,
    loadHalfEvalU16MSB]
  have hscalar :
      Eval.eval env input.cols.msb =
        Expression.eval env input.cols.msb :=
    ProvableType.eval_field env input.cols.msb
  rw [hscalar]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfU16MSBAssertions
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
    rw [loadHalfEvalU16MSBInput, loadHalfEvalU16MSB] at h
    simpa only [CircuitType.eval_expression,
      ProvableType.eval_field] using h.symm
  rw [loadHalfNativeU16MSBAssertionList]
  simp only [Extracted.U16MSBOperation.asserts, List.Forall,
    eval_sub, Expression.eval, hreal, hmsbEval, hmsb]

private def loadHalfChipRustColumns
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    LoadHalfChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (loadHalfAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Eval.eval env input.offset_bit
    selected_half := Expression.eval env input.selected_half
    msb := Eval.eval env
      (⟨input.msb⟩ : Extracted.U16MSBOperation (Expression (ZMod p)))
    is_lh := Expression.eval env input.is_lh
    is_lhu := Expression.eval env input.is_lhu }

private def loadHalfNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (loadHalfCpuInput input)).operations offset))

private def loadHalfNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (loadHalfAddressInput input)).operations offset))

private def loadHalfNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (loadHalfMemoryAssertionValues env
      (loadHalfMemoryInput input offset))

private def loadHalfNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReader.main
        (loadHalfITypeInput input)).operations (offset + 4)))

private def loadHalfNativeU16MSBMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((U16MSBOperation.main
        (loadHalfU16MSBInput input)).operations (offset + 4)))

private def loadHalfNativeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadHalfNativeCpuMeaning env input offset ∧
    loadHalfNativeAddressMeaning env input offset ∧
    loadHalfNativeMemoryMeaning env input offset ∧
    loadHalfNativeU16MSBMeaning env input offset ∧
    loadHalfNativeITypeMeaning env input offset ∧
    Expression.eval env (loadHalfSelect0 input) = 0 ∧
    Expression.eval env (loadHalfSelect1 input) = 0 ∧
    Expression.eval env (loadHalfSelect2 input) = 0 ∧
    Expression.eval env (loadHalfSelect3 input) = 0 ∧
    Expression.eval env input.adapter.op_a_0 = 0 ∧
    Expression.eval env (loadHalfMsbZero input) = 0 ∧
    Expression.eval env (loadHalfLhBool input) = 0 ∧
    Expression.eval env (loadHalfLhuBool input) = 0 ∧
    Expression.eval env
      ((input.is_lh + input.is_lhu) *
        (input.is_lh + input.is_lhu - 1)) = 0

private def loadHalfRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadHalfChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      (0 : ZMod p) cols.offset_bit[0] cols.offset_bit[1]
      (cols.is_lh + cols.is_lhu)
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def loadHalfRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadHalfChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 (cols.is_lh + cols.is_lhu))

private def loadHalfRustU16MSBMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadHalfChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.U16MSBOperation.asserts (F := ZMod p)
      cols.selected_half cols.msb cols.is_lh)

private def loadHalfRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadHalfChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReader.asserts cols.state.clk_high clkLow
      cols.state.pc (30 * cols.is_lh + 33 * cols.is_lhu)
      #v[cols.selected_half, 65535 * cols.msb.msb,
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
      (cols.is_lh + cols.is_lhu) (cols.is_lh + cols.is_lhu))

private def loadHalfRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := loadHalfChipRustColumns env input offset
  let ts := cols.memory_access.access_timestamp
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let isReal := cols.is_lh + cols.is_lhu
  List.Forall (· = 0)
    [ cols.is_lh * (cols.is_lh - 1),
      cols.is_lhu * (cols.is_lhu - 1),
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
      (cols.offset_bit[0] - 1) * ((cols.offset_bit[1] - 1) *
        (cols.selected_half - cols.memory_access.prev_value[0])),
      cols.offset_bit[0] * ((cols.offset_bit[1] - 1) *
        (cols.selected_half - cols.memory_access.prev_value[1])),
      (cols.offset_bit[0] - 1) * (cols.offset_bit[1] *
        (cols.selected_half - cols.memory_access.prev_value[2])),
      cols.offset_bit[0] * (cols.offset_bit[1] *
        (cols.selected_half - cols.memory_access.prev_value[3])),
      cols.is_lhu * cols.msb.msb ]

private def loadHalfRustMeaning
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  loadHalfRustAddressMeaning env input offset ∧
    loadHalfRustU16MSBMeaning env input offset ∧
    loadHalfRustCpuMeaning env input offset ∧
    loadHalfRustITypeMeaning env input offset ∧
    loadHalfRustTailMeaning env input offset

private theorem loadHalfNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadHalfChip.main input).operations offset)) ↔
      loadHalfNativeMeaning env input offset := by
  rw [loadHalfNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (loadHalfMemoryInput input offset)).operations (offset + 4)) =
        loadHalfMemoryAssertionValues env
          (loadHalfMemoryInput input offset) by
    exact loadHalfMemoryAssertionList env
      (loadHalfMemoryInput input offset) (offset + 4)]
  rw [CanonicalReader.registerWriteAssertions]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval, true_and]
  rfl

private def loadHalfExtractedMeaning
    (cols : LoadHalfChip.Columns (ZMod p)) : Prop :=
  let isReal := cols.is_lh + cols.is_lhu
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let ts := cols.memory_access.access_timestamp
  List.Forall (· = 0)
      (Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        0 cols.offset_bit[0] cols.offset_bit[1] isReal
        { addr_operation :=
            { value := cols.address_operation.addr_operation.value }
          top_two_limb_inv := cols.address_operation.top_two_limb_inv }) ∧
    List.Forall (· = 0)
      (Extracted.U16MSBOperation.asserts (F := ZMod p)
        cols.selected_half cols.msb cols.is_lh) ∧
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
        cols.state.pc (30 * cols.is_lh + 33 * cols.is_lhu)
        #v[cols.selected_half, 65535 * cols.msb.msb,
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
      [ cols.is_lh * (cols.is_lh - 1),
        cols.is_lhu * (cols.is_lhu - 1),
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
        (cols.offset_bit[0] - 1) * ((cols.offset_bit[1] - 1) *
          (cols.selected_half - cols.memory_access.prev_value[0])),
        cols.offset_bit[0] * ((cols.offset_bit[1] - 1) *
          (cols.selected_half - cols.memory_access.prev_value[1])),
        (cols.offset_bit[0] - 1) * (cols.offset_bit[1] *
          (cols.selected_half - cols.memory_access.prev_value[2])),
        cols.offset_bit[0] * (cols.offset_bit[1] *
          (cols.selected_half - cols.memory_access.prev_value[3])),
        cols.is_lhu * cols.msb.msb ]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfExtractedAssertionsDecompose
    (cols : LoadHalfChip.Columns (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.LoadHalfOracle.LoadHalfColumns.asserts
          (loadHalfChipReconfigure cols)) ↔
      loadHalfExtractedMeaning cols := by
  simp only [Extracted.LoadHalfOracle.LoadHalfColumns.asserts, List.forall_append]
  dsimp only [loadHalfChipReconfigure, loadHalfOracleAddressOperation]
  simp only [loadHalfOracle_address_asserts_eq, loadHalfOracle_u16msb_asserts_eq]
  simp only [loadHalfVec3Eta, loadHalfVec4Eta]
  simp only [loadHalfExtractedMeaning, List.Forall, Nat.cast_one]
  have hAddress := congrArg
    (fun address =>
      Extracted.AddressOperation.asserts
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
        0 cols.offset_bit[0] cols.offset_bit[1]
        (cols.is_lh + cols.is_lhu) address)
    (loadHalfAddressEta (cols := cols.address_operation))
  have hCpu := congrArg
    (fun state =>
      Extracted.CPUState.asserts state
        #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
        8 (cols.is_lh + cols.is_lhu))
    (loadHalfCpuEta (cols := cols.state))
  have hIType := congrArg
    (fun adapter =>
      Extracted.ITypeReader.asserts cols.state.clk_high
        (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
        cols.state.pc (30 * cols.is_lh + 33 * cols.is_lhu)
        #v[cols.selected_half, 65535 * cols.msb.msb,
          65535 * cols.msb.msb, 65535 * cols.msb.msb]
        adapter (cols.is_lh + cols.is_lhu) (cols.is_lh + cols.is_lhu))
    (loadHalfITypeEta (cols := cols.adapter))
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
private theorem loadHalfRustMeaning_eq
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustMeaning env input offset =
      loadHalfExtractedMeaning
        (loadHalfChipRustColumns env input offset) := by
  apply propext
  unfold loadHalfRustMeaning loadHalfRustAddressMeaning
    loadHalfRustU16MSBMeaning loadHalfRustCpuMeaning
    loadHalfRustITypeMeaning loadHalfRustTailMeaning
    loadHalfExtractedMeaning
  simp only [loadHalfVec4Eta]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadHalfChipOracle.nativeAssertZeros
          (loadHalfChipRustColumns env input offset)) ↔
      loadHalfRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, loadHalfChipOracle]
  rw [loadHalfRustMeaning_eq]
  exact loadHalfExtractedAssertionsDecompose
    (loadHalfChipRustColumns env input offset)

private theorem loadHalfAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustAddressMeaning env input offset ↔
      loadHalfNativeAddressMeaning env input offset := by
  have hAddress := loadHalfAddressAssertions (p := p) env
    (loadHalfAddressInput input) offset
  unfold loadHalfRustAddressMeaning loadHalfNativeAddressMeaning
  dsimp only [loadHalfChipRustColumns]
  rw [loadHalfEvalAddressCols]
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
    exact loadHalfEvalVec4Components env
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
    exact loadHalfEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [loadHalfAddressInput] at hAddress
  rw [ProvableType.getElem_eval_fields env input.offset_bit 0 (by decide),
    ProvableType.getElem_eval_fields env input.offset_bit 1 (by decide)] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfU16MSBMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustU16MSBMeaning env input offset ↔
      loadHalfNativeU16MSBMeaning env input offset := by
  have h := loadHalfU16MSBAssertions (p := p) env
    (loadHalfU16MSBInput input) (offset + 4)
    (Expression.eval env input.selected_half)
    (Expression.eval env input.msb)
    (Expression.eval env input.is_lh) rfl rfl
  unfold loadHalfRustU16MSBMeaning loadHalfNativeU16MSBMeaning
  dsimp only [loadHalfChipRustColumns]
  simpa only [loadHalfU16MSBInput, loadHalfEvalU16MSB,
    ProvableType.eval_field] using h

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustCpuMeaning env input offset ↔
      loadHalfNativeCpuMeaning env input offset := by
  let cpu := loadHalfCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env (input.is_lh + input.is_lhu)) (by
      simp only [cpu, loadHalfCpuInput,
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
  unfold loadHalfRustCpuMeaning loadHalfNativeCpuMeaning
  dsimp only [loadHalfChipRustColumns]
  rw [hNext]
  simp only [cpu, loadHalfCpuInput] at hCpu
  exact hCpu

private theorem loadHalfITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustITypeMeaning env input offset ↔
      loadHalfNativeITypeMeaning env input offset := by
  let readerInput := loadHalfITypeInput input
  have hIType := CanonicalReader.iTypeAssertionsExact
    (p := p) env readerInput (offset + 4)
    (Expression.eval env input.state.clk_high)
    (Expression.eval env
      (input.state.clk_0_16 + input.state.clk_16_24 * 65536))
    (Expression.eval env (input.is_lh * 30 + input.is_lhu * 33))
    (Expression.eval env (input.is_lh + input.is_lhu))
    (Expression.eval env (input.is_lh + input.is_lhu))
    (Eval.eval env input.state.pc)
    #v[Expression.eval env input.selected_half,
      65535 * Expression.eval env input.msb,
      65535 * Expression.eval env input.msb,
      65535 * Expression.eval env input.msb]
    (Eval.eval env input.adapter)
    (by
      simp only [readerInput, loadHalfITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadHalfITypeInput,
        ProvableStruct.eval_eq_eval,
        ProvableStruct.structEvalLiteralProc])
    (by
      simp only [readerInput, loadHalfITypeInput]
      rw [Readers.ITypeReader.eval_cols]
      simp only [ProvableType.eval_field])
    (by
      simp only [readerInput, loadHalfITypeInput]
      rfl)
    (by
      simp only [readerInput, loadHalfITypeInput]
      rfl)
    (by
      rfl)
    (by
      rfl)
    rfl
  unfold loadHalfRustITypeMeaning loadHalfNativeITypeMeaning
  dsimp only [loadHalfChipRustColumns]
  simp only [readerInput, loadHalfITypeInput] at hIType
  simpa only [loadHalfITypeInput, eval_cpuState, loadHalfEvalMemoryCols,
    loadHalfEvalU16MSB,
    Readers.ITypeReader.eval_cols, ProvableType.eval_field,
    eval_add, eval_mul, Expression.eval, mul_comm] using hIType

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustTailMeaning env input offset ↔
      loadHalfNativeMemoryMeaning env input offset ∧
        Expression.eval env (loadHalfSelect0 input) = 0 ∧
        Expression.eval env (loadHalfSelect1 input) = 0 ∧
        Expression.eval env (loadHalfSelect2 input) = 0 ∧
        Expression.eval env (loadHalfSelect3 input) = 0 ∧
        Expression.eval env input.adapter.op_a_0 = 0 ∧
        Expression.eval env (loadHalfMsbZero input) = 0 ∧
        Expression.eval env (loadHalfLhBool input) = 0 ∧
        Expression.eval env (loadHalfLhuBool input) = 0 ∧
        Expression.eval env
          ((input.is_lh + input.is_lhu) *
            (input.is_lh + input.is_lhu - 1)) = 0 := by
  unfold loadHalfRustTailMeaning loadHalfNativeMemoryMeaning
  dsimp only [loadHalfChipRustColumns]
  simp only [loadHalfMemoryAssertionValues, loadHalfMemoryInput,
    List.Forall, Readers.ITypeReader.eval_opA0,
    eval_cpuState, loadHalfEvalMemoryCols,
    loadHalfEvalMemoryTimestamp, loadHalfEvalU16MSB,
    ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    loadHalfSelect0, loadHalfSelect1, loadHalfSelect2, loadHalfSelect3,
    loadHalfMsbZero, loadHalfLhBool, loadHalfLhuBool,
    eval_sub, Expression.eval, Nat.cast_one, sub_zero]
  ring_nf
  tauto

private theorem loadHalfChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    loadHalfRustMeaning env input offset ↔
      loadHalfNativeMeaning env input offset := by
  unfold loadHalfRustMeaning loadHalfNativeMeaning
  rw [loadHalfAddressMeaningFaithful, loadHalfU16MSBMeaningFaithful,
    loadHalfCpuMeaningFaithful,
    loadHalfITypeMeaningFaithful, loadHalfTailMeaningFaithful]
  tauto

private theorem loadHalfChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (loadHalfChipOracle.nativeAssertZeros
          (loadHalfChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadHalfChip.main input).operations offset)) :=
  (loadHalfRustAssertionsDecompose (p := p) env input offset).trans
    ((loadHalfChipMeaningFaithful (p := p) env input offset).trans
      (loadHalfNativeAssertionsDecompose (p := p) env input offset).symm)

theorem loadHalfChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadHalfChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadHalfChip.main env input offset cols) :
    List.Forall (· = 0)
        (loadHalfChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((LoadHalfChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadHalfChip.elaborated (p := p)) hbind
  rw [LoadHalfChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadHalfChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadHalfChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact loadHalfChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem loadHalfChipConstraintsConstructive
    (rustCols : Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadHalfChipRowCodec.assignment
      (loadHalfChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (loadHalfChipOracle.assertZeros rustCols) ↔
      (⟨LoadHalfChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := loadHalfChipOracle.deconfigure rustCols
  let assignment := loadHalfChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadHalfChip.main assignment.environment
        (⟨LoadHalfChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadHalfChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadHalfChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadHalfChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨LoadHalfChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadHalfChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (loadHalfChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨LoadHalfChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      LoadHalfChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (LoadHalfChip.circuit (p := p))
      assignment.environment loadHalfChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private def loadHalfStateInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def loadHalfProgramInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       input.is_lh * 30 + input.is_lhu * 33,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem loadHalfStateInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadHalfChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (loadHalfStateInteractions input).map ChannelInteraction.toRaw :=
  (LoadHalfChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (loadHalfStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadHalfChip.circuit, loadHalfStateInteractions, expose])

private theorem loadHalfProgramInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadHalfChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (loadHalfProgramInteractions input).map ChannelInteraction.toRaw :=
  (LoadHalfChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (loadHalfProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [LoadHalfChip.circuit, loadHalfProgramInteractions, expose])

private theorem loadHalfStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((loadHalfStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.LoadHalfOracle.LoadHalfColumns.interactions
          (loadHalfChipReconfigure
            (loadHalfChipRustColumns env input offset))).map
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
  simp only [loadHalfStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.LoadHalfOracle.LoadHalfColumns.interactions,
    loadHalfChipReconfigure, loadHalfOracleAddressOperation,
    Extracted.LoadHalfOracle.AddressOperation.interactions,
    Extracted.LoadHalfOracle.AddrAddOperation.interactions,
    Extracted.LoadHalfOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadHalfChipRustColumns, loadHalfEvalAddressCols,
    loadHalfEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem loadHalfProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((loadHalfProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.LoadHalfOracle.LoadHalfColumns.interactions
          (loadHalfChipReconfigure
            (loadHalfChipRustColumns env input offset))).map
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
  simp only [loadHalfProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.LoadHalfOracle.LoadHalfColumns.interactions,
    loadHalfChipReconfigure, loadHalfOracleAddressOperation,
    Extracted.LoadHalfOracle.AddressOperation.interactions,
    Extracted.LoadHalfOracle.AddrAddOperation.interactions,
    Extracted.LoadHalfOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    loadHalfChipRustColumns, loadHalfEvalAddressCols,
    loadHalfEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat]
  rw [show
    -(ProvableStruct.eval env input).is_lhu +
        -(ProvableStruct.eval env input).is_lh =
      -((ProvableStruct.eval env input).is_lh +
        (ProvableStruct.eval env input).is_lhu) by
    ring_nf]
  rw [signedVal_neg hp2]
  simp only [neg_neg]
  constructor
  · congr 1
    ring_nf
  · trivial

private theorem loadHalfPermMemoryBlocks {α : Type}
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

private theorem loadHalfMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((LoadHalfChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.LoadHalfOracle.LoadHalfColumns.interactions
          (loadHalfChipReconfigure
            (loadHalfChipRustColumns env input offset))).map
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
  simp only [LoadHalfChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.LoadHalfOracle.LoadHalfColumns.interactions,
    loadHalfChipReconfigure, loadHalfOracleAddressOperation,
    Extracted.LoadHalfOracle.AddressOperation.interactions,
    Extracted.LoadHalfOracle.AddrAddOperation.interactions,
    Extracted.LoadHalfOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadHalfOracle.AddressOperation.value,
    loadHalfChipRustColumns, loadHalfEvalAddressCols,
    loadHalfEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadHalfEvalMemoryCols, loadHalfEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, sub_zero,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  have hGateNeg :
      -(ProvableStruct.eval env input).is_lhu +
          -(ProvableStruct.eval env input).is_lh =
        -((ProvableStruct.eval env input).is_lh +
          (ProvableStruct.eval env input).is_lhu) := by
    ring_nf
  simp only [hGateNeg, signedVal_neg hp2, neg_neg]
  exact loadHalfPermMemoryBlocks [_, _] _ _ _ _

private def loadHalfCpuByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def loadHalfAddressByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, var { index := offset },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, var { index := offset + 1 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, var { index := offset + 2 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, ((var { index := offset } : Expression (ZMod p)) -
          (4 : Expression (ZMod p)) * input.offset_bit[1] -
          (2 : Expression (ZMod p)) * input.offset_bit[0] - 0) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def loadHalfMemoryByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def loadHalfU16MSBByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_lh
      ⟨6, (2 : Expression (ZMod p)) * input.selected_half -
          input.msb * 65536,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩ ]

private def loadHalfITypeByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 +
    input.state.clk_16_24 * 65536
  [ byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨3, 0, (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨3, 0, (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩ ]

private def loadHalfByteInteractions
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  loadHalfCpuByteInteractions input ++
    loadHalfAddressByteInteractions input offset ++
    loadHalfMemoryByteInteractions input ++
    loadHalfU16MSBByteInteractions input ++
    loadHalfITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfCpuByteInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (loadHalfCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadHalfCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [loadHalfCpuInput, loadHalfCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem loadHalfAddressByteInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (loadHalfAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadHalfAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [loadHalfAddressInput, loadHalfAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfMemoryByteInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (loadHalfMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadHalfMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [loadHalfMemoryInput, loadHalfMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

omit [Fact (2 ^ 17 < p)] in
private theorem loadHalfU16MSBByteInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((U16MSBOperation.main
        (loadHalfU16MSBInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadHalfU16MSBByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadHalfU16MSBInput, loadHalfU16MSBByteInteractions,
    U16MSBOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadHalfITypeByteInteractionsEq
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReader.main
        (loadHalfITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (loadHalfITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [loadHalfITypeInput, loadHalfITypeByteInteractions,
    Readers.ITypeReader.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem loadHalfByteInteractionsDecompose
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    ((LoadHalfChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (loadHalfByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [show
      ((LoadHalfChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (loadHalfCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (loadHalfAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (loadHalfMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((U16MSBOperation.main
            (loadHalfU16MSBInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReader.main
            (loadHalfITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [LoadHalfChip.main, loadHalfCpuInput, loadHalfAddressInput,
    loadHalfMemoryInput, loadHalfAddressValue, loadHalfAddressCols,
    loadHalfU16MSBInput, loadHalfITypeInput,
    Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    U16MSBOperation.circuit,
    Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Gadgets.Equality.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Operations.interactionsWith]]
  rw [loadHalfCpuByteInteractionsEq,
    loadHalfAddressByteInteractionsEq,
    loadHalfMemoryByteInteractionsEq,
    loadHalfU16MSBByteInteractionsEq,
    loadHalfITypeByteInteractionsEq]
  simp only [loadHalfByteInteractions, List.map_append]

private theorem loadHalfPermFiveBlocks {α : Type}
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

private theorem loadHalfByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((LoadHalfChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.LoadHalfOracle.LoadHalfColumns.interactions
          (loadHalfChipReconfigure
            (loadHalfChipRustColumns env input offset))).map
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
  rw [loadHalfByteInteractionsDecompose]
  simp only [loadHalfByteInteractions, List.map_append]
  simp only [loadHalfCpuByteInteractions,
    loadHalfAddressByteInteractions, loadHalfMemoryByteInteractions,
    loadHalfU16MSBByteInteractions, loadHalfITypeByteInteractions,
    List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.LoadHalfOracle.LoadHalfColumns.interactions,
    loadHalfChipReconfigure, loadHalfOracleAddressOperation,
    Extracted.LoadHalfOracle.AddressOperation.interactions,
    Extracted.LoadHalfOracle.AddrAddOperation.interactions,
    Extracted.LoadHalfOracle.U16MSBOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReader.interactions,
    Extracted.LoadHalfOracle.AddressOperation.value,
    loadHalfChipRustColumns, loadHalfEvalAddressCols,
    loadHalfEvalU16MSB,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    loadHalfEvalMemoryCols, loadHalfEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, sub_zero,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    LoadHalfChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, loadHalfEvalMemoryCols,
    loadHalfEvalMemoryTimestamp, ProvableType.eval_field]
  exact loadHalfPermFiveBlocks
    [_, _] [_, _, _, _] [_, _] [_] [_, _, _, _]

private theorem loadHalfUnexpectedInteractionsEmpty
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((LoadHalfChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((LoadHalfChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (LoadHalfChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [LoadHalfChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem loadHalfChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : LoadHalfChip.Columns (ZMod p))
    (hbind : BindsChipOutput LoadHalfChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((LoadHalfChip.main input).operations offset))
      (loadHalfChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (LoadHalfChip.elaborated (p := p)) hbind
  rw [LoadHalfChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    LoadHalfChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change loadHalfChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.LoadHalfOracle.LoadHalfColumns.interactions
      (loadHalfChipReconfigure
        (loadHalfChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [loadHalfUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, loadHalfChipOracle]
  rw [loadHalfStateInteractionsEq,
    LoadHalfChip.interactionsWith_memory_eq,
    loadHalfProgramInteractionsEq]
  have hState :=
    loadHalfStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    loadHalfByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    loadHalfMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    loadHalfProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind_of_exit_nil rustAccesses
      (Extracted.map_toAccess_exit_filter _)).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem loadHalfChipInteractionsConstructive
    (rustCols : Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := loadHalfChipRowCodec.assignment
      (loadHalfChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨LoadHalfChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (loadHalfChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := loadHalfChipOracle.deconfigure rustCols
  let assignment := loadHalfChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput LoadHalfChip.main assignment.environment
        (⟨LoadHalfChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨LoadHalfChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [LoadHalfChip.circuit_main_eq] at h
    exact h
  have hfaithful := loadHalfChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨LoadHalfChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨LoadHalfChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (LoadHalfChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    LoadHalfChip.circuit_main_eq] using hfaithful

theorem loadHalfChip_faithful :
    ChipFaithful (p := p) LoadHalfChip.Inputs
      LoadHalfChip.Columns Extracted.LoadHalfOracle.LoadHalfColumns
      LoadHalfChip.circuit loadHalfChipRowCodec
      loadHalfChipOracle where
  constraints := loadHalfChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (loadHalfChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
