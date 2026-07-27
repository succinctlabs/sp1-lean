import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.StoreByte
import SP1Clean.Proofs.Chips.StoreByteChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `StoreByte`

This file relates the native Clean `StoreByteChip` row to the complete generated row-level oracle
for pinned SP1 v6.3.1. The `ChipFaithful` theorem below covers every `assertZero` expression and the
entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated StoreByte oracle namespace. -/
def storeByteOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.StoreByteOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `storeByteOracleAddressOperation`. -/
def storeByteNativeAddressOperation {F : Type}
    (cols : Extracted.StoreByteOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address block is copied into Rust's chip-private operation row. This is not
an operation-level faithfulness claim. -/
def storeByteChipReconfigure {F : Type} (cols : StoreByteChip.Columns F) :
    Extracted.StoreByteOracle.StoreByteColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeByteOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    mem_limb := cols.mem_limb
    mem_limb_low_byte := cols.mem_limb_low_byte
    register_low_byte := cols.register_low_byte
    increment := cols.increment
    store_value := cols.store_value
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def storeByteChipDeconfigure {F : Type} (cols : Extracted.StoreByteOracle.StoreByteColumns F) :
    StoreByteChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeByteNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    mem_limb := cols.mem_limb
    mem_limb_low_byte := cols.mem_limb_low_byte
    register_low_byte := cols.register_low_byte
    increment := cols.increment
    store_value := cols.store_value
    is_real := cols.is_real }

/-- SP1 Rust's complete StoreByte-chip oracle, viewed from the native Lean row. -/
def storeByteChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F StoreByteChip.Columns Extracted.StoreByteOracle.StoreByteColumns where
  reconfigure := storeByteChipReconfigure
  deconfigure := storeByteChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.StoreByteOracle.StoreByteColumns.asserts
  interactions := Extracted.StoreByteOracle.StoreByteColumns.interactions

/- Namespace bridges between the StoreByte oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address-op
lemmas below stay stated once against the standalone modules (also consumed by the other load and
store chips). -/

private theorem storeByteOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreByteOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.StoreByteOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem storeByteOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreByteOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.StoreByteOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem storeByteOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreByteOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreByteOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [storeByteOracle_addrAdd_asserts_eq]

private theorem storeByteOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreByteOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreByteOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [storeByteOracle_addrAdd_interactions_eq]

def storeByteChipInput {F : Type}
    (cols : StoreByteChip.Columns F) : StoreByteChip.Inputs F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    mem_limb := cols.mem_limb
    mem_limb_low_byte := cols.mem_limb_low_byte
    register_low_byte := cols.register_low_byte
    increment := cols.increment
    store_value := cols.store_value }

def storeByteChipLocals {F : Type}
    (cols : StoreByteChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def storeByteChipPhysicalRow {F : Type}
    (cols : StoreByteChip.Columns F) : Array F :=
  inputFirstRow (storeByteChipInput cols) (storeByteChipLocals cols)

def storeByteChipColumnsOfInput {F : Type}
    (input : StoreByteChip.Inputs F) (locals : Vector F 4) :
    StoreByteChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.mem_limb,
    input.mem_limb_low_byte, input.register_low_byte, input.increment,
    input.store_value, input.is_real⟩

private theorem storeByteVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeByteVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeByteEvalVec4Components
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

private theorem storeByteAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem storeByteCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem storeByteITypeEta {F : Type}
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

theorem storeByteChipColumnsOfInput_roundtrip {F : Type}
    (cols : StoreByteChip.Columns F) :
    storeByteChipColumnsOfInput
        (storeByteChipInput cols) (storeByteChipLocals cols) = cols := by
  cases cols
  simp [storeByteChipColumnsOfInput, storeByteChipInput,
    storeByteChipLocals, storeByteVec3Eta]

@[circuit_norm] private theorem storeByteEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeByteEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeByteEvalAddrAddInput
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

@[circuit_norm] private theorem storeByteEvalAddressInput
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

@[circuit_norm] private theorem storeByteEvalMemoryInput
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

@[circuit_norm] private theorem storeByteEvalMemoryTimestamp
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

@[circuit_norm] private theorem storeByteEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem evalStoreByteDirectOutput
    (input : StoreByteChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((StoreByteChip.elaborated (p := p)).output
          (varFromOffset StoreByteChip.Inputs 0)
          (size StoreByteChip.Inputs)) =
      storeByteChipColumnsOfInput input locals := by
  rw [StoreByteChip.directOutput_eq]
  rw [← CircuitType.eval_expression, StoreByteChip.eval_columns]
  unfold storeByteChipColumnsOfInput
  rw [StoreByteChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [StoreByteChip.eval_inputs, StoreByteChip.Inputs.mk.injEq] at hinputEval
  refine
    ⟨hinputEval.2.1, hinputEval.2.2.1, ?_,
      hinputEval.2.2.2.1, hinputEval.2.2.2.2.1,
      hinputEval.2.2.2.2.2.1, hinputEval.2.2.2.2.2.2.1,
      hinputEval.2.2.2.2.2.2.2.1,
      hinputEval.2.2.2.2.2.2.2.2.1,
      hinputEval.2.2.2.2.2.2.2.2.2, hinputEval.1⟩
  rw [storeByteEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeByteEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size StoreByteChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size StoreByteChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size StoreByteChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))

def storeByteChipRowCodec :
    ChipRowCodec StoreByteChip.Inputs StoreByteChip.Columns
      (StoreByteChip.circuit (p := p)) where
  assignment cols data := {
    row := storeByteChipPhysicalRow cols
    input := storeByteChipInput cols
    width_eq := by
      rw [storeByteChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, StoreByteChip.circuit_size_eq]
    rowInput_eq := by
      exact rowInput_inputFirstRow (StoreByteChip.circuit (p := p))
        (storeByteChipInput cols) (storeByteChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((StoreByteChip.main _).output _) = _
      rw [StoreByteChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalStoreByteDirectOutput (p := p)
        (storeByteChipInput cols) (storeByteChipLocals cols) data).trans
          (storeByteChipColumnsOfInput_roundtrip cols) }

theorem storeByteChipLookupsEmpty :
    (⟨StoreByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    StoreByteChip.circuit_main_eq]
  simp [StoreByteChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def storeByteAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (storeByteAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [storeByteAddressCols]
  rw [storeByteEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeByteEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def storeByteAddressInput
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
    input.offset_bit[1], input.offset_bit[2], input.is_real⟩

private def storeByteAddressValue
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (storeByteAddressInput input) (storeByteAddressCols offset)

private def storeByteCpuInput
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_real⟩

private def storeByteMemoryInput
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (storeByteAddressValue input offset)[0],
    (storeByteAddressValue input offset)[1],
    (storeByteAddressValue input offset)[2],
    input.store_value, input.is_real⟩

private def storeByteITypeInput
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, 36⟩

private def storeByteSelect0
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.mem_limb - input.memory_access.prev_value[0]) *
    (input.offset_bit[1] - (1 : Expression (ZMod p))) *
      (input.offset_bit[2] - (1 : Expression (ZMod p)))

private def storeByteSelect1
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.mem_limb - input.memory_access.prev_value[1]) *
    input.offset_bit[1] *
      (input.offset_bit[2] - (1 : Expression (ZMod p)))

private def storeByteSelect2
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.mem_limb - input.memory_access.prev_value[2]) *
    (input.offset_bit[1] - (1 : Expression (ZMod p))) *
      input.offset_bit[2]

private def storeByteSelect3
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.mem_limb - input.memory_access.prev_value[3]) *
    input.offset_bit[1] * input.offset_bit[2]

private def storeByteIncrementConstraint
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  let memHigh := (input.mem_limb - input.mem_limb_low_byte) *
    Expression.const ((256 : ZMod p)⁻¹)
  input.increment -
    ((input.register_low_byte - input.mem_limb_low_byte) *
        ((1 : Expression (ZMod p)) - input.offset_bit[0]) +
      Expression.const (256 : ZMod p) *
        (input.register_low_byte - memHigh) * input.offset_bit[0])

private def storeByteWrite0
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.store_value[0] - (input.memory_access.prev_value[0] +
    input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
      ((1 : Expression (ZMod p)) - input.offset_bit[2]))

private def storeByteWrite1
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.store_value[1] - (input.memory_access.prev_value[1] +
    input.increment * input.offset_bit[1] *
      ((1 : Expression (ZMod p)) - input.offset_bit[2]))

private def storeByteWrite2
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.store_value[2] - (input.memory_access.prev_value[2] +
    input.increment * ((1 : Expression (ZMod p)) - input.offset_bit[1]) *
      input.offset_bit[2])

private def storeByteWrite3
    (input : Var StoreByteChip.Inputs (ZMod p)) : Expression (ZMod p) :=
  input.store_value[3] - (input.memory_access.prev_value[3] +
    input.increment * input.offset_bit[1] * input.offset_bit[2])

private theorem storeByteNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreByteChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (storeByteCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (storeByteAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (storeByteMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReaderImmutable.main
              (storeByteITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteSelect0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteSelect1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteSelect2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteSelect3 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteIncrementConstraint input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteWrite0 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteWrite1 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteWrite2 input, 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (storeByteWrite3 input, 0)).operations (offset + 4))) ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  simp only [nativeAssertZeros, StoreByteChip.main,
    storeByteCpuInput, storeByteAddressInput, storeByteAddressCols,
    storeByteAddressValue, storeByteMemoryInput, storeByteITypeInput,
    storeByteSelect0, storeByteSelect1, storeByteSelect2,
    storeByteSelect3, storeByteIncrementConstraint,
    storeByteWrite0, storeByteWrite1, storeByteWrite2, storeByteWrite3,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit, Readers.ITypeReaderImmutable.circuit,
    circuit_norm, List.map_append, List.forall_append]

omit [Fact (2 ^ 17 < p)] in
set_option maxHeartbeats 1000000 in
private theorem storeByteAddrAddAssertions
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
    storeByteEvalAddrAddInput, storeByteEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

set_option maxHeartbeats 2000000 in
private theorem storeByteAddressAssertions
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
  let cols := storeByteAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := storeByteAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, storeByteAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    storeByteEvalAddressInput, ProvableType.eval_field,
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

private def storeByteITypeImmutableAssertionValues
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) :
    List (ZMod p) :=
  [ Expression.eval env (input.is_real * (input.is_real - 1)),
    Expression.eval env (input.is_real * (input.is_real - 1)),
    Expression.eval env (input.is_trusted * (input.is_trusted - 1)),
    Expression.eval env
        (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[0]) -
      Expression.eval env 0,
    Expression.eval env
        (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[1]) -
      Expression.eval env 0,
    Expression.eval env
        (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[2]) -
      Expression.eval env 0,
    Expression.eval env
        (input.cols.op_a_0 * input.cols.op_a_memory.prev_value[3]) -
      Expression.eval env 0 ]

set_option maxHeartbeats 1000000 in
private theorem storeByteITypeImmutableAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.ITypeReaderImmutable.main input).operations offset)) =
      storeByteITypeImmutableAssertionValues env input := by
  simp only [Readers.ITypeReaderImmutable.main, circuit_norm]
  simp only [Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, circuit_norm,
    constraints_formalAssertion_toSubcircuit]
  simp only [List.map_append, List.map_cons]
  simp only [CanonicalReader.registerAccessTimestampAssertions]
  repeat' rw [CanonicalReader.equalityAssertionList]
  rfl

set_option maxHeartbeats 1000000 in
private theorem storeByteITypeImmutableAssertions
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
    (offset : ℕ)
    (htrust :
      Expression.eval env input.is_trusted =
        Expression.eval env input.is_real) :
    List.Forall (· = 0)
        (Extracted.ITypeReaderImmutable.asserts
          (Expression.eval env input.clk_high)
          (Expression.eval env input.clk_low)
          (Eval.eval env input.pc)
          (Expression.eval env input.opcode)
          (Eval.eval env input.cols)
          (Expression.eval env input.is_real)
          (Expression.eval env input.is_trusted)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((Readers.ITypeReaderImmutable.main input).operations offset)) := by
  rw [show nativeAssertZeros env
      ((Readers.ITypeReaderImmutable.main input).operations offset) =
        storeByteITypeImmutableAssertionValues env input by
    exact storeByteITypeImmutableAssertionList env input offset]
  simp only [Extracted.ITypeReaderImmutable.asserts,
    storeByteITypeImmutableAssertionValues, List.Forall]
  simp only [Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    eval_sub, Expression.eval, sub_zero]
  rw [htrust]
  tauto

private def storeByteMemoryAssertionValues
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

set_option maxHeartbeats 1000000 in
omit [Fact (2 ^ 17 < p)] in
private theorem storeByteMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      storeByteMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [storeByteMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, storeByteEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

private def storeByteChipRustColumns
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    StoreByteChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (storeByteAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Eval.eval env input.offset_bit
    mem_limb := Expression.eval env input.mem_limb
    mem_limb_low_byte := Expression.eval env input.mem_limb_low_byte
    register_low_byte := Expression.eval env input.register_low_byte
    increment := Expression.eval env input.increment
    store_value := Eval.eval env input.store_value
    is_real := Expression.eval env input.is_real }

private def storeByteNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (storeByteCpuInput input)).operations offset))

private def storeByteNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (storeByteAddressInput input)).operations offset))

private def storeByteNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (storeByteMemoryAssertionValues env
      (storeByteMemoryInput input offset))

private def storeByteNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReaderImmutable.main
        (storeByteITypeInput input)).operations (offset + 4)))

private def storeByteNativeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeByteNativeCpuMeaning env input offset ∧
    storeByteNativeAddressMeaning env input offset ∧
    storeByteNativeMemoryMeaning env input offset ∧
    storeByteNativeITypeMeaning env input offset ∧
    Expression.eval env (storeByteSelect0 input) = 0 ∧
    Expression.eval env (storeByteSelect1 input) = 0 ∧
    Expression.eval env (storeByteSelect2 input) = 0 ∧
    Expression.eval env (storeByteSelect3 input) = 0 ∧
    Expression.eval env (storeByteIncrementConstraint input) = 0 ∧
    Expression.eval env (storeByteWrite0 input) = 0 ∧
    Expression.eval env (storeByteWrite1 input) = 0 ∧
    Expression.eval env (storeByteWrite2 input) = 0 ∧
    Expression.eval env (storeByteWrite3 input) = 0 ∧
    Expression.eval env (input.is_real * (input.is_real - 1)) = 0

private def storeByteRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeByteChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
      cols.is_real
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def storeByteRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeByteChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 cols.is_real)

private def storeByteRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeByteChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReaderImmutable.asserts cols.state.clk_high clkLow
      cols.state.pc 36
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
      cols.is_real cols.is_real)

private def storeByteRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeByteChipRustColumns env input offset
  let ts := cols.memory_access.access_timestamp
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    [ cols.is_real * (cols.is_real - 1),
      cols.is_real * (cols.is_real - 1),
      cols.is_real * (ts.compare_low * (ts.compare_low - 1)),
      cols.is_real * (ts.compare_low *
        (cols.state.clk_high - ts.prev_high)),
      cols.is_real *
        ((ts.compare_low * (clkLow + 1) +
            (1 - ts.compare_low) * cols.state.clk_high -
            (ts.compare_low * ts.prev_low +
              (1 - ts.compare_low) * ts.prev_high) - 1) -
          (ts.diff_low_limb + ts.diff_high_limb * 65536)),
      (cols.offset_bit[1] - 1) *
        ((cols.offset_bit[2] - 1) *
          (cols.mem_limb - cols.memory_access.prev_value[0])),
      cols.offset_bit[1] *
        ((cols.offset_bit[2] - 1) *
          (cols.mem_limb - cols.memory_access.prev_value[1])),
      (cols.offset_bit[1] - 1) *
        (cols.offset_bit[2] *
          (cols.mem_limb - cols.memory_access.prev_value[2])),
      cols.offset_bit[1] *
        (cols.offset_bit[2] *
          (cols.mem_limb - cols.memory_access.prev_value[3])),
      cols.increment -
        ((cols.register_low_byte - cols.mem_limb_low_byte) *
            (1 - cols.offset_bit[0]) +
          256 * (cols.register_low_byte -
            (cols.mem_limb - cols.mem_limb_low_byte) * (256 : ZMod p)⁻¹) *
              cols.offset_bit[0]),
      cols.store_value[0] -
        (cols.increment * (1 - cols.offset_bit[1]) *
            (1 - cols.offset_bit[2]) + cols.memory_access.prev_value[0]),
      cols.store_value[1] -
        (cols.increment * cols.offset_bit[1] *
            (1 - cols.offset_bit[2]) + cols.memory_access.prev_value[1]),
      cols.store_value[2] -
        (cols.increment * (1 - cols.offset_bit[1]) *
            cols.offset_bit[2] + cols.memory_access.prev_value[2]),
      cols.store_value[3] -
        (cols.increment * cols.offset_bit[1] * cols.offset_bit[2] +
          cols.memory_access.prev_value[3]) ]

private def storeByteRustMeaning
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeByteRustAddressMeaning env input offset ∧
    storeByteRustCpuMeaning env input offset ∧
    storeByteRustITypeMeaning env input offset ∧
    storeByteRustTailMeaning env input offset

private theorem storeByteNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreByteChip.main input).operations offset)) ↔
      storeByteNativeMeaning env input offset := by
  rw [storeByteNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (storeByteMemoryInput input offset)).operations (offset + 4)) =
        storeByteMemoryAssertionValues env
          (storeByteMemoryInput input offset) by
    exact storeByteMemoryAssertionList env
      (storeByteMemoryInput input offset) (offset + 4)]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeByteChipOracle.nativeAssertZeros
          (storeByteChipRustColumns env input offset)) ↔
      storeByteRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, storeByteChipOracle]
  rw [Extracted.StoreByteOracle.StoreByteColumns.asserts]
  dsimp only [storeByteChipReconfigure, storeByteOracleAddressOperation]
  simp only [storeByteOracle_address_asserts_eq]
  unfold storeByteRustMeaning storeByteRustAddressMeaning
    storeByteRustCpuMeaning storeByteRustITypeMeaning
    storeByteRustTailMeaning
  simp only [List.forall_append, storeByteVec3Eta, storeByteVec4Eta,
    Nat.cast_one, Nat.cast_ofNat]
  tauto

private theorem storeByteAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    storeByteRustAddressMeaning env input offset ↔
      storeByteNativeAddressMeaning env input offset := by
  have hAddress := storeByteAddressAssertions (p := p) env
    (storeByteAddressInput input) offset
  unfold storeByteRustAddressMeaning storeByteNativeAddressMeaning
  dsimp only [storeByteChipRustColumns]
  rw [storeByteEvalAddressCols]
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
    exact storeByteEvalVec4Components env
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
    exact storeByteEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  rw [← ProvableType.getElem_eval_fields env input.offset_bit 0 (by decide),
    ← ProvableType.getElem_eval_fields env input.offset_bit 1 (by decide),
    ← ProvableType.getElem_eval_fields env input.offset_bit 2 (by decide)]
  simp only [storeByteAddressInput] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    storeByteRustCpuMeaning env input offset ↔
      storeByteNativeCpuMeaning env input offset := by
  let cpu := storeByteCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env input.is_real) (by
      simp only [cpu, storeByteCpuInput,
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
  unfold storeByteRustCpuMeaning storeByteNativeCpuMeaning
  dsimp only [storeByteChipRustColumns]
  rw [hNext]
  simp only [cpu, storeByteCpuInput] at hCpu
  exact hCpu

set_option maxHeartbeats 1000000 in
private theorem storeByteITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    storeByteRustITypeMeaning env input offset ↔
      storeByteNativeITypeMeaning env input offset := by
  have hIType := storeByteITypeImmutableAssertions (p := p) env
    (storeByteITypeInput input) (offset + 4) (by
      simp only [storeByteITypeInput])
  have hHigh :
      (Eval.eval env input.state).clk_high =
        Expression.eval env input.state.clk_high := by
    rw [eval_cpuState]
    simp only [ProvableType.eval_field]
  have hLow :
      (Eval.eval env input.state).clk_0_16 +
          (Eval.eval env input.state).clk_16_24 * 65536 =
        Expression.eval env
          (input.state.clk_0_16 + input.state.clk_16_24 * 65536) := by
    rw [eval_cpuState]
    dsimp only
    simp only [ProvableType.eval_field, Expression.eval]
  have hPc :
      (Eval.eval env input.state).pc =
        Eval.eval env input.state.pc := by
    rw [eval_cpuState]
  unfold storeByteRustITypeMeaning storeByteNativeITypeMeaning
  dsimp only [storeByteChipRustColumns]
  rw [hHigh, hLow, hPc]
  simp only [storeByteITypeInput] at hIType
  exact hIType

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    storeByteRustTailMeaning env input offset ↔
      storeByteNativeMemoryMeaning env input offset ∧
        Expression.eval env (storeByteSelect0 input) = 0 ∧
        Expression.eval env (storeByteSelect1 input) = 0 ∧
        Expression.eval env (storeByteSelect2 input) = 0 ∧
        Expression.eval env (storeByteSelect3 input) = 0 ∧
        Expression.eval env (storeByteIncrementConstraint input) = 0 ∧
        Expression.eval env (storeByteWrite0 input) = 0 ∧
        Expression.eval env (storeByteWrite1 input) = 0 ∧
        Expression.eval env (storeByteWrite2 input) = 0 ∧
        Expression.eval env (storeByteWrite3 input) = 0 ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  unfold storeByteRustTailMeaning storeByteNativeMemoryMeaning
  dsimp only [storeByteChipRustColumns]
  simp only [storeByteMemoryAssertionValues, storeByteMemoryInput,
    List.Forall, eval_cpuState, storeByteEvalMemoryCols,
    storeByteEvalMemoryTimestamp,
    ProvableType.eval_field, ← ProvableType.getElem_eval_fields, eval_sub,
    storeByteSelect0, storeByteSelect1, storeByteSelect2,
    storeByteSelect3, storeByteIncrementConstraint,
    storeByteWrite0, storeByteWrite1, storeByteWrite2, storeByteWrite3,
    Expression.eval, Nat.cast_one, sub_zero]
  ring_nf
  tauto

private theorem storeByteChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    storeByteRustMeaning env input offset ↔
      storeByteNativeMeaning env input offset := by
  unfold storeByteRustMeaning storeByteNativeMeaning
  rw [storeByteAddressMeaningFaithful, storeByteCpuMeaningFaithful,
    storeByteITypeMeaningFaithful, storeByteTailMeaningFaithful]
  tauto

private theorem storeByteChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeByteChipOracle.nativeAssertZeros
          (storeByteChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreByteChip.main input).operations offset)) :=
  (storeByteRustAssertionsDecompose (p := p) env input offset).trans
    ((storeByteChipMeaningFaithful (p := p) env input offset).trans
      (storeByteNativeAssertionsDecompose (p := p) env input offset).symm)

theorem storeByteChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreByteChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreByteChip.main env input offset cols) :
    List.Forall (· = 0)
        (storeByteChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreByteChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreByteChip.elaborated (p := p)) hbind
  rw [StoreByteChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreByteChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeByteChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact storeByteChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem storeByteChipConstraintsConstructive
    (rustCols : Extracted.StoreByteOracle.StoreByteColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeByteChipRowCodec.assignment
      (storeByteChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (storeByteChipOracle.assertZeros rustCols) ↔
      (⟨StoreByteChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := storeByteChipOracle.deconfigure rustCols
  let assignment := storeByteChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreByteChip.main assignment.environment
        (⟨StoreByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreByteChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeByteChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨StoreByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (storeByteChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨StoreByteChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      StoreByteChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (StoreByteChip.circuit (p := p))
      assignment.environment storeByteChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

private def storeByteStateInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def storeByteProgramInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 36,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem storeByteStateInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreByteChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (storeByteStateInteractions input).map ChannelInteraction.toRaw := by
  exact (StoreByteChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (storeByteStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreByteChip.circuit, storeByteStateInteractions, expose])

private theorem storeByteProgramInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreByteChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (storeByteProgramInteractions input).map ChannelInteraction.toRaw := by
  exact (StoreByteChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (storeByteProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreByteChip.circuit, storeByteProgramInteractions, expose])

private theorem storeByteStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((storeByteStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.StoreByteOracle.StoreByteColumns.interactions
          (storeByteChipReconfigure
            (storeByteChipRustColumns env input offset))).map
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
  simp only [storeByteStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.StoreByteOracle.StoreByteColumns.interactions,
    storeByteChipReconfigure, storeByteOracleAddressOperation,
    Extracted.StoreByteOracle.AddressOperation.interactions,
    Extracted.StoreByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeByteChipRustColumns, storeByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem storeByteProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((storeByteProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.StoreByteOracle.StoreByteColumns.interactions
          (storeByteChipReconfigure
            (storeByteChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have h36 : (36 : ZMod p).val = 36 := by
    have hp : 2 ^ 17 < p := Fact.out
    have hsmall : (36 : ℕ) < 2 ^ 17 := by norm_num
    exact ZMod.val_natCast_of_lt (Nat.lt_trans hsmall hp)
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
  simp only [storeByteProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.StoreByteOracle.StoreByteColumns.interactions,
    storeByteChipReconfigure, storeByteOracleAddressOperation,
    Extracted.StoreByteOracle.AddressOperation.interactions,
    Extracted.StoreByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeByteChipRustColumns, storeByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat, h36]

private theorem storeByteMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((StoreByteChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.StoreByteOracle.StoreByteColumns.interactions
          (storeByteChipReconfigure
            (storeByteChipRustColumns env input offset))).map
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
  simp only [StoreByteChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.StoreByteOracle.StoreByteColumns.interactions,
    storeByteChipReconfigure, storeByteOracleAddressOperation,
    Extracted.StoreByteOracle.AddressOperation.interactions,
    Extracted.StoreByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreByteOracle.AddressOperation.value,
    storeByteChipRustColumns, storeByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeByteEvalMemoryCols, storeByteEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  exact List.perm_append_comm
    (l₁ := [_, _]) (l₂ := [_, _, _, _])

private def storeByteCpuByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def storeByteAddressByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, var { index := offset },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var { index := offset + 1 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var { index := offset + 2 },
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, ((var { index := offset } : Expression (ZMod p)) -
          (4 : Expression (ZMod p)) * input.offset_bit[2] -
          (2 : Expression (ZMod p)) * input.offset_bit[1] -
          input.offset_bit[0]) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def storeByteMemoryByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def storeByteITypeByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 +
    input.state.clk_16_24 * 65536
  [ byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, (clkLow + 4 -
          input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, (clkLow + 3 -
          input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
        (65536 : ZMod p)⁻¹, 0⟩ ]

private def storeByteInlineByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let regHigh :=
    (input.adapter.op_a_memory.prev_value[0] - input.register_low_byte) *
      Expression.const ((256 : ZMod p)⁻¹)
  let memHigh := (input.mem_limb - input.mem_limb_low_byte) *
    Expression.const ((256 : ZMod p)⁻¹)
  [ byteChannel.pulledIf input.is_real
      ⟨3, 0, input.register_low_byte, regHigh⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.mem_limb_low_byte, memHigh⟩ ]

private def storeByteByteInteractions
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  storeByteCpuByteInteractions input ++
    storeByteAddressByteInteractions input offset ++
    storeByteMemoryByteInteractions input ++
    storeByteITypeByteInteractions input ++
    storeByteInlineByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteCpuByteInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (storeByteCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeByteCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [storeByteCpuInput, storeByteCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem storeByteAddressByteInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (storeByteAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeByteAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [storeByteAddressInput, storeByteAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem storeByteMemoryByteInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (storeByteMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeByteMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [storeByteMemoryInput, storeByteMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

private theorem storeByteITypeByteInteractionsEq
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.main
        (storeByteITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeByteITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [storeByteITypeInput, storeByteITypeByteInteractions,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem storeByteByteInteractionsDecompose
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreByteChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeByteByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  rw [show
      ((StoreByteChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (storeByteCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (storeByteAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (storeByteMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReaderImmutable.main
            (storeByteITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        (storeByteInlineByteInteractions input).map
          ChannelInteraction.toRaw by
  simp [StoreByteChip.main, storeByteCpuInput, storeByteAddressInput,
    storeByteMemoryInput, storeByteAddressValue, storeByteAddressCols,
    storeByteITypeInput, storeByteInlineByteInteractions,
    Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReaderImmutable.circuit, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, heq]
  simp only [Operations.interactionsWith]]
  rw [storeByteCpuByteInteractionsEq,
    storeByteAddressByteInteractionsEq,
    storeByteMemoryByteInteractionsEq,
    storeByteITypeByteInteractionsEq]
  simp only [storeByteByteInteractions, List.map_append]

private theorem storeBytePermFourBlocks {α : Type}
    (a b c d : List α) :
    List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ d ++ c) := by
  have hab : List.Perm (a ++ b ++ c ++ d)
      (b ++ a ++ c ++ d) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right (c ++ d)
  have hcd : List.Perm (b ++ a ++ c ++ d)
      (b ++ a ++ d ++ c) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := c) (l₂ := d)).append_left (b ++ a)
  exact hab.trans hcd

set_option maxRecDepth 2000 in
private theorem storeByteByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((StoreByteChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.StoreByteOracle.StoreByteColumns.interactions
          (storeByteChipReconfigure
            (storeByteChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  have h6 : (6 : ZMod p).val = 6 := by
    exact ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num)
      (Fact.out (p := 2 ^ 17 < p)))
  have h3 : (3 : ZMod p).val = 3 := by
    exact ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num)
      (Fact.out (p := 2 ^ 17 < p)))
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
  rw [storeByteByteInteractionsDecompose]
  simp only [storeByteByteInteractions, List.map_append]
  simp only [storeByteCpuByteInteractions,
    storeByteAddressByteInteractions, storeByteMemoryByteInteractions,
    storeByteITypeByteInteractions, storeByteInlineByteInteractions,
    List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.StoreByteOracle.StoreByteColumns.interactions,
    storeByteChipReconfigure, storeByteOracleAddressOperation,
    Extracted.StoreByteOracle.AddressOperation.interactions,
    Extracted.StoreByteOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreByteOracle.AddressOperation.value,
    storeByteChipRustColumns, storeByteEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeByteEvalMemoryCols, storeByteEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    StoreByteChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, storeByteEvalMemoryCols,
    storeByteEvalMemoryTimestamp, ProvableType.eval_field]
  exact (storeBytePermFourBlocks
    [_, _] [_, _, _, _] [_, _] [_, _, _, _]).append_right [_, _]

private theorem storeByteUnexpectedInteractionsEmpty
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((StoreByteChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((StoreByteChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (StoreByteChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [StoreByteChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem storeByteChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreByteChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreByteChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((StoreByteChip.main input).operations offset))
      (storeByteChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreByteChip.elaborated (p := p)) hbind
  rw [StoreByteChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreByteChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeByteChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.StoreByteOracle.StoreByteColumns.interactions
      (storeByteChipReconfigure
        (storeByteChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [storeByteUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, storeByteChipOracle]
  rw [storeByteStateInteractionsEq,
    StoreByteChip.interactionsWith_memory_eq,
    storeByteProgramInteractionsEq]
  have hState :=
    storeByteStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    storeByteByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    storeByteMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    storeByteProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem storeByteChipInteractionsConstructive
    (rustCols : Extracted.StoreByteOracle.StoreByteColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeByteChipRowCodec.assignment
      (storeByteChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨StoreByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (storeByteChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := storeByteChipOracle.deconfigure rustCols
  let assignment := storeByteChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreByteChip.main assignment.environment
        (⟨StoreByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreByteChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreByteChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeByteChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨StoreByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreByteChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (StoreByteChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    StoreByteChip.circuit_main_eq] using hfaithful

theorem storeByteChip_faithful :
    ChipFaithful (p := p) StoreByteChip.Inputs
      StoreByteChip.Columns Extracted.StoreByteOracle.StoreByteColumns
      StoreByteChip.circuit storeByteChipRowCodec
      storeByteChipOracle where
  constraints := storeByteChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (storeByteChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
