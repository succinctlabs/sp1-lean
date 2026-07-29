import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.StoreWord
import SP1Clean.Proofs.Chips.StoreWordChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `StoreWord`

This file relates the native Clean `StoreWordChip` row to the complete generated row-level oracle
for pinned SP1 v6.3.1. The `ChipFaithful` theorem at the bottom covers every `assertZero` expression and the
entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated StoreWord oracle namespace. -/
def storeWordOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.StoreWordOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `storeWordOracleAddressOperation`. -/
def storeWordNativeAddressOperation {F : Type}
    (cols : Extracted.StoreWordOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address block is copied into Rust's chip-private operation row. This is not
an operation-level faithfulness claim. -/
def storeWordChipReconfigure {F : Type} (cols : StoreWordChip.Columns F) :
    Extracted.StoreWordOracle.StoreWordColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeWordOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    store_value := cols.store_value
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def storeWordChipDeconfigure {F : Type} (cols : Extracted.StoreWordOracle.StoreWordColumns F) :
    StoreWordChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeWordNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    store_value := cols.store_value
    is_real := cols.is_real }

/-- SP1 Rust's complete StoreWord-chip oracle, viewed from the native Lean row. -/
def storeWordChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F StoreWordChip.Columns Extracted.StoreWordOracle.StoreWordColumns where
  reconfigure := storeWordChipReconfigure
  deconfigure := storeWordChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.StoreWordOracle.StoreWordColumns.asserts
  interactions := Extracted.StoreWordOracle.StoreWordColumns.interactions

/- Namespace bridges between the StoreWord oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address-op
lemmas below stay stated once against the standalone modules (also consumed by the other load and
store chips). -/

private theorem storeWordOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreWordOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.StoreWordOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem storeWordOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreWordOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.StoreWordOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem storeWordOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreWordOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreWordOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [storeWordOracle_addrAdd_asserts_eq]

private theorem storeWordOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreWordOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreWordOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [storeWordOracle_addrAdd_interactions_eq]

def storeWordChipInput {F : Type}
    (cols : StoreWordChip.Columns F) : StoreWordChip.Inputs F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access
    offset_bit := cols.offset_bit
    store_value := cols.store_value }

def storeWordChipLocals {F : Type}
    (cols : StoreWordChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def storeWordChipPhysicalRow {F : Type}
    (cols : StoreWordChip.Columns F) : Array F :=
  inputFirstRow (storeWordChipInput cols) (storeWordChipLocals cols)

def storeWordChipColumnsOfInput {F : Type}
    (input : StoreWordChip.Inputs F) (locals : Vector F 4) :
    StoreWordChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.offset_bit, input.store_value, input.is_real⟩

private theorem storeWordVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeWordVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeWordEvalVec4Components
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

private theorem storeWordAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem storeWordCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem storeWordITypeEta {F : Type}
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

theorem storeWordChipColumnsOfInput_roundtrip {F : Type}
    (cols : StoreWordChip.Columns F) :
    storeWordChipColumnsOfInput
        (storeWordChipInput cols) (storeWordChipLocals cols) = cols := by
  cases cols
  simp [storeWordChipColumnsOfInput, storeWordChipInput,
    storeWordChipLocals, storeWordVec3Eta]

@[circuit_norm] private theorem storeWordEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeWordEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeWordEvalAddrAddInput
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

@[circuit_norm] private theorem storeWordEvalAddressInput
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

@[circuit_norm] private theorem storeWordEvalMemoryInput
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

@[circuit_norm] private theorem storeWordEvalMemoryTimestamp
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

@[circuit_norm] private theorem storeWordEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem evalStoreWordDirectOutput
    (input : StoreWordChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((StoreWordChip.elaborated (p := p)).output
          (varFromOffset StoreWordChip.Inputs 0)
          (size StoreWordChip.Inputs)) =
      storeWordChipColumnsOfInput input locals := by
  rw [StoreWordChip.directOutput_eq]
  rw [← CircuitType.eval_expression, StoreWordChip.eval_columns]
  unfold storeWordChipColumnsOfInput
  rw [StoreWordChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [StoreWordChip.eval_inputs, StoreWordChip.Inputs.mk.injEq] at hinputEval
  refine
    ⟨hinputEval.2.1, hinputEval.2.2.1, ?_,
      hinputEval.2.2.2.1, hinputEval.2.2.2.2.1,
      hinputEval.2.2.2.2.2, hinputEval.1⟩
  rw [storeWordEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeWordEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size StoreWordChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size StoreWordChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size StoreWordChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))

def storeWordChipRowCodec :
    ChipRowCodec StoreWordChip.Inputs StoreWordChip.Columns
      (StoreWordChip.circuit (p := p)) where
  assignment cols data := {
    row := storeWordChipPhysicalRow cols
    input := storeWordChipInput cols
    width_eq := by
      rw [storeWordChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, StoreWordChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (StoreWordChip.circuit (p := p))
        (storeWordChipInput cols) (storeWordChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((StoreWordChip.main _).output _) = _
      rw [StoreWordChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalStoreWordDirectOutput (p := p)
        (storeWordChipInput cols) (storeWordChipLocals cols) data).trans
          (storeWordChipColumnsOfInput_roundtrip cols) }

theorem storeWordChipLookupsEmpty :
    (⟨StoreWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    StoreWordChip.circuit_main_eq]
  simp [StoreWordChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def storeWordAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (storeWordAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [storeWordAddressCols]
  rw [storeWordEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeWordEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def storeWordAddressInput
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩

private def storeWordAddressValue
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (storeWordAddressInput input) (storeWordAddressCols offset)

private def storeWordCpuInput
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_real⟩

private def storeWordMemoryInput
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (storeWordAddressValue input offset)[0],
    (storeWordAddressValue input offset)[1],
    (storeWordAddressValue input offset)[2],
    input.store_value, input.is_real⟩

private def storeWordITypeInput
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, 38⟩

private theorem storeWordNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreWordChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (storeWordCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (storeWordAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (storeWordMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReaderImmutable.main
              (storeWordITypeInput input)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.store_value[0] -
                (input.memory_access.prev_value[0] +
                  (input.adapter.op_a_memory.prev_value[0] -
                    input.memory_access.prev_value[0]) *
                      (1 - input.offset_bit)), 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.store_value[1] -
                (input.memory_access.prev_value[1] +
                  (input.adapter.op_a_memory.prev_value[1] -
                    input.memory_access.prev_value[1]) *
                      (1 - input.offset_bit)), 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.store_value[2] -
                (input.memory_access.prev_value[2] +
                  (input.adapter.op_a_memory.prev_value[0] -
                    input.memory_access.prev_value[2]) *
                      input.offset_bit), 0)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Gadgets.Equality.main (M := field)
              (input.store_value[3] -
                (input.memory_access.prev_value[3] +
                  (input.adapter.op_a_memory.prev_value[1] -
                    input.memory_access.prev_value[3]) *
                      input.offset_bit), 0)).operations (offset + 4))) ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  simp only [nativeAssertZeros, StoreWordChip.main,
    storeWordCpuInput, storeWordAddressInput, storeWordAddressCols,
    storeWordAddressValue, storeWordMemoryInput, storeWordITypeInput,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit, Readers.ITypeReaderImmutable.circuit,
    circuit_norm, List.map_append, List.forall_append]

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordAddrAddAssertions
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
    storeWordEvalAddrAddInput, storeWordEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem storeWordAddressAssertions
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
  let cols := storeWordAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := storeWordAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, storeWordAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    storeWordEvalAddressInput, ProvableType.eval_field,
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

private def storeWordITypeImmutableAssertionValues
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

private theorem storeWordITypeImmutableAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.ITypeReaderImmutable.main input).operations offset)) =
      storeWordITypeImmutableAssertionValues env input := by
  simp only [Readers.ITypeReaderImmutable.main, circuit_norm]
  simp only [Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, circuit_norm,
    constraints_formalAssertion_toSubcircuit]
  simp only [List.map_append, List.map_cons]
  simp only [CanonicalReader.registerAccessTimestampAssertions]
  repeat' rw [CanonicalReader.equalityAssertionList]
  rfl

private theorem storeWordITypeImmutableAssertions
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
        storeWordITypeImmutableAssertionValues env input by
    exact storeWordITypeImmutableAssertionList env input offset]
  simp only [Extracted.ITypeReaderImmutable.asserts,
    storeWordITypeImmutableAssertionValues, List.Forall]
  simp only [Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    eval_sub, Expression.eval, sub_zero]
  rw [htrust]
  tauto

private def storeWordMemoryAssertionValues
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
private theorem storeWordMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      storeWordMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [storeWordMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, storeWordEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

private def storeWordChipRustColumns
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    StoreWordChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (storeWordAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    offset_bit := Expression.eval env input.offset_bit
    store_value := Eval.eval env input.store_value
    is_real := Expression.eval env input.is_real }

private def storeWordNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (storeWordCpuInput input)).operations offset))

private def storeWordNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (storeWordAddressInput input)).operations offset))

private def storeWordNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (storeWordMemoryAssertionValues env
      (storeWordMemoryInput input offset))

private def storeWordNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReaderImmutable.main
        (storeWordITypeInput input)).operations (offset + 4)))

private def storeWordNativeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeWordNativeCpuMeaning env input offset ∧
    storeWordNativeAddressMeaning env input offset ∧
    storeWordNativeMemoryMeaning env input offset ∧
    storeWordNativeITypeMeaning env input offset ∧
    Expression.eval env
        (input.store_value[0] -
          (input.memory_access.prev_value[0] +
            (input.adapter.op_a_memory.prev_value[0] -
              input.memory_access.prev_value[0]) *
                (1 - input.offset_bit))) = 0 ∧
    Expression.eval env
        (input.store_value[1] -
          (input.memory_access.prev_value[1] +
            (input.adapter.op_a_memory.prev_value[1] -
              input.memory_access.prev_value[1]) *
                (1 - input.offset_bit))) = 0 ∧
    Expression.eval env
        (input.store_value[2] -
          (input.memory_access.prev_value[2] +
            (input.adapter.op_a_memory.prev_value[0] -
              input.memory_access.prev_value[2]) *
                input.offset_bit)) = 0 ∧
    Expression.eval env
        (input.store_value[3] -
          (input.memory_access.prev_value[3] +
            (input.adapter.op_a_memory.prev_value[1] -
              input.memory_access.prev_value[3]) *
                input.offset_bit)) = 0 ∧
    Expression.eval env (input.is_real * (input.is_real - 1)) = 0

private def storeWordRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeWordChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      (0 : ZMod p) (0 : ZMod p) cols.offset_bit
      cols.is_real
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def storeWordRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeWordChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 cols.is_real)

private def storeWordRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeWordChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReaderImmutable.asserts cols.state.clk_high clkLow
      cols.state.pc 38
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

private def storeWordRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeWordChipRustColumns env input offset
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
      cols.store_value[0] -
        (cols.memory_access.prev_value[0] +
          (cols.adapter.op_a_memory.prev_value[0] -
            cols.memory_access.prev_value[0]) * (1 - cols.offset_bit)),
      cols.store_value[1] -
        (cols.memory_access.prev_value[1] +
          (cols.adapter.op_a_memory.prev_value[1] -
            cols.memory_access.prev_value[1]) * (1 - cols.offset_bit)),
      cols.store_value[2] -
        (cols.memory_access.prev_value[2] +
          (cols.adapter.op_a_memory.prev_value[0] -
            cols.memory_access.prev_value[2]) * cols.offset_bit),
      cols.store_value[3] -
        (cols.memory_access.prev_value[3] +
          (cols.adapter.op_a_memory.prev_value[1] -
            cols.memory_access.prev_value[3]) * cols.offset_bit) ]

private def storeWordRustMeaning
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeWordRustAddressMeaning env input offset ∧
    storeWordRustCpuMeaning env input offset ∧
    storeWordRustITypeMeaning env input offset ∧
    storeWordRustTailMeaning env input offset

private theorem storeWordNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreWordChip.main input).operations offset)) ↔
      storeWordNativeMeaning env input offset := by
  rw [storeWordNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (storeWordMemoryInput input offset)).operations (offset + 4)) =
        storeWordMemoryAssertionValues env
          (storeWordMemoryInput input offset) by
    exact storeWordMemoryAssertionList env
      (storeWordMemoryInput input offset) (offset + 4)]
  repeat' rw [CanonicalReader.equalityAssertions]
  simp only [Expression.eval]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeWordChipOracle.nativeAssertZeros
          (storeWordChipRustColumns env input offset)) ↔
      storeWordRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, storeWordChipOracle]
  rw [Extracted.StoreWordOracle.StoreWordColumns.asserts]
  dsimp only [storeWordChipReconfigure, storeWordOracleAddressOperation]
  simp only [storeWordOracle_address_asserts_eq]
  unfold storeWordRustMeaning storeWordRustAddressMeaning
    storeWordRustCpuMeaning storeWordRustITypeMeaning
    storeWordRustTailMeaning
  simp only [List.forall_append, storeWordVec3Eta, storeWordVec4Eta]
  tauto

private theorem storeWordAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    storeWordRustAddressMeaning env input offset ↔
      storeWordNativeAddressMeaning env input offset := by
  have hAddress := storeWordAddressAssertions (p := p) env
    (storeWordAddressInput input) offset
  unfold storeWordRustAddressMeaning storeWordNativeAddressMeaning
  dsimp only [storeWordChipRustColumns]
  rw [storeWordEvalAddressCols]
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
    exact storeWordEvalVec4Components env
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
    exact storeWordEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [storeWordAddressInput] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    storeWordRustCpuMeaning env input offset ↔
      storeWordNativeCpuMeaning env input offset := by
  let cpu := storeWordCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env input.is_real) (by
      simp only [cpu, storeWordCpuInput,
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
  unfold storeWordRustCpuMeaning storeWordNativeCpuMeaning
  dsimp only [storeWordChipRustColumns]
  rw [hNext]
  simp only [cpu, storeWordCpuInput] at hCpu
  exact hCpu

private theorem storeWordITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    storeWordRustITypeMeaning env input offset ↔
      storeWordNativeITypeMeaning env input offset := by
  have hIType := storeWordITypeImmutableAssertions (p := p) env
    (storeWordITypeInput input) (offset + 4) (by
      simp only [storeWordITypeInput])
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
  unfold storeWordRustITypeMeaning storeWordNativeITypeMeaning
  dsimp only [storeWordChipRustColumns]
  rw [hHigh, hLow, hPc]
  simp only [storeWordITypeInput] at hIType
  exact hIType

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    storeWordRustTailMeaning env input offset ↔
      storeWordNativeMemoryMeaning env input offset ∧
        Expression.eval env
            (input.store_value[0] -
              (input.memory_access.prev_value[0] +
                (input.adapter.op_a_memory.prev_value[0] -
                  input.memory_access.prev_value[0]) *
                    (1 - input.offset_bit))) = 0 ∧
        Expression.eval env
            (input.store_value[1] -
              (input.memory_access.prev_value[1] +
                (input.adapter.op_a_memory.prev_value[1] -
                  input.memory_access.prev_value[1]) *
                    (1 - input.offset_bit))) = 0 ∧
        Expression.eval env
            (input.store_value[2] -
              (input.memory_access.prev_value[2] +
                (input.adapter.op_a_memory.prev_value[0] -
                  input.memory_access.prev_value[2]) *
                    input.offset_bit)) = 0 ∧
        Expression.eval env
            (input.store_value[3] -
              (input.memory_access.prev_value[3] +
                (input.adapter.op_a_memory.prev_value[1] -
                  input.memory_access.prev_value[3]) *
                    input.offset_bit)) = 0 ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  unfold storeWordRustTailMeaning storeWordNativeMemoryMeaning
  dsimp only [storeWordChipRustColumns]
  simp only [storeWordMemoryAssertionValues, storeWordMemoryInput,
    List.Forall, eval_cpuState, storeWordEvalMemoryCols,
    storeWordEvalMemoryTimestamp,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp,
    ProvableType.eval_field, ← ProvableType.getElem_eval_fields, eval_sub,
    Expression.eval, sub_zero]
  tauto

private theorem storeWordChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    storeWordRustMeaning env input offset ↔
      storeWordNativeMeaning env input offset := by
  unfold storeWordRustMeaning storeWordNativeMeaning
  rw [storeWordAddressMeaningFaithful, storeWordCpuMeaningFaithful,
    storeWordITypeMeaningFaithful, storeWordTailMeaningFaithful]
  tauto

private theorem storeWordChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeWordChipOracle.nativeAssertZeros
          (storeWordChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreWordChip.main input).operations offset)) :=
  (storeWordRustAssertionsDecompose (p := p) env input offset).trans
    ((storeWordChipMeaningFaithful (p := p) env input offset).trans
      (storeWordNativeAssertionsDecompose (p := p) env input offset).symm)

theorem storeWordChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreWordChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreWordChip.main env input offset cols) :
    List.Forall (· = 0)
        (storeWordChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreWordChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreWordChip.elaborated (p := p)) hbind
  rw [StoreWordChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreWordChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeWordChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact storeWordChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem storeWordChipConstraintsConstructive
    (rustCols : Extracted.StoreWordOracle.StoreWordColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeWordChipRowCodec.assignment
      (storeWordChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (storeWordChipOracle.assertZeros rustCols) ↔
      (⟨StoreWordChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := storeWordChipOracle.deconfigure rustCols
  let assignment := storeWordChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreWordChip.main assignment.environment
        (⟨StoreWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreWordChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeWordChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨StoreWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (storeWordChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨StoreWordChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      StoreWordChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (StoreWordChip.circuit (p := p))
      assignment.environment storeWordChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open SP1Clean.InteractionRecovery

private def storeWordStateInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def storeWordProgramInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 38,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem storeWordStateInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreWordChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (storeWordStateInteractions input).map ChannelInteraction.toRaw :=
  (StoreWordChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (storeWordStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreWordChip.circuit, storeWordStateInteractions, expose])

private theorem storeWordProgramInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreWordChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (storeWordProgramInteractions input).map ChannelInteraction.toRaw :=
  (StoreWordChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (storeWordProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreWordChip.circuit, storeWordProgramInteractions, expose])

private theorem storeWordStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((storeWordStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.StoreWordOracle.StoreWordColumns.interactions
          (storeWordChipReconfigure
            (storeWordChipRustColumns env input offset))).map
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
  simp only [storeWordStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.StoreWordOracle.StoreWordColumns.interactions,
    storeWordChipReconfigure, storeWordOracleAddressOperation,
    Extracted.StoreWordOracle.AddressOperation.interactions,
    Extracted.StoreWordOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeWordChipRustColumns, storeWordEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem storeWordProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((storeWordProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.StoreWordOracle.StoreWordColumns.interactions
          (storeWordChipReconfigure
            (storeWordChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have h38 : (38 : ZMod p).val = 38 := by
    have hp : 2 ^ 17 < p := Fact.out
    have hsmall : (38 : ℕ) < 2 ^ 17 := by norm_num
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
  simp only [storeWordProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.StoreWordOracle.StoreWordColumns.interactions,
    storeWordChipReconfigure, storeWordOracleAddressOperation,
    Extracted.StoreWordOracle.AddressOperation.interactions,
    Extracted.StoreWordOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeWordChipRustColumns, storeWordEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat, h38]

private theorem storeWordMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((StoreWordChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.StoreWordOracle.StoreWordColumns.interactions
          (storeWordChipReconfigure
            (storeWordChipRustColumns env input offset))).map
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
  simp only [StoreWordChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.StoreWordOracle.StoreWordColumns.interactions,
    storeWordChipReconfigure, storeWordOracleAddressOperation,
    Extracted.StoreWordOracle.AddressOperation.interactions,
    Extracted.StoreWordOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreWordOracle.AddressOperation.value,
    storeWordChipRustColumns, storeWordEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeWordEvalMemoryCols, storeWordEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  exact List.perm_append_comm
    (l₁ := [_, _]) (l₂ := [_, _, _, _])

private def storeWordCpuByteInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def storeWordAddressByteInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
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
          (4 : Expression (ZMod p)) * input.offset_bit -
          (2 : Expression (ZMod p)) * 0 - 0) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def storeWordMemoryByteInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def storeWordITypeByteInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) :
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

private def storeWordByteInteractions
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  storeWordCpuByteInteractions input ++
    storeWordAddressByteInteractions input offset ++
    storeWordMemoryByteInteractions input ++
    storeWordITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordCpuByteInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (storeWordCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeWordCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [storeWordCpuInput, storeWordCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem storeWordAddressByteInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (storeWordAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeWordAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [storeWordAddressInput, storeWordAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem storeWordMemoryByteInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (storeWordMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeWordMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [storeWordMemoryInput, storeWordMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

private theorem storeWordITypeByteInteractionsEq
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.main
        (storeWordITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeWordITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [storeWordITypeInput, storeWordITypeByteInteractions,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem storeWordByteInteractionsDecompose
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreWordChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeWordByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  rw [show
      ((StoreWordChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (storeWordCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (storeWordAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (storeWordMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReaderImmutable.main
            (storeWordITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [StoreWordChip.main, storeWordCpuInput, storeWordAddressInput,
    storeWordMemoryInput, storeWordAddressValue, storeWordAddressCols,
    storeWordITypeInput, Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReaderImmutable.circuit, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, heq]
  simp only [Operations.interactionsWith]]
  rw [storeWordCpuByteInteractionsEq,
    storeWordAddressByteInteractionsEq,
    storeWordMemoryByteInteractionsEq,
    storeWordITypeByteInteractionsEq]
  simp only [storeWordByteInteractions, List.map_append]

private theorem storeWordPermFourBlocks {α : Type}
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
private theorem storeWordByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((StoreWordChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.StoreWordOracle.StoreWordColumns.interactions
          (storeWordChipReconfigure
            (storeWordChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Byte)) := by
  have h6 : (6 : ZMod p).val = 6 :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) (Fact.out (p := 2 ^ 17 < p)))
  have h3 : (3 : ZMod p).val = 3 :=
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
  rw [storeWordByteInteractionsDecompose]
  simp only [storeWordByteInteractions, List.map_append]
  simp only [storeWordCpuByteInteractions,
    storeWordAddressByteInteractions, storeWordMemoryByteInteractions,
    storeWordITypeByteInteractions, List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.StoreWordOracle.StoreWordColumns.interactions,
    storeWordChipReconfigure, storeWordOracleAddressOperation,
    Extracted.StoreWordOracle.AddressOperation.interactions,
    Extracted.StoreWordOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreWordOracle.AddressOperation.value,
    storeWordChipRustColumns, storeWordEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeWordEvalMemoryCols, storeWordEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    StoreWordChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, storeWordEvalMemoryCols,
    storeWordEvalMemoryTimestamp, ProvableType.eval_field]
  exact storeWordPermFourBlocks
    [_, _] [_, _, _, _] [_, _] [_, _, _, _]

private theorem storeWordUnexpectedInteractionsEmpty
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((StoreWordChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((StoreWordChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (StoreWordChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [StoreWordChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem storeWordChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreWordChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreWordChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((StoreWordChip.main input).operations offset))
      (storeWordChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreWordChip.elaborated (p := p)) hbind
  rw [StoreWordChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreWordChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeWordChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.StoreWordOracle.StoreWordColumns.interactions
      (storeWordChipReconfigure
        (storeWordChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [storeWordUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, storeWordChipOracle]
  rw [storeWordStateInteractionsEq,
    StoreWordChip.interactionsWith_memory_eq,
    storeWordProgramInteractionsEq]
  have hState :=
    storeWordStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    storeWordByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    storeWordMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    storeWordProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind rustAccesses).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem storeWordChipInteractionsConstructive
    (rustCols : Extracted.StoreWordOracle.StoreWordColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeWordChipRowCodec.assignment
      (storeWordChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨StoreWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (storeWordChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := storeWordChipOracle.deconfigure rustCols
  let assignment := storeWordChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreWordChip.main assignment.environment
        (⟨StoreWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreWordChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreWordChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeWordChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨StoreWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreWordChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (StoreWordChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    StoreWordChip.circuit_main_eq] using hfaithful

theorem storeWordChip_faithful :
    ChipFaithful (p := p) StoreWordChip.Inputs
      StoreWordChip.Columns Extracted.StoreWordOracle.StoreWordColumns
      StoreWordChip.circuit storeWordChipRowCodec
      storeWordChipOracle where
  constraints := storeWordChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (storeWordChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
