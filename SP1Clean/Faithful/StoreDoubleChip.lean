import SP1Clean.Faithful.ChipOracle
import SP1Clean.Extracted.ChipOracle.StoreDouble
import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `StoreDouble`

This file relates the native Clean `StoreDoubleChip` row to the complete generated row-level oracle
for SP1 v6.4.0. The `ChipFaithful` theorem at the bottom covers every `assertZero` expression and the
entire interaction multiset, including inactive rows.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Rebuild the shared standalone `AddressOperation` block as the byte-identical struct embedded in
the generated StoreDouble oracle namespace. -/
def storeDoubleOracleAddressOperation {F : Type} (cols : Extracted.AddressOperation F) :
    Extracted.StoreDoubleOracle.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Inverse of `storeDoubleOracleAddressOperation`. -/
def storeDoubleNativeAddressOperation {F : Type}
    (cols : Extracted.StoreDoubleOracle.AddressOperation F) :
    Extracted.AddressOperation F :=
  { addr_operation := { value := cols.addr_operation.value }
    top_two_limb_inv := cols.top_two_limb_inv }

/-- Whole-chip row reconfiguration. The reader and memory-access blocks are already the canonical
generated substrate; the address block is copied into Rust's chip-private operation row. This is not
an operation-level faithfulness claim. -/
def storeDoubleChipReconfigure {F : Type} (cols : StoreDoubleChip.Columns F) :
    Extracted.StoreDoubleOracle.StoreDoubleColumns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeDoubleOracleAddressOperation cols.address_operation
    memory_access := cols.memory_access
    is_real := cols.is_real }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def storeDoubleChipDeconfigure {F : Type} (cols : Extracted.StoreDoubleOracle.StoreDoubleColumns F) :
    StoreDoubleChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    address_operation := storeDoubleNativeAddressOperation cols.address_operation
    memory_access := cols.memory_access
    is_real := cols.is_real }

/-- SP1 Rust's complete StoreDouble-chip oracle, viewed from the native Lean row. -/
def storeDoubleChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F StoreDoubleChip.Columns Extracted.StoreDoubleOracle.StoreDoubleColumns where
  reconfigure := storeDoubleChipReconfigure
  deconfigure := storeDoubleChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.StoreDoubleOracle.StoreDoubleColumns.asserts
  interactions := Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions

/- Namespace bridges between the StoreDouble oracle's embedded chip-private helper copies and the
canonical standalone generated modules. The two bodies are rendered from the same compiler output,
so each bridge is a definitional unfolding, not a mathematical claim. They let the address-op
lemmas below stay stated once against the standalone modules (also consumed by the other load and
store chips). -/

private theorem storeDoubleOracle_addrAdd_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreDoubleOracle.AddrAddOperation.asserts a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.asserts a b ⟨value⟩ is_real := by
  rw [Extracted.StoreDoubleOracle.AddrAddOperation.asserts,
    Extracted.AddrAddOperation.asserts]

private theorem storeDoubleOracle_addrAdd_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (a b : Word F) (value : Vector F 3) (is_real : F) :
    Extracted.StoreDoubleOracle.AddrAddOperation.interactions a b ⟨value⟩ is_real =
      Extracted.AddrAddOperation.interactions a b ⟨value⟩ is_real := by
  rw [Extracted.StoreDoubleOracle.AddrAddOperation.interactions,
    Extracted.AddrAddOperation.interactions]

private theorem storeDoubleOracle_address_asserts_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreDoubleOracle.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.asserts b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreDoubleOracle.AddressOperation.asserts,
    Extracted.AddressOperation.asserts]
  simp only [storeDoubleOracle_addrAdd_asserts_eq]

private theorem storeDoubleOracle_address_interactions_eq {F : Type} [Field F] [CoeHead F ℕ]
    (b cc : Word F) (offset_bit0 offset_bit1 offset_bit2 is_real : F)
    (value : Vector F 3) (top_two_limb_inv : F) :
    Extracted.StoreDoubleOracle.AddressOperation.interactions b cc offset_bit0 offset_bit1
        offset_bit2 is_real ⟨⟨value⟩, top_two_limb_inv⟩ =
      Extracted.AddressOperation.interactions b cc offset_bit0 offset_bit1 offset_bit2
        is_real ⟨⟨value⟩, top_two_limb_inv⟩ := by
  rw [Extracted.StoreDoubleOracle.AddressOperation.interactions,
    Extracted.AddressOperation.interactions]
  simp only [storeDoubleOracle_addrAdd_interactions_eq]

def storeDoubleChipInput {F : Type}
    (cols : StoreDoubleChip.Columns F) : StoreDoubleChip.Inputs F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter
    memory_access := cols.memory_access }

def storeDoubleChipLocals {F : Type}
    (cols : StoreDoubleChip.Columns F) : Vector F 4 :=
  #v[cols.address_operation.addr_operation.value[0],
    cols.address_operation.addr_operation.value[1],
    cols.address_operation.addr_operation.value[2],
    cols.address_operation.top_two_limb_inv]

def storeDoubleChipPhysicalRow {F : Type}
    (cols : StoreDoubleChip.Columns F) : Array F :=
  inputFirstRow (storeDoubleChipInput cols) (storeDoubleChipLocals cols)

def storeDoubleChipColumnsOfInput {F : Type}
    (input : StoreDoubleChip.Inputs F) (locals : Vector F 4) :
    StoreDoubleChip.Columns F :=
  ⟨input.state, input.adapter,
    ⟨⟨#v[locals[0], locals[1], locals[2]]⟩, locals[3]⟩,
    input.memory_access, input.is_real⟩

private theorem storeDoubleVec3Eta {F : Type} (value : Vector F 3) :
    #v[value[0], value[1], value[2]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeDoubleVec4Eta {F : Type} (value : Vector F 4) :
    #v[value[0], value[1], value[2], value[3]] = value := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem storeDoubleEvalVec4Components
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

private theorem storeDoubleAddressEta {F : Type}
    (cols : Extracted.AddressOperation F) :
    ({ addr_operation := { value := cols.addr_operation.value }
       top_two_limb_inv := cols.top_two_limb_inv } :
      Extracted.AddressOperation F) = cols := by
  cases cols with
  | mk addr top =>
    cases addr
    rfl

private theorem storeDoubleCpuEta {F : Type}
    (cols : Extracted.CPUState F) :
    ({ clk_high := cols.clk_high
       clk_16_24 := cols.clk_16_24
       clk_0_16 := cols.clk_0_16
       pc := cols.pc } : Extracted.CPUState F) = cols := by
  cases cols
  rfl

private theorem storeDoubleITypeEta {F : Type}
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

theorem storeDoubleChipColumnsOfInput_roundtrip {F : Type}
    (cols : StoreDoubleChip.Columns F) :
    storeDoubleChipColumnsOfInput
        (storeDoubleChipInput cols) (storeDoubleChipLocals cols) = cols := by
  cases cols
  simp [storeDoubleChipColumnsOfInput, storeDoubleChipInput,
    storeDoubleChipLocals, storeDoubleVec3Eta]

@[circuit_norm] private theorem storeDoubleEvalAddress
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddressOperation (Expression F)) :
    Eval.eval env cols =
      ({ addr_operation := Eval.eval env cols.addr_operation
         top_two_limb_inv := Eval.eval env cols.top_two_limb_inv } :
        Extracted.AddressOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeDoubleEvalAddrAdd
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.AddrAddOperation (Expression F)) :
    Eval.eval env cols =
      ({ value := Eval.eval env cols.value } :
        Extracted.AddrAddOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] private theorem storeDoubleEvalAddrAddInput
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

@[circuit_norm] private theorem storeDoubleEvalAddressInput
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

@[circuit_norm] private theorem storeDoubleEvalMemoryInput
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

@[circuit_norm] private theorem storeDoubleEvalMemoryTimestamp
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

@[circuit_norm] private theorem storeDoubleEvalMemoryCols
    {F : Type} [FiniteField F] (env : Environment F)
    (cols : Extracted.MemoryAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.MemoryAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem evalStoreDoubleDirectOutput
    (input : StoreDoubleChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 4) (data : ProverData (ZMod p)) :
    ProvableType.eval (Environment.fromArray (inputFirstRow input locals) data)
        ((StoreDoubleChip.elaborated (p := p)).output
          (varFromOffset StoreDoubleChip.Inputs 0)
          (size StoreDoubleChip.Inputs)) =
      storeDoubleChipColumnsOfInput input locals := by
  rw [StoreDoubleChip.directOutput_eq]
  rw [← CircuitType.eval_expression, StoreDoubleChip.eval_columns]
  unfold storeDoubleChipColumnsOfInput
  rw [StoreDoubleChip.Columns.mk.injEq]
  dsimp only
  have hinputEval := eval_inputFirstRow input locals data
  rw [StoreDoubleChip.eval_inputs, StoreDoubleChip.Inputs.mk.injEq] at hinputEval
  refine ⟨hinputEval.2.1, hinputEval.2.2.1, ?_, hinputEval.2.2.2, hinputEval.1⟩
  rw [storeDoubleEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeDoubleEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    change
      (Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (Vector.mapRange 3 fun i =>
          var { index := size StoreDoubleChip.Inputs + i }))[i] =
        #v[locals[0], locals[1], locals[2]][i]
    rw [← ProvableType.getElem_eval_fields
      (Environment.fromArray (inputFirstRow input locals) data)
      (Vector.mapRange 3 fun i =>
        var { index := size StoreDoubleChip.Inputs + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i
    · exact eval_local_inputFirstRow input locals data 0 (by decide)
    · exact eval_local_inputFirstRow input locals data 1 (by decide)
    · exact eval_local_inputFirstRow input locals data 2 (by decide)
  · exact (ProvableType.eval_field
      (Environment.fromArray (inputFirstRow input locals) data)
      (var { index := size StoreDoubleChip.Inputs + 3 })).trans
        (eval_local_inputFirstRow input locals data 3 (by decide))

def storeDoubleChipRowCodec :
    ChipRowCodec StoreDoubleChip.Inputs StoreDoubleChip.Columns
      (StoreDoubleChip.circuit (p := p)) where
  assignment cols data := {
    row := storeDoubleChipPhysicalRow cols
    input := storeDoubleChipInput cols
    width_eq := by
      rw [storeDoubleChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, StoreDoubleChip.circuit_size_eq]
    rowInput_eq := rowInput_inputFirstRow (StoreDoubleChip.circuit (p := p))
        (storeDoubleChipInput cols) (storeDoubleChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((StoreDoubleChip.main _).output _) = _
      rw [StoreDoubleChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact (evalStoreDoubleDirectOutput (p := p)
        (storeDoubleChipInput cols) (storeDoubleChipLocals cols) data).trans
          (storeDoubleChipColumnsOfInput_roundtrip cols) }

theorem storeDoubleChipLookupsEmpty :
    (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    StoreDoubleChip.circuit_main_eq]
  simp [StoreDoubleChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, AddressOperation.circuit, AddressOperation.main,
    AddrAddOperation.circuit, AddrAddOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, Gadgets.Equality.main, circuit_norm]

private def storeDoubleAddressCols (offset : ℕ) :
    Extracted.AddressOperation (Expression (ZMod p)) :=
  ⟨⟨Vector.mapRange 3 fun i => var { index := offset + i }⟩,
    var { index := offset + 3 }⟩

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleEvalAddressCols
    (env : Environment (ZMod p)) (offset : ℕ) :
    Eval.eval env (storeDoubleAddressCols (p := p) offset) =
      ({ addr_operation :=
          { value := #v[env.get offset, env.get (offset + 1),
            env.get (offset + 2)] }
         top_two_limb_inv := env.get (offset + 3) } :
        Extracted.AddressOperation (ZMod p)) := by
  simp only [storeDoubleAddressCols]
  rw [storeDoubleEvalAddress, Extracted.AddressOperation.mk.injEq]
  constructor
  · rw [storeDoubleEvalAddrAdd, Extracted.AddrAddOperation.mk.injEq]
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_fields env
      (Vector.mapRange 3 fun i => var { index := offset + i }) i hi]
    rw [Vector.getElem_mapRange]
    interval_cases i <;> rfl
  · simp only [ProvableType.eval_field, Expression.eval]

private def storeDoubleAddressInput
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    Var AddressOperation.Inputs (ZMod p) :=
  ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩

private def storeDoubleAddressValue
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    Vector (Expression (ZMod p)) 3 :=
  AddressOperation.alignedValue
    (storeDoubleAddressInput input) (storeDoubleAddressCols offset)

private def storeDoubleCpuInput
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    Var Readers.CPUState.Inputs (ZMod p) :=
  ⟨input.state,
    #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
    8, input.is_real⟩

private def storeDoubleMemoryInput
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    Var Readers.MemoryAccess.Inputs (ZMod p) :=
  ⟨input.memory_access, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    (storeDoubleAddressValue input offset)[0],
    (storeDoubleAddressValue input offset)[1],
    (storeDoubleAddressValue input offset)[2],
    input.adapter.op_a_memory.prev_value, input.is_real⟩

private def storeDoubleITypeInput
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    Var Readers.ITypeReaderImmutable.Inputs (ZMod p) :=
  ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
    input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.state.pc, 39⟩

private theorem storeDoubleNativeConstraintsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreDoubleChip.main input).operations offset)) ↔
      List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.CPUState.main
              (storeDoubleCpuInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((AddressOperation.main
              (storeDoubleAddressInput input)).operations offset)) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.MemoryAccess.main
              (storeDoubleMemoryInput input offset)).operations (offset + 4))) ∧
        List.Forall (· = 0)
          (nativeAssertZeros env
            ((Readers.ITypeReaderImmutable.main
              (storeDoubleITypeInput input)).operations (offset + 4))) ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  simp only [nativeAssertZeros, StoreDoubleChip.main,
    storeDoubleCpuInput, storeDoubleAddressInput, storeDoubleAddressCols,
    storeDoubleAddressValue, storeDoubleMemoryInput, storeDoubleITypeInput,
    Readers.CPUState.circuit, AddressOperation.circuit,
    Readers.MemoryAccess.circuit, Readers.ITypeReaderImmutable.circuit,
    circuit_norm, List.map_append, List.forall_append]

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleAddrAddAssertions
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
    storeDoubleEvalAddrAddInput, storeDoubleEvalAddrAdd,
    ProvableType.eval_field, ProvableType.getElem_eval_fields]
  simp only [List.singleton_append, List.Forall]

private theorem storeDoubleAddressAssertions
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
  let cols := storeDoubleAddressCols (p := p) offset
  let addrAddInput : Var AddrAddOperation.Inputs (ZMod p) :=
    ⟨input.b, input.cc, cols.addr_operation, input.is_real⟩
  have hAddrAdd := storeDoubleAddrAddAssertions (p := p) env addrAddInput
    (offset + 3)
  rw [Extracted.AddressOperation.asserts]
  simp only [nativeAssertZeros, AddressOperation.main,
    AddrAddOperation.circuit, circuit_norm, List.map_append,
    List.forall_append, List.Forall]
  simp only [addrAddInput, cols, storeDoubleAddressCols] at hAddrAdd
  simp only [← ProvableStruct.eval_eq_eval,
    storeDoubleEvalAddressInput, ProvableType.eval_field,
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

private def storeDoubleITypeImmutableAssertionValues
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

private theorem storeDoubleITypeImmutableAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.ITypeReaderImmutable.main input).operations offset)) =
      storeDoubleITypeImmutableAssertionValues env input := by
  simp only [Readers.ITypeReaderImmutable.main, circuit_norm]
  simp only [Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, circuit_norm,
    constraints_formalAssertion_toSubcircuit]
  simp only [List.map_append, List.map_cons]
  simp only [CanonicalReader.registerAccessTimestampAssertions]
  repeat' rw [CanonicalReader.equalityAssertionList]
  rfl

private theorem storeDoubleITypeImmutableAssertions
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
        storeDoubleITypeImmutableAssertionValues env input by
    exact storeDoubleITypeImmutableAssertionList env input offset]
  simp only [Extracted.ITypeReaderImmutable.asserts,
    storeDoubleITypeImmutableAssertionValues, List.Forall]
  simp only [Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, ProvableType.eval_field,
    ← ProvableType.getElem_eval_fields,
    eval_sub, Expression.eval, sub_zero]
  rw [htrust]
  tauto

private def storeDoubleMemoryAssertionValues
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
private theorem storeDoubleMemoryAssertionList
    (env : Environment (ZMod p))
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (offset : ℕ) :
    List.map (Expression.eval env)
        (Operations.constraints
          ((Readers.MemoryAccess.main input).operations offset)) =
      storeDoubleMemoryAssertionValues env input := by
  simp only [Readers.MemoryAccess.main, circuit_norm]
  simp only [List.map_append]
  repeat' rw [CanonicalReader.equalityAssertionList]
  simp only [storeDoubleMemoryAssertionValues,
    List.singleton_append]
  rw [← ProvableStruct.eval_eq_eval, storeDoubleEvalMemoryInput]
  simp only [ProvableType.eval_field, eval_sub, Expression.eval]

private def storeDoubleChipRustColumns
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    StoreDoubleChip.Columns (ZMod p) :=
  { state := Eval.eval env input.state
    adapter := Eval.eval env input.adapter
    address_operation := Eval.eval env (storeDoubleAddressCols (p := p) offset)
    memory_access := Eval.eval env input.memory_access
    is_real := Expression.eval env input.is_real }

private def storeDoubleNativeCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.CPUState.main
        (storeDoubleCpuInput input)).operations offset))

private def storeDoubleNativeAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((AddressOperation.main
        (storeDoubleAddressInput input)).operations offset))

private def storeDoubleNativeMemoryMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (storeDoubleMemoryAssertionValues env
      (storeDoubleMemoryInput input offset))

private def storeDoubleNativeITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  List.Forall (· = 0)
    (nativeAssertZeros env
      ((Readers.ITypeReaderImmutable.main
        (storeDoubleITypeInput input)).operations (offset + 4)))

private def storeDoubleNativeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeDoubleNativeCpuMeaning env input offset ∧
    storeDoubleNativeAddressMeaning env input offset ∧
    storeDoubleNativeMemoryMeaning env input offset ∧
    storeDoubleNativeITypeMeaning env input offset ∧
    Expression.eval env (input.is_real * (input.is_real - 1)) = 0

private def storeDoubleRustAddressMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeDoubleChipRustColumns env input offset
  List.Forall (fun x : ZMod p => x = 0)
    (Extracted.AddressOperation.asserts
      #v[cols.adapter.op_b_memory.prev_value[0],
        cols.adapter.op_b_memory.prev_value[1],
        cols.adapter.op_b_memory.prev_value[2],
        cols.adapter.op_b_memory.prev_value[3]]
      #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
        cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
      (0 : ZMod p) (0 : ZMod p) (0 : ZMod p)
      cols.is_real
      { addr_operation :=
          { value := cols.address_operation.addr_operation.value }
        top_two_limb_inv := cols.address_operation.top_two_limb_inv })

private def storeDoubleRustCpuMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeDoubleChipRustColumns env input offset
  List.Forall (· = 0)
    (Extracted.CPUState.asserts
      { clk_high := cols.state.clk_high
        clk_16_24 := cols.state.clk_16_24
        clk_0_16 := cols.state.clk_0_16
        pc := cols.state.pc }
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]]
      8 cols.is_real)

private def storeDoubleRustITypeMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeDoubleChipRustColumns env input offset
  let clkLow := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  List.Forall (· = 0)
    (Extracted.ITypeReaderImmutable.asserts cols.state.clk_high clkLow
      cols.state.pc 39
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

private def storeDoubleRustTailMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  let cols := storeDoubleChipRustColumns env input offset
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
          (ts.diff_low_limb + ts.diff_high_limb * 65536)) ]

private def storeDoubleRustMeaning
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) : Prop :=
  storeDoubleRustAddressMeaning env input offset ∧
    storeDoubleRustCpuMeaning env input offset ∧
    storeDoubleRustITypeMeaning env input offset ∧
    storeDoubleRustTailMeaning env input offset

private theorem storeDoubleNativeAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreDoubleChip.main input).operations offset)) ↔
      storeDoubleNativeMeaning env input offset := by
  rw [storeDoubleNativeConstraintsDecompose]
  rw [show nativeAssertZeros env
      ((Readers.MemoryAccess.main
        (storeDoubleMemoryInput input offset)).operations (offset + 4)) =
        storeDoubleMemoryAssertionValues env
          (storeDoubleMemoryInput input offset) by
    exact storeDoubleMemoryAssertionList env
      (storeDoubleMemoryInput input offset) (offset + 4)]
  rfl

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleRustAssertionsDecompose
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeDoubleChipOracle.nativeAssertZeros
          (storeDoubleChipRustColumns env input offset)) ↔
      storeDoubleRustMeaning env input offset := by
  simp only [ChipOracle.nativeAssertZeros, storeDoubleChipOracle]
  rw [Extracted.StoreDoubleOracle.StoreDoubleColumns.asserts]
  dsimp only [storeDoubleChipReconfigure, storeDoubleOracleAddressOperation]
  simp only [storeDoubleOracle_address_asserts_eq]
  unfold storeDoubleRustMeaning storeDoubleRustAddressMeaning
    storeDoubleRustCpuMeaning storeDoubleRustITypeMeaning
    storeDoubleRustTailMeaning
  simp only [List.forall_append, storeDoubleVec3Eta, storeDoubleVec4Eta]
  tauto

private theorem storeDoubleAddressMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    storeDoubleRustAddressMeaning env input offset ↔
      storeDoubleNativeAddressMeaning env input offset := by
  have hAddress := storeDoubleAddressAssertions (p := p) env
    (storeDoubleAddressInput input) offset
  unfold storeDoubleRustAddressMeaning storeDoubleNativeAddressMeaning
  dsimp only [storeDoubleChipRustColumns]
  rw [storeDoubleEvalAddressCols]
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
    exact storeDoubleEvalVec4Components env
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
    exact storeDoubleEvalVec4Components env input.adapter.op_c_imm
  rw [hb, hc]
  simp only [storeDoubleAddressInput] at hAddress
  exact hAddress

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleCpuMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    storeDoubleRustCpuMeaning env input offset ↔
      storeDoubleNativeCpuMeaning env input offset := by
  let cpu := storeDoubleCpuInput input
  have hCpu := CanonicalReader.cpuStateAssertions
    (p := p) env cpu offset
    (Eval.eval env input.state)
    #v[Expression.eval env (input.state.pc[0] + 4),
      Expression.eval env input.state.pc[1],
      Expression.eval env input.state.pc[2]]
    8 (Expression.eval env input.is_real) (by
      simp only [cpu, storeDoubleCpuInput,
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
  unfold storeDoubleRustCpuMeaning storeDoubleNativeCpuMeaning
  dsimp only [storeDoubleChipRustColumns]
  rw [hNext]
  simp only [cpu, storeDoubleCpuInput] at hCpu
  exact hCpu

private theorem storeDoubleITypeMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    storeDoubleRustITypeMeaning env input offset ↔
      storeDoubleNativeITypeMeaning env input offset := by
  have hIType := storeDoubleITypeImmutableAssertions (p := p) env
    (storeDoubleITypeInput input) (offset + 4) (by
      simp only [storeDoubleITypeInput])
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
  unfold storeDoubleRustITypeMeaning storeDoubleNativeITypeMeaning
  dsimp only [storeDoubleChipRustColumns]
  rw [hHigh, hLow, hPc]
  simp only [storeDoubleITypeInput] at hIType
  exact hIType

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleTailMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    storeDoubleRustTailMeaning env input offset ↔
      storeDoubleNativeMemoryMeaning env input offset ∧
        Expression.eval env
          (input.is_real * (input.is_real - 1)) = 0 := by
  unfold storeDoubleRustTailMeaning storeDoubleNativeMemoryMeaning
  dsimp only [storeDoubleChipRustColumns]
  simp only [storeDoubleMemoryAssertionValues, storeDoubleMemoryInput,
    List.Forall, eval_cpuState, storeDoubleEvalMemoryCols,
    storeDoubleEvalMemoryTimestamp,
    ProvableType.eval_field, eval_sub,
    Expression.eval, sub_zero]
  tauto

private theorem storeDoubleChipMeaningFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    storeDoubleRustMeaning env input offset ↔
      storeDoubleNativeMeaning env input offset := by
  unfold storeDoubleRustMeaning storeDoubleNativeMeaning
  rw [storeDoubleAddressMeaningFaithful, storeDoubleCpuMeaningFaithful,
    storeDoubleITypeMeaningFaithful, storeDoubleTailMeaningFaithful]
  tauto

private theorem storeDoubleChipConstraintsFaithfulOutput
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (storeDoubleChipOracle.nativeAssertZeros
          (storeDoubleChipRustColumns env input offset)) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreDoubleChip.main input).operations offset)) :=
  (storeDoubleRustAssertionsDecompose (p := p) env input offset).trans
    ((storeDoubleChipMeaningFaithful (p := p) env input offset).trans
      (storeDoubleNativeAssertionsDecompose (p := p) env input offset).symm)

theorem storeDoubleChipConstraintsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreDoubleChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreDoubleChip.main env input offset cols) :
    List.Forall (· = 0)
        (storeDoubleChipOracle.nativeAssertZeros cols) ↔
      List.Forall (· = 0)
        (nativeAssertZeros env
          ((StoreDoubleChip.main input).operations offset)) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreDoubleChip.elaborated (p := p)) hbind
  rw [StoreDoubleChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreDoubleChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeDoubleChipRustColumns env input offset = cols at hbind
  rw [← hbind]
  exact storeDoubleChipConstraintsFaithfulOutput
    (p := p) env input offset

theorem storeDoubleChipConstraintsConstructive
    (rustCols : Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeDoubleChipRowCodec.assignment
      (storeDoubleChipOracle.deconfigure rustCols) data
    List.Forall (· = 0)
        (storeDoubleChipOracle.assertZeros rustCols) ↔
      (⟨StoreDoubleChip.circuit (p := p)⟩ :
        Air.Flat.Component (ZMod p)).operations.ConstraintsHold
          assignment.environment := by
  dsimp only
  let cols := storeDoubleChipOracle.deconfigure rustCols
  let assignment := storeDoubleChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreDoubleChip.main assignment.environment
        (⟨StoreDoubleChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreDoubleChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreDoubleChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeDoubleChipConstraintsFaithful
    (p := p) assignment.environment
    (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  have hassertions :
      List.Forall (· = 0)
          (storeDoubleChipOracle.assertZeros rustCols) ↔
        List.Forall (· = 0)
          (nativeAssertZeros assignment.environment
            (⟨StoreDoubleChip.circuit (p := p)⟩ :
              Air.Flat.Component (ZMod p)).rowOperations) := by
    simpa only [cols,
      ChipOracle.nativeAssertZeros_deconfigure,
      Air.Flat.Component.rowOperations_mk,
      Air.Flat.Component.rowInputVar_mk,
      Air.Flat.Component.rowOffset_mk,
      StoreDoubleChip.circuit_main_eq] using hfaithful
  exact hassertions.trans
    (constraintsHold_iff_nativeAssertZeros
      (StoreDoubleChip.circuit (p := p))
      assignment.environment storeDoubleChipLookupsEmpty).symm

open SP1Clean.Channels
  (stateChannel byteChannel memoryChannel programChannel)
open InteractionRecovery

private def storeDoubleStateInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

private def storeDoubleProgramInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 39,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

private theorem storeDoubleStateInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreDoubleChip.main input).operations offset).interactionsWith
        stateChannel.toRaw =
      (storeDoubleStateInteractions input).map ChannelInteraction.toRaw :=
  (StoreDoubleChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨stateChannel.toRaw,
      (storeDoubleStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreDoubleChip.circuit, storeDoubleStateInteractions, expose])

private theorem storeDoubleProgramInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreDoubleChip.main input).operations offset).interactionsWith
        programChannel.toRaw =
      (storeDoubleProgramInteractions input).map ChannelInteraction.toRaw :=
  (StoreDoubleChip.circuit (p := p)).interactionsWith_eq_of_mem_exposedChannels
    input offset
    ⟨programChannel.toRaw,
      (storeDoubleProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [StoreDoubleChip.circuit, storeDoubleProgramInteractions, expose])

private theorem storeDoubleStateInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((((storeDoubleStateInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env))) =
      (((Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions
          (storeDoubleChipReconfigure
            (storeDoubleChipRustColumns env input offset))).map
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
  simp only [storeDoubleStateInteractions,
    List.map_cons, List.map_nil, hStatePull, hStatePush]
  simp [Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions,
    storeDoubleChipReconfigure, storeDoubleOracleAddressOperation,
    Extracted.StoreDoubleOracle.AddressOperation.interactions,
    Extracted.StoreDoubleOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeDoubleChipRustColumns, storeDoubleEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]

private theorem storeDoubleProgramInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    (((((storeDoubleProgramInteractions input).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult)) =
      (((Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions
          (storeDoubleChipReconfigure
            (storeDoubleChipRustColumns env input offset))).map
            Extracted.Interaction.toAccess).filter
        (fun access => access.1 = InteractionKind.Program)) := by
  have hp2 : 2 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have h39 : (39 : ZMod p).val = 39 := by
    have hp : 2 ^ 17 < p := Fact.out
    have hsmall : (39 : ℕ) < 2 ^ 17 := by norm_num
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
  simp only [storeDoubleProgramInteractions,
    List.map_cons, List.map_nil, hProgramPull]
  simp [Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions,
    storeDoubleChipReconfigure, storeDoubleOracleAddressOperation,
    Extracted.StoreDoubleOracle.AddressOperation.interactions,
    Extracted.StoreDoubleOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    storeDoubleChipRustColumns, storeDoubleEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    Expression.eval, LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign, Opcode.ofNat, h39]

private theorem storeDoubleMemoryInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      (((((StoreDoubleChip.exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw).map
          (AbstractInteraction.toAccess env)).map
            LookupAccessList.negMult))
      (((Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions
          (storeDoubleChipReconfigure
            (storeDoubleChipRustColumns env input offset))).map
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
  simp only [StoreDoubleChip.exposedMemoryInteractions,
    List.map_cons, List.map_nil, hMemoryPull, hMemoryPush]
  simp [Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions,
    storeDoubleChipReconfigure, storeDoubleOracleAddressOperation,
    Extracted.StoreDoubleOracle.AddressOperation.interactions,
    Extracted.StoreDoubleOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreDoubleOracle.AddressOperation.value,
    storeDoubleChipRustColumns, storeDoubleEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeDoubleEvalMemoryCols, storeDoubleEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    LookupAccessList.negMult,
    signedVal_neg hp2, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  exact List.perm_append_comm
    (l₁ := [_, _]) (l₂ := [_, _, _, _])

private def storeDoubleCpuByteInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩ ]

private def storeDoubleAddressByteInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
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
          (4 : Expression (ZMod p)) * 0 -
          (2 : Expression (ZMod p)) * 0 - 0) *
        (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ ]

private def storeDoubleMemoryByteInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  [ byteChannel.pulledIf input.is_real
      ⟨6, input.memory_access.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.memory_access.access_timestamp.diff_high_limb, 0⟩ ]

private def storeDoubleITypeByteInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) :
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

private def storeDoubleByteInteractions
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  storeDoubleCpuByteInteractions input ++
    storeDoubleAddressByteInteractions input offset ++
    storeDoubleMemoryByteInteractions input ++
    storeDoubleITypeByteInteractions input

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleCpuByteInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main
        (storeDoubleCpuInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeDoubleCpuByteInteractions input).map ChannelInteraction.toRaw := by
  simp [storeDoubleCpuInput, storeDoubleCpuByteInteractions,
    Readers.CPUState.main, Operations.interactionsWith, circuit_norm]

private theorem storeDoubleAddressByteInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((AddressOperation.main
        (storeDoubleAddressInput input)).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeDoubleAddressByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  simp [storeDoubleAddressInput, storeDoubleAddressByteInteractions,
    AddressOperation.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Operations.interactionsWith,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem storeDoubleMemoryByteInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.MemoryAccess.main
        (storeDoubleMemoryInput input offset)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeDoubleMemoryByteInteractions input).map
        ChannelInteraction.toRaw := by
  have heq := fun (n : ℕ)
      (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp [storeDoubleMemoryInput, storeDoubleMemoryByteInteractions,
    Readers.MemoryAccess.main, Operations.interactionsWith,
    circuit_norm, heq]

private theorem storeDoubleITypeByteInteractionsEq
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.main
        (storeDoubleITypeInput input)).operations
          (offset + 4)).interactionsWith byteChannel.toRaw =
      (storeDoubleITypeByteInteractions input).map
        ChannelInteraction.toRaw := by
  simp [storeDoubleITypeInput, storeDoubleITypeByteInteractions,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Operations.interactionsWith, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem storeDoubleByteInteractionsDecompose
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    ((StoreDoubleChip.main input).operations offset).interactionsWith
        byteChannel.toRaw =
      (storeDoubleByteInteractions input offset).map
        ChannelInteraction.toRaw := by
  rw [show
      ((StoreDoubleChip.main input).operations offset).interactionsWith
          byteChannel.toRaw =
        ((Readers.CPUState.main
            (storeDoubleCpuInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((AddressOperation.main
            (storeDoubleAddressInput input)).operations offset).interactionsWith
            byteChannel.toRaw ++
        ((Readers.MemoryAccess.main
            (storeDoubleMemoryInput input offset)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw ++
        ((Readers.ITypeReaderImmutable.main
            (storeDoubleITypeInput input)).operations
              (offset + 4)).interactionsWith byteChannel.toRaw by
  simp [StoreDoubleChip.main, storeDoubleCpuInput, storeDoubleAddressInput,
    storeDoubleMemoryInput, storeDoubleAddressValue, storeDoubleAddressCols,
    storeDoubleITypeInput, Readers.CPUState.circuit,
    AddressOperation.circuit, Readers.MemoryAccess.circuit,
    Readers.ITypeReaderImmutable.circuit, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Operations.interactionsWith]]
  rw [storeDoubleCpuByteInteractionsEq,
    storeDoubleAddressByteInteractionsEq,
    storeDoubleMemoryByteInteractionsEq,
    storeDoubleITypeByteInteractionsEq]
  simp only [storeDoubleByteInteractions, List.map_append]

private theorem storeDoublePermFourBlocks {α : Type}
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

private theorem storeDoubleByteInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((StoreDoubleChip.main input).operations offset).interactionsWith
          byteChannel.toRaw).map
            (AbstractInteraction.toAccess env))
      (((Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions
          (storeDoubleChipReconfigure
            (storeDoubleChipRustColumns env input offset))).map
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
  rw [storeDoubleByteInteractionsDecompose]
  simp only [storeDoubleByteInteractions, List.map_append]
  simp only [storeDoubleCpuByteInteractions,
    storeDoubleAddressByteInteractions, storeDoubleMemoryByteInteractions,
    storeDoubleITypeByteInteractions, List.map_cons, List.map_nil,
    hBytePull]
  simp [Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions,
    storeDoubleChipReconfigure, storeDoubleOracleAddressOperation,
    Extracted.StoreDoubleOracle.AddressOperation.interactions,
    Extracted.StoreDoubleOracle.AddrAddOperation.interactions,
    Extracted.CPUState.interactions,
    Extracted.ITypeReaderImmutable.interactions,
    Extracted.StoreDoubleOracle.AddressOperation.value,
    storeDoubleChipRustColumns, storeDoubleEvalAddressCols,
    eval_cpuState, Readers.ITypeReader.eval_cols,
    eval_registerAccessCols, eval_registerAccessTimestamp,
    storeDoubleEvalMemoryCols, storeDoubleEvalMemoryTimestamp,
    ← ProvableType.getElem_eval_fields, ProvableType.eval_field,
    eval_sub, Expression.eval, mul_zero, sub_zero,
    h6, h3, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  simp only [← ProvableStruct.eval_eq_eval,
    StoreDoubleChip.eval_inputs, eval_cpuState,
    Readers.ITypeReader.eval_cols, eval_registerAccessCols,
    eval_registerAccessTimestamp, storeDoubleEvalMemoryCols,
    storeDoubleEvalMemoryTimestamp, ProvableType.eval_field]
  exact storeDoublePermFourBlocks
    [_, _] [_, _, _, _] [_, _] [_, _, _, _]

private theorem storeDoubleUnexpectedInteractionsEmpty
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ) :
    unexpectedInteractions
        ((StoreDoubleChip.main input).operations offset) = [] := by
  unfold unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction hmem hunexpected
  have hchannel :
      interaction.channel ∈
        ((StoreDoubleChip.main input).operations offset).channels := by
    rw [Operations.channels]
    exact List.mem_map.mpr ⟨interaction, hmem, rfl⟩
  have hknown :=
    (StoreDoubleChip.circuit (p := p)).channels_subset
      input offset hchannel
  simp only [StoreDoubleChip.circuit,
    FormalCircuitBase.channelsWithGuarantees_def,
    FormalCircuitBase.channelsWithRequirements_def,
    circuit_norm] at hknown
  simp only [decide_eq_true_eq] at hunexpected
  tauto

theorem storeDoubleChipInteractionsFaithful
    (env : Environment (ZMod p))
    (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ)
    (cols : StoreDoubleChip.Columns (ZMod p))
    (hbind : BindsChipOutput StoreDoubleChip.main env input offset cols) :
    List.Perm
      (nativeAccesses env
        ((StoreDoubleChip.main input).operations offset))
      (storeDoubleChipOracle.accesses cols) := by
  replace hbind := BindsChipOutput.ofElaborated
    (StoreDoubleChip.elaborated (p := p)) hbind
  rw [StoreDoubleChip.directOutput_eq] at hbind
  rw [← ProvableStruct.eval_eq_eval,
    StoreDoubleChip.eval_columns] at hbind
  simp only [ProvableType.eval_field] at hbind
  change storeDoubleChipRustColumns env input offset = cols at hbind
  subst cols
  let rustAccesses :=
    (Extracted.StoreDoubleOracle.StoreDoubleColumns.interactions
      (storeDoubleChipReconfigure
        (storeDoubleChipRustColumns env input offset))).map
        Extracted.Interaction.toAccess
  simp only [nativeAccesses]
  rw [storeDoubleUnexpectedInteractionsEmpty]
  simp only [List.map_nil, List.append_nil]
  simp only [ChipOracle.accesses,
    ChipOracle.nativeInteractions, storeDoubleChipOracle]
  rw [storeDoubleStateInteractionsEq,
    StoreDoubleChip.interactionsWith_memory_eq,
    storeDoubleProgramInteractionsEq]
  have hState :=
    storeDoubleStateInteractionsFaithful (p := p) env input offset
  have hByte :=
    storeDoubleByteInteractionsFaithful (p := p) env input offset
  have hMemory :=
    storeDoubleMemoryInteractionsFaithful (p := p) env input offset
  have hProgram :=
    storeDoubleProgramInteractionsFaithful (p := p) env input offset
  refine List.Perm.trans ?_
    (LookupAccessList.perm_filter_by_kind_of_exit_nil rustAccesses
      (Extracted.map_toAccess_exit_filter _)).symm
  dsimp only [rustAccesses] at hState hByte hMemory hProgram ⊢
  rw [hState, hProgram]
  simpa only [List.append_assoc] using
    ((hByte.append_left _).append hMemory).append_right _

theorem storeDoubleChipInteractionsConstructive
    (rustCols : Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p))
    (data : ProverData (ZMod p)) :
    let assignment := storeDoubleChipRowCodec.assignment
      (storeDoubleChipOracle.deconfigure rustCols) data
    List.Perm
      (nativeAccesses assignment.environment
        (⟨StoreDoubleChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).operations)
      (storeDoubleChipOracle.rustAccesses rustCols) := by
  dsimp only
  let cols := storeDoubleChipOracle.deconfigure rustCols
  let assignment := storeDoubleChipRowCodec.assignment cols data
  have hbind :
      BindsChipOutput StoreDoubleChip.main assignment.environment
        (⟨StoreDoubleChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowInputVar
        (⟨StoreDoubleChip.circuit (p := p)⟩ :
          Air.Flat.Component (ZMod p)).rowOffset cols := by
    have h := NativeRowAssignment.bindsOutput assignment
    rw [StoreDoubleChip.circuit_main_eq] at h
    exact h
  have hfaithful := storeDoubleChipInteractionsFaithful
    (p := p) assignment.environment
    (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowInputVar
    (⟨StoreDoubleChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).rowOffset cols hbind
  rw [nativeAccesses_component_eq_rowOperations
    (StoreDoubleChip.circuit (p := p))
    assignment.environment]
  simpa only [cols, ChipOracle.accesses_deconfigure,
    Air.Flat.Component.rowOperations_mk,
    Air.Flat.Component.rowInputVar_mk,
    Air.Flat.Component.rowOffset_mk,
    StoreDoubleChip.circuit_main_eq] using hfaithful

theorem storeDoubleChip_faithful :
    ChipFaithful (p := p) StoreDoubleChip.Inputs
      StoreDoubleChip.Columns Extracted.StoreDoubleOracle.StoreDoubleColumns
      StoreDoubleChip.circuit storeDoubleChipRowCodec
      storeDoubleChipOracle where
  constraints := storeDoubleChipConstraintsConstructive (p := p)
  interactions := fun rustCols data _ =>
    LookupAccessList.active_perm
      (storeDoubleChipInteractionsConstructive (p := p) rustCols data)

end SP1Clean.Faithful
