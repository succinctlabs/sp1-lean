import SP1Clean.Composition.SystemTables
import SP1Clean.Extracted.InteractionModel

/-! # Semantic views of the simple Core system-table seams

The exact Core AIR adapter deliberately keeps generated rows flat.  This module is the small,
audited naming layer for the system-table facts that can be exposed without interpreting the large
Global accumulator:

* `StateBump` and `MemoryBump` already have native Clean circuits and whole-row codecs.  The first
  two theorems below expose the exact native input reconstructed by the table transport.
* `SyscallCore` and `SyscallInstrs` project the same Model-layer `SyscallMsg`; the exact lists prove
  the receive/send endpoints without introducing a second hand-written interaction ledger.
* `MemoryLocal` names every main column once, its two typed Memory endpoints, selector binarity, and
  the two asserted limb recombinations.

These are local row facts only.  In particular, the raw Syscall/Global payloads do not acquire a
semantic meaning merely by being named, and MemoryLocal's words and clocks do not acquire range
bounds merely from its four local assertions.  The generated oracle lists remain the sole complete
interaction ledgers; transcript consistency and Memory ordering remain trace-level obligations.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

open Air.Flat (Component)
open Circuit
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Native bump-row decoding -/

/-- The physical row installed by the exact `MemoryBump` transport decodes to the codec's native
semantic input. -/
theorem transportMemoryBumpRow_input
    (row : CoreAIR.Current.Row p .memoryBump) (data : ProverData (ZMod p)) :
    (⟨MemoryBumpChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray (transportMemoryBumpRow row) data) =
      Faithful.memoryBumpDeconfigure row.main := by
  exact Faithful.memoryBumpEnvironment_rowInput row.main data

/-- The physical row installed by the exact `StateBump` transport decodes to the codec's native
semantic input. -/
theorem transportStateBumpRow_input
    (row : CoreAIR.Current.Row p .stateBump) (data : ProverData (ZMod p)) :
    (⟨StateBumpChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        (Environment.fromArray (transportStateBumpRow row) data) =
      Faithful.stateBumpDeconfigure row.main := by
  exact Faithful.stateBumpEnvironment_rowInput row.main data

/-! ## SyscallCore -/

/-- All ten main columns of one exact `SyscallCore` row, grouped around the shared typed message. -/
structure SyscallCoreView (F : Type) where
  message : Channels.SyscallMsg F
  isReal : F

/-- Audited column projection for the pinned ten-column `SyscallCore` layout. -/
def syscallCoreView (row : CoreAIR.Current.Row p .syscallCore) :
    SyscallCoreView (ZMod p) where
  message :=
    { clk_high := row.main.values[0]
      clk_low := row.main.values[1]
      syscall_id := row.main.values[2]
      arg1 := #v[row.main.values[3], row.main.values[4], row.main.values[5]]
      arg2 := #v[row.main.values[6], row.main.values[7], row.main.values[8]] }
  isReal := row.main.values[9]

omit [Fact (2 ^ 17 < p)] in
/-- `SyscallCore`'s local selector assertion makes the view's activity flag boolean. -/
theorem syscallCore_isReal_bool
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .syscallCore)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .syscallCore row)) :
    (syscallCoreView row).isReal = 0 ∨ (syscallCoreView row).isReal = 1 := by
  apply bool_of_mul_pred
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[9] * (row.main.values[9] - 1) ∈
    Extracted.SyscallCoreCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.SyscallCoreCols.asserts]
  simp

omit [Fact (2 ^ 17 < p)] in
/-- Complete local assertion semantics for `SyscallCore`: its second generated assertion is an
algebraic identity, so the whole list holds exactly when the activity selector is boolean. -/
theorem syscallCore_assertions_iff
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .syscallCore) :
    List.Forall (· = 0) (CoreAIR.Current.assertions publicValues .syscallCore row) ↔
      (syscallCoreView row).isReal = 0 ∨ (syscallCoreView row).isReal = 1 := by
  constructor
  · exact syscallCore_isReal_bool publicValues row
  · intro active
    change row.main.values[9] = 0 ∨ row.main.values[9] = 1 at active
    change List.Forall (· = 0)
      (Extracted.SyscallCoreCols.asserts row.main row.preprocessed
        publicValues.toBaseVector)
    rw [Extracted.SyscallCoreCols.asserts]
    rcases active with inactive | active
    · simp [inactive]
    · simp [active]

omit [Fact (2 ^ 17 < p)] in
/-- The generated `SyscallCore` row receives exactly the typed message named by its view. -/
theorem syscallCore_syscall_receive_mem
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .syscallCore) :
    (⟨.receive,
        Extracted.AirInteraction.ofSyscallMsg (syscallCoreView row).message,
        (syscallCoreView row).isReal⟩ : Extracted.Interaction (ZMod p)) ∈
      CoreAIR.Current.interactions publicValues .syscallCore row := by
  rw [CoreAIR.Current.interactions, Extracted.SyscallCoreCols.interactions]
  simp [syscallCoreView, Extracted.AirInteraction.ofSyscallMsg,
    Channels.SyscallMsg.toElements_toList]

omit [Fact (2 ^ 17 < p)] in
/-- Exact execution-cluster validity fans the complete local SyscallCore contract out to every
physical row, without exposing the conjunction layout of `CoreAIR.System.relation`. -/
theorem syscallCore_rowFacts_of_relation {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness)
    (row : CoreAIR.Current.Row p .syscallCore)
    (rowMem : row ∈ witness.trace.rows .syscallCore) :
    (syscallCoreView row).isReal = 0 ∨ (syscallCoreView row).isReal = 1 := by
  apply (syscallCore_assertions_iff statement.publicValues row).mp
  exact (CoreAIR.Current.system binds).localValid_of_relationFor valid rowMem

/-! ## SyscallInstrs -/

/-- The exact helper output that decomposes the raw syscall-code word into bytes. -/
def syscallInstrsCodeBytes (row : CoreAIR.Current.Row p .syscallInstrs) : Vector (ZMod p) 8 :=
  Extracted.U16toU8OperationSafe.value
    #v[row.main.values[7], row.main.values[8], row.main.values[9], row.main.values[10]]
    { low_bytes :=
        #v[row.main.values[36], row.main.values[37], row.main.values[38], row.main.values[39]] }
    row.main.values[64]

/-- The narrow Syscall-bus projection of a 65-column `SyscallInstrs` row. Byte zero is the syscall
id; byte one is the Boolean `send_to_table` multiplicity used by upstream. -/
structure SyscallInstrsSyscallView (F : Type) where
  message : Channels.SyscallMsg F
  sendToTable : F

/-- Project precisely the fields consumed by upstream's `send_syscall` call. -/
def syscallInstrsSyscallView (row : CoreAIR.Current.Row p .syscallInstrs) :
    SyscallInstrsSyscallView (ZMod p) :=
  let codeBytes := syscallInstrsCodeBytes row
  { message :=
      { clk_high := row.main.values[0]
        clk_low := row.main.values[2] + row.main.values[1] * 65536
        syscall_id := codeBytes[0]
        arg1 := #v[row.main.values[15], row.main.values[16], row.main.values[17]]
        arg2 := #v[row.main.values[22], row.main.values[23], row.main.values[24]] }
    sendToTable := codeBytes[1] }

omit [Fact (2 ^ 17 < p)] in
/-- The generated instruction row sends exactly the same typed Syscall message carrier consumed by
`SyscallCore`, at its generated `send_to_table` multiplicity. -/
theorem syscallInstrs_syscall_send_mem
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .syscallInstrs) :
    (⟨.send,
        Extracted.AirInteraction.ofSyscallMsg (syscallInstrsSyscallView row).message,
        (syscallInstrsSyscallView row).sendToTable⟩ : Extracted.Interaction (ZMod p)) ∈
      CoreAIR.Current.interactions publicValues .syscallInstrs row := by
  rw [CoreAIR.Current.interactions, Extracted.SyscallInstrsCols.interactions]
  simp [syscallInstrsSyscallView, syscallInstrsCodeBytes,
    Extracted.AirInteraction.ofSyscallMsg, Channels.SyscallMsg.toElements_toList]

/-! ## MemoryLocal -/

/-- All twenty main columns of one exact `MemoryLocal` row, grouped into its initial/final records. -/
structure MemoryLocalView (F : Type) where
  addr : Vector F 3
  initialClkHigh : F
  finalClkHigh : F
  initialClkLow : F
  finalClkLow : F
  initialValue : Word F
  finalValue : Word F
  initialLimb2Bytes : Vector F 2
  finalLimb2Bytes : Vector F 2
  isReal : F

/-- Audited column projection for the pinned twenty-column `MemoryLocal` layout. -/
def memoryLocalView (row : CoreAIR.Current.Row p .memoryLocal) :
    MemoryLocalView (ZMod p) where
  addr := #v[row.main.values[0], row.main.values[1], row.main.values[2]]
  initialClkHigh := row.main.values[3]
  finalClkHigh := row.main.values[4]
  initialClkLow := row.main.values[5]
  finalClkLow := row.main.values[6]
  initialValue :=
    #v[row.main.values[7], row.main.values[8], row.main.values[9], row.main.values[10]]
  finalValue :=
    #v[row.main.values[11], row.main.values[12], row.main.values[13], row.main.values[14]]
  initialLimb2Bytes := #v[row.main.values[15], row.main.values[16]]
  finalLimb2Bytes := #v[row.main.values[17], row.main.values[18]]
  isReal := row.main.values[19]

/-- The initial typed Memory record named by a `MemoryLocal` row. -/
def MemoryLocalView.initialMessage (view : MemoryLocalView (ZMod p)) :
    Channels.MemoryMsg (ZMod p) :=
  ⟨view.initialClkHigh, view.initialClkLow, view.addr[0], view.addr[1], view.addr[2],
    view.initialValue⟩

/-- The final typed Memory record named by a `MemoryLocal` row. -/
def MemoryLocalView.finalMessage (view : MemoryLocalView (ZMod p)) :
    Channels.MemoryMsg (ZMod p) :=
  ⟨view.finalClkHigh, view.finalClkLow, view.addr[0], view.addr[1], view.addr[2],
    view.finalValue⟩

omit [Fact (2 ^ 17 < p)] in
/-- `MemoryLocal`'s local selector assertion makes the view's activity flag boolean. -/
theorem memoryLocal_isReal_bool
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryLocal)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .memoryLocal row)) :
    (memoryLocalView row).isReal = 0 ∨ (memoryLocalView row).isReal = 1 := by
  apply bool_of_mul_pred
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[19] * (row.main.values[19] - 1) ∈
    Extracted.MemoryLocalCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.MemoryLocalCols.asserts]
  simp

omit [Fact (2 ^ 17 < p)] in
/-- The initial value's third u16 limb is exactly the two-byte recombination asserted upstream. -/
theorem memoryLocal_initialLimb2
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryLocal)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .memoryLocal row)) :
    (memoryLocalView row).initialValue[2] =
      (memoryLocalView row).initialLimb2Bytes[0] +
        (memoryLocalView row).initialLimb2Bytes[1] * 256 := by
  apply sub_eq_zero.mp
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[9] - (row.main.values[15] + row.main.values[16] * 256) ∈
    Extracted.MemoryLocalCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.MemoryLocalCols.asserts]
  simp

omit [Fact (2 ^ 17 < p)] in
/-- The final value's third u16 limb is exactly the two-byte recombination asserted upstream. -/
theorem memoryLocal_finalLimb2
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryLocal)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .memoryLocal row)) :
    (memoryLocalView row).finalValue[2] =
      (memoryLocalView row).finalLimb2Bytes[0] +
        (memoryLocalView row).finalLimb2Bytes[1] * 256 := by
  apply sub_eq_zero.mp
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[13] - (row.main.values[17] + row.main.values[18] * 256) ∈
    Extracted.MemoryLocalCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.MemoryLocalCols.asserts]
  simp

omit [Fact (2 ^ 17 < p)] in
/-- Complete local assertion semantics for `MemoryLocal`. Its four generated assertions are
equivalent to selector binarity and the two named byte-recombination equations; no range, order, or
Global-bus meaning is smuggled into the row contract. -/
theorem memoryLocal_assertions_iff
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryLocal) :
    List.Forall (· = 0) (CoreAIR.Current.assertions publicValues .memoryLocal row) ↔
      ((memoryLocalView row).isReal = 0 ∨ (memoryLocalView row).isReal = 1) ∧
        (memoryLocalView row).initialValue[2] =
          (memoryLocalView row).initialLimb2Bytes[0] +
            (memoryLocalView row).initialLimb2Bytes[1] * 256 ∧
        (memoryLocalView row).finalValue[2] =
          (memoryLocalView row).finalLimb2Bytes[0] +
            (memoryLocalView row).finalLimb2Bytes[1] * 256 := by
  constructor
  · intro valid
    exact ⟨memoryLocal_isReal_bool publicValues row valid,
      memoryLocal_initialLimb2 publicValues row valid,
      memoryLocal_finalLimb2 publicValues row valid⟩
  · rintro ⟨active, initial, final⟩
    change row.main.values[19] = 0 ∨ row.main.values[19] = 1 at active
    change row.main.values[9] = row.main.values[15] + row.main.values[16] * 256 at initial
    change row.main.values[13] = row.main.values[17] + row.main.values[18] * 256 at final
    change List.Forall (· = 0)
      (Extracted.MemoryLocalCols.asserts row.main row.preprocessed
        publicValues.toBaseVector)
    rw [Extracted.MemoryLocalCols.asserts]
    rcases active with inactive | active
    · simp [inactive, initial, final]
    · simp [active, initial, final]

omit [Fact (2 ^ 17 < p)] in
/-- The generated row's two Memory-bus endpoints are exactly the typed initial/final messages named
by `MemoryLocalView`; the generated list remains the sole complete interaction ledger. -/
theorem memoryLocal_memory_endpoints_mem
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryLocal) :
    (⟨.receive,
        Extracted.AirInteraction.ofMemoryMsg (memoryLocalView row).initialMessage,
        (memoryLocalView row).isReal⟩ : Extracted.Interaction (ZMod p)) ∈
        CoreAIR.Current.interactions publicValues .memoryLocal row ∧
      (⟨.send,
        Extracted.AirInteraction.ofMemoryMsg (memoryLocalView row).finalMessage,
        (memoryLocalView row).isReal⟩ : Extracted.Interaction (ZMod p)) ∈
        CoreAIR.Current.interactions publicValues .memoryLocal row := by
  rw [CoreAIR.Current.interactions, Extracted.MemoryLocalCols.interactions]
  simp [memoryLocalView, MemoryLocalView.initialMessage, MemoryLocalView.finalMessage,
    Extracted.AirInteraction.ofMemoryMsg]

omit [Fact (2 ^ 17 < p)] in
/-- Exact execution-cluster validity supplies the complete local MemoryLocal row contract. -/
theorem memoryLocal_rowFacts_of_relation {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness)
    (row : CoreAIR.Current.Row p .memoryLocal)
    (rowMem : row ∈ witness.trace.rows .memoryLocal) :
    ((memoryLocalView row).isReal = 0 ∨ (memoryLocalView row).isReal = 1) ∧
      (memoryLocalView row).initialValue[2] =
        (memoryLocalView row).initialLimb2Bytes[0] +
          (memoryLocalView row).initialLimb2Bytes[1] * 256 ∧
      (memoryLocalView row).finalValue[2] =
        (memoryLocalView row).finalLimb2Bytes[0] +
          (memoryLocalView row).finalLimb2Bytes[1] * 256 := by
  apply (memoryLocal_assertions_iff statement.publicValues row).mp
  exact (CoreAIR.Current.system binds).localValid_of_relationFor valid rowMem

end SP1Clean.Composition
