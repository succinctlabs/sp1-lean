import SP1Clean.Extracted.ChipOracle.AluX0
import SP1Clean.Extracted.ChipOracle.Addi
import SP1Clean.Extracted.ChipOracle.Addw
import SP1Clean.Extracted.ChipOracle.Bitwise
import SP1Clean.Extracted.ChipOracle.Branch
import SP1Clean.Extracted.ChipOracle.Add
import SP1Clean.Extracted.ChipOracle.Sub
import SP1Clean.Extracted.ChipOracle.DivRem
import SP1Clean.Extracted.ChipOracle.Jal
import SP1Clean.Extracted.ChipOracle.Jalr
import SP1Clean.Extracted.ChipOracle.LoadByte
import SP1Clean.Extracted.ChipOracle.LoadDouble
import SP1Clean.Extracted.ChipOracle.LoadHalf
import SP1Clean.Extracted.ChipOracle.LoadWord
import SP1Clean.Extracted.ChipOracle.LoadX0
import SP1Clean.Extracted.ChipOracle.Lt
import SP1Clean.Extracted.ChipOracle.Mul
import SP1Clean.Extracted.ChipOracle.ShiftLeft
import SP1Clean.Extracted.ChipOracle.ShiftRight
import SP1Clean.Extracted.StoreByteChip
import SP1Clean.Extracted.StoreDoubleChip
import SP1Clean.Extracted.StoreHalfChip
import SP1Clean.Extracted.StoreWordChip
import SP1Clean.Extracted.ChipOracle.Subw
import SP1Clean.Extracted.SystemOracle.Byte
import SP1Clean.Extracted.SystemOracle.Global
import SP1Clean.Extracted.SystemOracle.MemoryBump
import SP1Clean.Extracted.SystemOracle.MemoryGlobalFinalize
import SP1Clean.Extracted.SystemOracle.MemoryGlobalInit
import SP1Clean.Extracted.SystemOracle.MemoryLocal
import SP1Clean.Extracted.SystemOracle.Program
import SP1Clean.Extracted.SystemOracle.PublicValues
import SP1Clean.Extracted.SystemOracle.Range
import SP1Clean.Extracted.SystemOracle.StateBump
import SP1Clean.Extracted.SystemOracle.SyscallCore
import SP1Clean.Extracted.SystemOracle.SyscallInstrs
import SP1Clean.Extracted.ChipOracle.UType
import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.CoreAIRRelation

/-! # Exact extracted Core AIR

This file is the small hand-written adapter over the generated Rust lists.  It assigns each audited
table name its exact extracted row type, supplies the correctly sized preprocessed row, and defines
validity directly from the generated `asserts` and `interactions` functions.  No generated circuit
is involved: native Clean circuits remain proof-oriented implementations, while these lists are the
whole-table Rust anchor.

The only parameter not determined by the AIR lists is `PreprocessedBinding`.  It says that the
preprocessed matrices used below open the commitment in the machine verifying key.  Its type exposes
only those matrices—not main rows or semantic claims—so a PCS/ArkLib adapter cannot smuggle execution
soundness through the commitment premise. -/

namespace SP1Clean.CoreAIR.Current

open SP1Clean.CoreProfile
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Exact main-row type selected by each table in the pinned profile. -/
def MainRow (p : ℕ) [Fact p.Prime] : Table → Type
  | .program => ProgramCols (ZMod p)
  | .byteLookup => ByteCols (ZMod p)
  | .rangeLookup => RangeCols (ZMod p)
  | .syscallCore => SyscallCoreCols (ZMod p)
  | .divRem => DivRemOracle.DivRemCols (ZMod p)
  | .add => AddOracle.AddCols (ZMod p)
  | .addi => AddiOracle.AddiCols (ZMod p)
  | .addw => AddwOracle.AddwCols (ZMod p)
  | .sub => SubOracle.SubCols (ZMod p)
  | .subw => SubwOracle.SubwCols (ZMod p)
  | .bitwise => BitwiseOracle.BitwiseCols (ZMod p)
  | .mul => MulOracle.MulCols (ZMod p)
  | .shiftRight => ShiftRightOracle.ShiftRightCols (ZMod p)
  | .shiftLeft => ShiftLeftOracle.ShiftLeftCols (ZMod p)
  | .lt => LtOracle.LtCols (ZMod p)
  | .aluX0 => AluX0Oracle.AluX0Cols (ZMod p)
  | .loadByte => LoadByteOracle.LoadByteColumns (ZMod p)
  | .loadHalf => LoadHalfOracle.LoadHalfColumns (ZMod p)
  | .loadWord => LoadWordOracle.LoadWordColumns (ZMod p)
  | .loadDouble => LoadDoubleOracle.LoadDoubleColumns (ZMod p)
  | .loadX0 => LoadX0Oracle.LoadX0Columns (ZMod p)
  | .storeByte => StoreByteColumns (ZMod p)
  | .storeHalf => StoreHalfColumns (ZMod p)
  | .storeWord => StoreWordColumns (ZMod p)
  | .storeDouble => StoreDoubleColumns (ZMod p)
  | .uType => UTypeOracle.UTypeColumns (ZMod p)
  | .branch => BranchOracle.BranchColumns (ZMod p)
  | .jal => JalOracle.JalColumns (ZMod p)
  | .jalr => JalrOracle.JalrColumns (ZMod p)
  | .syscallInstrs => SyscallInstrsCols (ZMod p)
  | .memoryBump => MemoryBumpCols (ZMod p)
  | .stateBump => StateBumpCols (ZMod p)
  | .memoryLocal => MemoryLocalCols (ZMod p)
  | .global => GlobalCols (ZMod p)
  | .memoryGlobalInit => MemoryGlobalInitCols (ZMod p)
  | .memoryGlobalFinalize => MemoryGlobalFinalizeCols (ZMod p)

/-- Width of the paired preprocessed row passed to the upstream `PairBuilder`.
Only the three committed lookup/provider tables have nonzero width in the baseline profile. -/
abbrev preprocessedWidth := Table.preprocessedWidth

/-- One exact AIR row.  Keeping preprocessing beside the corresponding main row makes every
generated row predicate total while leaving commitment authentication at the trace level. -/
structure Row (p : ℕ) [Fact p.Prime] (table : Table) where
  main : MainRow p table
  preprocessed : Vector (ZMod p) (preprocessedWidth table)

/-- Complete extracted assertion list for one physical row. -/
def assertions (publicValues : SP1PublicValues (ZMod p)) (table : Table)
    (row : Row p table) : List (ZMod p) :=
  match table with
  | .program => ProgramCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .byteLookup => ByteCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .rangeLookup => RangeCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .syscallCore => SyscallCoreCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .divRem => DivRemOracle.DivRemCols.asserts row.main
  | .add => AddOracle.AddCols.asserts row.main
  | .addi => AddiOracle.AddiCols.asserts row.main
  | .addw => AddwOracle.AddwCols.asserts row.main
  | .sub => SubOracle.SubCols.asserts row.main
  | .subw => SubwOracle.SubwCols.asserts row.main
  | .bitwise => BitwiseOracle.BitwiseCols.asserts row.main
  | .mul => MulOracle.MulCols.asserts row.main
  | .shiftRight => ShiftRightOracle.ShiftRightCols.asserts row.main
  | .shiftLeft => ShiftLeftOracle.ShiftLeftCols.asserts row.main
  | .lt => LtOracle.LtCols.asserts row.main
  | .aluX0 => AluX0Oracle.AluX0Cols.asserts row.main
  | .loadByte => LoadByteOracle.LoadByteColumns.asserts row.main
  | .loadHalf => LoadHalfOracle.LoadHalfColumns.asserts row.main
  | .loadWord => LoadWordOracle.LoadWordColumns.asserts row.main
  | .loadDouble => LoadDoubleOracle.LoadDoubleColumns.asserts row.main
  | .loadX0 => LoadX0Oracle.LoadX0Columns.asserts row.main
  | .storeByte => StoreByteColumns.asserts row.main
  | .storeHalf => StoreHalfColumns.asserts row.main
  | .storeWord => StoreWordColumns.asserts row.main
  | .storeDouble => StoreDoubleColumns.asserts row.main
  | .uType => UTypeOracle.UTypeColumns.asserts row.main
  | .branch => BranchOracle.BranchColumns.asserts row.main
  | .jal => JalOracle.JalColumns.asserts row.main
  | .jalr => JalrOracle.JalrColumns.asserts row.main
  | .syscallInstrs =>
      SyscallInstrsCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .memoryBump => MemoryBumpCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .stateBump => StateBumpCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .memoryLocal => MemoryLocalCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .global => GlobalCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .memoryGlobalInit =>
      MemoryGlobalInitCols.asserts row.main row.preprocessed publicValues.toBaseVector
  | .memoryGlobalFinalize =>
      MemoryGlobalFinalizeCols.asserts row.main row.preprocessed publicValues.toBaseVector

/-- Complete extracted interaction list for one physical row. -/
def interactions (publicValues : SP1PublicValues (ZMod p)) (table : Table)
    (row : Row p table) : List (Extracted.Interaction (ZMod p)) :=
  match table with
  | .program => ProgramCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .byteLookup => ByteCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .rangeLookup => RangeCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .syscallCore =>
      SyscallCoreCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .divRem => DivRemOracle.DivRemCols.interactions row.main
  | .add => AddOracle.AddCols.interactions row.main
  | .addi => AddiOracle.AddiCols.interactions row.main
  | .addw => AddwOracle.AddwCols.interactions row.main
  | .sub => SubOracle.SubCols.interactions row.main
  | .subw => SubwOracle.SubwCols.interactions row.main
  | .bitwise => BitwiseOracle.BitwiseCols.interactions row.main
  | .mul => MulOracle.MulCols.interactions row.main
  | .shiftRight => ShiftRightOracle.ShiftRightCols.interactions row.main
  | .shiftLeft => ShiftLeftOracle.ShiftLeftCols.interactions row.main
  | .lt => LtOracle.LtCols.interactions row.main
  | .aluX0 => AluX0Oracle.AluX0Cols.interactions row.main
  | .loadByte => LoadByteOracle.LoadByteColumns.interactions row.main
  | .loadHalf => LoadHalfOracle.LoadHalfColumns.interactions row.main
  | .loadWord => LoadWordOracle.LoadWordColumns.interactions row.main
  | .loadDouble => LoadDoubleOracle.LoadDoubleColumns.interactions row.main
  | .loadX0 => LoadX0Oracle.LoadX0Columns.interactions row.main
  | .storeByte => StoreByteColumns.interactions row.main
  | .storeHalf => StoreHalfColumns.interactions row.main
  | .storeWord => StoreWordColumns.interactions row.main
  | .storeDouble => StoreDoubleColumns.interactions row.main
  | .uType => UTypeOracle.UTypeColumns.interactions row.main
  | .branch => BranchOracle.BranchColumns.interactions row.main
  | .jal => JalOracle.JalColumns.interactions row.main
  | .jalr => JalrOracle.JalrColumns.interactions row.main
  | .syscallInstrs =>
      SyscallInstrsCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .memoryBump =>
      MemoryBumpCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .stateBump => StateBumpCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .memoryLocal =>
      MemoryLocalCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .global => GlobalCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .memoryGlobalInit =>
      MemoryGlobalInitCols.interactions row.main row.preprocessed publicValues.toBaseVector
  | .memoryGlobalFinalize =>
      MemoryGlobalFinalizeCols.interactions row.main row.preprocessed publicValues.toBaseVector

/-- The preprocessed matrices, with no access to main rows or semantic evidence. -/
structure PreprocessedTrace (p : ℕ) [Fact p.Prime] where
  rows : (table : Table) → List (Vector (ZMod p) (preprocessedWidth table))

/-- Project precisely the data committed by the verifying key. -/
def preprocessedTrace (witness : Witness (Row p)) : PreprocessedTrace p where
  rows table := (witness.trace.rows table).map Row.preprocessed

/-- A PCS-level opening statement for the preprocessed commitment. -/
abbrev PreprocessedBinding (p : ℕ) [Fact p.Prime] (Digest : Type) :=
  Digest → PreprocessedTrace p → Prop

namespace Balance

/-- Scope carried by the direction discriminator in the generated interaction DSL. -/
inductive Scope | local | global
deriving DecidableEq, Repr

def directionScope : Dir → Scope
  | .send | .receive => .local
  | .sendGlobal | .receiveGlobal => .global

/-- Canonical natural multiplicity sent for one payload in one interaction scope. -/
def sentCount (scope : Scope) (all : List (Extracted.Interaction (ZMod p)))
    (payload : AirInteraction (ZMod p)) : ℕ :=
  (all.filter fun interaction =>
      directionScope interaction.dir = scope ∧ interaction.payload = payload ∧
        (interaction.dir = .send ∨ interaction.dir = .sendGlobal)).map
    (fun interaction => interaction.mult.val) |>.sum

/-- Canonical natural multiplicity received for one payload in one interaction scope. -/
def receivedCount (scope : Scope) (all : List (Extracted.Interaction (ZMod p)))
    (payload : AirInteraction (ZMod p)) : ℕ :=
  (all.filter fun interaction =>
      directionScope interaction.dir = scope ∧ interaction.payload = payload ∧
        (interaction.dir = .receive ∨ interaction.dir = .receiveGlobal)).map
    (fun interaction => interaction.mult.val) |>.sum

/-- Exact local interaction relation supplied by the LogUp/GKR knowledge extractor.

This is deliberately an equality of canonical natural multiplicities, not merely a field-valued
sum.  A modular equality can wrap at the field characteristic and is not by itself enough to recover
an execution multiset.  ArkLib's interaction-argument theorem must extract this stronger fact (with
its own error term and trace/multiplicity bounds).  Global-scope interactions are rejected because
the pinned baseline emits none; a future pin that introduces them must add the corresponding
cross-shard accumulator relation explicitly. -/
def Valid (all : List (Extracted.Interaction (ZMod p))) : Prop :=
  (∀ interaction ∈ all, directionScope interaction.dir = Scope.local) ∧
    ∀ payload, sentCount Scope.local all payload = receivedCount Scope.local all payload

end Balance

/-- All row interactions in table-list order, preceded by the machine-level public-value block. -/
def allInteractions (publicValues : SP1PublicValues (ZMod p))
    (witness : Witness (Row p)) : List (Extracted.Interaction (ZMod p)) :=
  PublicValuesOracle.interactions publicValues.toBaseVector ++
    witness.activeTables.flatMap fun table =>
      (witness.trace.rows table).flatMap (interactions publicValues table)

/-- Exact non-row obligations of one baseline shard. -/
def GlobalValid {Digest : Type} (binds : PreprocessedBinding p Digest)
    (statement : SP1ShardStatement (ZMod p) Digest) (witness : Witness (Row p)) : Prop :=
  statement.verifyingKey.WellFormed .base ∧
    statement.ConfigurationMatches ∧
    statement.publicValues.mprotect = none ∧
    List.Forall (· = 0)
      (PublicValuesOracle.asserts statement.publicValues.toBaseVector) ∧
    Balance.Valid (allInteractions statement.publicValues witness) ∧
    binds statement.verifyingKey.preprocessed_commit (preprocessedTrace witness)

/-- Concrete exact-table system at the checked-in semantic revision. -/
def system {Digest : Type} (binds : PreprocessedBinding p Digest) :
    System (SP1ShardStatement (ZMod p) Digest) where
  profile := CoreProfile.current
  Row := Row p
  localValid table statement row :=
    List.Forall (· = 0) (assertions statement.publicValues table row)
  globalValid := GlobalValid binds

/-- Public name of the exact witness relation for one pinned upstream cluster.

The cluster argument is intentionally explicit.  In particular, the six-table memory-boundary
cluster cannot be passed to the execution-shard soundness theorem merely because it uses the same
heterogeneous row universe. -/
abbrev Relation {Digest : Type} (binds : PreprocessedBinding p Digest) (cluster : Cluster) :=
  (system binds).relationFor cluster

/-! ## Audited syscall-row view -/

/-- Reassemble four little-endian 16-bit row limbs as the 64-bit word used by SP1. -/
def word64 (values : Vector (ZMod p) 65) (i0 i1 i2 i3 : Fin 65) : BitVec 64 :=
  BitVec.ofNat 64 (values[i0].val + values[i1].val * 2 ^ 16 +
    values[i2].val * 2 ^ 32 + values[i3].val * 2 ^ 48)

/-- Reassemble a three-limb pc in the same little-endian layout. -/
def pc64 (values : Vector (ZMod p) 65) (i0 i1 i2 : Fin 65) : BitVec 64 :=
  BitVec.ofNat 64
    (values[i0].val + values[i1].val * 2 ^ 16 + values[i2].val * 2 ^ 32)

/-- Read the timestamp represented by `CPUState`'s `(high, 8, 16)` columns. -/
def clock (values : Vector (ZMod p) 65) : ℕ :=
  values[0].val * 2 ^ 24 + values[1].val * 2 ^ 16 + values[2].val

/-- Total decoder of one physical `SyscallInstrs` row.  The indices are the flattened field order of
`SyscallInstrColumns<T, SupervisorMode>` at the pinned Rust revision:
`state = 0..5`, `RTypeReader = 6..27`, `next_pc = 28..30`, `op_a_value = 32..35`, and
`is_real = 64`. -/
def decodeSyscallRow (row : SyscallInstrsCols (ZMod p)) : Machine.CoreSyscallEvent where
  clock := clock row.values
  pc := pc64 row.values 3 4 5
  nextPc := pc64 row.values 28 29 30
  rawCode := word64 row.values 7 8 9 10
  arg1 := word64 row.values 15 16 17 18
  arg2 := word64 row.values 22 23 24 25
  result := word64 row.values 32 33 34 35

/-- Decode exactly the real syscall rows, preserving physical table order. -/
def syscallEvents (witness : Witness (Row p)) : List Machine.CoreSyscallEvent :=
  (witness.trace.rows .syscallInstrs).filterMap fun row =>
    if row.main.values[64] = 1 then some (decodeSyscallRow row.main) else none

/-- Total event decoder paired with the concrete exact-table system. -/
def eventDecoder {Digest : Type} (binds : PreprocessedBinding p Digest) :
    EventDecoder (system binds) where
  syscallEvents _ witness := syscallEvents witness

omit [Fact (2 ^ 17 < p)] in
theorem system_isCurrent {Digest : Type} (binds : PreprocessedBinding p Digest) :
    (system binds).IsCurrent := rfl

end SP1Clean.CoreAIR.Current
