import Mathlib.Data.List.Nodup
import SP1Clean.Extracted.CoreAIRManifest

/-! # The pinned SP1 Core AIR profile

This file is the small, hand-auditable manifest for the AIR target.  It is transcribed from
`RiscvAir::machine` in the pinned Rust checkout, rather than inferred from whichever extracted Lean
files happen to exist.  Generated extraction metadata must prove that it has exactly this profile
before it can instantiate the full Core AIR relation.

The target is the trusted/supervisor baseline Core cluster and its separate memory-boundary cluster.
The optional retention extensions, user-mode `mprotect` clusters, and precompile clusters are distinct
profiles; silently admitting one of those tables into this profile would change the theorem. -/

namespace SP1Clean.CoreProfile

/-- Exact Rust checkout used as the current semantic ground truth.  The extraction compiler still has
its own separately audited provenance until its patches have been rebased and regenerated. -/
def sp1SemanticRevision : String := "a630089d9ff484ec6f2feade8d0afbb1447eed11"

/-- Human-readable description emitted by `git describe --tags --always` at the semantic revision. -/
def sp1SemanticDescription : String := "v6.3.1-8-ga630089d9"

/-- Generated AIR artifacts and the hand-audited profile name the same unmodified Rust source. -/
theorem checkedIn_semanticRevision :
    SP1Clean.Extracted.checkedInProvenance.semanticRevision = sp1SemanticRevision := rfl

/-- Tables in the trusted baseline Core and memory-boundary clusters. -/
inductive Table
  | program
  | byteLookup
  | rangeLookup
  | syscallCore
  | divRem
  | add
  | addi
  | addw
  | sub
  | subw
  | bitwise
  | mul
  | shiftRight
  | shiftLeft
  | lt
  | aluX0
  | loadByte
  | loadHalf
  | loadWord
  | loadDouble
  | loadX0
  | storeByte
  | storeHalf
  | storeWord
  | storeDouble
  | uType
  | branch
  | jal
  | jalr
  | syscallInstrs
  | memoryBump
  | stateBump
  | memoryLocal
  | global
  | memoryGlobalInit
  | memoryGlobalFinalize
deriving DecidableEq, Repr

/-- The exact `MachineAir::name` spelling used in Rust.  Extraction compares names at the whole-table
boundary, so enum-variant spellings such as Rust's `MemoryGlobalFinal` are deliberately irrelevant. -/
def Table.airName : Table → String
  | .program => "Program"
  | .byteLookup => "Byte"
  | .rangeLookup => "Range"
  | .syscallCore => "SyscallCore"
  | .divRem => "DivRem"
  | .add => "Add"
  | .addi => "Addi"
  | .addw => "Addw"
  | .sub => "Sub"
  | .subw => "Subw"
  | .bitwise => "Bitwise"
  | .mul => "Mul"
  | .shiftRight => "ShiftRight"
  | .shiftLeft => "ShiftLeft"
  | .lt => "Lt"
  | .aluX0 => "AluX0"
  | .loadByte => "LoadByte"
  | .loadHalf => "LoadHalf"
  | .loadWord => "LoadWord"
  | .loadDouble => "LoadDouble"
  | .loadX0 => "LoadX0"
  | .storeByte => "StoreByte"
  | .storeHalf => "StoreHalf"
  | .storeWord => "StoreWord"
  | .storeDouble => "StoreDouble"
  | .uType => "UType"
  | .branch => "Branch"
  | .jal => "Jal"
  | .jalr => "Jalr"
  | .syscallInstrs => "SyscallInstrs"
  | .memoryBump => "MemoryBump"
  | .stateBump => "StateBump"
  | .memoryLocal => "MemoryLocal"
  | .global => "Global"
  | .memoryGlobalInit => "MemoryGlobalInit"
  | .memoryGlobalFinalize => "MemoryGlobalFinalize"

/-- Main-trace width reported by the pinned `MachineAir`.  The generated manifest equality below
turns this readable table into a pin-change tripwire. -/
def Table.mainWidth : Table → ℕ
  | .program => 1
  | .byteLookup => 6
  | .rangeLookup => 1
  | .syscallCore => 10
  | .divRem => 246
  | .add => 33
  | .addi => 30
  | .addw => 36
  | .sub => 33
  | .subw => 32
  | .bitwise => 51
  | .mul => 82
  | .shiftRight => 69
  | .shiftLeft => 65
  | .lt => 44
  | .aluX0 => 34
  | .loadByte => 47
  | .loadHalf => 44
  | .loadWord => 44
  | .loadDouble => 39
  | .loadX0 => 48
  | .storeByte => 50
  | .storeHalf => 45
  | .storeWord => 44
  | .storeDouble => 39
  | .uType => 31
  | .branch => 45
  | .jal => 31
  | .jalr => 35
  | .syscallInstrs => 65
  | .memoryBump => 15
  | .stateBump => 14
  | .memoryLocal => 20
  | .global => 241
  | .memoryGlobalInit | .memoryGlobalFinalize => 30

/-- Width of the preprocessed row paired with this AIR. -/
def Table.preprocessedWidth : Table → ℕ
  | .program => 16
  | .byteLookup => 7
  | .rangeLookup => 2
  | _ => 0

/-- Manifest view of one audited table. -/
def Table.extractedShape (table : Table) : SP1Clean.Extracted.CoreAIRTableShape :=
  ⟨table.airName, table.mainWidth, table.preprocessedWidth⟩

/-- The three preprocessed tables included in every current cluster. -/
def preprocessedTables : List Table := [.program, .byteLookup, .rangeLookup]

/-- The 25 instruction tables in the baseline trusted Core cluster. -/
def instructionTables : List Table :=
  [ .divRem, .add, .addi, .addw, .sub, .subw, .bitwise, .mul, .shiftRight,
    .shiftLeft, .lt, .aluX0, .loadByte, .loadHalf, .loadWord, .loadDouble, .loadX0,
    .storeByte, .storeHalf, .storeWord, .storeDouble, .uType, .branch, .jal, .jalr ]

/-- Non-instruction tables in the baseline trusted Core cluster. -/
def coreSystemTables : List Table :=
  [.syscallCore, .syscallInstrs, .memoryBump, .stateBump, .memoryLocal, .global]

/-- Exact table set of the baseline trusted Core cluster.  The order here is explanatory; Rust stores
the cluster in a `BTreeSet`, so equality with extraction is set/no-dup equality, not list order. -/
def coreCluster : List Table :=
  preprocessedTables ++ [.syscallCore] ++ instructionTables ++
    [.syscallInstrs, .memoryBump, .stateBump, .memoryLocal, .global]

/-- Exact table set of the separate trusted memory-boundary cluster. -/
def memoryBoundaryCluster : List Table :=
  preprocessedTables ++ [.memoryGlobalInit, .memoryGlobalFinalize, .global]

theorem instructionTables_length : instructionTables.length = 25 := rfl

theorem coreSystemTables_length : coreSystemTables.length = 6 := rfl

theorem coreCluster_length : coreCluster.length = 34 := rfl

theorem memoryBoundaryCluster_length : memoryBoundaryCluster.length = 6 := rfl

theorem coreCluster_nodup : coreCluster.Nodup := by decide

theorem memoryBoundaryCluster_nodup : memoryBoundaryCluster.Nodup := by decide

/-- The hand-auditable enum and the machine-generated baseline cluster contain exactly the same AIR
names.  This theorem deliberately ignores ordering: Rust stores a cluster as a `BTreeSet`, whereas
the list above is organized by semantic role. -/
theorem coreCluster_matchesExtracted :
    (coreCluster.map Table.airName).Perm
      (SP1Clean.Extracted.currentCoreCluster.map
        SP1Clean.Extracted.CoreAIRTableShape.name) := by decide

/-- Membership and both row widths agree with the manifest emitted from `RiscvAir::machine()`. -/
theorem coreClusterShapes_matchExtracted :
    (coreCluster.map Table.extractedShape).Perm
      SP1Clean.Extracted.currentCoreCluster := by decide

/-- The memory-boundary companion cluster is likewise exact at the extraction pin. -/
theorem memoryBoundaryCluster_matchesExtracted :
    (memoryBoundaryCluster.map Table.airName).Perm
      (SP1Clean.Extracted.currentMemoryBoundaryCluster.map
        SP1Clean.Extracted.CoreAIRTableShape.name) := by decide

/-- The complete memory-boundary table shapes agree with the generated Rust manifest. -/
theorem memoryBoundaryClusterShapes_matchExtracted :
    (memoryBoundaryCluster.map Table.extractedShape).Perm
      SP1Clean.Extracted.currentMemoryBoundaryCluster := by decide

/-- The semantic public-values encoder and Rust's machine manifest agree on the base width. -/
theorem publicValuesWidth_matchesExtracted :
    SP1Clean.Extracted.currentCorePublicValuesWidth = 160 := rfl

/-- A profile value passed to relation/extraction adapters.  Keeping the revision in the value makes
cross-version composition an explicit equality obligation. -/
structure Profile where
  semanticRevision : String
  core : List Table
  memoryBoundary : List Table
  core_nodup : core.Nodup
  memoryBoundary_nodup : memoryBoundary.Nodup

/-- The current baseline Core target. -/
def current : Profile where
  semanticRevision := sp1SemanticRevision
  core := coreCluster
  memoryBoundary := memoryBoundaryCluster
  core_nodup := coreCluster_nodup
  memoryBoundary_nodup := memoryBoundaryCluster_nodup

end SP1Clean.CoreProfile
