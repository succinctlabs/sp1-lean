import SP1Clean.Extracted.Provenance

/-! # AUTO-GENERATED Core AIR machine manifest — do not edit by hand.

Generated directly from `RiscvAir::machine().shape().chip_clusters` by the pinned
list-only extractor. Each entry records the runtime `MachineAir::name`, main width, and
preprocessed width. Regeneration fails unless the two theorem clusters occur exactly once
and the public-value width remains 160. -/

set_option linter.all false  -- auto-generated: skip linters

namespace SP1Clean.Extracted

structure CoreAIRTableShape where
  name : String
  mainWidth : Nat
  preprocessedWidth : Nat
deriving DecidableEq, Repr

/-- Exact baseline trusted Core cluster at `checkedInProvenance`. -/
def currentCoreCluster : List CoreAIRTableShape := [
  ⟨"Add", 33, 0⟩,
  ⟨"Addi", 30, 0⟩,
  ⟨"Addw", 36, 0⟩,
  ⟨"AluX0", 34, 0⟩,
  ⟨"Bitwise", 51, 0⟩,
  ⟨"Branch", 45, 0⟩,
  ⟨"Byte", 6, 7⟩,
  ⟨"DivRem", 246, 0⟩,
  ⟨"Global", 241, 0⟩,
  ⟨"Jal", 31, 0⟩,
  ⟨"Jalr", 35, 0⟩,
  ⟨"LoadByte", 47, 0⟩,
  ⟨"LoadDouble", 39, 0⟩,
  ⟨"LoadHalf", 44, 0⟩,
  ⟨"LoadWord", 44, 0⟩,
  ⟨"LoadX0", 48, 0⟩,
  ⟨"Lt", 44, 0⟩,
  ⟨"MemoryBump", 15, 0⟩,
  ⟨"MemoryLocal", 20, 0⟩,
  ⟨"Mul", 82, 0⟩,
  ⟨"Program", 1, 16⟩,
  ⟨"Range", 1, 2⟩,
  ⟨"ShiftLeft", 65, 0⟩,
  ⟨"ShiftRight", 69, 0⟩,
  ⟨"StateBump", 14, 0⟩,
  ⟨"StoreByte", 50, 0⟩,
  ⟨"StoreDouble", 39, 0⟩,
  ⟨"StoreHalf", 45, 0⟩,
  ⟨"StoreWord", 44, 0⟩,
  ⟨"Sub", 33, 0⟩,
  ⟨"Subw", 32, 0⟩,
  ⟨"SyscallCore", 10, 0⟩,
  ⟨"SyscallInstrs", 65, 0⟩,
  ⟨"UType", 31, 0⟩,
]

/-- Exact trusted memory-boundary cluster at `checkedInProvenance`. -/
def currentMemoryBoundaryCluster : List CoreAIRTableShape := [
  ⟨"Byte", 6, 7⟩,
  ⟨"Global", 241, 0⟩,
  ⟨"MemoryGlobalFinalize", 30, 0⟩,
  ⟨"MemoryGlobalInit", 30, 0⟩,
  ⟨"Program", 1, 16⟩,
  ⟨"Range", 1, 2⟩,
]

/-- `RiscvAir::machine().num_pv_elts()` at the extraction revision. -/
def currentCorePublicValuesWidth : Nat := 160

end SP1Clean.Extracted
