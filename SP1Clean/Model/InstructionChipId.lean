import Mathlib.Data.List.Basic

/-!
# Stable identities for the supported instruction chips

`InstructionChipId` names the twenty-five instruction-table families in the native supported-core
profile, independently of their Clean circuits, dependent row types, Sail bridges, or trace
builders.  `InstructionChipId.all` fixes their physical table order once at the Model layer.

The provider and boundary tables are deliberately outside this type.  They have different roles
and no instruction-routing identity; any provider identity vocabulary should remain a separate
type rather than extending this enum into a heterogeneous 53-table descriptor.
-/

namespace SP1Clean

/-- Stable identity of one instruction-table family in the native supported-core profile. -/
inductive InstructionChipId where
  | add
  | addi
  | addw
  | sub
  | subw
  | bitwise
  | lt
  | shiftLeft
  | shiftRight
  | jal
  | jalr
  | branch
  | uType
  | loadByte
  | loadHalf
  | loadWord
  | loadDouble
  | loadX0
  | storeByte
  | storeHalf
  | storeWord
  | storeDouble
  | mul
  | divRem
  | aluX0
deriving DecidableEq, Repr, Inhabited

namespace InstructionChipId

/-- Every supported instruction-chip identity, in physical ensemble-table order. -/
def all : List InstructionChipId :=
  [.add, .addi, .addw, .sub, .subw, .bitwise, .lt, .shiftLeft, .shiftRight,
   .jal, .jalr, .branch, .uType, .loadByte, .loadHalf, .loadWord, .loadDouble,
   .loadX0, .storeByte, .storeHalf, .storeWord, .storeDouble, .mul, .divRem, .aluX0]

/-- Number of instruction tables in the native supported-core profile. -/
def count : ℕ := all.length

@[simp] theorem all_length : all.length = 25 := rfl

@[simp] theorem count_eq : count = 25 := rfl

/-- The canonical enumeration covers every instruction-chip identity. -/
@[simp] theorem mem_all (id : InstructionChipId) : id ∈ all := by
  cases id <;> simp [all]

/-- No instruction-chip identity occupies two physical positions. -/
theorem all_nodup : all.Nodup := by
  decide

end InstructionChipId

end SP1Clean
