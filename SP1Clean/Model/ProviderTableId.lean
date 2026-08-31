import Mathlib.Data.List.FinRange
import SP1Clean.Model.InstructionChipId

/-!
# Stable identities for native provider and boundary tables

Instruction tables and provider tables have different semantic roles and therefore different
identity types. `ProviderTableId` names the 29 non-instruction tables appended to the native
ensemble without importing Clean components or proof-layer provider implementations.

The seventeen Range tables are indexed rather than copied into seventeen constructors. This keeps
their width in the identity and makes completeness/provider registries total by construction.
-/

namespace SP1Clean

/-- The six fixed Byte-operation provider tables. -/
inductive ByteProviderId where
  | u8Range
  | msb
  | andByte
  | orByte
  | xorByte
  | ltu
deriving DecidableEq, Repr, Inhabited

namespace ByteProviderId

/-- Fixed Byte-provider order used by the native witness format. -/
def all : List ByteProviderId := [.u8Range, .msb, .andByte, .orByte, .xorByte, .ltu]

@[simp] theorem all_length : all.length = 6 := rfl

@[simp] theorem mem_all (id : ByteProviderId) : id ∈ all := by
  cases id <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end ByteProviderId

/-- Stable identity of one non-instruction table in the 54-table native ensemble. -/
inductive ProviderTableId where
  | byte (provider : ByteProviderId)
  | range (width : Fin 17)
  | program
  | memoryInit
  | memoryFinalize
  | memoryBump
  | stateBump
  | halt
deriving DecidableEq, Repr, Inhabited

namespace ProviderTableId

/-- Every provider/boundary identity in physical ensemble order: six Byte tables, Range widths
`0..16`, then Program, the two Memory boundaries, MemoryBump, StateBump, and the Halt table. -/
def all : List ProviderTableId :=
  ByteProviderId.all.map .byte ++ (List.finRange 17).map .range ++
    [.program, .memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt]

/-- Number of non-instruction tables in the native ensemble. -/
def count : ℕ := all.length

@[simp] theorem all_length : all.length = 29 := by
  simp [all, ByteProviderId.all]

@[simp] theorem count_eq : count = 29 := by
  simp [count]

@[simp] theorem mem_all (id : ProviderTableId) : id ∈ all := by
  cases id with
  | byte provider => simp [all]
  | range width => simp [all]
  | program => simp [all]
  | memoryInit => simp [all]
  | memoryFinalize => simp [all]
  | memoryBump => simp [all]
  | stateBump => simp [all]
  | halt => simp [all]

theorem all_nodup : all.Nodup := by
  decide

end ProviderTableId

/-- Position identity of every table in the native ensemble, while retaining the semantic split
between instruction execution and provider/boundary roles. -/
inductive NativeTableId where
  | instruction (chip : InstructionChipId)
  | provider (table : ProviderTableId)
deriving DecidableEq, Repr, Inhabited

namespace NativeTableId

/-- The complete 54-table witness order, derived from the two role-specific registries. -/
def all : List NativeTableId :=
  InstructionChipId.all.map .instruction ++ ProviderTableId.all.map .provider

@[simp] theorem all_length : all.length = 54 := by
  simp [all]

@[simp] theorem mem_all (id : NativeTableId) : id ∈ all := by
  cases id <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end NativeTableId

end SP1Clean
