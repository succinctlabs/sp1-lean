import SP1Clean.Model.Core.MemorySnapshot
import SP1Clean.Model.Semantics.Decode
import ToClean.Circuit.StaticTable

/-! # Fixed register rows from a finite source snapshot

The lookup binds the index and all four value limbs together. Its 32 rows are computed from the
supplied snapshot, independently of prover data or the instruction trace.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Soundness.Target

structure RegisterSnapshotRow (F : Type) where
  index : F
  value : Word F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas RegisterSnapshotRow

namespace MemorySnapshot

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def registerRow (snapshot : MemorySnapshot) (index : BitVec 5) : RegisterSnapshotRow (ZMod p) :=
  ⟨index.toNat, bitVecToWord (snapshot.read (.reg index))⟩

@[irreducible] def registerTable (snapshot : MemorySnapshot) : StaticTable (ZMod p) RegisterSnapshotRow :=
  StaticTable.ofRows "sp1.native.source_registers"
    (List.ofFn fun index : Fin 32 => snapshot.registerRow (BitVec.ofNat 5 index.val))

omit [Fact (2 ^ 17 < p)] in
theorem registerTable_spec (snapshot : MemorySnapshot) (row : RegisterSnapshotRow (ZMod p)) :
    snapshot.registerTable.Spec row ↔ ∃ index, snapshot.registerRow index = row := by
  rw [registerTable]
  change row ∈ List.ofFn _ ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨index, equal⟩
    exact ⟨BitVec.ofNat 5 index.val, equal⟩
  · rintro ⟨index, rfl⟩
    exact ⟨⟨index.toNat, index.isLt⟩, by simp⟩

theorem registerRow_index (snapshot : MemorySnapshot) (index : BitVec 5) :
    (snapshot.registerRow (p := p) index).index.val = index.toNat := by
  exact ZMod.val_natCast_of_lt (by have := index.isLt; have := Fact.out (p := 2 ^ 17 < p); omega)

/-- Static membership authenticates the full value at the row's decoded index. -/
theorem registerTable_sound (snapshot : MemorySnapshot) (row : RegisterSnapshotRow (ZMod p))
    (member : snapshot.registerTable.Spec row) :
    row.index.val < 32 ∧ Word.isU64 row.value ∧
      Word.toBitVec64 row.value = snapshot.read (.reg (BitVec.ofNat 5 row.index.val)) := by
  obtain ⟨index, rfl⟩ := (snapshot.registerTable_spec row).mp member
  rw [snapshot.registerRow_index]
  exact ⟨index.isLt, isU64_bitVecToWord _, by simp [registerRow, toBitVec64_bitVecToWord]⟩

end MemorySnapshot

end SP1Clean.Model.Core
