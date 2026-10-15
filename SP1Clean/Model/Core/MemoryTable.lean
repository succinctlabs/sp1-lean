import SP1Clean.Model.Core.MemoryIntervals
import SP1Clean.Model.Semantics.Decode
import ToClean.Circuit.StaticTable
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Concrete field rows for the native initial-memory lookup

The interval table is fixed by the sparse image. Its endpoints use full four-limb words so the
exclusive endpoint `2^48` is representable without field or address truncation. The static-table
predicate is literal membership in these encoded rows; its semantic consequences are proved here.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Soundness.Target

/-- The complete field payload of one constant-byte interval. -/
structure MemoryIntervalRow (F : Type) where
  lower : Word F
  upper : Word F
  value : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas MemoryIntervalRow

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Canonical four-limb encoding of both endpoints and one byte value. -/
def MemoryInterval.encode (interval : MemoryInterval) : MemoryIntervalRow (ZMod p) where
  lower := bitVecToWord (BitVec.ofNat 64 interval.lower)
  upper := bitVecToWord (BitVec.ofNat 64 interval.upper)
  value := interval.value.toNat

/-- Natural-address encoding agrees with the word's unsigned semantic value. -/
theorem endpoint_toNat (address : ℕ) (bound : address < 2 ^ 64) :
    Word.toNat (bitVecToWord (p := p) (BitVec.ofNat 64 address)) = address := by
  rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

/-- Endpoint encoding is exact throughout the supported word range. -/
theorem MemoryInterval.encode_endpoints (interval : MemoryInterval)
    (lowerBound : interval.lower < 2 ^ 64) (upperBound : interval.upper < 2 ^ 64) :
    Word.toNat (interval.encode (p := p)).lower = interval.lower ∧
      Word.toNat (interval.encode (p := p)).upper = interval.upper :=
  ⟨endpoint_toNat _ lowerBound, endpoint_toNat _ upperBound⟩

/-- A concrete fixed lookup instance; its size is bounded by the sparse image's size. -/
@[irreducible] def ByteMemory.fixedTable (memory : ByteMemory) (limit : ℕ) :
    StaticTable (ZMod p) MemoryIntervalRow :=
  StaticTable.ofRows "sp1.native.initial_memory" ((memory.intervals limit).map MemoryInterval.encode)

omit [Fact (2 ^ 17 < p)] in
theorem ByteMemory.fixedTable_spec (memory : ByteMemory) (limit : ℕ)
    (row : MemoryIntervalRow (ZMod p)) :
    (memory.fixedTable limit).Spec row ↔
      ∃ interval ∈ memory.intervals limit, interval.encode = row := by
  simpa only [fixedTable, StaticTable.ofRows] using
    (List.mem_map : row ∈ (memory.intervals limit).map MemoryInterval.encode ↔ _)

/-- Fixed-table membership establishes endpoint ranges and the original interval, with no
prover-selected interpretation of the lookup predicate. -/
theorem ByteMemory.fixedTable_sound (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64)
    (row : MemoryIntervalRow (ZMod p)) (member : (memory.fixedTable limit).Spec row) :
    Word.isU64 row.lower ∧ Word.isU64 row.upper ∧
      ∃ interval ∈ memory.intervals limit,
        Word.toNat row.lower = interval.lower ∧ Word.toNat row.upper = interval.upper ∧
          row.value = (interval.value.toNat : ZMod p) := by
  obtain ⟨interval, intervalMem, rfl⟩ := (memory.fixedTable_spec limit row).mp member
  have bounds := memory.intervals_bounds limit interval intervalMem
  exact ⟨isU64_bitVecToWord _, isU64_bitVecToWord _, interval, intervalMem,
    endpoint_toNat _ (by omega), endpoint_toNat _ (by omega), rfl⟩

/-- The field-level lookup and integer interval comparisons imply the semantic byte value. -/
theorem ByteMemory.fixedTable_read (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64)
    (row : MemoryIntervalRow (ZMod p)) (member : (memory.fixedTable limit).Spec row)
    (query : ℕ) (inside : Word.toNat row.lower ≤ query ∧ query < Word.toNat row.upper) :
    query < limit ∧ row.value = (memory.read query).toNat := by
  obtain ⟨_, _, interval, intervalMem, lowerEq, upperEq, valueEq⟩ :=
    memory.fixedTable_sound limit limitBound row member
  rw [lowerEq, upperEq] at inside
  have semantic := memory.intervals_sound limit interval intervalMem query inside
  exact ⟨semantic.1, by rw [semantic.2]; exact valueEq⟩

end SP1Clean.Model.Core
