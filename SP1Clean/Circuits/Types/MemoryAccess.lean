module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word

/-! # Native MemoryAccess columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `MemoryAccessTimestamp`. -/
structure MemoryAccessTimestamp (F : Type) where
  /-- High 24 bits of the previous access timestamp. -/
  prev_high : F
  /-- Low 24 bits of the previous access timestamp. -/
  prev_low : F
  /-- Select low-part comparison when the high timestamp parts agree. -/
  compare_low : F
  /-- Low 16 bits of the selected timestamp difference minus one. -/
  diff_low_limb : F
  /-- High 8 bits of the selected timestamp difference minus one. -/
  diff_high_limb : F
deriving ProvableStruct
provable_struct_eval_lemmas MemoryAccessTimestamp

/-- Circuit columns for `MemoryAccessCols`. -/
structure MemoryAccessCols (F : Type) where
  /-- Word stored before this access. -/
  prev_value : (Word F)
  /-- Ordering witness for this access and its predecessor. -/
  access_timestamp : (MemoryAccessTimestamp F)
deriving ProvableStruct
provable_struct_eval_lemmas MemoryAccessCols

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  MemoryAccessTimestamp.prev_high
  MemoryAccessTimestamp.prev_low
  MemoryAccessTimestamp.compare_low
  MemoryAccessTimestamp.diff_low_limb
  MemoryAccessTimestamp.diff_high_limb
  MemoryAccessCols.prev_value
  MemoryAccessCols.access_timestamp

end SP1Clean.Circuits.Types
