module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Math.Word

/-! # Native RegisterAccess columns

These circuit value types are owned by the native library. The transitional Rust
extractor checks their field order and shapes before reusing them in its oracles.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `RegisterAccessTimestamp`. -/
structure RegisterAccessTimestamp (F : Type) where
  /-- Low 24 bits of the previous access timestamp. -/
  prev_low : F
  /-- Low-part timestamp gap within a 16-bit register epoch. -/
  diff_low_limb : F
deriving ProvableStruct
provable_struct_eval_lemmas RegisterAccessTimestamp

/-- Circuit columns for `RegisterAccessCols`. -/
structure RegisterAccessCols (F : Type) where
  /-- Word stored before this access. -/
  prev_value : (Word F)
  /-- Ordering witness for this access and its predecessor. -/
  access_timestamp : (RegisterAccessTimestamp F)
deriving ProvableStruct
provable_struct_eval_lemmas RegisterAccessCols

-- Preserve Rust field spelling for independent layout checks while reverse extraction remains.
attribute [nolint defsWithUnderscore]
  RegisterAccessTimestamp.prev_low
  RegisterAccessTimestamp.diff_low_limb
  RegisterAccessCols.prev_value
  RegisterAccessCols.access_timestamp

end SP1Clean.Circuits.Types
