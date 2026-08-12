import SP1Clean.Math.Word
import SP1Clean.Extracted.ExtractionDSL
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # AUTO-GENERATED — do not edit by hand.

Struct-carrier module: the canonical definition site for `MemoryAccessTimestamp`, `MemoryAccessCols`.
Carved by `update_extracted.py` out of the `sp1-constraint-compiler --chip LoadByte`
discovery output (no standalone operation emits these structs; every load/store chip
row nests them). Regenerate with `SP1_DIR=… python3 update_extracted.py`. -/

set_option linter.all false  -- auto-generated: skip linters

namespace SP1Clean.Extracted
open SP1Clean

structure MemoryAccessTimestamp (F : Type) where
  prev_high : F
  prev_low : F
  compare_low : F
  diff_low_limb : F
  diff_high_limb : F
deriving ProvableStruct

structure MemoryAccessCols (F : Type) where
  prev_value : (Word F)
  access_timestamp : (MemoryAccessTimestamp F)
deriving ProvableStruct

end SP1Clean.Extracted
