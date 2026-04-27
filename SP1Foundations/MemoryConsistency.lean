import SP1Foundations.Word

structure MemoryAccessInShardTimestamp (F : Type) where
  prev_low : F
  diff_low_limb : F

structure MemoryAccessInSharedCols (F : Type) where
  prev_value : Word F
  access_timestamp : MemoryAccessInShardTimestamp F
