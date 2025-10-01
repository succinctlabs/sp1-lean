import SP1Foundations.Word

structure MemoryAccessInShardTimestamp where
  prev_low : Fin KB
  diff_low_limb : Fin KB

structure MemoryAccessInSharedCols where
  prev_value : Word (Fin KB)
  access_timestamp : MemoryAccessInShardTimestamp
