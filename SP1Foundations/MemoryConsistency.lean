import SP1Foundations.Word

structure MemoryAccessInShardTimestamp where
  prev_low : Fin BB
  diff_low_limb : Fin BB

structure MemoryAccessInSharedCols where
  prev_value : Word (Fin BB)
  access_timestamp : MemoryAccessInShardTimestamp
