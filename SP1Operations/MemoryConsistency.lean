import SP1Foundations

structure MemoryAccessInShardTimestamp where
  prev_low : Fin BB
  diff_low_limb : Fin BB

-- MemoryAccessInSharedCols is parameterized on type `T` because we may want to
-- dynamically enforce that `prev_value` is specifically some width, e.g. U16 or
-- U8, etc.
structure MemoryAccessInSharedCols where
  prev_value : Word (Fin BB)
  access_timestamp : MemoryAccessInShardTimestamp
