import SP1Foundations

structure MemoryAccessInShardTimestamp where
  prev_low : BabyBear
  diff_low_limb : BabyBear

-- MemoryAccessInSharedCols is parameterized on type `T` because we may want to
-- dynamically enforce that `prev_value` is specifically some width, e.g. U16 or
-- U8, etc.
structure MemoryAccessInSharedCols where
  prev_value : Word BabyBear
  access_timestamp : MemoryAccessInShardTimestamp
