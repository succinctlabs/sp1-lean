import SP1Foundations

--- A Reader that only accesses values of type `T`.
@[ext]
structure RTypeReader (F : Type) where
  op_a : F
  op_a_memory : MemoryAccessInSharedCols F
  op_a_0 : F
  op_b : F
  op_b_memory : MemoryAccessInSharedCols F
  op_c : F
  op_c_memory : MemoryAccessInSharedCols F
