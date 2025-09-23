import SP1Foundations

--- A Reader that only accesses values of type `T`.
structure RTypeReader where
  op_a : Fin KB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin KB
  op_b : Fin KB
  op_b_memory : MemoryAccessInSharedCols
  op_c : Fin KB
  op_c_memory : MemoryAccessInSharedCols
  is_trusted : Fin KB
