import SP1Foundations

--- A Reader that only accesses values of type `T`.
structure RTypeReader where
  op_a : Fin BB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin BB
  op_b : Fin BB
  op_b_memory : MemoryAccessInSharedCols
  op_c : Fin BB
  op_c_memory : MemoryAccessInSharedCols