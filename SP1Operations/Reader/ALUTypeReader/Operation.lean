import SP1Foundations


--- A Reader that only accesses values of type `T`.
structure ALUTypeReader where
  op_a : Fin KB
  op_a_memory : MemoryAccessInSharedCols (Fin KB)
  op_a_0 : Fin KB
  op_b : Fin KB
  op_b_memory : MemoryAccessInSharedCols (Fin KB)
  op_c : Word (Fin KB)
  op_c_memory : MemoryAccessInSharedCols (Fin KB)
  imm_c : Fin KB
