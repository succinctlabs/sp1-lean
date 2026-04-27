import SP1Foundations

structure ITypeReader where
  op_a : Fin KB
  op_a_memory : MemoryAccessInSharedCols (Fin KB)
  op_a_0 : Fin KB
  op_b : Fin KB
  op_b_memory : MemoryAccessInSharedCols (Fin KB)
  op_c_imm : Word (Fin KB)
