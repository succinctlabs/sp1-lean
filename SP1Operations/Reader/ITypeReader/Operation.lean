import SP1Foundations

structure ITypeReader where
  op_a : Fin BB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin BB
  op_b : Fin BB
  op_b_memory : MemoryAccessInSharedCols
  op_c_imm : Word (Fin BB)