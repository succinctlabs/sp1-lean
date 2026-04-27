import SP1Foundations

--- A Reader that only accesses values of type `T`.
structure JTypeReader where
  op_a : Fin KB
  op_a_memory : MemoryAccessInSharedCols (Fin KB)
  op_a_0 : Fin KB
  op_b_imm : Word (Fin KB)
  op_c_imm : Word (Fin KB)
