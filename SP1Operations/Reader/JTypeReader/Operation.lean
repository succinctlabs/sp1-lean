import SP1Foundations

--- A Reader that only accesses values of type `T`.
structure JTypeReader where
  op_a : Fin BB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin BB
  op_b_imm : Word (Fin BB)
  op_c_imm : Word (Fin BB)
