import SP1Foundations

--- A Reader that only accesses values of type `T`.
@[ext]
structure JTypeReader (F : Type) where
  op_a : F
  op_a_memory : MemoryAccessInSharedCols F
  op_a_0 : F
  op_b_imm : Word F
  op_c_imm : Word F
