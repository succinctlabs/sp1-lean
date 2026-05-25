import SP1Foundations

@[ext]
structure ITypeReader (F : Type) where
  op_a : F
  op_a_memory : MemoryAccessInSharedCols F
  op_a_0 : F
  op_b : F
  op_b_memory : MemoryAccessInSharedCols F
  op_c_imm : Word F
