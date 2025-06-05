import SP1Foundations
import SP1Operations.MemoryConsistency

--- A Reader that only accesses values of type `T`.
structure RTypeReader (T : Type) where
  op_a : T 
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T 
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T 
  op_c_memory : MemoryAccessInSharedCols T

namespace RTypeReader 

def b {T : Type} (cols : RTypeReader T) : Word T := cols.op_b_memory.prev_value

def c {T : Type} (cols : RTypeReader T) : Word T := cols.op_c_memory.prev_value

def spec {T : Type}
  (cols : RTypeReader T)
  (shard : BabyBear)
  (clk : BabyBear)
  (pc : BabyBear)
  (opcode : BabyBear)
  (op_a_write_value : Word T)
  (is_real : U1)
  : Prop := sorry

end RTypeReader
