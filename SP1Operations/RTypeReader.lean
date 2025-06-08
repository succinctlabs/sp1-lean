import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

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

def read_b_fun
  (cols : RTypeReader U16)
  (rs : regidx)
  : Prop := rX_bits rs = pure cols.b.toBV32_U16

def read_c_fun
  (cols : RTypeReader U16)
  (rs : regidx)
  : Prop := rX_bits rs = pure cols.c.toBV32_U16

end RTypeReader

structure MemRead (x : Word U16) where
  val : BitVec 32
  h_val : val = x.toBV32_U16
