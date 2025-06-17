import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

-- Version 1: RTypeReader parameterized by register indices
structure RTypeReader_v1 (T : Type) where
  rs1 : regidx  -- Source register 1
  rs2 : regidx  -- Source register 2
  rd : regidx   -- Destination register
  op_a : T 
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T 
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T 
  op_c_memory : MemoryAccessInSharedCols T

namespace RTypeReader_v1

def b {T : Type} (cols : RTypeReader_v1 T) : Word T := cols.op_b_memory.prev_value
def c {T : Type} (cols : RTypeReader_v1 T) : Word T := cols.op_c_memory.prev_value

-- Now the read functions are automatically tied to the correct registers
def read_b_constraint
  (cols : RTypeReader_v1 U16)
  : Prop := rX_bits cols.rs1 = pure cols.b.toBV32_U16

def read_c_constraint  
  (cols : RTypeReader_v1 U16)
  : Prop := rX_bits cols.rs2 = pure cols.c.toBV32_U16

-- The spec function can now validate that the registers match the instruction
def spec {T : Type}
  (cols : RTypeReader_v1 T)
  (shard : BabyBear)
  (clk : BabyBear) 
  (pc : BabyBear)
  (opcode : BabyBear)
  (op_a_write_value : Word T)
  (is_real : U1)
  : Prop := 
  -- Automatically enforce register consistency
  cols.read_b_constraint ∧ cols.read_c_constraint ∧ sorry

end RTypeReader_v1