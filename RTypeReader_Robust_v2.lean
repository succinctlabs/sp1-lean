import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions

-- Version 2: Instruction-aware RTypeReader
structure RTypeInstr where
  rd : regidx
  rs1 : regidx  
  rs2 : regidx
  opcode : BabyBear

structure RTypeReader_v2 (T : Type) where
  instr : RTypeInstr
  op_a : T 
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T 
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T 
  op_c_memory : MemoryAccessInSharedCols T

namespace RTypeReader_v2

def b {T : Type} (cols : RTypeReader_v2 T) : Word T := cols.op_b_memory.prev_value
def c {T : Type} (cols : RTypeReader_v2 T) : Word T := cols.op_c_memory.prev_value

-- Register constraints are automatically derived from instruction
def register_constraints
  (cols : RTypeReader_v2 U16)
  : Prop := 
  rX_bits cols.instr.rs1 = pure cols.b.toBV32_U16 ∧ 
  rX_bits cols.instr.rs2 = pure cols.c.toBV32_U16

-- Create from instruction
def from_instruction 
  (instr : RTypeInstr)
  (op_a : T) (op_a_memory : MemoryAccessInSharedCols T) (op_a_0 : T)
  (op_b : T) (op_b_memory : MemoryAccessInSharedCols T)
  (op_c : T) (op_c_memory : MemoryAccessInSharedCols T)
  : RTypeReader_v2 T :=
  ⟨instr, op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩

def spec {T : Type}
  (cols : RTypeReader_v2 T)
  (shard : BabyBear)
  (clk : BabyBear)
  (pc : BabyBear)
  (op_a_write_value : Word T)
  (is_real : U1)
  : Prop := 
  cols.register_constraints ∧ 
  cols.instr.opcode = 0 ∧  -- ADD opcode
  sorry

end RTypeReader_v2