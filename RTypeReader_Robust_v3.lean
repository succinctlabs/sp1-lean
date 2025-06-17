import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

-- Version 3: Dependent types with proof obligations
structure ValidatedRTypeReader (T : Type) (rs1 rs2 : regidx) where
  op_a : T 
  op_a_memory : MemoryAccessInSharedCols T
  op_a_0 : T
  op_b : T 
  op_b_memory : MemoryAccessInSharedCols T
  op_c : T 
  op_c_memory : MemoryAccessInSharedCols T
  -- Proof obligations built into the type
  h_rs1_matches : rX_bits rs1 = pure op_b_memory.prev_value.toBV32_U16
  h_rs2_matches : rX_bits rs2 = pure op_c_memory.prev_value.toBV32_U16

namespace ValidatedRTypeReader

def b {T : Type} {rs1 rs2 : regidx} (cols : ValidatedRTypeReader T rs1 rs2) : Word T := 
  cols.op_b_memory.prev_value

def c {T : Type} {rs1 rs2 : regidx} (cols : ValidatedRTypeReader T rs1 rs2) : Word T := 
  cols.op_c_memory.prev_value

-- Constructor that requires proof of register consistency
def mk {T : Type} (rs1 rs2 : regidx)
  (op_a : T) (op_a_memory : MemoryAccessInSharedCols T) (op_a_0 : T)
  (op_b : T) (op_b_memory : MemoryAccessInSharedCols T)
  (op_c : T) (op_c_memory : MemoryAccessInSharedCols T)
  (h_rs1 : rX_bits rs1 = pure op_b_memory.prev_value.toBV32_U16)
  (h_rs2 : rX_bits rs2 = pure op_c_memory.prev_value.toBV32_U16)
  : ValidatedRTypeReader T rs1 rs2 :=
  ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, h_rs1, h_rs2⟩

-- The register constraints are automatically satisfied by construction
def register_constraints {T : Type} {rs1 rs2 : regidx} 
  (cols : ValidatedRTypeReader T rs1 rs2) : Prop := 
  cols.h_rs1_matches ∧ cols.h_rs2_matches

def spec {T : Type} {rs1 rs2 : regidx}
  (cols : ValidatedRTypeReader T rs1 rs2)
  (shard : BabyBear)
  (clk : BabyBear)
  (pc : BabyBear)
  (opcode : BabyBear)
  (op_a_write_value : Word T)
  (is_real : U1)
  : Prop := 
  -- Register constraints are automatically satisfied
  cols.register_constraints ∧ sorry

end ValidatedRTypeReader